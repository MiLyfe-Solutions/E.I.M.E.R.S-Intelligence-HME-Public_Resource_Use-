import V185TrunkScan22Chunk084

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental

namespace V185TrunkScan22Incremental

def tailWord_762005 : List Nat := [1, 3, 2, 1, 1, 1, 4, 2, 1, 6]
def baseStart_762005 : Nat := 118140960795 + 762005 * 2 ^ 59
def prefixEnd_762005 : Nat := 4983230072969 + 3 ^ 40 * 762005 * 2
def baseEnd_762005 : Nat := 260849884086264257088739

theorem tailTrace_762005 : CollatzResearch.WordTrace tailWord_762005 prefixEnd_762005 260849884086264257088739 := by
  unfold tailWord_762005
  simp only [CollatzResearch.WordTrace]
  refine ⟨27792605604393499938127469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18528403736262333292084979 27792605604393499938127469)
  ·
    refine ⟨10422227101647562476797801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27792605604393499938127469 10422227101647562476797801)
    ·
      refine ⟨7816670326235671857598351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10422227101647562476797801 7816670326235671857598351)
      ·
        refine ⟨11725005489353507786397527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7816670326235671857598351 11725005489353507786397527)
        ·
          refine ⟨17587508234030261679596291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11725005489353507786397527 17587508234030261679596291)
          ·
            refine ⟨26381262351045392519394437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17587508234030261679596291 26381262351045392519394437)
            ·
              refine ⟨4946486690821011097386457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 26381262351045392519394437 4946486690821011097386457)
              ·
                refine ⟨3709865018115758323039843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4946486690821011097386457 3709865018115758323039843)
                ·
                  refine ⟨5564797527173637484559765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3709865018115758323039843 5564797527173637484559765)
                  ·
                    refine ⟨260849884086264257088739, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5564797527173637484559765 260849884086264257088739)
                    ·
                      rfl

theorem cell22_762005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 4, 2, 1, 6].length) (baseStart_762005 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_762005 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_762005 prefixEnd_762005 := by exact prefixLift 762005
  have htrace : WordTrace (prefixWord ++ tailWord_762005) baseStart_762005 baseEnd_762005 := by
    simpa [prefixWord, tailWord_762005, baseEnd_762005] using wordTrace_append hprefix tailTrace_762005
  have hstable : (prefixWord ++ tailWord_762005).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_762005).length < 2 ^ (prefixWord ++ tailWord_762005).sum := by decide
  have hdescent : baseEnd_762005 < baseStart_762005 := by decide
  rcases family_descends (prefixWord ++ tailWord_762005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_762129 : List Nat := [1, 2, 2, 1, 1, 5, 3, 2, 1, 4]
def baseStart_762129 : Nat := 118140960795 + 762129 * 2 ^ 59
def prefixEnd_762129 : Nat := 4983230072969 + 3 ^ 40 * 762129 * 2
def baseEnd_762129 : Nat := 260892331820369266988359

theorem tailTrace_762129 : CollatzResearch.WordTrace tailWord_762129 prefixEnd_762129 260892331820369266988359 := by
  unfold tailWord_762129
  simp only [CollatzResearch.WordTrace]
  refine ⟨27797128255944269115641441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18531418837296179410427627 27797128255944269115641441)
  ·
    refine ⟨20847846191958201836731081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27797128255944269115641441 20847846191958201836731081)
    ·
      refine ⟨15635884643968651377548311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20847846191958201836731081 15635884643968651377548311)
      ·
        refine ⟨23453826965952977066322467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15635884643968651377548311 23453826965952977066322467)
        ·
          refine ⟨35180740448929465599483701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23453826965952977066322467 35180740448929465599483701)
          ·
            refine ⟨3298194417087137399951597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 35180740448929465599483701 3298194417087137399951597)
            ·
              refine ⟨1236822906407676524981849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3298194417087137399951597 1236822906407676524981849)
              ·
                refine ⟨927617179805757393736387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1236822906407676524981849 927617179805757393736387)
                ·
                  refine ⟨1391425769708636090604581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 927617179805757393736387 1391425769708636090604581)
                  ·
                    refine ⟨260892331820369266988359, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1391425769708636090604581 260892331820369266988359)
                    ·
                      rfl

theorem cell22_762129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 4].length) (baseStart_762129 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_762129 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_762129 prefixEnd_762129 := by exact prefixLift 762129
  have htrace : WordTrace (prefixWord ++ tailWord_762129) baseStart_762129 baseEnd_762129 := by
    simpa [prefixWord, tailWord_762129, baseEnd_762129] using wordTrace_append hprefix tailTrace_762129
  have hstable : (prefixWord ++ tailWord_762129).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_762129).length < 2 ^ (prefixWord ++ tailWord_762129).sum := by decide
  have hdescent : baseEnd_762129 < baseStart_762129 := by decide
  rcases family_descends (prefixWord ++ tailWord_762129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_762159 : List Nat := [1, 1, 2, 1, 2, 1, 5, 4, 2, 3]
def baseStart_762159 : Nat := 118140960795 + 762159 * 2 ^ 59
def prefixEnd_762159 : Nat := 4983230072969 + 3 ^ 40 * 762159 * 2
def baseEnd_762159 : Nat := 260902601433459188738267

theorem tailTrace_762159 : CollatzResearch.WordTrace tailWord_762159 prefixEnd_762159 260902601433459188738267 := by
  unfold tailWord_762159
  simp only [CollatzResearch.WordTrace]
  refine ⟨27798222445835584239233531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18532148297223722826155687 27798222445835584239233531)
  ·
    refine ⟨41697333668753376358850297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27798222445835584239233531 41697333668753376358850297)
    ·
      refine ⟨31273000251565032269137723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41697333668753376358850297 31273000251565032269137723)
      ·
        refine ⟨46909500377347548403706585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31273000251565032269137723 46909500377347548403706585)
        ·
          refine ⟨35182125283010661302779939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46909500377347548403706585 35182125283010661302779939)
          ·
            refine ⟨52773187924515991954169909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35182125283010661302779939 52773187924515991954169909)
            ·
              refine ⟨4947486367923374245703429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 52773187924515991954169909 4947486367923374245703429)
              ·
                refine ⟨927653693985632671069393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4947486367923374245703429 927653693985632671069393)
                ·
                  refine ⟨695740270489224503302045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 927653693985632671069393 695740270489224503302045)
                  ·
                    refine ⟨260902601433459188738267, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 695740270489224503302045 260902601433459188738267)
                    ·
                      rfl

theorem cell22_762159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 5, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 5, 4, 2, 3].length) (baseStart_762159 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_762159 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_762159 prefixEnd_762159 := by exact prefixLift 762159
  have htrace : WordTrace (prefixWord ++ tailWord_762159) baseStart_762159 baseEnd_762159 := by
    simpa [prefixWord, tailWord_762159, baseEnd_762159] using wordTrace_append hprefix tailTrace_762159
  have hstable : (prefixWord ++ tailWord_762159).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_762159).length < 2 ^ (prefixWord ++ tailWord_762159).sum := by decide
  have hdescent : baseEnd_762159 < baseStart_762159 := by decide
  rcases family_descends (prefixWord ++ tailWord_762159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_762161 : List Nat := [1, 2, 2, 3, 4, 1, 1, 4, 4]
def baseStart_762161 : Nat := 118140960795 + 762161 * 2 ^ 59
def prefixEnd_762161 : Nat := 4983230072969 + 3 ^ 40 * 762161 * 2
def baseEnd_762161 : Nat := 86967762024777283396087

theorem tailTrace_762161 : CollatzResearch.WordTrace tailWord_762161 prefixEnd_762161 86967762024777283396087 := by
  unfold tailWord_762161
  simp only [CollatzResearch.WordTrace]
  refine ⟨27798295391828338580806337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18532196927885559053870891 27798295391828338580806337)
  ·
    refine ⟨20848721543871253935604753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27798295391828338580806337 20848721543871253935604753)
    ·
      refine ⟨15636541157903440451703565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20848721543871253935604753 15636541157903440451703565)
      ·
        refine ⟨5863702934213790169388837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15636541157903440451703565 5863702934213790169388837)
        ·
          refine ⟨1099444300165085656760407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5863702934213790169388837 1099444300165085656760407)
          ·
            refine ⟨1649166450247628485140611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1099444300165085656760407 1649166450247628485140611)
            ·
              refine ⟨2473749675371442727710917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1649166450247628485140611 2473749675371442727710917)
              ·
                refine ⟨463828064132145511445797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2473749675371442727710917 463828064132145511445797)
                ·
                  refine ⟨86967762024777283396087, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 463828064132145511445797 86967762024777283396087)
                  ·
                    rfl

theorem cell22_762161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 4, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 4, 1, 1, 4, 4].length) (baseStart_762161 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_762161 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_762161 prefixEnd_762161 := by exact prefixLift 762161
  have htrace : WordTrace (prefixWord ++ tailWord_762161) baseStart_762161 baseEnd_762161 := by
    simpa [prefixWord, tailWord_762161, baseEnd_762161] using wordTrace_append hprefix tailTrace_762161
  have hstable : (prefixWord ++ tailWord_762161).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_762161).length < 2 ^ (prefixWord ++ tailWord_762161).sum := by decide
  have hdescent : baseEnd_762161 < baseStart_762161 := by decide
  rcases family_descends (prefixWord ++ tailWord_762161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_762217 : List Nat := [1, 2, 1, 1, 1, 3, 5, 1, 7]
def baseStart_762217 : Nat := 118140960795 + 762217 * 2 ^ 59
def prefixEnd_762217 : Nat := 4983230072969 + 3 ^ 40 * 762217 * 2
def baseEnd_762217 : Nat := 86974152006255456929363

theorem tailTrace_762217 : CollatzResearch.WordTrace tailWord_762217 prefixEnd_762217 86974152006255456929363 := by
  unfold tailWord_762217
  simp only [CollatzResearch.WordTrace]
  refine ⟨27800337879625460144844905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18533558586416973429896603 27800337879625460144844905)
  ·
    refine ⟨20850253409719095108633679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27800337879625460144844905 20850253409719095108633679)
    ·
      refine ⟨31275380114578642662950519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20850253409719095108633679 31275380114578642662950519)
      ·
        refine ⟨46913070171867963994425779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31275380114578642662950519 46913070171867963994425779)
        ·
          refine ⟨70369605257801945991638669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46913070171867963994425779 70369605257801945991638669)
          ·
            refine ⟨26388601971675729746864501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 70369605257801945991638669 26388601971675729746864501)
            ·
              refine ⟨2473931434844599663768547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 26388601971675729746864501 2473931434844599663768547)
              ·
                refine ⟨3710897152266899495652821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2473931434844599663768547 3710897152266899495652821)
                ·
                  refine ⟨86974152006255456929363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3710897152266899495652821 86974152006255456929363)
                  ·
                    rfl

theorem cell22_762217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 5, 1, 7].length) (baseStart_762217 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_762217 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_762217 prefixEnd_762217 := by exact prefixLift 762217
  have htrace : WordTrace (prefixWord ++ tailWord_762217) baseStart_762217 baseEnd_762217 := by
    simpa [prefixWord, tailWord_762217, baseEnd_762217] using wordTrace_append hprefix tailTrace_762217
  have hstable : (prefixWord ++ tailWord_762217).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_762217).length < 2 ^ (prefixWord ++ tailWord_762217).sum := by decide
  have hdescent : baseEnd_762217 < baseStart_762217 := by decide
  rcases family_descends (prefixWord ++ tailWord_762217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_762221 : List Nat := [1, 5, 1, 1, 1, 2, 4, 1, 3, 3]
def baseStart_762221 : Nat := 118140960795 + 762221 * 2 ^ 59
def prefixEnd_762221 : Nat := 4983230072969 + 3 ^ 40 * 762221 * 2
def baseEnd_762221 : Nat := 260923825300511693688077

theorem tailTrace_762221 : CollatzResearch.WordTrace tailWord_762221 prefixEnd_762221 260923825300511693688077 := by
  unfold tailWord_762221
  simp only [CollatzResearch.WordTrace]
  refine ⟨27800483771610968827990517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18533655847740645885327011 27800483771610968827990517)
  ·
    refine ⟨2606295353588528327624111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 27800483771610968827990517 2606295353588528327624111)
    ·
      refine ⟨3909443030382792491436167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2606295353588528327624111 3909443030382792491436167)
      ·
        refine ⟨5864164545574188737154251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3909443030382792491436167 5864164545574188737154251)
        ·
          refine ⟨8796246818361283105731377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5864164545574188737154251 8796246818361283105731377)
          ·
            refine ⟨6597185113770962329298533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8796246818361283105731377 6597185113770962329298533)
            ·
              refine ⟨1236972208832055436743475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6597185113770962329298533 1236972208832055436743475)
              ·
                refine ⟨1855458313248083155115213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1236972208832055436743475 1855458313248083155115213)
                ·
                  refine ⟨695796867468031183168205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1855458313248083155115213 695796867468031183168205)
                  ·
                    refine ⟨260923825300511693688077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 695796867468031183168205 260923825300511693688077)
                    ·
                      rfl

theorem cell22_762221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 4, 1, 3, 3].length) (baseStart_762221 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_762221 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_762221 prefixEnd_762221 := by exact prefixLift 762221
  have htrace : WordTrace (prefixWord ++ tailWord_762221) baseStart_762221 baseEnd_762221 := by
    simpa [prefixWord, tailWord_762221, baseEnd_762221] using wordTrace_append hprefix tailTrace_762221
  have hstable : (prefixWord ++ tailWord_762221).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_762221).length < 2 ^ (prefixWord ++ tailWord_762221).sum := by decide
  have hdescent : baseEnd_762221 < baseStart_762221 := by decide
  rcases family_descends (prefixWord ++ tailWord_762221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_762285 : List Nat := [1, 5, 2, 2, 2, 2, 2, 1, 5]
def baseStart_762285 : Nat := 118140960795 + 762285 * 2 ^ 59
def prefixEnd_762285 : Nat := 4983230072969 + 3 ^ 40 * 762285 * 2
def baseEnd_762285 : Nat := 86981911269478953362627

theorem tailTrace_762285 : CollatzResearch.WordTrace tailWord_762285 prefixEnd_762285 86981911269478953362627 := by
  unfold tailWord_762285
  simp only [CollatzResearch.WordTrace]
  refine ⟨27802818043379107758320309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18535212028919405172213539 27802818043379107758320309)
  ·
    refine ⟨2606514191566791352342529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 27802818043379107758320309 2606514191566791352342529)
    ·
      refine ⟨1954885643675093514256897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2606514191566791352342529 1954885643675093514256897)
      ·
        refine ⟨1466164232756320135692673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1954885643675093514256897 1466164232756320135692673)
        ·
          refine ⟨1099623174567240101769505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1466164232756320135692673 1099623174567240101769505)
          ·
            refine ⟨824717380925430076327129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1099623174567240101769505 824717380925430076327129)
            ·
              refine ⟨618538035694072557245347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 824717380925430076327129 618538035694072557245347)
              ·
                refine ⟨927807053541108835868021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 618538035694072557245347 927807053541108835868021)
                ·
                  refine ⟨86981911269478953362627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 927807053541108835868021 86981911269478953362627)
                  ·
                    rfl

theorem cell22_762285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 2, 2, 2, 1, 5].length) (baseStart_762285 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_762285 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_762285 prefixEnd_762285 := by exact prefixLift 762285
  have htrace : WordTrace (prefixWord ++ tailWord_762285) baseStart_762285 baseEnd_762285 := by
    simpa [prefixWord, tailWord_762285, baseEnd_762285] using wordTrace_append hprefix tailTrace_762285
  have hstable : (prefixWord ++ tailWord_762285).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_762285).length < 2 ^ (prefixWord ++ tailWord_762285).sum := by decide
  have hdescent : baseEnd_762285 < baseStart_762285 := by decide
  rcases family_descends (prefixWord ++ tailWord_762285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_762324 : List Nat := [2, 4, 1, 2, 2, 11]
def baseStart_762324 : Nat := 118140960795 + 762324 * 2 ^ 59
def prefixEnd_762324 : Nat := 4983230072969 + 3 ^ 40 * 762324 * 2
def baseEnd_762324 : Nat := 3221717090190787140281

theorem tailTrace_762324 : CollatzResearch.WordTrace tailWord_762324 prefixEnd_762324 3221717090190787140281 := by
  unfold tailWord_762324
  simp only [CollatzResearch.WordTrace]
  refine ⟨13902120245118908709495013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18536160326825211612660017 13902120245118908709495013)
  ·
    refine ⟨2606647545959795383030315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 13902120245118908709495013 2606647545959795383030315)
    ·
      refine ⟨3909971318939693074545473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2606647545959795383030315 3909971318939693074545473)
      ·
        refine ⟨2932478489204769805909105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3909971318939693074545473 2932478489204769805909105)
        ·
          refine ⟨2199358866903577354431829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2932478489204769805909105 2199358866903577354431829)
          ·
            refine ⟨3221717090190787140281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 2199358866903577354431829 3221717090190787140281)
            ·
              rfl

theorem cell22_762324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 11].length) (baseStart_762324 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_762324 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_762324 prefixEnd_762324 := by exact prefixLift 762324
  have htrace : WordTrace (prefixWord ++ tailWord_762324) baseStart_762324 baseEnd_762324 := by
    simpa [prefixWord, tailWord_762324, baseEnd_762324] using wordTrace_append hprefix tailTrace_762324
  have hstable : (prefixWord ++ tailWord_762324).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_762324).length < 2 ^ (prefixWord ++ tailWord_762324).sum := by decide
  have hdescent : baseEnd_762324 < baseStart_762324 := by decide
  rcases family_descends (prefixWord ++ tailWord_762324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_762373 : List Nat := [1, 3, 1, 1, 2, 2, 3, 5, 1, 3]
def baseStart_762373 : Nat := 118140960795 + 762373 * 2 ^ 59
def prefixEnd_762373 : Nat := 4983230072969 + 3 ^ 40 * 762373 * 2
def baseEnd_762373 : Nat := 260975858006833963887611

theorem tailTrace_762373 : CollatzResearch.WordTrace tailWord_762373 prefixEnd_762373 260975858006833963887611 := by
  unfold tailWord_762373
  simp only [CollatzResearch.WordTrace]
  refine ⟨27806027667060298787523773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18537351778040199191682515 27806027667060298787523773)
  ·
    refine ⟨10427260375147612045321415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27806027667060298787523773 10427260375147612045321415)
    ·
      refine ⟨15640890562721418067982123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10427260375147612045321415 15640890562721418067982123)
      ·
        refine ⟨23461335844082127101973185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15640890562721418067982123 23461335844082127101973185)
        ·
          refine ⟨17596001883061595326479889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23461335844082127101973185 17596001883061595326479889)
          ·
            refine ⟨13197001412296196494859917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17596001883061595326479889 13197001412296196494859917)
            ·
              refine ⟨4948875529611073685572469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13197001412296196494859917 4948875529611073685572469)
              ·
                refine ⟨463957080901038158022419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 4948875529611073685572469 463957080901038158022419)
                ·
                  refine ⟨695935621351557237033629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 463957080901038158022419 695935621351557237033629)
                  ·
                    refine ⟨260975858006833963887611, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 695935621351557237033629 260975858006833963887611)
                    ·
                      rfl

theorem cell22_762373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 3, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 3, 5, 1, 3].length) (baseStart_762373 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_762373 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_762373 prefixEnd_762373 := by exact prefixLift 762373
  have htrace : WordTrace (prefixWord ++ tailWord_762373) baseStart_762373 baseEnd_762373 := by
    simpa [prefixWord, tailWord_762373, baseEnd_762373] using wordTrace_append hprefix tailTrace_762373
  have hstable : (prefixWord ++ tailWord_762373).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_762373).length < 2 ^ (prefixWord ++ tailWord_762373).sum := by decide
  have hdescent : baseEnd_762373 < baseStart_762373 := by decide
  rcases family_descends (prefixWord ++ tailWord_762373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_762403 : List Nat := [1, 1, 1, 4, 4, 2, 3, 1, 5]
def baseStart_762403 : Nat := 118140960795 + 762403 * 2 ^ 59
def prefixEnd_762403 : Nat := 4983230072969 + 3 ^ 40 * 762403 * 2
def baseEnd_762403 : Nat := 86995375873307961879173

theorem tailTrace_762403 : CollatzResearch.WordTrace tailWord_762403 prefixEnd_762403 86995375873307961879173 := by
  unfold tailWord_762403
  simp only [CollatzResearch.WordTrace]
  refine ⟨27807121856951613911115863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18538081237967742607410575 27807121856951613911115863)
  ·
    refine ⟨41710682785427420866673795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27807121856951613911115863 41710682785427420866673795)
    ·
      refine ⟨62566024178141131300010693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41710682785427420866673795 62566024178141131300010693)
      ·
        refine ⟨11731129533401462118752005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 62566024178141131300010693 11731129533401462118752005)
        ·
          refine ⟨2199586787512774147266001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11731129533401462118752005 2199586787512774147266001)
          ·
            refine ⟨1649690090634580610449501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2199586787512774147266001 1649690090634580610449501)
            ·
              refine ⟨618633783987967728918563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1649690090634580610449501 618633783987967728918563)
              ·
                refine ⟨927950675981951593377845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 618633783987967728918563 927950675981951593377845)
                ·
                  refine ⟨86995375873307961879173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 927950675981951593377845 86995375873307961879173)
                  ·
                    rfl

theorem cell22_762403_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 2, 3, 1, 5].length) (baseStart_762403 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_762403 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_762403 prefixEnd_762403 := by exact prefixLift 762403
  have htrace : WordTrace (prefixWord ++ tailWord_762403) baseStart_762403 baseEnd_762403 := by
    simpa [prefixWord, tailWord_762403, baseEnd_762403] using wordTrace_append hprefix tailTrace_762403
  have hstable : (prefixWord ++ tailWord_762403).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_762403).length < 2 ^ (prefixWord ++ tailWord_762403).sum := by decide
  have hdescent : baseEnd_762403 < baseStart_762403 := by decide
  rcases family_descends (prefixWord ++ tailWord_762403) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_762416 : List Nat := [2, 1, 1, 1, 2, 3, 3, 4, 1, 4]
def baseStart_762416 : Nat := 118140960795 + 762416 * 2 ^ 59
def prefixEnd_762416 : Nat := 4983230072969 + 3 ^ 40 * 762416 * 2
def baseEnd_762416 : Nat := 260990577785596185062479

theorem tailTrace_762416 : CollatzResearch.WordTrace tailWord_762416 prefixEnd_762416 260990577785596185062479 := by
  unfold tailWord_762416
  simp only [CollatzResearch.WordTrace]
  refine ⟨13903798002952258565669551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18538397337269678087559401 13903798002952258565669551)
  ·
    refine ⟨20855697004428387848504327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13903798002952258565669551 20855697004428387848504327)
    ·
      refine ⟨31283545506642581772756491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20855697004428387848504327 31283545506642581772756491)
      ·
        refine ⟨46925318259963872659134737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31283545506642581772756491 46925318259963872659134737)
        ·
          refine ⟨35193988694972904494351053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46925318259963872659134737 35193988694972904494351053)
          ·
            refine ⟨13197745760614839185381645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35193988694972904494351053 13197745760614839185381645)
            ·
              refine ⟨4949154660230564694518117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13197745760614839185381645 4949154660230564694518117)
              ·
                refine ⟨927966498793230880222147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4949154660230564694518117 927966498793230880222147)
                ·
                  refine ⟨1391949748189846320333221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 927966498793230880222147 1391949748189846320333221)
                  ·
                    refine ⟨260990577785596185062479, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1391949748189846320333221 260990577785596185062479)
                    ·
                      rfl

theorem cell22_762416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 3, 4, 1, 4].length) (baseStart_762416 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_762416 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_762416 prefixEnd_762416 := by exact prefixLift 762416
  have htrace : WordTrace (prefixWord ++ tailWord_762416) baseStart_762416 baseEnd_762416 := by
    simpa [prefixWord, tailWord_762416, baseEnd_762416] using wordTrace_append hprefix tailTrace_762416
  have hstable : (prefixWord ++ tailWord_762416).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_762416).length < 2 ^ (prefixWord ++ tailWord_762416).sum := by decide
  have hdescent : baseEnd_762416 < baseStart_762416 := by decide
  rcases family_descends (prefixWord ++ tailWord_762416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_762433 : List Nat := [1, 2, 5, 1, 1, 2, 2, 3, 1, 4]
def baseStart_762433 : Nat := 118140960795 + 762433 * 2 ^ 59
def prefixEnd_762433 : Nat := 4983230072969 + 3 ^ 40 * 762433 * 2
def baseEnd_762433 : Nat := 260996397233013807387427

theorem tailTrace_762433 : CollatzResearch.WordTrace tailWord_762433 prefixEnd_762433 260996397233013807387427 := by
  unfold tailWord_762433
  simp only [CollatzResearch.WordTrace]
  refine ⟨27808216046842929034707953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18538810697895286023138635 27808216046842929034707953)
  ·
    refine ⟨20856162035132196776030965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27808216046842929034707953 20856162035132196776030965)
    ·
      refine ⟨1955265190793643447752903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 20856162035132196776030965 1955265190793643447752903)
      ·
        refine ⟨2932897786190465171629355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1955265190793643447752903 2932897786190465171629355)
        ·
          refine ⟨4399346679285697757444033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2932897786190465171629355 4399346679285697757444033)
          ·
            refine ⟨3299510009464273318083025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4399346679285697757444033 3299510009464273318083025)
            ·
              refine ⟨2474632507098204988562269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3299510009464273318083025 2474632507098204988562269)
              ·
                refine ⟨927987190161826870710851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2474632507098204988562269 927987190161826870710851)
                ·
                  refine ⟨1391980785242740306066277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 927987190161826870710851 1391980785242740306066277)
                  ·
                    refine ⟨260996397233013807387427, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1391980785242740306066277 260996397233013807387427)
                    ·
                      rfl

theorem cell22_762433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 2, 2, 3, 1, 4].length) (baseStart_762433 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_762433 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_762433 prefixEnd_762433 := by exact prefixLift 762433
  have htrace : WordTrace (prefixWord ++ tailWord_762433) baseStart_762433 baseEnd_762433 := by
    simpa [prefixWord, tailWord_762433, baseEnd_762433] using wordTrace_append hprefix tailTrace_762433
  have hstable : (prefixWord ++ tailWord_762433).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_762433).length < 2 ^ (prefixWord ++ tailWord_762433).sum := by decide
  have hdescent : baseEnd_762433 < baseStart_762433 := by decide
  rcases family_descends (prefixWord ++ tailWord_762433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_762478 : List Nat := [4, 1, 2, 2, 2, 1, 1, 3, 2, 4]
def baseStart_762478 : Nat := 118140960795 + 762478 * 2 ^ 59
def prefixEnd_762478 : Nat := 4983230072969 + 3 ^ 40 * 762478 * 2
def baseEnd_762478 : Nat := 261011801652648690012289

theorem tailTrace_762478 : CollatzResearch.WordTrace tailWord_762478 prefixEnd_762478 261011801652648690012289 := by
  unfold tailWord_762478
  simp only [CollatzResearch.WordTrace]
  refine ⟨3476232166459987715012011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 18539904887786601146730725 3476232166459987715012011)
  ·
    refine ⟨5214348249689981572518017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3476232166459987715012011 5214348249689981572518017)
    ·
      refine ⟨3910761187267486179388513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5214348249689981572518017 3910761187267486179388513)
      ·
        refine ⟨2933070890450614634541385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3910761187267486179388513 2933070890450614634541385)
        ·
          refine ⟨2199803167837960975906039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2933070890450614634541385 2199803167837960975906039)
          ·
            refine ⟨3299704751756941463859059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2199803167837960975906039 3299704751756941463859059)
            ·
              refine ⟨4949557127635412195788589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3299704751756941463859059 4949557127635412195788589)
              ·
                refine ⟨1856083922863279573420721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4949557127635412195788589 1856083922863279573420721)
                ·
                  refine ⟨1392062942147459680065541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1856083922863279573420721 1392062942147459680065541)
                  ·
                    refine ⟨261011801652648690012289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1392062942147459680065541 261011801652648690012289)
                    ·
                      rfl

theorem cell22_762478_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 1, 1, 3, 2, 4].length) (baseStart_762478 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_762478 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_762478 prefixEnd_762478 := by exact prefixLift 762478
  have htrace : WordTrace (prefixWord ++ tailWord_762478) baseStart_762478 baseEnd_762478 := by
    simpa [prefixWord, tailWord_762478, baseEnd_762478] using wordTrace_append hprefix tailTrace_762478
  have hstable : (prefixWord ++ tailWord_762478).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_762478).length < 2 ^ (prefixWord ++ tailWord_762478).sum := by decide
  have hdescent : baseEnd_762478 < baseStart_762478 := by decide
  rcases family_descends (prefixWord ++ tailWord_762478) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_762491 : List Nat := [1, 1, 1, 1, 1, 4, 2, 1, 7, 3]
def baseStart_762491 : Nat := 118140960795 + 762491 * 2 ^ 59
def prefixEnd_762491 : Nat := 4983230072969 + 3 ^ 40 * 762491 * 2
def baseEnd_762491 : Nat := 261016251818320989437249

theorem tailTrace_762491 : CollatzResearch.WordTrace tailWord_762491 prefixEnd_762491 261016251818320989437249 := by
  unfold tailWord_762491
  simp only [CollatzResearch.WordTrace]
  refine ⟨27810331480632804940319327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18540220987088536626879551 27810331480632804940319327)
  ·
    refine ⟨41715497220949207410478991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27810331480632804940319327 41715497220949207410478991)
    ·
      refine ⟨62573245831423811115718487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41715497220949207410478991 62573245831423811115718487)
      ·
        refine ⟨93859868747135716673577731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62573245831423811115718487 93859868747135716673577731)
        ·
          refine ⟨140789803120703575010366597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 93859868747135716673577731 140789803120703575010366597)
          ·
            refine ⟨26398088085131920314443737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 140789803120703575010366597 26398088085131920314443737)
            ·
              refine ⟨19798566063848940235832803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26398088085131920314443737 19798566063848940235832803)
              ·
                refine ⟨29697849095773410353749205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19798566063848940235832803 29697849095773410353749205)
                ·
                  refine ⟨696043338182189305165997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 29697849095773410353749205 696043338182189305165997)
                  ·
                    refine ⟨261016251818320989437249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 696043338182189305165997 261016251818320989437249)
                    ·
                      rfl

theorem cell22_762491_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 2, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 2, 1, 7, 3].length) (baseStart_762491 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_762491 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_762491 prefixEnd_762491 := by exact prefixLift 762491
  have htrace : WordTrace (prefixWord ++ tailWord_762491) baseStart_762491 baseEnd_762491 := by
    simpa [prefixWord, tailWord_762491, baseEnd_762491] using wordTrace_append hprefix tailTrace_762491
  have hstable : (prefixWord ++ tailWord_762491).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_762491).length < 2 ^ (prefixWord ++ tailWord_762491).sum := by decide
  have hdescent : baseEnd_762491 < baseStart_762491 := by decide
  rcases family_descends (prefixWord ++ tailWord_762491) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_762521 : List Nat := [1, 2, 1, 2, 1, 2, 3, 5, 5]
def baseStart_762521 : Nat := 118140960795 + 762521 * 2 ^ 59
def prefixEnd_762521 : Nat := 4983230072969 + 3 ^ 40 * 762521 * 2
def baseEnd_762521 : Nat := 87008840477136970395719

theorem tailTrace_762521 : CollatzResearch.WordTrace tailWord_762521 prefixEnd_762521 87008840477136970395719 := by
  unfold tailWord_762521
  simp only [CollatzResearch.WordTrace]
  refine ⟨27811425670524120063911417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18540950447016080042607611 27811425670524120063911417)
  ·
    refine ⟨20858569252893090047933563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27811425670524120063911417 20858569252893090047933563)
    ·
      refine ⟨31287853879339635071900345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20858569252893090047933563 31287853879339635071900345)
      ·
        refine ⟨23465890409504726303925259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31287853879339635071900345 23465890409504726303925259)
        ·
          refine ⟨35198835614257089455887889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23465890409504726303925259 35198835614257089455887889)
          ·
            refine ⟨26399126710692817091915917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35198835614257089455887889 26399126710692817091915917)
            ·
              refine ⟨9899672516509806409468469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26399126710692817091915917 9899672516509806409468469)
              ·
                refine ⟨928094298422794350887669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 9899672516509806409468469 928094298422794350887669)
                ·
                  refine ⟨87008840477136970395719, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 928094298422794350887669 87008840477136970395719)
                  ·
                    rfl

theorem cell22_762521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 3, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 3, 5, 5].length) (baseStart_762521 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_762521 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_762521 prefixEnd_762521 := by exact prefixLift 762521
  have htrace : WordTrace (prefixWord ++ tailWord_762521) baseStart_762521 baseEnd_762521 := by
    simpa [prefixWord, tailWord_762521, baseEnd_762521] using wordTrace_append hprefix tailTrace_762521
  have hstable : (prefixWord ++ tailWord_762521).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_762521).length < 2 ^ (prefixWord ++ tailWord_762521).sum := by decide
  have hdescent : baseEnd_762521 < baseStart_762521 := by decide
  rcases family_descends (prefixWord ++ tailWord_762521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_762628 : List Nat := [2, 3, 2, 2, 1, 1, 4, 7]
def baseStart_762628 : Nat := 118140960795 + 762628 * 2 ^ 59
def prefixEnd_762628 : Nat := 4983230072969 + 3 ^ 40 * 762628 * 2
def baseEnd_762628 : Nat := 29007016635344255417981

theorem tailTrace_762628 : CollatzResearch.WordTrace tailWord_762628 prefixEnd_762628 29007016635344255417981 := by
  unfold tailWord_762628
  simp only [CollatzResearch.WordTrace]
  refine ⟨13907664140568238669028269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18543552187424318225371025 13907664140568238669028269)
  ·
    refine ⟨5215374052713089500885601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13907664140568238669028269 5215374052713089500885601)
    ·
      refine ⟨3911530539534817125664201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5215374052713089500885601 3911530539534817125664201)
      ·
        refine ⟨2933647904651112844248151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3911530539534817125664201 2933647904651112844248151)
        ·
          refine ⟨4400471856976669266372227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2933647904651112844248151 4400471856976669266372227)
          ·
            refine ⟨6600707785465003899558341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4400471856976669266372227 6600707785465003899558341)
            ·
              refine ⟨1237632709774688231167189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6600707785465003899558341 1237632709774688231167189)
              ·
                refine ⟨29007016635344255417981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1237632709774688231167189 29007016635344255417981)
                ·
                  rfl

theorem cell22_762628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 4, 7].length) (baseStart_762628 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_762628 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_762628 prefixEnd_762628 := by exact prefixLift 762628
  have htrace : WordTrace (prefixWord ++ tailWord_762628) baseStart_762628 baseEnd_762628 := by
    simpa [prefixWord, tailWord_762628, baseEnd_762628] using wordTrace_append hprefix tailTrace_762628
  have hstable : (prefixWord ++ tailWord_762628).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_762628).length < 2 ^ (prefixWord ++ tailWord_762628).sum := by decide
  have hdescent : baseEnd_762628 < baseStart_762628 := by decide
  rcases family_descends (prefixWord ++ tailWord_762628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_762632 : List Nat := [2, 1, 3, 2, 2, 2, 4, 1, 2, 3]
def baseStart_762632 : Nat := 118140960795 + 762632 * 2 ^ 59
def prefixEnd_762632 : Nat := 4983230072969 + 3 ^ 40 * 762632 * 2
def baseEnd_762632 : Nat := 261064518999843621661817

theorem tailTrace_762632 : CollatzResearch.WordTrace tailWord_762632 prefixEnd_762632 261064518999843621661817 := by
  unfold tailWord_762632
  simp only [CollatzResearch.WordTrace]
  refine ⟨13907737086560993010601075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18543649448747990680801433 13907737086560993010601075)
  ·
    refine ⟨20861605629841489515901613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13907737086560993010601075 20861605629841489515901613)
    ·
      refine ⟨7823102111190558568463105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20861605629841489515901613 7823102111190558568463105)
      ·
        refine ⟨5867326583392918926347329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7823102111190558568463105 5867326583392918926347329)
        ·
          refine ⟨4400494937544689194760497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5867326583392918926347329 4400494937544689194760497)
          ·
            refine ⟨3300371203158516896070373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4400494937544689194760497 3300371203158516896070373)
            ·
              refine ⟨618819600592221918013195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3300371203158516896070373 618819600592221918013195)
              ·
                refine ⟨928229400888332877019793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 618819600592221918013195 928229400888332877019793)
                ·
                  refine ⟨696172050666249657764845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 928229400888332877019793 696172050666249657764845)
                  ·
                    refine ⟨261064518999843621661817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 696172050666249657764845 261064518999843621661817)
                    ·
                      rfl

theorem cell22_762632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 2, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 2, 4, 1, 2, 3].length) (baseStart_762632 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_762632 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_762632 prefixEnd_762632 := by exact prefixLift 762632
  have htrace : WordTrace (prefixWord ++ tailWord_762632) baseStart_762632 baseEnd_762632 := by
    simpa [prefixWord, tailWord_762632, baseEnd_762632] using wordTrace_append hprefix tailTrace_762632
  have hstable : (prefixWord ++ tailWord_762632).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_762632).length < 2 ^ (prefixWord ++ tailWord_762632).sum := by decide
  have hdescent : baseEnd_762632 < baseStart_762632 := by decide
  rcases family_descends (prefixWord ++ tailWord_762632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_762643 : List Nat := [1, 1, 1, 2, 1, 3, 4, 1, 5, 3]
def baseStart_762643 : Nat := 118140960795 + 762643 * 2 ^ 59
def prefixEnd_762643 : Nat := 4983230072969 + 3 ^ 40 * 762643 * 2
def baseEnd_762643 : Nat := 261068284524643259636783

theorem tailTrace_762643 : CollatzResearch.WordTrace tailWord_762643 prefixEnd_762643 261068284524643259636783 := by
  unfold tailWord_762643
  simp only [CollatzResearch.WordTrace]
  refine ⟨27815875376082134899852583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18543916917388089933235055 27815875376082134899852583)
  ·
    refine ⟨41723813064123202349778875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27815875376082134899852583 41723813064123202349778875)
    ·
      refine ⟨62585719596184803524668313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41723813064123202349778875 62585719596184803524668313)
      ·
        refine ⟨46939289697138602643501235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62585719596184803524668313 46939289697138602643501235)
        ·
          refine ⟨70408934545707903965251853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46939289697138602643501235 70408934545707903965251853)
          ·
            refine ⟨26403350454640463986969445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 70408934545707903965251853 26403350454640463986969445)
            ·
              refine ⟨4950628210245086997556771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 26403350454640463986969445 4950628210245086997556771)
              ·
                refine ⟨7425942315367630496335157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4950628210245086997556771 7425942315367630496335157)
                ·
                  refine ⟨696182092065715359031421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 7425942315367630496335157 696182092065715359031421)
                  ·
                    refine ⟨261068284524643259636783, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 696182092065715359031421 261068284524643259636783)
                    ·
                      rfl

theorem cell22_762643_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 4, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 4, 1, 5, 3].length) (baseStart_762643 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_762643 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_762643 prefixEnd_762643 := by exact prefixLift 762643
  have htrace : WordTrace (prefixWord ++ tailWord_762643) baseStart_762643 baseEnd_762643 := by
    simpa [prefixWord, tailWord_762643, baseEnd_762643] using wordTrace_append hprefix tailTrace_762643
  have hstable : (prefixWord ++ tailWord_762643).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_762643).length < 2 ^ (prefixWord ++ tailWord_762643).sum := by decide
  have hdescent : baseEnd_762643 < baseStart_762643 := by decide
  rcases family_descends (prefixWord ++ tailWord_762643) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_762720 : List Nat := [2, 1, 1, 3, 3, 1, 3, 3, 1, 4]
def baseStart_762720 : Nat := 118140960795 + 762720 * 2 ^ 59
def prefixEnd_762720 : Nat := 4983230072969 + 3 ^ 40 * 762720 * 2
def baseEnd_762720 : Nat := 261094643198240725461547

theorem tailTrace_762720 : CollatzResearch.WordTrace tailWord_762720 prefixEnd_762720 261094643198240725461547 := by
  unfold tailWord_762720
  simp only [CollatzResearch.WordTrace]
  refine ⟨13909341898401588525202807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18545789197868784700270409 13909341898401588525202807)
  ·
    refine ⟨20864012847602382787804211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13909341898401588525202807 20864012847602382787804211)
    ·
      refine ⟨31296019271403574181706317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20864012847602382787804211 31296019271403574181706317)
      ·
        refine ⟨11736007226776340318139869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31296019271403574181706317 11736007226776340318139869)
        ·
          refine ⟨4401002710041127619302451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11736007226776340318139869 4401002710041127619302451)
          ·
            refine ⟨6601504065061691428953677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4401002710041127619302451 6601504065061691428953677)
            ·
              refine ⟨2475564024398134285857629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6601504065061691428953677 2475564024398134285857629)
              ·
                refine ⟨928336509149300357196611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2475564024398134285857629 928336509149300357196611)
                ·
                  refine ⟨1392504763723950535794917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 928336509149300357196611 1392504763723950535794917)
                  ·
                    refine ⟨261094643198240725461547, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1392504763723950535794917 261094643198240725461547)
                    ·
                      rfl

theorem cell22_762720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 3, 3, 1, 4].length) (baseStart_762720 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_762720 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_762720 prefixEnd_762720 := by exact prefixLift 762720
  have htrace : WordTrace (prefixWord ++ tailWord_762720) baseStart_762720 baseEnd_762720 := by
    simpa [prefixWord, tailWord_762720, baseEnd_762720] using wordTrace_append hprefix tailTrace_762720
  have hstable : (prefixWord ++ tailWord_762720).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_762720).length < 2 ^ (prefixWord ++ tailWord_762720).sum := by decide
  have hdescent : baseEnd_762720 < baseStart_762720 := by decide
  rcases family_descends (prefixWord ++ tailWord_762720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_762793 : List Nat := [1, 2, 1, 1, 1, 1, 6, 1, 2, 6]
def baseStart_762793 : Nat := 118140960795 + 762793 * 2 ^ 59
def prefixEnd_762793 : Nat := 4983230072969 + 3 ^ 40 * 762793 * 2
def baseEnd_762793 : Nat := 261119632590092868386323

theorem tailTrace_762793 : CollatzResearch.WordTrace tailWord_762793 prefixEnd_762793 261119632590092868386323 := by
  unfold tailWord_762793
  simp only [CollatzResearch.WordTrace]
  refine ⟨27821346325538710517813033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18547564217025807011875355 27821346325538710517813033)
  ·
    refine ⟨20866009744154032888359775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27821346325538710517813033 20866009744154032888359775)
    ·
      refine ⟨31299014616231049332539663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20866009744154032888359775 31299014616231049332539663)
      ·
        refine ⟨46948521924346573998809495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31299014616231049332539663 46948521924346573998809495)
        ·
          refine ⟨70422782886519860998214243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46948521924346573998809495 70422782886519860998214243)
          ·
            refine ⟨105634174329779791497321365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 70422782886519860998214243 105634174329779791497321365)
            ·
              refine ⟨4951601921708427726436939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 105634174329779791497321365 4951601921708427726436939)
              ·
                refine ⟨7427402882562641589655409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4951601921708427726436939 7427402882562641589655409)
                ·
                  refine ⟨5570552161921981192241557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7427402882562641589655409 5570552161921981192241557)
                  ·
                    refine ⟨261119632590092868386323, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5570552161921981192241557 261119632590092868386323)
                    ·
                      rfl

theorem cell22_762793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 6, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 6, 1, 2, 6].length) (baseStart_762793 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_762793 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_762793 prefixEnd_762793 := by exact prefixLift 762793
  have htrace : WordTrace (prefixWord ++ tailWord_762793) baseStart_762793 baseEnd_762793 := by
    simpa [prefixWord, tailWord_762793, baseEnd_762793] using wordTrace_append hprefix tailTrace_762793
  have hstable : (prefixWord ++ tailWord_762793).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_762793).length < 2 ^ (prefixWord ++ tailWord_762793).sum := by decide
  have hdescent : baseEnd_762793 < baseStart_762793 := by decide
  rcases family_descends (prefixWord ++ tailWord_762793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_762801 : List Nat := [1, 2, 2, 4, 3, 2, 2, 1, 2, 3]
def baseStart_762801 : Nat := 118140960795 + 762801 * 2 ^ 59
def prefixEnd_762801 : Nat := 4983230072969 + 3 ^ 40 * 762801 * 2
def baseEnd_762801 : Nat := 261122371153583514186299

theorem tailTrace_762801 : CollatzResearch.WordTrace tailWord_762801 prefixEnd_762801 261122371153583514186299 := by
  unfold tailWord_762801
  simp only [CollatzResearch.WordTrace]
  refine ⟨27821638109509727884104257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18547758739673151922736171 27821638109509727884104257)
  ·
    refine ⟨20866228582132295913078193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27821638109509727884104257 20866228582132295913078193)
    ·
      refine ⟨15649671436599221934808645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20866228582132295913078193 15649671436599221934808645)
      ·
        refine ⟨2934313394362354112776621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 15649671436599221934808645 2934313394362354112776621)
        ·
          refine ⟨1100367522885882792291233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2934313394362354112776621 1100367522885882792291233)
          ·
            refine ⟨825275642164412094218425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1100367522885882792291233 825275642164412094218425)
            ·
              refine ⟨618956731623309070663819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 825275642164412094218425 618956731623309070663819)
              ·
                refine ⟨928435097434963605995729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 618956731623309070663819 928435097434963605995729)
                ·
                  refine ⟨696326323076222704496797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 928435097434963605995729 696326323076222704496797)
                  ·
                    refine ⟨261122371153583514186299, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 696326323076222704496797 261122371153583514186299)
                    ·
                      rfl

theorem cell22_762801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 3, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 3, 2, 2, 1, 2, 3].length) (baseStart_762801 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_762801 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_762801 prefixEnd_762801 := by exact prefixLift 762801
  have htrace : WordTrace (prefixWord ++ tailWord_762801) baseStart_762801 baseEnd_762801 := by
    simpa [prefixWord, tailWord_762801, baseEnd_762801] using wordTrace_append hprefix tailTrace_762801
  have hstable : (prefixWord ++ tailWord_762801).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_762801).length < 2 ^ (prefixWord ++ tailWord_762801).sum := by decide
  have hdescent : baseEnd_762801 < baseStart_762801 := by decide
  rcases family_descends (prefixWord ++ tailWord_762801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_762842 : List Nat := [3, 1, 1, 2, 4, 2, 2, 2, 5]
def baseStart_762842 : Nat := 118140960795 + 762842 * 2 ^ 59
def prefixEnd_762842 : Nat := 4983230072969 + 3 ^ 40 * 762842 * 2
def baseEnd_762842 : Nat := 87045468763824357970391

theorem tailTrace_762842 : CollatzResearch.WordTrace tailWord_762842 prefixEnd_762842 87045468763824357970391 := by
  unfold tailWord_762842
  simp only [CollatzResearch.WordTrace]
  refine ⟨6955783375590297971586695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18548755668240794590897853 6955783375590297971586695)
  ·
    refine ⟨10433675063385446957380043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6955783375590297971586695 10433675063385446957380043)
    ·
      refine ⟨15650512595078170436070065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10433675063385446957380043 15650512595078170436070065)
      ·
        refine ⟨11737884446308627827052549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15650512595078170436070065 11737884446308627827052549)
        ·
          refine ⟨2200853333682867717572353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11737884446308627827052549 2200853333682867717572353)
          ·
            refine ⟨1650640000262150788179265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2200853333682867717572353 1650640000262150788179265)
            ·
              refine ⟨1237980000196613091134449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1650640000262150788179265 1237980000196613091134449)
              ·
                refine ⟨928485000147459818350837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1237980000196613091134449 928485000147459818350837)
                ·
                  refine ⟨87045468763824357970391, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 928485000147459818350837 87045468763824357970391)
                  ·
                    rfl

theorem cell22_762842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 2, 2, 2, 5].length) (baseStart_762842 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_762842 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_762842 prefixEnd_762842 := by exact prefixLift 762842
  have htrace : WordTrace (prefixWord ++ tailWord_762842) baseStart_762842 baseEnd_762842 := by
    simpa [prefixWord, tailWord_762842, baseEnd_762842] using wordTrace_append hprefix tailTrace_762842
  have hstable : (prefixWord ++ tailWord_762842).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_762842).length < 2 ^ (prefixWord ++ tailWord_762842).sum := by decide
  have hdescent : baseEnd_762842 < baseStart_762842 := by decide
  rcases family_descends (prefixWord ++ tailWord_762842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_762885 : List Nat := [1, 3, 1, 1, 2, 3, 1, 4, 1, 5]
def baseStart_762885 : Nat := 118140960795 + 762885 * 2 ^ 59
def prefixEnd_762885 : Nat := 4983230072969 + 3 ^ 40 * 762885 * 2
def baseEnd_762885 : Nat := 261151126070235295086041

theorem tailTrace_762885 : CollatzResearch.WordTrace tailWord_762885 prefixEnd_762885 261151126070235295086041 := by
  unfold tailWord_762885
  simp only [CollatzResearch.WordTrace]
  refine ⟨27824701841205410230162109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18549801227470273486774739 27824701841205410230162109)
  ·
    refine ⟨10434263190452028836310791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27824701841205410230162109 10434263190452028836310791)
    ·
      refine ⟨15651394785678043254466187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10434263190452028836310791 15651394785678043254466187)
      ·
        refine ⟨23477092178517064881699281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15651394785678043254466187 23477092178517064881699281)
        ·
          refine ⟨17607819133887798661274461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23477092178517064881699281 17607819133887798661274461)
          ·
            refine ⟨6602932175207924497977923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17607819133887798661274461 6602932175207924497977923)
            ·
              refine ⟨9904398262811886746966885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6602932175207924497977923 9904398262811886746966885)
              ·
                refine ⟨1857074674277228765056291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9904398262811886746966885 1857074674277228765056291)
                ·
                  refine ⟨2785612011415843147584437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1857074674277228765056291 2785612011415843147584437)
                  ·
                    refine ⟨261151126070235295086041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2785612011415843147584437 261151126070235295086041)
                    ·
                      rfl

theorem cell22_762885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 1, 4, 1, 5].length) (baseStart_762885 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_762885 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_762885 prefixEnd_762885 := by exact prefixLift 762885
  have htrace : WordTrace (prefixWord ++ tailWord_762885) baseStart_762885 baseEnd_762885 := by
    simpa [prefixWord, tailWord_762885, baseEnd_762885] using wordTrace_append hprefix tailTrace_762885
  have hstable : (prefixWord ++ tailWord_762885).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_762885).length < 2 ^ (prefixWord ++ tailWord_762885).sum := by decide
  have hdescent : baseEnd_762885 < baseStart_762885 := by decide
  rcases family_descends (prefixWord ++ tailWord_762885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_762919 : List Nat := [1, 1, 7, 1, 1, 1, 3, 1, 1, 5]
def baseStart_762919 : Nat := 118140960795 + 762919 * 2 ^ 59
def prefixEnd_762919 : Nat := 4983230072969 + 3 ^ 40 * 762919 * 2
def baseEnd_762919 : Nat := 261162764965070539735937

theorem tailTrace_762919 : CollatzResearch.WordTrace tailWord_762919 prefixEnd_762919 261162764965070539735937 := by
  unfold tailWord_762919
  simp only [CollatzResearch.WordTrace]
  refine ⟨27825941923082234036899811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18550627948721489357933207 27825941923082234036899811)
  ·
    refine ⟨41738912884623351055349717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27825941923082234036899811 41738912884623351055349717)
    ·
      refine ⟨978255770733359790359759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 41738912884623351055349717 978255770733359790359759)
      ·
        refine ⟨1467383656100039685539639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 978255770733359790359759 1467383656100039685539639)
        ·
          refine ⟨2201075484150059528309459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1467383656100039685539639 2201075484150059528309459)
          ·
            refine ⟨3301613226225089292464189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2201075484150059528309459 3301613226225089292464189)
            ·
              refine ⟨1238104959834408484674071, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3301613226225089292464189 1238104959834408484674071)
              ·
                refine ⟨1857157439751612727011107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1238104959834408484674071 1857157439751612727011107)
                ·
                  refine ⟨2785736159627419090516661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1857157439751612727011107 2785736159627419090516661)
                  ·
                    refine ⟨261162764965070539735937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2785736159627419090516661 261162764965070539735937)
                    ·
                      rfl

theorem cell22_762919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 1, 3, 1, 1, 5].length) (baseStart_762919 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_762919 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_762919 prefixEnd_762919 := by exact prefixLift 762919
  have htrace : WordTrace (prefixWord ++ tailWord_762919) baseStart_762919 baseEnd_762919 := by
    simpa [prefixWord, tailWord_762919, baseEnd_762919] using wordTrace_append hprefix tailTrace_762919
  have hstable : (prefixWord ++ tailWord_762919).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_762919).length < 2 ^ (prefixWord ++ tailWord_762919).sum := by decide
  have hdescent : baseEnd_762919 < baseStart_762919 := by decide
  rcases family_descends (prefixWord ++ tailWord_762919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_762930 : List Nat := [3, 2, 1, 1, 2, 2, 1, 1, 2, 7]
def baseStart_762930 : Nat := 118140960795 + 762930 * 2 ^ 59
def prefixEnd_762930 : Nat := 4983230072969 + 3 ^ 40 * 762930 * 2
def baseEnd_762930 : Nat := 261166530489870177710903

theorem tailTrace_762930 : CollatzResearch.WordTrace tailWord_762930 prefixEnd_762930 261166530489870177710903 := by
  unfold tailWord_762930
  simp only [CollatzResearch.WordTrace]
  refine ⟨6956585781510595728887561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18550895417361588610366829 6956585781510595728887561)
  ·
    refine ⟨5217439336132946796665671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6956585781510595728887561 5217439336132946796665671)
    ·
      refine ⟨7826159004199420194998507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5217439336132946796665671 7826159004199420194998507)
      ·
        refine ⟨11739238506299130292497761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7826159004199420194998507 11739238506299130292497761)
        ·
          refine ⟨8804428879724347719373321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11739238506299130292497761 8804428879724347719373321)
          ·
            refine ⟨6603321659793260789529991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8804428879724347719373321 6603321659793260789529991)
            ·
              refine ⟨9904982489689891184294987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6603321659793260789529991 9904982489689891184294987)
              ·
                refine ⟨14857473734534836776442481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9904982489689891184294987 14857473734534836776442481)
                ·
                  refine ⟨11143105300901127582331861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14857473734534836776442481 11143105300901127582331861)
                  ·
                    refine ⟨261166530489870177710903, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 11143105300901127582331861 261166530489870177710903)
                    ·
                      rfl

theorem cell22_762930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 1, 1, 2, 7].length) (baseStart_762930 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_762930 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_762930 prefixEnd_762930 := by exact prefixLift 762930
  have htrace : WordTrace (prefixWord ++ tailWord_762930) baseStart_762930 baseEnd_762930 := by
    simpa [prefixWord, tailWord_762930, baseEnd_762930] using wordTrace_append hprefix tailTrace_762930
  have hstable : (prefixWord ++ tailWord_762930).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_762930).length < 2 ^ (prefixWord ++ tailWord_762930).sum := by decide
  have hdescent : baseEnd_762930 < baseStart_762930 := by decide
  rcases family_descends (prefixWord ++ tailWord_762930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_762964 : List Nat := [2, 4, 1, 1, 1, 1, 5, 1, 3, 3]
def baseStart_762964 : Nat := 118140960795 + 762964 * 2 ^ 59
def prefixEnd_762964 : Nat := 4983230072969 + 3 ^ 40 * 762964 * 2
def baseEnd_762964 : Nat := 261178169384705422360799

theorem tailTrace_762964 : CollatzResearch.WordTrace tailWord_762964 prefixEnd_762964 261178169384705422360799 := by
  unfold tailWord_762964
  simp only [CollatzResearch.WordTrace]
  refine ⟨13913791603959603361143973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18551722138612804481525297 13913791603959603361143973)
  ·
    refine ⟨2608835925742425630214495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 13913791603959603361143973 2608835925742425630214495)
    ·
      refine ⟨3913253888613638445321743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2608835925742425630214495 3913253888613638445321743)
      ·
        refine ⟨5869880832920457667982615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3913253888613638445321743 5869880832920457667982615)
        ·
          refine ⟨8804821249380686501973923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5869880832920457667982615 8804821249380686501973923)
          ·
            refine ⟨13207231874071029752960885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8804821249380686501973923 13207231874071029752960885)
            ·
              refine ⟨1238177988194159039340083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 13207231874071029752960885 1238177988194159039340083)
              ·
                refine ⟨1857266982291238559010125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1238177988194159039340083 1857266982291238559010125)
                ·
                  refine ⟨696475118359214459628797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1857266982291238559010125 696475118359214459628797)
                  ·
                    refine ⟨261178169384705422360799, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 696475118359214459628797 261178169384705422360799)
                    ·
                      rfl

theorem cell22_762964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 5, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 5, 1, 3, 3].length) (baseStart_762964 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_762964 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_762964 prefixEnd_762964 := by exact prefixLift 762964
  have htrace : WordTrace (prefixWord ++ tailWord_762964) baseStart_762964 baseEnd_762964 := by
    simpa [prefixWord, tailWord_762964, baseEnd_762964] using wordTrace_append hprefix tailTrace_762964
  have hstable : (prefixWord ++ tailWord_762964).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_762964).length < 2 ^ (prefixWord ++ tailWord_762964).sum := by decide
  have hdescent : baseEnd_762964 < baseStart_762964 := by decide
  rcases family_descends (prefixWord ++ tailWord_762964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_762966 : List Nat := [5, 2, 2, 1, 2, 1, 2, 7]
def baseStart_762966 : Nat := 118140960795 + 762966 * 2 ^ 59
def prefixEnd_762966 : Nat := 4983230072969 + 3 ^ 40 * 762966 * 2
def baseEnd_762966 : Nat := 29019872669508675978977

theorem tailTrace_762966 : CollatzResearch.WordTrace tailWord_762966 prefixEnd_762966 29019872669508675978977 := by
  unfold tailWord_762966
  simp only [CollatzResearch.WordTrace]
  refine ⟨1739228509619497566491297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 18551770769274640709240501 1739228509619497566491297)
  ·
    refine ⟨1304421382214623174868473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1739228509619497566491297 1304421382214623174868473)
    ·
      refine ⟨978316036660967381151355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1304421382214623174868473 978316036660967381151355)
      ·
        refine ⟨1467474054991451071727033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 978316036660967381151355 1467474054991451071727033)
        ·
          refine ⟨1100605541243588303795275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1467474054991451071727033 1100605541243588303795275)
          ·
            refine ⟨1650908311865382455692913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1100605541243588303795275 1650908311865382455692913)
            ·
              refine ⟨1238181233899036841769685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1650908311865382455692913 1238181233899036841769685)
              ·
                refine ⟨29019872669508675978977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1238181233899036841769685 29019872669508675978977)
                ·
                  rfl

theorem cell22_762966_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 2, 1, 2, 7].length) (baseStart_762966 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_762966 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_762966 prefixEnd_762966 := by exact prefixLift 762966
  have htrace : WordTrace (prefixWord ++ tailWord_762966) baseStart_762966 baseEnd_762966 := by
    simpa [prefixWord, tailWord_762966, baseEnd_762966] using wordTrace_append hprefix tailTrace_762966
  have hstable : (prefixWord ++ tailWord_762966).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_762966).length < 2 ^ (prefixWord ++ tailWord_762966).sum := by decide
  have hdescent : baseEnd_762966 < baseStart_762966 := by decide
  rcases family_descends (prefixWord ++ tailWord_762966) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_762975 : List Nat := [1, 1, 2, 3, 1, 1, 4, 1, 1, 7]
def baseStart_762975 : Nat := 118140960795 + 762975 * 2 ^ 59
def prefixEnd_762975 : Nat := 4983230072969 + 3 ^ 40 * 762975 * 2
def baseEnd_762975 : Nat := 261181934909505060335765

theorem tailTrace_762975 : CollatzResearch.WordTrace tailWord_762975 prefixEnd_762975 261181934909505060335765 := by
  unfold tailWord_762975
  simp only [CollatzResearch.WordTrace]
  refine ⟨27827984410879355600938379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18551989607252903733958919 27827984410879355600938379)
  ·
    refine ⟨41741976616319033401407569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27827984410879355600938379 41741976616319033401407569)
    ·
      refine ⟨31306482462239275051055677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41741976616319033401407569 31306482462239275051055677)
      ·
        refine ⟨11739930923339728144145879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31306482462239275051055677 11739930923339728144145879)
        ·
          refine ⟨17609896385009592216218819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11739930923339728144145879 17609896385009592216218819)
          ·
            refine ⟨26414844577514388324328229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17609896385009592216218819 26414844577514388324328229)
            ·
              refine ⟨4952783358283947810811543, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 26414844577514388324328229 4952783358283947810811543)
              ·
                refine ⟨7429175037425921716217315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4952783358283947810811543 7429175037425921716217315)
                ·
                  refine ⟨11143762556138882574325973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7429175037425921716217315 11143762556138882574325973)
                  ·
                    refine ⟨261181934909505060335765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 11143762556138882574325973 261181934909505060335765)
                    ·
                      rfl

theorem cell22_762975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 4, 1, 1, 7].length) (baseStart_762975 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_762975 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_762975 prefixEnd_762975 := by exact prefixLift 762975
  have htrace : WordTrace (prefixWord ++ tailWord_762975) baseStart_762975 baseEnd_762975 := by
    simpa [prefixWord, tailWord_762975, baseEnd_762975] using wordTrace_append hprefix tailTrace_762975
  have hstable : (prefixWord ++ tailWord_762975).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_762975).length < 2 ^ (prefixWord ++ tailWord_762975).sum := by decide
  have hdescent : baseEnd_762975 < baseStart_762975 := by decide
  rcases family_descends (prefixWord ++ tailWord_762975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_763039 : List Nat := [1, 1, 2, 6, 2, 1, 1, 2, 6]
def baseStart_763039 : Nat := 118140960795 + 763039 * 2 ^ 59
def prefixEnd_763039 : Nat := 4983230072969 + 3 ^ 40 * 763039 * 2
def baseEnd_763039 : Nat := 87067947805810075578523

theorem tailTrace_763039 : CollatzResearch.WordTrace tailWord_763039 prefixEnd_763039 87067947805810075578523 := by
  unfold tailWord_763039
  simp only [CollatzResearch.WordTrace]
  refine ⟨27830318682647494531268171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18553545788431663020845447 27830318682647494531268171)
  ·
    refine ⟨41745478023971241796902257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27830318682647494531268171 41745478023971241796902257)
    ·
      refine ⟨31309108517978431347676693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41745478023971241796902257 31309108517978431347676693)
      ·
        refine ⟨1467614461780238969422345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 31309108517978431347676693 1467614461780238969422345)
        ·
          refine ⟨1100710846335179227066759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1467614461780238969422345 1100710846335179227066759)
          ·
            refine ⟨1651066269502768840600139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1100710846335179227066759 1651066269502768840600139)
            ·
              refine ⟨2476599404254153260900209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1651066269502768840600139 2476599404254153260900209)
              ·
                refine ⟨1857449553190614945675157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2476599404254153260900209 1857449553190614945675157)
                ·
                  refine ⟨87067947805810075578523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1857449553190614945675157 87067947805810075578523)
                  ·
                    rfl

theorem cell22_763039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 2, 1, 1, 2, 6].length) (baseStart_763039 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_763039 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_763039 prefixEnd_763039 := by exact prefixLift 763039
  have htrace : WordTrace (prefixWord ++ tailWord_763039) baseStart_763039 baseEnd_763039 := by
    simpa [prefixWord, tailWord_763039, baseEnd_763039] using wordTrace_append hprefix tailTrace_763039
  have hstable : (prefixWord ++ tailWord_763039).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_763039).length < 2 ^ (prefixWord ++ tailWord_763039).sum := by decide
  have hdescent : baseEnd_763039 < baseStart_763039 := by decide
  rcases family_descends (prefixWord ++ tailWord_763039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_763052 : List Nat := [2, 2, 1, 1, 1, 1, 1, 7, 2, 4]
def baseStart_763052 : Nat := 118140960795 + 763052 * 2 ^ 59
def prefixEnd_763052 : Nat := 4983230072969 + 3 ^ 40 * 763052 * 2
def baseEnd_763052 : Nat := 261208293583102526160529

theorem tailTrace_763052 : CollatzResearch.WordTrace tailWord_763052 prefixEnd_763052 261208293583102526160529 := by
  unfold tailWord_763052
  simp only [CollatzResearch.WordTrace]
  refine ⟨13915396415800198875745705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18553861887733598500994273 13915396415800198875745705)
  ·
    refine ⟨10436547311850149156809279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13915396415800198875745705 10436547311850149156809279)
    ·
      refine ⟨15654820967775223735213919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10436547311850149156809279 15654820967775223735213919)
      ·
        refine ⟨23482231451662835602820879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15654820967775223735213919 23482231451662835602820879)
        ·
          refine ⟨35223347177494253404231319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23482231451662835602820879 35223347177494253404231319)
          ·
            refine ⟨52835020766241380106346979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35223347177494253404231319 52835020766241380106346979)
            ·
              refine ⟨79252531149362070159520469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52835020766241380106346979 79252531149362070159520469)
              ·
                refine ⟨1857481198813173519363761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 79252531149362070159520469 1857481198813173519363761)
                ·
                  refine ⟨1393110899109880139522821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1857481198813173519363761 1393110899109880139522821)
                  ·
                    refine ⟨261208293583102526160529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1393110899109880139522821 261208293583102526160529)
                    ·
                      rfl

theorem cell22_763052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 2, 4].length) (baseStart_763052 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_763052 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_763052 prefixEnd_763052 := by exact prefixLift 763052
  have htrace : WordTrace (prefixWord ++ tailWord_763052) baseStart_763052 baseEnd_763052 := by
    simpa [prefixWord, tailWord_763052, baseEnd_763052] using wordTrace_append hprefix tailTrace_763052
  have hstable : (prefixWord ++ tailWord_763052).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_763052).length < 2 ^ (prefixWord ++ tailWord_763052).sum := by decide
  have hdescent : baseEnd_763052 < baseStart_763052 := by decide
  rcases family_descends (prefixWord ++ tailWord_763052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_763112 : List Nat := [2, 1, 4, 1, 2, 1, 1, 1, 9]
def baseStart_763112 : Nat := 118140960795 + 763112 * 2 ^ 59
def prefixEnd_763112 : Nat := 4983230072969 + 3 ^ 40 * 763112 * 2
def baseEnd_763112 : Nat := 87076277603094123220115

theorem tailTrace_763112 : CollatzResearch.WordTrace tailWord_763112 prefixEnd_763112 87076277603094123220115 := by
  unfold tailWord_763112
  simp only [CollatzResearch.WordTrace]
  refine ⟨13916490605691513999337795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18555320807588685332450393 13916490605691513999337795)
  ·
    refine ⟨20874735908537270999006693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13916490605691513999337795 20874735908537270999006693)
    ·
      refine ⟨3914012982850738312313755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 20874735908537270999006693 3914012982850738312313755)
      ·
        refine ⟨5871019474276107468470633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3914012982850738312313755 5871019474276107468470633)
        ·
          refine ⟨4403264605707080601352975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5871019474276107468470633 4403264605707080601352975)
          ·
            refine ⟨6604896908560620902029463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4403264605707080601352975 6604896908560620902029463)
            ·
              refine ⟨9907345362840931353044195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6604896908560620902029463 9907345362840931353044195)
              ·
                refine ⟨14861018044261397029566293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9907345362840931353044195 14861018044261397029566293)
                ·
                  refine ⟨87076277603094123220115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 14861018044261397029566293 87076277603094123220115)
                  ·
                    rfl

theorem cell22_763112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 1, 1, 9].length) (baseStart_763112 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_763112 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_763112 prefixEnd_763112 := by exact prefixLift 763112
  have htrace : WordTrace (prefixWord ++ tailWord_763112) baseStart_763112 baseEnd_763112 := by
    simpa [prefixWord, tailWord_763112, baseEnd_763112] using wordTrace_append hprefix tailTrace_763112
  have hstable : (prefixWord ++ tailWord_763112).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_763112).length < 2 ^ (prefixWord ++ tailWord_763112).sum := by decide
  have hdescent : baseEnd_763112 < baseStart_763112 := by decide
  rcases family_descends (prefixWord ++ tailWord_763112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_763157 : List Nat := [1, 3, 2, 1, 2, 1, 1, 3, 8]
def baseStart_763157 : Nat := 118140960795 + 763157 * 2 ^ 59
def prefixEnd_763157 : Nat := 4983230072969 + 3 ^ 40 * 763157 * 2
def baseEnd_763157 : Nat := 87081412409639084095069

theorem tailTrace_763157 : CollatzResearch.WordTrace tailWord_763157 prefixEnd_763157 87081412409639084095069 := by
  unfold tailWord_763157
  simp only [CollatzResearch.WordTrace]
  refine ⟨27834622496220000684063725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18556414997480000456042483 27834622496220000684063725)
  ·
    refine ⟨10437983436082500256523897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27834622496220000684063725 10437983436082500256523897)
    ·
      refine ⟨7828487577061875192392923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10437983436082500256523897 7828487577061875192392923)
      ·
        refine ⟨11742731365592812788589385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7828487577061875192392923 11742731365592812788589385)
        ·
          refine ⟨8807048524194609591442039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11742731365592812788589385 8807048524194609591442039)
          ·
            refine ⟨13210572786291914387163059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8807048524194609591442039 13210572786291914387163059)
            ·
              refine ⟨19815859179437871580744589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13210572786291914387163059 19815859179437871580744589)
              ·
                refine ⟨7430947192289201842779221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19815859179437871580744589 7430947192289201842779221)
                ·
                  refine ⟨87081412409639084095069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 7430947192289201842779221 87081412409639084095069)
                  ·
                    rfl

theorem cell22_763157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 1, 3, 8].length) (baseStart_763157 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_763157 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_763157 prefixEnd_763157 := by exact prefixLift 763157
  have htrace : WordTrace (prefixWord ++ tailWord_763157) baseStart_763157 baseEnd_763157 := by
    simpa [prefixWord, tailWord_763157, baseEnd_763157] using wordTrace_append hprefix tailTrace_763157
  have hstable : (prefixWord ++ tailWord_763157).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_763157).length < 2 ^ (prefixWord ++ tailWord_763157).sum := by decide
  have hdescent : baseEnd_763157 < baseStart_763157 := by decide
  rcases family_descends (prefixWord ++ tailWord_763157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_763159 : List Nat := [1, 1, 3, 4, 1, 1, 3, 1, 3, 4]
def baseStart_763159 : Nat := 118140960795 + 763159 * 2 ^ 59
def prefixEnd_763159 : Nat := 4983230072969 + 3 ^ 40 * 763159 * 2
def baseEnd_763159 : Nat := 261244921869789913735201

theorem tailTrace_763159 : CollatzResearch.WordTrace tailWord_763159 prefixEnd_763159 261244921869789913735201 := by
  unfold tailWord_763159
  simp only [CollatzResearch.WordTrace]
  refine ⟨27834695442212755025636531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18556463628141836683757687 27834695442212755025636531)
  ·
    refine ⟨41752043163319132538454797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27834695442212755025636531 41752043163319132538454797)
    ·
      refine ⟨15657016186244674701920549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 41752043163319132538454797 15657016186244674701920549)
      ·
        refine ⟨2935690534920876506610103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 15657016186244674701920549 2935690534920876506610103)
        ·
          refine ⟨4403535802381314759915155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2935690534920876506610103 4403535802381314759915155)
          ·
            refine ⟨6605303703571972139872733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4403535802381314759915155 6605303703571972139872733)
            ·
              refine ⟨2476988888839489552452275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6605303703571972139872733 2476988888839489552452275)
              ·
                refine ⟨3715483333259234328678413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2476988888839489552452275 3715483333259234328678413)
                ·
                  refine ⟨1393306249972212873254405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3715483333259234328678413 1393306249972212873254405)
                  ·
                    refine ⟨261244921869789913735201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1393306249972212873254405 261244921869789913735201)
                    ·
                      rfl

theorem cell22_763159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 3, 1, 3, 4].length) (baseStart_763159 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_763159 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_763159 prefixEnd_763159 := by exact prefixLift 763159
  have htrace : WordTrace (prefixWord ++ tailWord_763159) baseStart_763159 baseEnd_763159 := by
    simpa [prefixWord, tailWord_763159, baseEnd_763159] using wordTrace_append hprefix tailTrace_763159
  have hstable : (prefixWord ++ tailWord_763159).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_763159).length < 2 ^ (prefixWord ++ tailWord_763159).sum := by decide
  have hdescent : baseEnd_763159 < baseStart_763159 := by decide
  rcases family_descends (prefixWord ++ tailWord_763159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_763219 : List Nat := [1, 1, 1, 2, 1, 1, 9, 6]
def baseStart_763219 : Nat := 118140960795 + 763219 * 2 ^ 59
def prefixEnd_763219 : Nat := 4983230072969 + 3 ^ 40 * 763219 * 2
def baseEnd_763219 : Nat := 29029495677329973026113

theorem tailTrace_763219 : CollatzResearch.WordTrace tailWord_763219 prefixEnd_763219 29029495677329973026113 := by
  unfold tailWord_763219
  simp only [CollatzResearch.WordTrace]
  refine ⟨27836883821995385272820711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18557922547996923515213807 27836883821995385272820711)
  ·
    refine ⟨41755325732993077909231067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27836883821995385272820711 41755325732993077909231067)
    ·
      refine ⟨62632988599489616863846601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41755325732993077909231067 62632988599489616863846601)
      ·
        refine ⟨46974741449617212647884951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62632988599489616863846601 46974741449617212647884951)
        ·
          refine ⟨70462112174425818971827427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46974741449617212647884951 70462112174425818971827427)
          ·
            refine ⟨105693168261638728457741141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 70462112174425818971827427 105693168261638728457741141)
            ·
              refine ⟨619295907783039424557077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 105693168261638728457741141 619295907783039424557077)
              ·
                refine ⟨29029495677329973026113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 619295907783039424557077 29029495677329973026113)
                ·
                  rfl

theorem cell22_763219_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 9, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 9, 6].length) (baseStart_763219 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_763219 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_763219 prefixEnd_763219 := by exact prefixLift 763219
  have htrace : WordTrace (prefixWord ++ tailWord_763219) baseStart_763219 baseEnd_763219 := by
    simpa [prefixWord, tailWord_763219, baseEnd_763219] using wordTrace_append hprefix tailTrace_763219
  have hstable : (prefixWord ++ tailWord_763219).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_763219).length < 2 ^ (prefixWord ++ tailWord_763219).sum := by decide
  have hdescent : baseEnd_763219 < baseStart_763219 := by decide
  rcases family_descends (prefixWord ++ tailWord_763219) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_763221 : List Nat := [1, 3, 2, 2, 3, 1, 3, 1, 2, 4]
def baseStart_763221 : Nat := 118140960795 + 763221 * 2 ^ 59
def prefixEnd_763221 : Nat := 4983230072969 + 3 ^ 40 * 763221 * 2
def baseEnd_763221 : Nat := 261266145736842418685011

theorem tailTrace_763221 : CollatzResearch.WordTrace tailWord_763221 prefixEnd_763221 261266145736842418685011 := by
  unfold tailWord_763221
  simp only [CollatzResearch.WordTrace]
  refine ⟨27836956767988139614393517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18557971178658759742929011 27836956767988139614393517)
  ·
    refine ⟨10438858787995552355397569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27836956767988139614393517 10438858787995552355397569)
    ·
      refine ⟨7829144090996664266548177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10438858787995552355397569 7829144090996664266548177)
      ·
        refine ⟨5871858068247498199911133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7829144090996664266548177 5871858068247498199911133)
        ·
          refine ⟨2201946775592811824966675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5871858068247498199911133 2201946775592811824966675)
          ·
            refine ⟨3302920163389217737450013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2201946775592811824966675 3302920163389217737450013)
            ·
              refine ⟨1238595061270956651543755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3302920163389217737450013 1238595061270956651543755)
              ·
                refine ⟨1857892591906434977315633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1238595061270956651543755 1857892591906434977315633)
                ·
                  refine ⟨1393419443929826232986725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1857892591906434977315633 1393419443929826232986725)
                  ·
                    refine ⟨261266145736842418685011, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1393419443929826232986725 261266145736842418685011)
                    ·
                      rfl

theorem cell22_763221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 1, 3, 1, 2, 4].length) (baseStart_763221 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_763221 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_763221 prefixEnd_763221 := by exact prefixLift 763221
  have htrace : WordTrace (prefixWord ++ tailWord_763221) baseStart_763221 baseEnd_763221 := by
    simpa [prefixWord, tailWord_763221, baseEnd_763221] using wordTrace_append hprefix tailTrace_763221
  have hstable : (prefixWord ++ tailWord_763221).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_763221).length < 2 ^ (prefixWord ++ tailWord_763221).sum := by decide
  have hdescent : baseEnd_763221 < baseStart_763221 := by decide
  rcases family_descends (prefixWord ++ tailWord_763221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_763240 : List Nat := [2, 1, 4, 2, 3, 2, 1, 2, 2, 3]
def baseStart_763240 : Nat := 118140960795 + 763240 * 2 ^ 59
def prefixEnd_763240 : Nat := 4983230072969 + 3 ^ 40 * 763240 * 2
def baseEnd_763240 : Nat := 261272649825132702459953

theorem tailTrace_763240 : CollatzResearch.WordTrace tailWord_763240 prefixEnd_763240 261272649825132702459953 := by
  unfold tailWord_763240
  simp only [CollatzResearch.WordTrace]
  refine ⟨13918824877459652929667587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18558433169946203906223449 13918824877459652929667587)
  ·
    refine ⟨20878237316189479394501381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13918824877459652929667587 20878237316189479394501381)
    ·
      refine ⟨3914669496785527386469009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 20878237316189479394501381 3914669496785527386469009)
      ·
        refine ⟨2936002122589145539851757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3914669496785527386469009 2936002122589145539851757)
        ·
          refine ⟨1101000795970929577444409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2936002122589145539851757 1101000795970929577444409)
          ·
            refine ⟨825750596978197183083307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1101000795970929577444409 825750596978197183083307)
            ·
              refine ⟨1238625895467295774624961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 825750596978197183083307 1238625895467295774624961)
              ·
                refine ⟨928969421600471830968721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1238625895467295774624961 928969421600471830968721)
                ·
                  refine ⟨696727066200353873226541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 928969421600471830968721 696727066200353873226541)
                  ·
                    refine ⟨261272649825132702459953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 696727066200353873226541 261272649825132702459953)
                    ·
                      rfl

theorem cell22_763240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 3, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 3, 2, 1, 2, 2, 3].length) (baseStart_763240 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_763240 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_763240 prefixEnd_763240 := by exact prefixLift 763240
  have htrace : WordTrace (prefixWord ++ tailWord_763240) baseStart_763240 baseEnd_763240 := by
    simpa [prefixWord, tailWord_763240, baseEnd_763240] using wordTrace_append hprefix tailTrace_763240
  have hstable : (prefixWord ++ tailWord_763240).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_763240).length < 2 ^ (prefixWord ++ tailWord_763240).sum := by decide
  have hdescent : baseEnd_763240 < baseStart_763240 := by decide
  rcases family_descends (prefixWord ++ tailWord_763240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_763264 : List Nat := [2, 1, 1, 2, 1, 2, 1, 7, 5]
def baseStart_763264 : Nat := 118140960795 + 763264 * 2 ^ 59
def prefixEnd_763264 : Nat := 4983230072969 + 3 ^ 40 * 763264 * 2
def baseEnd_763264 : Nat := 87093621838534879953293

theorem tailTrace_763264 : CollatzResearch.WordTrace tailWord_763264 prefixEnd_763264 87093621838534879953293 := by
  unfold tailWord_763264
  simp only [CollatzResearch.WordTrace]
  refine ⟨13919262553416178979104423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18559016737888238638805897 13919262553416178979104423)
  ·
    refine ⟨20878893830124268468656635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13919262553416178979104423 20878893830124268468656635)
    ·
      refine ⟨31318340745186402702984953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20878893830124268468656635 31318340745186402702984953)
      ·
        refine ⟨23488755558889802027238715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31318340745186402702984953 23488755558889802027238715)
        ·
          refine ⟨35233133338334703040858073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23488755558889802027238715 35233133338334703040858073)
          ·
            refine ⟨26424850003751027280643555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35233133338334703040858073 26424850003751027280643555)
            ·
              refine ⟨39637275005626540920965333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26424850003751027280643555 39637275005626540920965333)
              ·
                refine ⟨928998632944372052835125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 39637275005626540920965333 928998632944372052835125)
                ·
                  refine ⟨87093621838534879953293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 928998632944372052835125 87093621838534879953293)
                  ·
                    rfl

theorem cell22_763264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 1, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 1, 7, 5].length) (baseStart_763264 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_763264 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_763264 prefixEnd_763264 := by exact prefixLift 763264
  have htrace : WordTrace (prefixWord ++ tailWord_763264) baseStart_763264 baseEnd_763264 := by
    simpa [prefixWord, tailWord_763264, baseEnd_763264] using wordTrace_append hprefix tailTrace_763264
  have hstable : (prefixWord ++ tailWord_763264).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_763264).length < 2 ^ (prefixWord ++ tailWord_763264).sum := by decide
  have hdescent : baseEnd_763264 < baseStart_763264 := by decide
  rcases family_descends (prefixWord ++ tailWord_763264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_763339 : List Nat := [1, 1, 1, 1, 3, 3, 2, 3, 1, 6]
def baseStart_763339 : Nat := 118140960795 + 763339 * 2 ^ 59
def prefixEnd_763339 : Nat := 4983230072969 + 3 ^ 40 * 763339 * 2
def baseEnd_763339 : Nat := 261306539548329444234649

theorem tailTrace_763339 : CollatzResearch.WordTrace tailWord_763339 prefixEnd_763339 261306539548329444234649 := by
  unfold tailWord_763339
  simp only [CollatzResearch.WordTrace]
  refine ⟨27841260581560645767189071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18560840387707097178126047 27841260581560645767189071)
  ·
    refine ⟨41761890872340968650783607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27841260581560645767189071 41761890872340968650783607)
    ·
      refine ⟨62642836308511452976175411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41761890872340968650783607 62642836308511452976175411)
      ·
        refine ⟨93964254462767179464263117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62642836308511452976175411 93964254462767179464263117)
        ·
          refine ⟨35236595423537692299098669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 93964254462767179464263117 35236595423537692299098669)
          ·
            refine ⟨13213723283826634612162001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35236595423537692299098669 13213723283826634612162001)
            ·
              refine ⟨9910292462869975959121501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13213723283826634612162001 9910292462869975959121501)
              ·
                refine ⟨3716359673576240984670563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9910292462869975959121501 3716359673576240984670563)
                ·
                  refine ⟨5574539510364361477005845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3716359673576240984670563 5574539510364361477005845)
                  ·
                    refine ⟨261306539548329444234649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5574539510364361477005845 261306539548329444234649)
                    ·
                      rfl

theorem cell22_763339_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 2, 3, 1, 6].length) (baseStart_763339 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_763339 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_763339 prefixEnd_763339 := by exact prefixLift 763339
  have htrace : WordTrace (prefixWord ++ tailWord_763339) baseStart_763339 baseEnd_763339 := by
    simpa [prefixWord, tailWord_763339, baseEnd_763339] using wordTrace_append hprefix tailTrace_763339
  have hstable : (prefixWord ++ tailWord_763339).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_763339).length < 2 ^ (prefixWord ++ tailWord_763339).sum := by decide
  have hdescent : baseEnd_763339 < baseStart_763339 := by decide
  rcases family_descends (prefixWord ++ tailWord_763339) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_763354 : List Nat := [3, 1, 1, 2, 3, 12]
def baseStart_763354 : Nat := 118140960795 + 763354 * 2 ^ 59
def prefixEnd_763354 : Nat := 4983230072969 + 3 ^ 40 * 763354 * 2
def baseEnd_763354 : Nat := 3226070053763881544563

theorem tailTrace_763354 : CollatzResearch.WordTrace tailWord_763354 prefixEnd_763354 3226070053763881544563 := by
  unfold tailWord_763354
  simp only [CollatzResearch.WordTrace]
  refine ⟨6960451919126575832246279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18561205117670868885990077 6960451919126575832246279)
  ·
    refine ⟨10440677878689863748369419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6960451919126575832246279 10440677878689863748369419)
    ·
      refine ⟨15661016818034795622554129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10440677878689863748369419 15661016818034795622554129)
      ·
        refine ⟨11745762613526096716915597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15661016818034795622554129 11745762613526096716915597)
        ·
          refine ⟨4404660980072286268843349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11745762613526096716915597 4404660980072286268843349)
          ·
            refine ⟨3226070053763881544563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 12 4404660980072286268843349 3226070053763881544563)
            ·
              rfl

theorem cell22_763354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 12].length) (baseStart_763354 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_763354 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_763354 prefixEnd_763354 := by exact prefixLift 763354
  have htrace : WordTrace (prefixWord ++ tailWord_763354) baseStart_763354 baseEnd_763354 := by
    simpa [prefixWord, tailWord_763354, baseEnd_763354] using wordTrace_append hprefix tailTrace_763354
  have hstable : (prefixWord ++ tailWord_763354).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_763354).length < 2 ^ (prefixWord ++ tailWord_763354).sum := by decide
  have hdescent : baseEnd_763354 < baseStart_763354 := by decide
  rcases family_descends (prefixWord ++ tailWord_763354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_763390 : List Nat := [4, 2, 2, 3, 1, 1, 1, 1, 1, 6]
def baseStart_763390 : Nat := 118140960795 + 763390 * 2 ^ 59
def prefixEnd_763390 : Nat := 4983230072969 + 3 ^ 40 * 763390 * 2
def baseEnd_763390 : Nat := 261323997890582311209493

theorem tailTrace_763390 : CollatzResearch.WordTrace tailWord_763390 prefixEnd_763390 261323997890582311209493 := by
  unfold tailWord_763390
  simp only [CollatzResearch.WordTrace]
  refine ⟨3480390088046985184661953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 18562080469583920984863749 3480390088046985184661953)
  ·
    refine ⟨2610292566035238888496465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3480390088046985184661953 2610292566035238888496465)
    ·
      refine ⟨1957719424526429166372349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2610292566035238888496465 1957719424526429166372349)
      ·
        refine ⟨734144784197410937389631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1957719424526429166372349 734144784197410937389631)
        ·
          refine ⟨1101217176296116406084447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 734144784197410937389631 1101217176296116406084447)
          ·
            refine ⟨1651825764444174609126671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1101217176296116406084447 1651825764444174609126671)
            ·
              refine ⟨2477738646666261913690007, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1651825764444174609126671 2477738646666261913690007)
              ·
                refine ⟨3716607969999392870535011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2477738646666261913690007 3716607969999392870535011)
                ·
                  refine ⟨5574911954999089305802517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3716607969999392870535011 5574911954999089305802517)
                  ·
                    refine ⟨261323997890582311209493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5574911954999089305802517 261323997890582311209493)
                    ·
                      rfl

theorem cell22_763390_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 1, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 1, 1, 1, 1, 1, 6].length) (baseStart_763390 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_763390 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_763390 prefixEnd_763390 := by exact prefixLift 763390
  have htrace : WordTrace (prefixWord ++ tailWord_763390) baseStart_763390 baseEnd_763390 := by
    simpa [prefixWord, tailWord_763390, baseEnd_763390] using wordTrace_append hprefix tailTrace_763390
  have hstable : (prefixWord ++ tailWord_763390).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_763390).length < 2 ^ (prefixWord ++ tailWord_763390).sum := by decide
  have hdescent : baseEnd_763390 < baseStart_763390 := by decide
  rcases family_descends (prefixWord ++ tailWord_763390) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_763405 : List Nat := [1, 7, 1, 1, 2, 1, 9]
def baseStart_763405 : Nat := 118140960795 + 763405 * 2 ^ 59
def prefixEnd_763405 : Nat := 4983230072969 + 3 ^ 40 * 763405 * 2
def baseEnd_763405 : Nat := 9678856766560269336461

theorem tailTrace_763405 : CollatzResearch.WordTrace tailWord_763405 prefixEnd_763405 9678856766560269336461 := by
  unfold tailWord_763405
  simp only [CollatzResearch.WordTrace]
  refine ⟨27843667799321539039091669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18562445199547692692727779 27843667799321539039091669)
  ·
    refine ⟨652585964046598571228711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 27843667799321539039091669 652585964046598571228711)
    ·
      refine ⟨978878946069897856843067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 652585964046598571228711 978878946069897856843067)
      ·
        refine ⟨1468318419104846785264601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 978878946069897856843067 1468318419104846785264601)
        ·
          refine ⟨1101238814328635088948451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1468318419104846785264601 1101238814328635088948451)
          ·
            refine ⟨1651858221492952633422677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1101238814328635088948451 1651858221492952633422677)
            ·
              refine ⟨9678856766560269336461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 1651858221492952633422677 9678856766560269336461)
              ·
                rfl

theorem cell22_763405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 2, 1, 9].length) (baseStart_763405 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_763405 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_763405 prefixEnd_763405 := by exact prefixLift 763405
  have htrace : WordTrace (prefixWord ++ tailWord_763405) baseStart_763405 baseEnd_763405 := by
    simpa [prefixWord, tailWord_763405, baseEnd_763405] using wordTrace_append hprefix tailTrace_763405
  have hstable : (prefixWord ++ tailWord_763405).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_763405).length < 2 ^ (prefixWord ++ tailWord_763405).sum := by decide
  have hdescent : baseEnd_763405 < baseStart_763405 := by decide
  rcases family_descends (prefixWord ++ tailWord_763405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_763420 : List Nat := [2, 2, 3, 1, 2, 1, 1, 6, 1, 3]
def baseStart_763420 : Nat := 118140960795 + 763420 * 2 ^ 59
def prefixEnd_763420 : Nat := 4983230072969 + 3 ^ 40 * 763420 * 2
def baseEnd_763420 : Nat := 261334267503672232959401

theorem tailTrace_763420 : CollatzResearch.WordTrace tailWord_763420 prefixEnd_763420 261334267503672232959401 := by
  unfold tailWord_763420
  simp only [CollatzResearch.WordTrace]
  refine ⟨13922107447133598300443857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18562809929511464400591809 13922107447133598300443857)
  ·
    refine ⟨10441580585350198725332893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13922107447133598300443857 10441580585350198725332893)
    ·
      refine ⟨3915592719506324521999835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10441580585350198725332893 3915592719506324521999835)
      ·
        refine ⟨5873389079259486782999753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3915592719506324521999835 5873389079259486782999753)
        ·
          refine ⟨4405041809444615087249815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5873389079259486782999753 4405041809444615087249815)
          ·
            refine ⟨6607562714166922630874723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4405041809444615087249815 6607562714166922630874723)
            ·
              refine ⟨9911344071250383946312085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6607562714166922630874723 9911344071250383946312085)
              ·
                refine ⟨464594253339861747483379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 9911344071250383946312085 464594253339861747483379)
                ·
                  refine ⟨696891380009792621225069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 464594253339861747483379 696891380009792621225069)
                  ·
                    refine ⟨261334267503672232959401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 696891380009792621225069 261334267503672232959401)
                    ·
                      rfl

theorem cell22_763420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 1, 6, 1, 3].length) (baseStart_763420 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_763420 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_763420 prefixEnd_763420 := by exact prefixLift 763420
  have htrace : WordTrace (prefixWord ++ tailWord_763420) baseStart_763420 baseEnd_763420 := by
    simpa [prefixWord, tailWord_763420, baseEnd_763420] using wordTrace_append hprefix tailTrace_763420
  have hstable : (prefixWord ++ tailWord_763420).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_763420).length < 2 ^ (prefixWord ++ tailWord_763420).sum := by decide
  have hdescent : baseEnd_763420 < baseStart_763420 := by decide
  rcases family_descends (prefixWord ++ tailWord_763420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_763510 : List Nat := [5, 1, 1, 2, 2, 2, 1, 2, 1, 5]
def baseStart_763510 : Nat := 118140960795 + 763510 * 2 ^ 59
def prefixEnd_763510 : Nat := 4983230072969 + 3 ^ 40 * 763510 * 2
def baseEnd_763510 : Nat := 261365076342941998209125

theorem tailTrace_763510 : CollatzResearch.WordTrace tailWord_763510 prefixEnd_763510 261365076342941998209125 := by
  unfold tailWord_763510
  simp only [CollatzResearch.WordTrace]
  refine ⟨1740468591496321373228999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 18564998309294094647775989 1740468591496321373228999)
  ·
    refine ⟨2610702887244482059843499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1740468591496321373228999 2610702887244482059843499)
    ·
      refine ⟨3916054330866723089765249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2610702887244482059843499 3916054330866723089765249)
      ·
        refine ⟨2937040748150042317323937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3916054330866723089765249 2937040748150042317323937)
        ·
          refine ⟨2202780561112531737992953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2937040748150042317323937 2202780561112531737992953)
          ·
            refine ⟨1652085420834398803494715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2202780561112531737992953 1652085420834398803494715)
            ·
              refine ⟨2478128131251598205242073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1652085420834398803494715 2478128131251598205242073)
              ·
                refine ⟨1858596098438698653931555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2478128131251598205242073 1858596098438698653931555)
                ·
                  refine ⟨2787894147658047980897333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1858596098438698653931555 2787894147658047980897333)
                  ·
                    refine ⟨261365076342941998209125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2787894147658047980897333 261365076342941998209125)
                    ·
                      rfl

theorem cell22_763510_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 2, 1, 2, 1, 5].length) (baseStart_763510 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_763510 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_763510 prefixEnd_763510 := by exact prefixLift 763510
  have htrace : WordTrace (prefixWord ++ tailWord_763510) baseStart_763510 baseEnd_763510 := by
    simpa [prefixWord, tailWord_763510, baseEnd_763510] using wordTrace_append hprefix tailTrace_763510
  have hstable : (prefixWord ++ tailWord_763510).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_763510).length < 2 ^ (prefixWord ++ tailWord_763510).sum := by decide
  have hdescent : baseEnd_763510 < baseStart_763510 := by decide
  rcases family_descends (prefixWord ++ tailWord_763510) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_763602 : List Nat := [3, 2, 2, 2, 2, 2, 3, 1, 5]
def baseStart_763602 : Nat := 118140960795 + 763602 * 2 ^ 59
def prefixEnd_763602 : Nat := 4983230072969 + 3 ^ 40 * 763602 * 2
def baseEnd_763602 : Nat := 87132189941028141636281

theorem tailTrace_763602 : CollatzResearch.WordTrace tailWord_763602 prefixEnd_763602 87132189941028141636281 := by
  unfold tailWord_763602
  simp only [CollatzResearch.WordTrace]
  refine ⟨6962713244901960421003265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18567235319738561122675373 6962713244901960421003265)
  ·
    refine ⟨5222034933676470315752449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6962713244901960421003265 5222034933676470315752449)
    ·
      refine ⟨3916526200257352736814337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5222034933676470315752449 3916526200257352736814337)
      ·
        refine ⟨2937394650193014552610753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3916526200257352736814337 2937394650193014552610753)
        ·
          refine ⟨2203045987644760914458065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2937394650193014552610753 2203045987644760914458065)
          ·
            refine ⟨1652284490733570685843549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2203045987644760914458065 1652284490733570685843549)
            ·
              refine ⟨619606684025089007191331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1652284490733570685843549 619606684025089007191331)
              ·
                refine ⟨929410026037633510786997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 619606684025089007191331 929410026037633510786997)
                ·
                  refine ⟨87132189941028141636281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 929410026037633510786997 87132189941028141636281)
                  ·
                    rfl

theorem cell22_763602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 2, 3, 1, 5].length) (baseStart_763602 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_763602 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_763602 prefixEnd_763602 := by exact prefixLift 763602
  have htrace : WordTrace (prefixWord ++ tailWord_763602) baseStart_763602 baseEnd_763602 := by
    simpa [prefixWord, tailWord_763602, baseEnd_763602] using wordTrace_append hprefix tailTrace_763602
  have hstable : (prefixWord ++ tailWord_763602).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_763602).length < 2 ^ (prefixWord ++ tailWord_763602).sum := by decide
  have hdescent : baseEnd_763602 < baseStart_763602 := by decide
  rcases family_descends (prefixWord ++ tailWord_763602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_763615 : List Nat := [1, 1, 2, 3, 2, 2, 4, 2, 1, 4]
def baseStart_763615 : Nat := 118140960795 + 763615 * 2 ^ 59
def prefixEnd_763615 : Nat := 4983230072969 + 3 ^ 40 * 763615 * 2
def baseEnd_763615 : Nat := 261401019988756724333803

theorem tailTrace_763615 : CollatzResearch.WordTrace tailWord_763615 prefixEnd_763615 261401019988756724333803 := by
  unfold tailWord_763615
  simp only [CollatzResearch.WordTrace]
  refine ⟨27851327128560744904236299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18567551419040496602824199 27851327128560744904236299)
  ·
    refine ⟨41776990692841117356354449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27851327128560744904236299 41776990692841117356354449)
    ·
      refine ⟨31332743019630838017265837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41776990692841117356354449 31332743019630838017265837)
      ·
        refine ⟨11749778632361564256474689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31332743019630838017265837 11749778632361564256474689)
        ·
          refine ⟨8812333974271173192356017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11749778632361564256474689 8812333974271173192356017)
          ·
            refine ⟨6609250480703379894267013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8812333974271173192356017 6609250480703379894267013)
            ·
              refine ⟨1239234465131883730175065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6609250480703379894267013 1239234465131883730175065)
              ·
                refine ⟨929425848848912797631299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1239234465131883730175065 929425848848912797631299)
                ·
                  refine ⟨1394138773273369196446949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 929425848848912797631299 1394138773273369196446949)
                  ·
                    refine ⟨261401019988756724333803, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1394138773273369196446949 261401019988756724333803)
                    ·
                      rfl

theorem cell22_763615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 4, 2, 1, 4].length) (baseStart_763615 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_763615 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_763615 prefixEnd_763615 := by exact prefixLift 763615
  have htrace : WordTrace (prefixWord ++ tailWord_763615) baseStart_763615 baseEnd_763615 := by
    simpa [prefixWord, tailWord_763615, baseEnd_763615] using wordTrace_append hprefix tailTrace_763615
  have hstable : (prefixWord ++ tailWord_763615).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_763615).length < 2 ^ (prefixWord ++ tailWord_763615).sum := by decide
  have hdescent : baseEnd_763615 < baseStart_763615 := by decide
  rcases family_descends (prefixWord ++ tailWord_763615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_763623 : List Nat := [1, 1, 5, 4, 2, 1, 1, 3, 1, 3]
def baseStart_763623 : Nat := 118140960795 + 763623 * 2 ^ 59
def prefixEnd_763623 : Nat := 4983230072969 + 3 ^ 40 * 763623 * 2
def baseEnd_763623 : Nat := 261403758552247370133779

theorem tailTrace_763623 : CollatzResearch.WordTrace tailWord_763623 prefixEnd_763623 261403758552247370133779 := by
  unfold tailWord_763623
  simp only [CollatzResearch.WordTrace]
  refine ⟨27851618912531762270527523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18567745941687841513685015 27851618912531762270527523)
  ·
    refine ⟨41777428368797643405791285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27851618912531762270527523 41777428368797643405791285)
    ·
      refine ⟨3916633909574779069292933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 41777428368797643405791285 3916633909574779069292933)
      ·
        refine ⟨734368858045271075492425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3916633909574779069292933 734368858045271075492425)
        ·
          refine ⟨550776643533953306619319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 734368858045271075492425 550776643533953306619319)
          ·
            refine ⟨826164965300929959928979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 550776643533953306619319 826164965300929959928979)
            ·
              refine ⟨1239247447951394939893469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 826164965300929959928979 1239247447951394939893469)
              ·
                refine ⟨464717792981773102460051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1239247447951394939893469 464717792981773102460051)
                ·
                  refine ⟨697076689472659653690077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 464717792981773102460051 697076689472659653690077)
                  ·
                    refine ⟨261403758552247370133779, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 697076689472659653690077 261403758552247370133779)
                    ·
                      rfl

theorem cell22_763623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 2, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 2, 1, 1, 3, 1, 3].length) (baseStart_763623 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_763623 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_763623 prefixEnd_763623 := by exact prefixLift 763623
  have htrace : WordTrace (prefixWord ++ tailWord_763623) baseStart_763623 baseEnd_763623 := by
    simpa [prefixWord, tailWord_763623, baseEnd_763623] using wordTrace_append hprefix tailTrace_763623
  have hstable : (prefixWord ++ tailWord_763623).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_763623).length < 2 ^ (prefixWord ++ tailWord_763623).sum := by decide
  have hdescent : baseEnd_763623 < baseStart_763623 := by decide
  rcases family_descends (prefixWord ++ tailWord_763623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_763628 : List Nat := [2, 2, 1, 1, 2, 2, 2, 4, 1, 5]
def baseStart_763628 : Nat := 118140960795 + 763628 * 2 ^ 59
def prefixEnd_763628 : Nat := 4983230072969 + 3 ^ 40 * 763628 * 2
def baseEnd_763628 : Nat := 261405470154429023758763

theorem tailTrace_763628 : CollatzResearch.WordTrace tailWord_763628 prefixEnd_763628 261405470154429023758763 := by
  unfold tailWord_763628
  simp only [CollatzResearch.WordTrace]
  refine ⟨13925900638756824062229769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18567867518342432082973025 13925900638756824062229769)
  ·
    refine ⟨10444425479067618046672327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13925900638756824062229769 10444425479067618046672327)
    ·
      refine ⟨15666638218601427070008491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10444425479067618046672327 15666638218601427070008491)
      ·
        refine ⟨23499957327902140605012737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15666638218601427070008491 23499957327902140605012737)
        ·
          refine ⟨17624967995926605453759553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23499957327902140605012737 17624967995926605453759553)
          ·
            refine ⟨13218725996944954090319665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17624967995926605453759553 13218725996944954090319665)
            ·
              refine ⟨9914044497708715567739749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13218725996944954090319665 9914044497708715567739749)
              ·
                refine ⟨1858883343320384168951203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9914044497708715567739749 1858883343320384168951203)
                ·
                  refine ⟨2788325014980576253426805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1858883343320384168951203 2788325014980576253426805)
                  ·
                    refine ⟨261405470154429023758763, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2788325014980576253426805 261405470154429023758763)
                    ·
                      rfl

theorem cell22_763628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 5].length) (baseStart_763628 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_763628 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_763628 prefixEnd_763628 := by exact prefixLift 763628
  have htrace : WordTrace (prefixWord ++ tailWord_763628) baseStart_763628 baseEnd_763628 := by
    simpa [prefixWord, tailWord_763628, baseEnd_763628] using wordTrace_append hprefix tailTrace_763628
  have hstable : (prefixWord ++ tailWord_763628).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_763628).length < 2 ^ (prefixWord ++ tailWord_763628).sum := by decide
  have hdescent : baseEnd_763628 < baseStart_763628 := by decide
  rcases family_descends (prefixWord ++ tailWord_763628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_763658 : List Nat := [3, 1, 2, 2, 1, 3, 1, 9]
def baseStart_763658 : Nat := 118140960795 + 763658 * 2 ^ 59
def prefixEnd_763658 : Nat := 4983230072969 + 3 ^ 40 * 763658 * 2
def baseEnd_763658 : Nat := 29046193307502105056519

theorem tailTrace_763658 : CollatzResearch.WordTrace tailWord_763658 prefixEnd_763658 29046193307502105056519 := by
  unfold tailWord_763658
  simp only [CollatzResearch.WordTrace]
  refine ⟨6963223866851240812012907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18568596978269975498701085 6963223866851240812012907)
  ·
    refine ⟨10444835800276861218019361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6963223866851240812012907 10444835800276861218019361)
    ·
      refine ⟨7833626850207645913514521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10444835800276861218019361 7833626850207645913514521)
      ·
        refine ⟨5875220137655734435135891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7833626850207645913514521 5875220137655734435135891)
        ·
          refine ⟨8812830206483601652703837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5875220137655734435135891 8812830206483601652703837)
          ·
            refine ⟨3304811327431350619763939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8812830206483601652703837 3304811327431350619763939)
            ·
              refine ⟨4957216991147025929645909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3304811327431350619763939 4957216991147025929645909)
              ·
                refine ⟨29046193307502105056519, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 4957216991147025929645909 29046193307502105056519)
                ·
                  rfl

theorem cell22_763658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 3, 1, 9].length) (baseStart_763658 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_763658 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_763658 prefixEnd_763658 := by exact prefixLift 763658
  have htrace : WordTrace (prefixWord ++ tailWord_763658) baseStart_763658 baseEnd_763658 := by
    simpa [prefixWord, tailWord_763658, baseEnd_763658] using wordTrace_append hprefix tailTrace_763658
  have hstable : (prefixWord ++ tailWord_763658).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_763658).length < 2 ^ (prefixWord ++ tailWord_763658).sum := by decide
  have hdescent : baseEnd_763658 < baseStart_763658 := by decide
  rcases family_descends (prefixWord ++ tailWord_763658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_763720 : List Nat := [2, 1, 3, 1, 1, 4, 2, 3, 5]
def baseStart_763720 : Nat := 118140960795 + 763720 * 2 ^ 59
def prefixEnd_763720 : Nat := 4983230072969 + 3 ^ 40 * 763720 * 2
def baseEnd_763720 : Nat := 87145654544857150152827

theorem tailTrace_763720 : CollatzResearch.WordTrace tailWord_763720 prefixEnd_763720 87145654544857150152827 := by
  unfold tailWord_763720
  simp only [CollatzResearch.WordTrace]
  refine ⟨13927578396590173918404307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18570104528786898557872409 13927578396590173918404307)
  ·
    refine ⟨20891367594885260877606461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13927578396590173918404307 20891367594885260877606461)
    ·
      refine ⟨7834262848081972829102423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20891367594885260877606461 7834262848081972829102423)
      ·
        refine ⟨11751394272122959243653635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7834262848081972829102423 11751394272122959243653635)
        ·
          refine ⟨17627091408184438865480453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11751394272122959243653635 17627091408184438865480453)
          ·
            refine ⟨3305079639034582287277585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 17627091408184438865480453 3305079639034582287277585)
            ·
              refine ⟨2478809729275936715458189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3305079639034582287277585 2478809729275936715458189)
              ·
                refine ⟨929553648478476268296821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2478809729275936715458189 929553648478476268296821)
                ·
                  refine ⟨87145654544857150152827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 929553648478476268296821 87145654544857150152827)
                  ·
                    rfl

theorem cell22_763720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 4, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 4, 2, 3, 5].length) (baseStart_763720 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_763720 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_763720 prefixEnd_763720 := by exact prefixLift 763720
  have htrace : WordTrace (prefixWord ++ tailWord_763720) baseStart_763720 baseEnd_763720 := by
    simpa [prefixWord, tailWord_763720, baseEnd_763720] using wordTrace_append hprefix tailTrace_763720
  have hstable : (prefixWord ++ tailWord_763720).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_763720).length < 2 ^ (prefixWord ++ tailWord_763720).sum := by decide
  have hdescent : baseEnd_763720 < baseStart_763720 := by decide
  rcases family_descends (prefixWord ++ tailWord_763720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_763784 : List Nat := [2, 1, 3, 3, 3, 1, 2, 2, 1, 4]
def baseStart_763784 : Nat := 118140960795 + 763784 * 2 ^ 59
def prefixEnd_763784 : Nat := 4983230072969 + 3 ^ 40 * 763784 * 2
def baseEnd_763784 : Nat := 261458872142496616858285

theorem tailTrace_763784 : CollatzResearch.WordTrace tailWord_763784 prefixEnd_763784 261458872142496616858285 := by
  unfold tailWord_763784
  simp only [CollatzResearch.WordTrace]
  refine ⟨13928745532474243383569203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18571660709965657844758937 13928745532474243383569203)
  ·
    refine ⟨20893118298711365075353805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13928745532474243383569203 20893118298711365075353805)
    ·
      refine ⟨7834919362016761903257677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20893118298711365075353805 7834919362016761903257677)
      ·
        refine ⟨2938094760756285713721629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7834919362016761903257677 2938094760756285713721629)
        ·
          refine ⟨1101785535283607142645611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2938094760756285713721629 1101785535283607142645611)
          ·
            refine ⟨1652678302925410713968417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1101785535283607142645611 1652678302925410713968417)
            ·
              refine ⟨1239508727194058035476313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1652678302925410713968417 1239508727194058035476313)
              ·
                refine ⟨929631545395543526607235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1239508727194058035476313 929631545395543526607235)
                ·
                  refine ⟨1394447318093315289910853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 929631545395543526607235 1394447318093315289910853)
                  ·
                    refine ⟨261458872142496616858285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1394447318093315289910853 261458872142496616858285)
                    ·
                      rfl

theorem cell22_763784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 3, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 3, 1, 2, 2, 1, 4].length) (baseStart_763784 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_763784 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_763784 prefixEnd_763784 := by exact prefixLift 763784
  have htrace : WordTrace (prefixWord ++ tailWord_763784) baseStart_763784 baseEnd_763784 := by
    simpa [prefixWord, tailWord_763784, baseEnd_763784] using wordTrace_append hprefix tailTrace_763784
  have hstable : (prefixWord ++ tailWord_763784).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_763784).length < 2 ^ (prefixWord ++ tailWord_763784).sum := by decide
  have hdescent : baseEnd_763784 < baseStart_763784 := by decide
  rcases family_descends (prefixWord ++ tailWord_763784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_763799 : List Nat := [1, 1, 3, 3, 1, 5, 1, 3, 4]
def baseStart_763799 : Nat := 118140960795 + 763799 * 2 ^ 59
def prefixEnd_763799 : Nat := 4983230072969 + 3 ^ 40 * 763799 * 2
def baseEnd_763799 : Nat := 87154668983013859244413

theorem tailTrace_763799 : CollatzResearch.WordTrace tailWord_763799 prefixEnd_763799 87154668983013859244413 := by
  unfold tailWord_763799
  simp only [CollatzResearch.WordTrace]
  refine ⟨27858038159894144328934451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18572025439929429552622967 27858038159894144328934451)
  ·
    refine ⟨41787057239841216493401677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27858038159894144328934451 41787057239841216493401677)
    ·
      refine ⟨15670146464940456185025629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 41787057239841216493401677 15670146464940456185025629)
      ·
        refine ⟨5876304924352671069384611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15670146464940456185025629 5876304924352671069384611)
        ·
          refine ⟨8814457386529006604076917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5876304924352671069384611 8814457386529006604076917)
          ·
            refine ⟨826355379987094369132211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 8814457386529006604076917 826355379987094369132211)
            ·
              refine ⟨1239533069980641553698317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 826355379987094369132211 1239533069980641553698317)
              ·
                refine ⟨464824901242740582636869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1239533069980641553698317 464824901242740582636869)
                ·
                  refine ⟨87154668983013859244413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 464824901242740582636869 87154668983013859244413)
                  ·
                    rfl

theorem cell22_763799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 5, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 5, 1, 3, 4].length) (baseStart_763799 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_763799 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_763799 prefixEnd_763799 := by exact prefixLift 763799
  have htrace : WordTrace (prefixWord ++ tailWord_763799) baseStart_763799 baseEnd_763799 := by
    simpa [prefixWord, tailWord_763799, baseEnd_763799] using wordTrace_append hprefix tailTrace_763799
  have hstable : (prefixWord ++ tailWord_763799).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_763799).length < 2 ^ (prefixWord ++ tailWord_763799).sum := by decide
  have hdescent : baseEnd_763799 < baseStart_763799 := by decide
  rcases family_descends (prefixWord ++ tailWord_763799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_763812 : List Nat := [2, 3, 1, 2, 1, 4, 1, 2, 2, 4]
def baseStart_763812 : Nat := 118140960795 + 763812 * 2 ^ 59
def prefixEnd_763812 : Nat := 4983230072969 + 3 ^ 40 * 763812 * 2
def baseEnd_763812 : Nat := 261468457114713877158199

theorem tailTrace_763812 : CollatzResearch.WordTrace tailWord_763812 prefixEnd_763812 261468457114713877158199 := by
  unfold tailWord_763812
  simp only [CollatzResearch.WordTrace]
  refine ⟨13929256154423523774578845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18572341539231365032771793 13929256154423523774578845)
  ·
    refine ⟨5223471057908821415467067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13929256154423523774578845 5223471057908821415467067)
    ·
      refine ⟨7835206586863232123200601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5223471057908821415467067 7835206586863232123200601)
      ·
        refine ⟨5876404940147424092400451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7835206586863232123200601 5876404940147424092400451)
        ·
          refine ⟨8814607410221136138600677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5876404940147424092400451 8814607410221136138600677)
          ·
            refine ⟨1652738889416463025987627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8814607410221136138600677 1652738889416463025987627)
            ·
              refine ⟨2479108334124694538981441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1652738889416463025987627 2479108334124694538981441)
              ·
                refine ⟨1859331250593520904236081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2479108334124694538981441 1859331250593520904236081)
                ·
                  refine ⟨1394498437945140678177061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1859331250593520904236081 1394498437945140678177061)
                  ·
                    refine ⟨261468457114713877158199, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1394498437945140678177061 261468457114713877158199)
                    ·
                      rfl

theorem cell22_763812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 4, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 4, 1, 2, 2, 4].length) (baseStart_763812 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_763812 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_763812 prefixEnd_763812 := by exact prefixLift 763812
  have htrace : WordTrace (prefixWord ++ tailWord_763812) baseStart_763812 baseEnd_763812 := by
    simpa [prefixWord, tailWord_763812, baseEnd_763812] using wordTrace_append hprefix tailTrace_763812
  have hstable : (prefixWord ++ tailWord_763812).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_763812).length < 2 ^ (prefixWord ++ tailWord_763812).sum := by decide
  have hdescent : baseEnd_763812 < baseStart_763812 := by decide
  rcases family_descends (prefixWord ++ tailWord_763812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_763816 : List Nat := [2, 1, 6, 2, 1, 2, 1, 1, 6]
def baseStart_763816 : Nat := 118140960795 + 763816 * 2 ^ 59
def prefixEnd_763816 : Nat := 4983230072969 + 3 ^ 40 * 763816 * 2
def baseEnd_763816 : Nat := 87156608798819733352729

theorem tailTrace_763816 : CollatzResearch.WordTrace tailWord_763816 prefixEnd_763816 87156608798819733352729 := by
  unfold tailWord_763816
  simp only [CollatzResearch.WordTrace]
  refine ⟨13929329100416278116151651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18572438800555037488202201 13929329100416278116151651)
  ·
    refine ⟨20893993650624417174227477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13929329100416278116151651 20893993650624417174227477)
    ·
      refine ⟨979405952373019555041913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 20893993650624417174227477 979405952373019555041913)
      ·
        refine ⟨734554464279764666281435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 979405952373019555041913 734554464279764666281435)
        ·
          refine ⟨1101831696419646999422153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 734554464279764666281435 1101831696419646999422153)
          ·
            refine ⟨826373772314735249566615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1101831696419646999422153 826373772314735249566615)
            ·
              refine ⟨1239560658472102874349923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 826373772314735249566615 1239560658472102874349923)
              ·
                refine ⟨1859340987708154311524885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1239560658472102874349923 1859340987708154311524885)
                ·
                  refine ⟨87156608798819733352729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1859340987708154311524885 87156608798819733352729)
                  ·
                    rfl

theorem cell22_763816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 1, 2, 1, 1, 6].length) (baseStart_763816 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_763816 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_763816 prefixEnd_763816 := by exact prefixLift 763816
  have htrace : WordTrace (prefixWord ++ tailWord_763816) baseStart_763816 baseEnd_763816 := by
    simpa [prefixWord, tailWord_763816, baseEnd_763816] using wordTrace_append hprefix tailTrace_763816
  have hstable : (prefixWord ++ tailWord_763816).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_763816).length < 2 ^ (prefixWord ++ tailWord_763816).sum := by decide
  have hdescent : baseEnd_763816 < baseStart_763816 := by decide
  rcases family_descends (prefixWord ++ tailWord_763816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_764101 : List Nat := [1, 3, 1, 1, 1, 1, 7, 2, 2, 3]
def baseStart_764101 : Nat := 118140960795 + 764101 * 2 ^ 59
def prefixEnd_764101 : Nat := 4983230072969 + 3 ^ 40 * 764101 * 2
def baseEnd_764101 : Nat := 261567387720813456682313

theorem tailTrace_764101 : CollatzResearch.WordTrace tailWord_764101 prefixEnd_764101 261567387720813456682313 := by
  unfold tailWord_764101
  simp only [CollatzResearch.WordTrace]
  refine ⟨27869053004800049906428157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18579368669866699937618771 27869053004800049906428157)
  ·
    refine ⟨10450894876800018714910559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27869053004800049906428157 10450894876800018714910559)
    ·
      refine ⟨15676342315200028072365839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10450894876800018714910559 15676342315200028072365839)
      ·
        refine ⟨23514513472800042108548759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15676342315200028072365839 23514513472800042108548759)
        ·
          refine ⟨35271770209200063162823139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23514513472800042108548759 35271770209200063162823139)
          ·
            refine ⟨52907655313800094744234709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35271770209200063162823139 52907655313800094744234709)
            ·
              refine ⟨1240023171417189720568001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 52907655313800094744234709 1240023171417189720568001)
              ·
                refine ⟨930017378562892290426001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1240023171417189720568001 930017378562892290426001)
                ·
                  refine ⟨697513033922169217819501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 930017378562892290426001 697513033922169217819501)
                  ·
                    refine ⟨261567387720813456682313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 697513033922169217819501 261567387720813456682313)
                    ·
                      rfl

theorem cell22_764101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 7, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 7, 2, 2, 3].length) (baseStart_764101 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_764101 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_764101 prefixEnd_764101 := by exact prefixLift 764101
  have htrace : WordTrace (prefixWord ++ tailWord_764101) baseStart_764101 baseEnd_764101 := by
    simpa [prefixWord, tailWord_764101, baseEnd_764101] using wordTrace_append hprefix tailTrace_764101
  have hstable : (prefixWord ++ tailWord_764101).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_764101).length < 2 ^ (prefixWord ++ tailWord_764101).sum := by decide
  have hdescent : baseEnd_764101 < baseStart_764101 := by decide
  rcases family_descends (prefixWord ++ tailWord_764101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_764118 : List Nat := [5, 2, 1, 2, 1, 1, 3, 1, 1, 5]
def baseStart_764118 : Nat := 118140960795 + 764118 * 2 ^ 59
def prefixEnd_764118 : Nat := 4983230072969 + 3 ^ 40 * 764118 * 2
def baseEnd_764118 : Nat := 261573207168231079007261

theorem tailTrace_764118 : CollatzResearch.WordTrace tailWord_764118 prefixEnd_764118 261573207168231079007261 := by
  unfold tailWord_764118
  simp only [CollatzResearch.WordTrace]
  refine ⟨1741854565358653863112313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 18579782030492307873198005 1741854565358653863112313)
  ·
    refine ⟨1306390924018990397334235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1741854565358653863112313 1306390924018990397334235)
    ·
      refine ⟨1959586386028485596001353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1306390924018990397334235 1959586386028485596001353)
      ·
        refine ⟨1469689789521364197001015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1959586386028485596001353 1469689789521364197001015)
        ·
          refine ⟨2204534684282046295501523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1469689789521364197001015 2204534684282046295501523)
          ·
            refine ⟨3306802026423069443252285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2204534684282046295501523 3306802026423069443252285)
            ·
              refine ⟨1240050759908651041219607, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3306802026423069443252285 1240050759908651041219607)
              ·
                refine ⟨1860076139862976561829411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1240050759908651041219607 1860076139862976561829411)
                ·
                  refine ⟨2790114209794464842744117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1860076139862976561829411 2790114209794464842744117)
                  ·
                    refine ⟨261573207168231079007261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2790114209794464842744117 261573207168231079007261)
                    ·
                      rfl

theorem cell22_764118_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 1, 3, 1, 1, 5].length) (baseStart_764118 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_764118 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_764118 prefixEnd_764118 := by exact prefixLift 764118
  have htrace : WordTrace (prefixWord ++ tailWord_764118) baseStart_764118 baseEnd_764118 := by
    simpa [prefixWord, tailWord_764118, baseEnd_764118] using wordTrace_append hprefix tailTrace_764118
  have hstable : (prefixWord ++ tailWord_764118).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_764118).length < 2 ^ (prefixWord ++ tailWord_764118).sum := by decide
  have hdescent : baseEnd_764118 < baseStart_764118 := by decide
  rcases family_descends (prefixWord ++ tailWord_764118) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_764131 : List Nat := [1, 1, 1, 8, 1, 1, 1, 8]
def baseStart_764131 : Nat := 118140960795 + 764131 * 2 ^ 59
def prefixEnd_764131 : Nat := 4983230072969 + 3 ^ 40 * 764131 * 2
def baseEnd_764131 : Nat := 29064184148211486492469

theorem tailTrace_764131 : CollatzResearch.WordTrace tailWord_764131 prefixEnd_764131 29064184148211486492469 := by
  unfold tailWord_764131
  simp only [CollatzResearch.WordTrace]
  refine ⟨27870147194691365030020247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18580098129794243353346831 27870147194691365030020247)
  ·
    refine ⟨41805220792037047545030371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27870147194691365030020247 41805220792037047545030371)
    ·
      refine ⟨62707831188055571317545557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41805220792037047545030371 62707831188055571317545557)
      ·
        refine ⟨734857396735026226377487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 8 62707831188055571317545557 734857396735026226377487)
        ·
          refine ⟨1102286095102539339566231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 734857396735026226377487 1102286095102539339566231)
          ·
            refine ⟨1653429142653809009349347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1102286095102539339566231 1653429142653809009349347)
            ·
              refine ⟨2480143713980713514024021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1653429142653809009349347 2480143713980713514024021)
              ·
                refine ⟨29064184148211486492469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 2480143713980713514024021 29064184148211486492469)
                ·
                  rfl

theorem cell22_764131_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 1, 1, 1, 8].length) (baseStart_764131 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_764131 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_764131 prefixEnd_764131 := by exact prefixLift 764131
  have htrace : WordTrace (prefixWord ++ tailWord_764131) baseStart_764131 baseEnd_764131 := by
    simpa [prefixWord, tailWord_764131, baseEnd_764131] using wordTrace_append hprefix tailTrace_764131
  have hstable : (prefixWord ++ tailWord_764131).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_764131).length < 2 ^ (prefixWord ++ tailWord_764131).sum := by decide
  have hdescent : baseEnd_764131 < baseStart_764131 := by decide
  rcases family_descends (prefixWord ++ tailWord_764131) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_764159 : List Nat := [1, 1, 2, 2, 1, 4, 2, 4, 5]
def baseStart_764159 : Nat := 118140960795 + 764159 * 2 ^ 59
def prefixEnd_764159 : Nat := 4983230072969 + 3 ^ 40 * 764159 * 2
def baseEnd_764159 : Nat := 87195747435373546244045

theorem tailTrace_764159 : CollatzResearch.WordTrace tailWord_764159 prefixEnd_764159 87195747435373546244045 := by
  unfold tailWord_764159
  simp only [CollatzResearch.WordTrace]
  refine ⟨27871168438589925812039531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18580778959059950541359687 27871168438589925812039531)
  ·
    refine ⟨41806752657884888718059297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27871168438589925812039531 41806752657884888718059297)
    ·
      refine ⟨31355064493413666538544473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41806752657884888718059297 31355064493413666538544473)
      ·
        refine ⟨23516298370060249903908355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31355064493413666538544473 23516298370060249903908355)
        ·
          refine ⟨35274447555090374855862533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23516298370060249903908355 35274447555090374855862533)
          ·
            refine ⟨6613958916579445285474225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 35274447555090374855862533 6613958916579445285474225)
            ·
              refine ⟨4960469187434583964105669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6613958916579445285474225 4960469187434583964105669)
              ·
                refine ⟨930087972643984493269813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4960469187434583964105669 930087972643984493269813)
                ·
                  refine ⟨87195747435373546244045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 930087972643984493269813 87195747435373546244045)
                  ·
                    rfl

theorem cell22_764159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 2, 4, 5].length) (baseStart_764159 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_764159 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_764159 prefixEnd_764159 := by exact prefixLift 764159
  have htrace : WordTrace (prefixWord ++ tailWord_764159) baseStart_764159 baseEnd_764159 := by
    simpa [prefixWord, tailWord_764159, baseEnd_764159] using wordTrace_append hprefix tailTrace_764159
  have hstable : (prefixWord ++ tailWord_764159).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_764159).length < 2 ^ (prefixWord ++ tailWord_764159).sum := by decide
  have hdescent : baseEnd_764159 < baseStart_764159 := by decide
  rcases family_descends (prefixWord ++ tailWord_764159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_764174 : List Nat := [4, 1, 1, 2, 1, 2, 2, 1, 1, 7]
def baseStart_764174 : Nat := 118140960795 + 764174 * 2 ^ 59
def prefixEnd_764174 : Nat := 4983230072969 + 3 ^ 40 * 764174 * 2
def baseEnd_764174 : Nat := 261592377112665599607089

theorem tailTrace_764174 : CollatzResearch.WordTrace tailWord_764174 prefixEnd_764174 261592377112665599607089 := by
  unfold tailWord_764174
  simp only [CollatzResearch.WordTrace]
  refine ⟨3483964441691947921729447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 18581143689023722249223717 3483964441691947921729447)
  ·
    refine ⟨5225946662537921882594171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3483964441691947921729447 5225946662537921882594171)
    ·
      refine ⟨7838919993806882823891257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5225946662537921882594171 7838919993806882823891257)
      ·
        refine ⟨5879189995355162117918443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7838919993806882823891257 5879189995355162117918443)
        ·
          refine ⟨8818784993032743176877665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5879189995355162117918443 8818784993032743176877665)
          ·
            refine ⟨6614088744774557382658249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8818784993032743176877665 6614088744774557382658249)
            ·
              refine ⟨4960566558580918036993687, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6614088744774557382658249 4960566558580918036993687)
              ·
                refine ⟨7440849837871377055490531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4960566558580918036993687 7440849837871377055490531)
                ·
                  refine ⟨11161274756807065583235797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7440849837871377055490531 11161274756807065583235797)
                  ·
                    refine ⟨261592377112665599607089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 11161274756807065583235797 261592377112665599607089)
                    ·
                      rfl

theorem cell22_764174_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 2, 1, 1, 7].length) (baseStart_764174 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_764174 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_764174 prefixEnd_764174 := by exact prefixLift 764174
  have htrace : WordTrace (prefixWord ++ tailWord_764174) baseStart_764174 baseEnd_764174 := by
    simpa [prefixWord, tailWord_764174, baseEnd_764174] using wordTrace_append hprefix tailTrace_764174
  have hstable : (prefixWord ++ tailWord_764174).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_764174).length < 2 ^ (prefixWord ++ tailWord_764174).sum := by decide
  have hdescent : baseEnd_764174 < baseStart_764174 := by decide
  rcases family_descends (prefixWord ++ tailWord_764174) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_764236 : List Nat := [2, 2, 1, 3, 2, 1, 4, 1, 1, 5]
def baseStart_764236 : Nat := 118140960795 + 764236 * 2 ^ 59
def prefixEnd_764236 : Nat := 4983230072969 + 3 ^ 40 * 764236 * 2
def baseEnd_764236 : Nat := 261613600979718104556899

theorem tailTrace_764236 : CollatzResearch.WordTrace tailWord_764236 prefixEnd_764236 261613600979718104556899 := by
  unfold tailWord_764236
  simp only [CollatzResearch.WordTrace]
  refine ⟨13936988429655483981296281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18582651239540645308395041 13936988429655483981296281)
  ·
    refine ⟨10452741322241612985972211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13936988429655483981296281 10452741322241612985972211)
    ·
      refine ⟨15679111983362419478958317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10452741322241612985972211 15679111983362419478958317)
      ·
        refine ⟨5879666993760907304609369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15679111983362419478958317 5879666993760907304609369)
        ·
          refine ⟨4409750245320680478457027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5879666993760907304609369 4409750245320680478457027)
          ·
            refine ⟨6614625367981020717685541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4409750245320680478457027 6614625367981020717685541)
            ·
              refine ⟨1240242256496441384566039, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6614625367981020717685541 1240242256496441384566039)
              ·
                refine ⟨1860363384744662076849059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1240242256496441384566039 1860363384744662076849059)
                ·
                  refine ⟨2790545077116993115273589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1860363384744662076849059 2790545077116993115273589)
                  ·
                    refine ⟨261613600979718104556899, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2790545077116993115273589 261613600979718104556899)
                    ·
                      rfl

theorem cell22_764236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 4, 1, 1, 5].length) (baseStart_764236 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_764236 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_764236 prefixEnd_764236 := by exact prefixLift 764236
  have htrace : WordTrace (prefixWord ++ tailWord_764236) baseStart_764236 baseEnd_764236 := by
    simpa [prefixWord, tailWord_764236, baseEnd_764236] using wordTrace_append hprefix tailTrace_764236
  have hstable : (prefixWord ++ tailWord_764236).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_764236).length < 2 ^ (prefixWord ++ tailWord_764236).sum := by decide
  have hdescent : baseEnd_764236 < baseStart_764236 := by decide
  rcases family_descends (prefixWord ++ tailWord_764236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_764266 : List Nat := [3, 1, 3, 3, 1, 2, 9]
def baseStart_764266 : Nat := 118140960795 + 764266 * 2 ^ 59
def prefixEnd_764266 : Nat := 4983230072969 + 3 ^ 40 * 764266 * 2
def baseEnd_764266 : Nat := 9689772984918815789141

theorem tailTrace_764266 : CollatzResearch.WordTrace tailWord_764266 prefixEnd_764266 9689772984918815789141 := by
  unfold tailWord_764266
  simp only [CollatzResearch.WordTrace]
  refine ⟨6968767762300570771546163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18583380699468188724123101 6968767762300570771546163)
  ·
    refine ⟨10453151643450856157319245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6968767762300570771546163 10453151643450856157319245)
    ·
      refine ⟨3919931866294071058994717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10453151643450856157319245 3919931866294071058994717)
      ·
        refine ⟨1469974449860276647123019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3919931866294071058994717 1469974449860276647123019)
        ·
          refine ⟨2204961674790414970684529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1469974449860276647123019 2204961674790414970684529)
          ·
            refine ⟨1653721256092811228013397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2204961674790414970684529 1653721256092811228013397)
            ·
              refine ⟨9689772984918815789141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 1653721256092811228013397 9689772984918815789141)
              ·
                rfl

theorem cell22_764266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 2, 9].length) (baseStart_764266 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_764266 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_764266 prefixEnd_764266 := by exact prefixLift 764266
  have htrace : WordTrace (prefixWord ++ tailWord_764266) baseStart_764266 baseEnd_764266 := by
    simpa [prefixWord, tailWord_764266, baseEnd_764266] using wordTrace_append hprefix tailTrace_764266
  have hstable : (prefixWord ++ tailWord_764266).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_764266).length < 2 ^ (prefixWord ++ tailWord_764266).sum := by decide
  have hdescent : baseEnd_764266 < baseStart_764266 := by decide
  rcases family_descends (prefixWord ++ tailWord_764266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_764279 : List Nat := [1, 1, 3, 1, 1, 2, 2, 3, 2, 6]
def baseStart_764279 : Nat := 118140960795 + 764279 * 2 ^ 59
def prefixEnd_764279 : Nat := 4983230072969 + 3 ^ 40 * 764279 * 2
def baseEnd_764279 : Nat := 261628320758480325731767

theorem tailTrace_764279 : CollatzResearch.WordTrace tailWord_764279 prefixEnd_764279 261628320758480325731767 := by
  unfold tailWord_764279
  simp only [CollatzResearch.WordTrace]
  refine ⟨27875545198155186306407891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18583696798770124204271927 27875545198155186306407891)
  ·
    refine ⟨41813317797232779459611837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27875545198155186306407891 41813317797232779459611837)
    ·
      refine ⟨15679994173962292297354439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 41813317797232779459611837 15679994173962292297354439)
      ·
        refine ⟨23519991260943438446031659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15679994173962292297354439 23519991260943438446031659)
        ·
          refine ⟨35279986891415157669047489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23519991260943438446031659 35279986891415157669047489)
          ·
            refine ⟨26459990168561368251785617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35279986891415157669047489 26459990168561368251785617)
            ·
              refine ⟨19844992626421026188839213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26459990168561368251785617 19844992626421026188839213)
              ·
                refine ⟨7441872234907884820814705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19844992626421026188839213 7441872234907884820814705)
                ·
                  refine ⟨5581404176180913615611029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7441872234907884820814705 5581404176180913615611029)
                  ·
                    refine ⟨261628320758480325731767, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5581404176180913615611029 261628320758480325731767)
                    ·
                      rfl

theorem cell22_764279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 2, 3, 2, 6].length) (baseStart_764279 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_764279 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_764279 prefixEnd_764279 := by exact prefixLift 764279
  have htrace : WordTrace (prefixWord ++ tailWord_764279) baseStart_764279 baseEnd_764279 := by
    simpa [prefixWord, tailWord_764279, baseEnd_764279] using wordTrace_append hprefix tailTrace_764279
  have hstable : (prefixWord ++ tailWord_764279).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_764279).length < 2 ^ (prefixWord ++ tailWord_764279).sum := by decide
  have hdescent : baseEnd_764279 < baseStart_764279 := by decide
  rcases family_descends (prefixWord ++ tailWord_764279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_764328 : List Nat := [2, 1, 6, 1, 1, 1, 2, 1, 7]
def baseStart_764328 : Nat := 118140960795 + 764328 * 2 ^ 59
def prefixEnd_764328 : Nat := 4983230072969 + 3 ^ 40 * 764328 * 2
def baseEnd_764328 : Nat := 87215031486620177085539

theorem tailTrace_764328 : CollatzResearch.WordTrace tailWord_764328 prefixEnd_764328 87215031486620177085539 := by
  unfold tailWord_764328
  simp only [CollatzResearch.WordTrace]
  refine ⟨13938666187488833837470819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18584888249985111783294425 13938666187488833837470819)
  ·
    refine ⟨20907999281233250756206229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13938666187488833837470819 20907999281233250756206229)
    ·
      refine ⟨980062466307808629197167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 20907999281233250756206229 980062466307808629197167)
      ·
        refine ⟨1470093699461712943795751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 980062466307808629197167 1470093699461712943795751)
        ·
          refine ⟨2205140549192569415693627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1470093699461712943795751 2205140549192569415693627)
          ·
            refine ⟨3307710823788854123540441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2205140549192569415693627 3307710823788854123540441)
            ·
              refine ⟨2480783117841640592655331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3307710823788854123540441 2480783117841640592655331)
              ·
                refine ⟨3721174676762460888982997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2480783117841640592655331 3721174676762460888982997)
                ·
                  refine ⟨87215031486620177085539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3721174676762460888982997 87215031486620177085539)
                  ·
                    rfl

theorem cell22_764328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 1, 2, 1, 7].length) (baseStart_764328 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_764328 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_764328 prefixEnd_764328 := by exact prefixLift 764328
  have htrace : WordTrace (prefixWord ++ tailWord_764328) baseStart_764328 baseEnd_764328 := by
    simpa [prefixWord, tailWord_764328, baseEnd_764328] using wordTrace_append hprefix tailTrace_764328
  have hstable : (prefixWord ++ tailWord_764328).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_764328).length < 2 ^ (prefixWord ++ tailWord_764328).sum := by decide
  have hdescent : baseEnd_764328 < baseStart_764328 := by decide
  rcases family_descends (prefixWord ++ tailWord_764328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_764345 : List Nat := [1, 2, 1, 4, 3, 3, 2, 1, 5]
def baseStart_764345 : Nat := 118140960795 + 764345 * 2 ^ 59
def prefixEnd_764345 : Nat := 4983230072969 + 3 ^ 40 * 764345 * 2
def baseEnd_764345 : Nat := 87216971302426051193855

theorem tailTrace_764345 : CollatzResearch.WordTrace tailWord_764345 prefixEnd_764345 87216971302426051193855 := by
  unfold tailWord_764345
  simp only [CollatzResearch.WordTrace]
  refine ⟨27877952415916079578310489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18585301610610719718873659 27877952415916079578310489)
  ·
    refine ⟨20908464311937059683732867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27877952415916079578310489 20908464311937059683732867)
    ·
      refine ⟨31362696467905589525599301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20908464311937059683732867 31362696467905589525599301)
      ·
        refine ⟨5880505587732298036049869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 31362696467905589525599301 5880505587732298036049869)
        ·
          refine ⟨2205189595399611763518701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5880505587732298036049869 2205189595399611763518701)
          ·
            refine ⟨826946098274854411319513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2205189595399611763518701 826946098274854411319513)
            ·
              refine ⟨620209573706140808489635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 826946098274854411319513 620209573706140808489635)
              ·
                refine ⟨930314360559211212734453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 620209573706140808489635 930314360559211212734453)
                ·
                  refine ⟨87216971302426051193855, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 930314360559211212734453 87216971302426051193855)
                  ·
                    rfl

theorem cell22_764345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 3, 2, 1, 5].length) (baseStart_764345 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_764345 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_764345 prefixEnd_764345 := by exact prefixLift 764345
  have htrace : WordTrace (prefixWord ++ tailWord_764345) baseStart_764345 baseEnd_764345 := by
    simpa [prefixWord, tailWord_764345, baseEnd_764345] using wordTrace_append hprefix tailTrace_764345
  have hstable : (prefixWord ++ tailWord_764345).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_764345).length < 2 ^ (prefixWord ++ tailWord_764345).sum := by decide
  have hdescent : baseEnd_764345 < baseStart_764345 := by decide
  rcases family_descends (prefixWord ++ tailWord_764345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_764420 : List Nat := [2, 3, 2, 3, 1, 1, 3, 1, 2, 4]
def baseStart_764420 : Nat := 118140960795 + 764420 * 2 ^ 59
def prefixEnd_764420 : Nat := 4983230072969 + 3 ^ 40 * 764420 * 2
def baseEnd_764420 : Nat := 261676587940002957956335

theorem tailTrace_764420 : CollatzResearch.WordTrace tailWord_764420 prefixEnd_764420 261676587940002957956335 := by
  unfold tailWord_764420
  simp only [CollatzResearch.WordTrace]
  refine ⟨13940343945322183693645357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18587125260429578258193809 13940343945322183693645357)
  ·
    refine ⟨5227628979495818885117009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13940343945322183693645357 5227628979495818885117009)
    ·
      refine ⟨3920721734621864163837757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5227628979495818885117009 3920721734621864163837757)
      ·
        refine ⟨1470270650483199061439159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3920721734621864163837757 1470270650483199061439159)
        ·
          refine ⟨2205405975724798592158739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1470270650483199061439159 2205405975724798592158739)
          ·
            refine ⟨3308108963587197888238109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2205405975724798592158739 3308108963587197888238109)
            ·
              refine ⟨1240540861345199208089291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3308108963587197888238109 1240540861345199208089291)
              ·
                refine ⟨1860811292017798812133937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1240540861345199208089291 1860811292017798812133937)
                ·
                  refine ⟨1395608469013349109100453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1860811292017798812133937 1395608469013349109100453)
                  ·
                    refine ⟨261676587940002957956335, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1395608469013349109100453 261676587940002957956335)
                    ·
                      rfl

theorem cell22_764420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 1, 3, 1, 2, 4].length) (baseStart_764420 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_764420 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_764420 prefixEnd_764420 := by exact prefixLift 764420
  have htrace : WordTrace (prefixWord ++ tailWord_764420) baseStart_764420 baseEnd_764420 := by
    simpa [prefixWord, tailWord_764420, baseEnd_764420] using wordTrace_append hprefix tailTrace_764420
  have hstable : (prefixWord ++ tailWord_764420).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_764420).length < 2 ^ (prefixWord ++ tailWord_764420).sum := by decide
  have hdescent : baseEnd_764420 < baseStart_764420 := by decide
  rcases family_descends (prefixWord ++ tailWord_764420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_764439 : List Nat := [1, 1, 3, 6, 1, 2, 1, 2, 2, 3]
def baseStart_764439 : Nat := 118140960795 + 764439 * 2 ^ 59
def prefixEnd_764439 : Nat := 4983230072969 + 3 ^ 40 * 764439 * 2
def baseEnd_764439 : Nat := 261683092028293241731277

theorem tailTrace_764439 : CollatzResearch.WordTrace tailWord_764439 prefixEnd_764439 261683092028293241731277 := by
  unfold tailWord_764439
  simp only [CollatzResearch.WordTrace]
  refine ⟨27881380877575533632232371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18587587251717022421488247 27881380877575533632232371)
  ·
    refine ⟨41822071316363300448348557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27881380877575533632232371 41822071316363300448348557)
    ·
      refine ⟨15683276743636237668130709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 41822071316363300448348557 15683276743636237668130709)
      ·
        refine ⟨735153597357948640693627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 15683276743636237668130709 735153597357948640693627)
        ·
          refine ⟨1102730396036922961040441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 735153597357948640693627 1102730396036922961040441)
          ·
            refine ⟨827047797027692220780331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1102730396036922961040441 827047797027692220780331)
            ·
              refine ⟨1240571695541538331170497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 827047797027692220780331 1240571695541538331170497)
              ·
                refine ⟨930428771656153748377873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1240571695541538331170497 930428771656153748377873)
                ·
                  refine ⟨697821578742115311283405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 930428771656153748377873 697821578742115311283405)
                  ·
                    refine ⟨261683092028293241731277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 697821578742115311283405 261683092028293241731277)
                    ·
                      rfl

theorem cell22_764439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 1, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 1, 2, 1, 2, 2, 3].length) (baseStart_764439 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_764439 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_764439 prefixEnd_764439 := by exact prefixLift 764439
  have htrace : WordTrace (prefixWord ++ tailWord_764439) baseStart_764439 baseEnd_764439 := by
    simpa [prefixWord, tailWord_764439, baseEnd_764439] using wordTrace_append hprefix tailTrace_764439
  have hstable : (prefixWord ++ tailWord_764439).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_764439).length < 2 ^ (prefixWord ++ tailWord_764439).sum := by decide
  have hdescent : baseEnd_764439 < baseStart_764439 := by decide
  rcases family_descends (prefixWord ++ tailWord_764439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_764491 : List Nat := [1, 1, 1, 1, 3, 1, 4, 2, 8]
def baseStart_764491 : Nat := 118140960795 + 764491 * 2 ^ 59
def prefixEnd_764491 : Nat := 4983230072969 + 3 ^ 40 * 764491 * 2
def baseEnd_764491 : Nat := 87233630896994146477039

theorem tailTrace_764491 : CollatzResearch.WordTrace tailWord_764491 prefixEnd_764491 87233630896994146477039 := by
  unfold tailWord_764491
  simp only [CollatzResearch.WordTrace]
  refine ⟨27883277473387146513125327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18588851648924764342083551 27883277473387146513125327)
  ·
    refine ⟨41824916210080719769687991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27883277473387146513125327 41824916210080719769687991)
    ·
      refine ⟨62737374315121079654531987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41824916210080719769687991 62737374315121079654531987)
      ·
        refine ⟨94106061472681619481797981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62737374315121079654531987 94106061472681619481797981)
        ·
          refine ⟨35289773052255607305674243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 94106061472681619481797981 35289773052255607305674243)
          ·
            refine ⟨52934659578383410958511365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35289773052255607305674243 52934659578383410958511365)
            ·
              refine ⟨9925248670946889554720881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 52934659578383410958511365 9925248670946889554720881)
              ·
                refine ⟨7443936503210167166040661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9925248670946889554720881 7443936503210167166040661)
                ·
                  refine ⟨87233630896994146477039, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 7443936503210167166040661 87233630896994146477039)
                  ·
                    rfl

theorem cell22_764491_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 4, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 4, 2, 8].length) (baseStart_764491 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_764491 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_764491 prefixEnd_764491 := by exact prefixLift 764491
  have htrace : WordTrace (prefixWord ++ tailWord_764491) baseStart_764491 baseEnd_764491 := by
    simpa [prefixWord, tailWord_764491, baseEnd_764491] using wordTrace_append hprefix tailTrace_764491
  have hstable : (prefixWord ++ tailWord_764491).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_764491).length < 2 ^ (prefixWord ++ tailWord_764491).sum := by decide
  have hdescent : baseEnd_764491 < baseStart_764491 := by decide
  rcases family_descends (prefixWord ++ tailWord_764491) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_764523 : List Nat := [1, 1, 1, 1, 2, 2, 1, 4, 6, 3]
def baseStart_764523 : Nat := 118140960795 + 764523 * 2 ^ 59
def prefixEnd_764523 : Nat := 4983230072969 + 3 ^ 40 * 764523 * 2
def baseEnd_764523 : Nat := 261711846944945022631019

theorem tailTrace_764523 : CollatzResearch.WordTrace tailWord_764523 prefixEnd_764523 261711846944945022631019 := by
  unfold tailWord_764523
  simp only [CollatzResearch.WordTrace]
  refine ⟨27884444609271215978290223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18589629739514143985526815 27884444609271215978290223)
  ·
    refine ⟨41826666913906823967435335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27884444609271215978290223 41826666913906823967435335)
    ·
      refine ⟨62740000370860235951153003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41826666913906823967435335 62740000370860235951153003)
      ·
        refine ⟨94110000556290353926729505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62740000370860235951153003 94110000556290353926729505)
        ·
          refine ⟨70582500417217765445047129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 94110000556290353926729505 70582500417217765445047129)
          ·
            refine ⟨52936875312913324083785347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 70582500417217765445047129 52936875312913324083785347)
            ·
              refine ⟨79405312969369986125678021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52936875312913324083785347 79405312969369986125678021)
              ·
                refine ⟨14888496181756872398564629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 79405312969369986125678021 14888496181756872398564629)
                ·
                  refine ⟨697898258519853393682717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 14888496181756872398564629 697898258519853393682717)
                  ·
                    refine ⟨261711846944945022631019, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 697898258519853393682717 261711846944945022631019)
                    ·
                      rfl

theorem cell22_764523_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 4, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 4, 6, 3].length) (baseStart_764523 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_764523 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_764523 prefixEnd_764523 := by exact prefixLift 764523
  have htrace : WordTrace (prefixWord ++ tailWord_764523) baseStart_764523 baseEnd_764523 := by
    simpa [prefixWord, tailWord_764523, baseEnd_764523] using wordTrace_append hprefix tailTrace_764523
  have hstable : (prefixWord ++ tailWord_764523).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_764523).length < 2 ^ (prefixWord ++ tailWord_764523).sum := by decide
  have hdescent : baseEnd_764523 < baseStart_764523 := by decide
  rcases family_descends (prefixWord ++ tailWord_764523) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_764632 : List Nat := [2, 1, 2, 2, 3, 3, 3, 1, 5]
def baseStart_764632 : Nat := 118140960795 + 764632 * 2 ^ 59
def prefixEnd_764632 : Nat := 4983230072969 + 3 ^ 40 * 764632 * 2
def baseEnd_764632 : Nat := 87249719957501690551895

theorem tailTrace_764632 : CollatzResearch.WordTrace tailWord_764632 prefixEnd_764632 87249719957501690551895 := by
  unfold tailWord_764632
  simp only [CollatzResearch.WordTrace]
  refine ⟨13944210082938163797004075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18592280110584218396005433 13944210082938163797004075)
  ·
    refine ⟨20916315124407245695506113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13944210082938163797004075 20916315124407245695506113)
    ·
      refine ⟨15687236343305434271629585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20916315124407245695506113 15687236343305434271629585)
      ·
        refine ⟨11765427257479075703722189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15687236343305434271629585 11765427257479075703722189)
        ·
          refine ⟨4412035221554653388895821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11765427257479075703722189 4412035221554653388895821)
          ·
            refine ⟨1654513208082995020835933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4412035221554653388895821 1654513208082995020835933)
            ·
              refine ⟨620442453031123132813475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1654513208082995020835933 620442453031123132813475)
              ·
                refine ⟨930663679546684699220213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 620442453031123132813475 930663679546684699220213)
                ·
                  refine ⟨87249719957501690551895, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 930663679546684699220213 87249719957501690551895)
                  ·
                    rfl

theorem cell22_764632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 3, 3, 1, 5].length) (baseStart_764632 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_764632 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_764632 prefixEnd_764632 := by exact prefixLift 764632
  have htrace : WordTrace (prefixWord ++ tailWord_764632) baseStart_764632 baseEnd_764632 := by
    simpa [prefixWord, tailWord_764632, baseEnd_764632] using wordTrace_append hprefix tailTrace_764632
  have hstable : (prefixWord ++ tailWord_764632).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_764632).length < 2 ^ (prefixWord ++ tailWord_764632).sum := by decide
  have hdescent : baseEnd_764632 < baseStart_764632 := by decide
  rcases family_descends (prefixWord ++ tailWord_764632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_764662 : List Nat := [5, 1, 1, 1, 1, 2, 1, 5, 1, 4]
def baseStart_764662 : Nat := 118140960795 + 764662 * 2 ^ 59
def prefixEnd_764662 : Nat := 4983230072969 + 3 ^ 40 * 764662 * 2
def baseEnd_764662 : Nat := 261759429485594993405593

theorem tailTrace_764662 : CollatzResearch.WordTrace tailWord_764662 prefixEnd_764662 261759429485594993405593 := by
  unfold tailWord_764662
  simp only [CollatzResearch.WordTrace]
  refine ⟨1743094647235477669850015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 18593009570511761811733493 1743094647235477669850015)
  ·
    refine ⟨2614641970853216504775023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1743094647235477669850015 2614641970853216504775023)
    ·
      refine ⟨3921962956279824757162535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2614641970853216504775023 3921962956279824757162535)
      ·
        refine ⟨5882944434419737135743803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3921962956279824757162535 5882944434419737135743803)
        ·
          refine ⟨8824416651629605703615705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5882944434419737135743803 8824416651629605703615705)
          ·
            refine ⟨6618312488722204277711779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8824416651629605703615705 6618312488722204277711779)
            ·
              refine ⟨9927468733083306416567669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6618312488722204277711779 9927468733083306416567669)
              ·
                refine ⟨930700193726559976553219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 9927468733083306416567669 930700193726559976553219)
                ·
                  refine ⟨1396050290589839964829829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 930700193726559976553219 1396050290589839964829829)
                  ·
                    refine ⟨261759429485594993405593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1396050290589839964829829 261759429485594993405593)
                    ·
                      rfl

theorem cell22_764662_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 1, 5, 1, 4].length) (baseStart_764662 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_764662 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_764662 prefixEnd_764662 := by exact prefixLift 764662
  have htrace : WordTrace (prefixWord ++ tailWord_764662) baseStart_764662 baseEnd_764662 := by
    simpa [prefixWord, tailWord_764662, baseEnd_764662] using wordTrace_append hprefix tailTrace_764662
  have hstable : (prefixWord ++ tailWord_764662).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_764662).length < 2 ^ (prefixWord ++ tailWord_764662).sum := by decide
  have hdescent : baseEnd_764662 < baseStart_764662 := by decide
  rcases family_descends (prefixWord ++ tailWord_764662) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_764735 : List Nat := [1, 1, 2, 2, 5, 1, 1, 1, 2, 6]
def baseStart_764735 : Nat := 118140960795 + 764735 * 2 ^ 59
def prefixEnd_764735 : Nat := 4983230072969 + 3 ^ 40 * 764735 * 2
def baseEnd_764735 : Nat := 261784418877447136330369

theorem tailTrace_764735 : CollatzResearch.WordTrace tailWord_764735 prefixEnd_764735 261784418877447136330369 := by
  unfold tailWord_764735
  simp only [CollatzResearch.WordTrace]
  refine ⟨27892176884503176185007659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18594784589668784123338439 27892176884503176185007659)
  ·
    refine ⟨41838265326754764277511489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27892176884503176185007659 41838265326754764277511489)
    ·
      refine ⟨31378698995066073208133617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41838265326754764277511489 31378698995066073208133617)
      ·
        refine ⟨23534024246299554906100213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31378698995066073208133617 23534024246299554906100213)
        ·
          refine ⟨2206314773090583272446895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 23534024246299554906100213 2206314773090583272446895)
          ·
            refine ⟨3309472159635874908670343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2206314773090583272446895 3309472159635874908670343)
            ·
              refine ⟨4964208239453812363005515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3309472159635874908670343 4964208239453812363005515)
              ·
                refine ⟨7446312359180718544508273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4964208239453812363005515 7446312359180718544508273)
                ·
                  refine ⟨5584734269385538908381205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7446312359180718544508273 5584734269385538908381205)
                  ·
                    refine ⟨261784418877447136330369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5584734269385538908381205 261784418877447136330369)
                    ·
                      rfl

theorem cell22_764735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 1, 1, 1, 2, 6].length) (baseStart_764735 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_764735 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_764735 prefixEnd_764735 := by exact prefixLift 764735
  have htrace : WordTrace (prefixWord ++ tailWord_764735) baseStart_764735 baseEnd_764735 := by
    simpa [prefixWord, tailWord_764735, baseEnd_764735] using wordTrace_append hprefix tailTrace_764735
  have hstable : (prefixWord ++ tailWord_764735).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_764735).length < 2 ^ (prefixWord ++ tailWord_764735).sum := by decide
  have hdescent : baseEnd_764735 < baseStart_764735 := by decide
  rcases family_descends (prefixWord ++ tailWord_764735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_764771 : List Nat := [1, 1, 1, 5, 3, 2, 2, 3, 1, 3]
def baseStart_764771 : Nat := 118140960795 + 764771 * 2 ^ 59
def prefixEnd_764771 : Nat := 4983230072969 + 3 ^ 40 * 764771 * 2
def baseEnd_764771 : Nat := 261796742413155042430259

theorem tailTrace_764771 : CollatzResearch.WordTrace tailWord_764771 prefixEnd_764771 261796742413155042430259 := by
  unfold tailWord_764771
  simp only [CollatzResearch.WordTrace]
  refine ⟨27893489912372754333318167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18595659941581836222212111 27893489912372754333318167)
  ·
    refine ⟨41840234868559131499977251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27893489912372754333318167 41840234868559131499977251)
    ·
      refine ⟨62760352302838697249965877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41840234868559131499977251 62760352302838697249965877)
      ·
        refine ⟨5883783028391127867184301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 62760352302838697249965877 5883783028391127867184301)
        ·
          refine ⟨2206418635646672950194113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5883783028391127867184301 2206418635646672950194113)
          ·
            refine ⟨1654813976735004712645585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2206418635646672950194113 1654813976735004712645585)
            ·
              refine ⟨1241110482551253534484189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1654813976735004712645585 1241110482551253534484189)
              ·
                refine ⟨465416430956720075431571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1241110482551253534484189 465416430956720075431571)
                ·
                  refine ⟨698124646435080113147357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 465416430956720075431571 698124646435080113147357)
                  ·
                    refine ⟨261796742413155042430259, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 698124646435080113147357 261796742413155042430259)
                    ·
                      rfl

theorem cell22_764771_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 2, 2, 3, 1, 3].length) (baseStart_764771 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_764771 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_764771 prefixEnd_764771 := by exact prefixLift 764771
  have htrace : WordTrace (prefixWord ++ tailWord_764771) baseStart_764771 baseEnd_764771 := by
    simpa [prefixWord, tailWord_764771, baseEnd_764771] using wordTrace_append hprefix tailTrace_764771
  have hstable : (prefixWord ++ tailWord_764771).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_764771).length < 2 ^ (prefixWord ++ tailWord_764771).sum := by decide
  have hdescent : baseEnd_764771 < baseStart_764771 := by decide
  rcases family_descends (prefixWord ++ tailWord_764771) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_764795 : List Nat := [1, 1, 1, 1, 1, 5, 3, 3, 6]
def baseStart_764795 : Nat := 118140960795 + 764795 * 2 ^ 59
def prefixEnd_764795 : Nat := 4983230072969 + 3 ^ 40 * 764795 * 2
def baseEnd_764795 : Nat := 87268319367875659943395

theorem tailTrace_764795 : CollatzResearch.WordTrace tailWord_764795 prefixEnd_764795 87268319367875659943395 := by
  unfold tailWord_764795
  simp only [CollatzResearch.WordTrace]
  refine ⟨27894365264285806432191839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18596243509523870954794559 27894365264285806432191839)
  ·
    refine ⟨41841547896428709648287759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27894365264285806432191839 41841547896428709648287759)
    ·
      refine ⟨62762321844643064472431639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41841547896428709648287759 62762321844643064472431639)
      ·
        refine ⟨94143482766964596708647459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62762321844643064472431639 94143482766964596708647459)
        ·
          refine ⟨141215224150446895062971189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 94143482766964596708647459 141215224150446895062971189)
          ·
            refine ⟨13238927264104396412153549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 141215224150446895062971189 13238927264104396412153549)
            ·
              refine ⟨4964597724039148654557581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13238927264104396412153549 4964597724039148654557581)
              ·
                refine ⟨1861724146514680745459093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4964597724039148654557581 1861724146514680745459093)
                ·
                  refine ⟨87268319367875659943395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1861724146514680745459093 87268319367875659943395)
                  ·
                    rfl

theorem cell22_764795_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 3, 3, 6].length) (baseStart_764795 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_764795 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_764795 prefixEnd_764795 := by exact prefixLift 764795
  have htrace : WordTrace (prefixWord ++ tailWord_764795) baseStart_764795 baseEnd_764795 := by
    simpa [prefixWord, tailWord_764795, baseEnd_764795] using wordTrace_append hprefix tailTrace_764795
  have hstable : (prefixWord ++ tailWord_764795).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_764795).length < 2 ^ (prefixWord ++ tailWord_764795).sum := by decide
  have hdescent : baseEnd_764795 < baseStart_764795 := by decide
  rcases family_descends (prefixWord ++ tailWord_764795) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_764822 : List Nat := [5, 3, 1, 1, 1, 3, 1, 3, 1, 3]
def baseStart_764822 : Nat := 118140960795 + 764822 * 2 ^ 59
def prefixEnd_764822 : Nat := 4983230072969 + 3 ^ 40 * 764822 * 2
def baseEnd_764822 : Nat := 261814200755407909405103

theorem tailTrace_764822 : CollatzResearch.WordTrace tailWord_764822 prefixEnd_764822 261814200755407909405103 := by
  unfold tailWord_764822
  simp only [CollatzResearch.WordTrace]
  refine ⟨1743459377199249377714045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 18596900023458660028949813 1743459377199249377714045)
  ·
    refine ⟨653797266449718516642767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1743459377199249377714045 653797266449718516642767)
    ·
      refine ⟨980695899674577774964151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 653797266449718516642767 980695899674577774964151)
      ·
        refine ⟨1471043849511866662446227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 980695899674577774964151 1471043849511866662446227)
        ·
          refine ⟨2206565774267799993669341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1471043849511866662446227 2206565774267799993669341)
          ·
            refine ⟨827462165350424997626003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2206565774267799993669341 827462165350424997626003)
            ·
              refine ⟨1241193248025637496439005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 827462165350424997626003 1241193248025637496439005)
              ·
                refine ⟨465447468009614061164627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1241193248025637496439005 465447468009614061164627)
                ·
                  refine ⟨698171202014421091746941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 465447468009614061164627 698171202014421091746941)
                  ·
                    refine ⟨261814200755407909405103, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 698171202014421091746941 261814200755407909405103)
                    ·
                      rfl

theorem cell22_764822_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 3, 1, 3, 1, 3].length) (baseStart_764822 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_764822 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_764822 prefixEnd_764822 := by exact prefixLift 764822
  have htrace : WordTrace (prefixWord ++ tailWord_764822) baseStart_764822 baseEnd_764822 := by
    simpa [prefixWord, tailWord_764822, baseEnd_764822] using wordTrace_append hprefix tailTrace_764822
  have hstable : (prefixWord ++ tailWord_764822).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_764822).length < 2 ^ (prefixWord ++ tailWord_764822).sum := by decide
  have hdescent : baseEnd_764822 < baseStart_764822 := by decide
  rcases family_descends (prefixWord ++ tailWord_764822) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_764857 : List Nat := [1, 2, 1, 4, 2, 3, 2, 7]
def baseStart_764857 : Nat := 118140960795 + 764857 * 2 ^ 59
def prefixEnd_764857 : Nat := 4983230072969 + 3 ^ 40 * 764857 * 2
def baseEnd_764857 : Nat := 29091797996742164975555

theorem tailTrace_764857 : CollatzResearch.WordTrace tailWord_764857 prefixEnd_764857 29091797996742164975555 := by
  unfold tailWord_764857
  simp only [CollatzResearch.WordTrace]
  refine ⟨27896626590061191020948825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18597751060040794013965883 27896626590061191020948825)
  ·
    refine ⟨20922469942545893265711619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27896626590061191020948825 20922469942545893265711619)
    ·
      refine ⟨31383704913818839898567429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20922469942545893265711619 31383704913818839898567429)
      ·
        refine ⟨5884444671341032480981393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 31383704913818839898567429 5884444671341032480981393)
        ·
          refine ⟨4413333503505774360736045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5884444671341032480981393 4413333503505774360736045)
          ·
            refine ⟨1655000063814665385276017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4413333503505774360736045 1655000063814665385276017)
            ·
              refine ⟨1241250047860999038957013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1655000063814665385276017 1241250047860999038957013)
              ·
                refine ⟨29091797996742164975555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1241250047860999038957013 29091797996742164975555)
                ·
                  rfl

theorem cell22_764857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 3, 2, 7].length) (baseStart_764857 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_764857 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_764857 prefixEnd_764857 := by exact prefixLift 764857
  have htrace : WordTrace (prefixWord ++ tailWord_764857) baseStart_764857 baseEnd_764857 := by
    simpa [prefixWord, tailWord_764857, baseEnd_764857] using wordTrace_append hprefix tailTrace_764857
  have hstable : (prefixWord ++ tailWord_764857).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_764857).length < 2 ^ (prefixWord ++ tailWord_764857).sum := by decide
  have hdescent : baseEnd_764857 < baseStart_764857 := by decide
  rcases family_descends (prefixWord ++ tailWord_764857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_764861 : List Nat := [1, 4, 1, 2, 4, 1, 1, 3, 2, 3]
def baseStart_764861 : Nat := 118140960795 + 764861 * 2 ^ 59
def prefixEnd_764861 : Nat := 4983230072969 + 3 ^ 40 * 764861 * 2
def baseEnd_764861 : Nat := 261827551252424807679983

theorem tailTrace_764861 : CollatzResearch.WordTrace tailWord_764861 prefixEnd_764861 261827551252424807679983 := by
  unfold tailWord_764861
  simp only [CollatzResearch.WordTrace]
  refine ⟨27896772482046699704094437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18597848321364466469396291 27896772482046699704094437)
  ·
    refine ⟨5230644840383756194517707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 27896772482046699704094437 5230644840383756194517707)
    ·
      refine ⟨7845967260575634291776561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5230644840383756194517707 7845967260575634291776561)
      ·
        refine ⟨5884475445431725718832421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7845967260575634291776561 5884475445431725718832421)
        ·
          refine ⟨1103339146018448572281079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5884475445431725718832421 1103339146018448572281079)
          ·
            refine ⟨1655008719027672858421619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1103339146018448572281079 1655008719027672858421619)
            ·
              refine ⟨2482513078541509287632429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1655008719027672858421619 2482513078541509287632429)
              ·
                refine ⟨930942404453065982862161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2482513078541509287632429 930942404453065982862161)
                ·
                  refine ⟨698206803339799487146621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 930942404453065982862161 698206803339799487146621)
                  ·
                    refine ⟨261827551252424807679983, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 698206803339799487146621 261827551252424807679983)
                    ·
                      rfl

theorem cell22_764861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 4, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 4, 1, 1, 3, 2, 3].length) (baseStart_764861 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_764861 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_764861 prefixEnd_764861 := by exact prefixLift 764861
  have htrace : WordTrace (prefixWord ++ tailWord_764861) baseStart_764861 baseEnd_764861 := by
    simpa [prefixWord, tailWord_764861, baseEnd_764861] using wordTrace_append hprefix tailTrace_764861
  have hstable : (prefixWord ++ tailWord_764861).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_764861).length < 2 ^ (prefixWord ++ tailWord_764861).sum := by decide
  have hdescent : baseEnd_764861 < baseStart_764861 := by decide
  rcases family_descends (prefixWord ++ tailWord_764861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_764964 : List Nat := [2, 3, 1, 4, 1, 1, 1, 3, 6]
def baseStart_764964 : Nat := 118140960795 + 764964 * 2 ^ 59
def prefixEnd_764964 : Nat := 4983230072969 + 3 ^ 40 * 764964 * 2
def baseEnd_764964 : Nat := 87287603419122290784889

theorem tailTrace_764964 : CollatzResearch.WordTrace tailWord_764964 prefixEnd_764964 87287603419122290784889 := by
  unfold tailWord_764964
  simp only [CollatzResearch.WordTrace]
  refine ⟨13950264600336774147546973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18600352800449032196729297 13950264600336774147546973)
  ·
    refine ⟨5231349225126290305330115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13950264600336774147546973 5231349225126290305330115)
    ·
      refine ⟨7847023837689435457995173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5231349225126290305330115 7847023837689435457995173)
      ·
        refine ⟨1471316969566769148374095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 7847023837689435457995173 1471316969566769148374095)
        ·
          refine ⟨2206975454350153722561143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1471316969566769148374095 2206975454350153722561143)
          ·
            refine ⟨3310463181525230583841715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2206975454350153722561143 3310463181525230583841715)
            ·
              refine ⟨4965694772287845875762573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3310463181525230583841715 4965694772287845875762573)
              ·
                refine ⟨1862135539607942203410965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4965694772287845875762573 1862135539607942203410965)
                ·
                  refine ⟨87287603419122290784889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1862135539607942203410965 87287603419122290784889)
                  ·
                    rfl

theorem cell22_764964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 1, 1, 3, 6].length) (baseStart_764964 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_764964 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_764964 prefixEnd_764964 := by exact prefixLift 764964
  have htrace : WordTrace (prefixWord ++ tailWord_764964) baseStart_764964 baseEnd_764964 := by
    simpa [prefixWord, tailWord_764964, baseEnd_764964] using wordTrace_append hprefix tailTrace_764964
  have hstable : (prefixWord ++ tailWord_764964).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_764964).length < 2 ^ (prefixWord ++ tailWord_764964).sum := by decide
  have hdescent : baseEnd_764964 < baseStart_764964 := by decide
  rcases family_descends (prefixWord ++ tailWord_764964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_764977 : List Nat := [1, 2, 2, 3, 1, 2, 1, 1, 3, 6]
def baseStart_764977 : Nat := 118140960795 + 764977 * 2 ^ 59
def prefixEnd_764977 : Nat := 4983230072969 + 3 ^ 40 * 764977 * 2
def baseEnd_764977 : Nat := 261867260423039171779627

theorem tailTrace_764977 : CollatzResearch.WordTrace tailWord_764977 prefixEnd_764977 261867260423039171779627 := by
  unfold tailWord_764977
  simp only [CollatzResearch.WordTrace]
  refine ⟨27901003349626451515317185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18600668899750967676878123 27901003349626451515317185)
  ·
    refine ⟨20925752512219838636487889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27901003349626451515317185 20925752512219838636487889)
    ·
      refine ⟨15694314384164878977365917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20925752512219838636487889 15694314384164878977365917)
      ·
        refine ⟨5885367894061829616512219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15694314384164878977365917 5885367894061829616512219)
        ·
          refine ⟨8828051841092744424768329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5885367894061829616512219 8828051841092744424768329)
          ·
            refine ⟨6621038880819558318576247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8828051841092744424768329 6621038880819558318576247)
            ·
              refine ⟨9931558321229337477864371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6621038880819558318576247 9931558321229337477864371)
              ·
                refine ⟨14897337481844006216796557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9931558321229337477864371 14897337481844006216796557)
                ·
                  refine ⟨5586501555691502331298709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14897337481844006216796557 5586501555691502331298709)
                  ·
                    refine ⟨261867260423039171779627, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5586501555691502331298709 261867260423039171779627)
                    ·
                      rfl

theorem cell22_764977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 1, 1, 3, 6].length) (baseStart_764977 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_764977 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_764977 prefixEnd_764977 := by exact prefixLift 764977
  have htrace : WordTrace (prefixWord ++ tailWord_764977) baseStart_764977 baseEnd_764977 := by
    simpa [prefixWord, tailWord_764977, baseEnd_764977] using wordTrace_append hprefix tailTrace_764977
  have hstable : (prefixWord ++ tailWord_764977).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_764977).length < 2 ^ (prefixWord ++ tailWord_764977).sum := by decide
  have hdescent : baseEnd_764977 < baseStart_764977 := by decide
  rcases family_descends (prefixWord ++ tailWord_764977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_764992 : List Nat := [2, 1, 1, 2, 2, 3, 3, 8]
def baseStart_764992 : Nat := 118140960795 + 764992 * 2 ^ 59
def prefixEnd_764992 : Nat := 4983230072969 + 3 ^ 40 * 764992 * 2
def baseEnd_764992 : Nat := 29096932803287125850509

theorem tailTrace_764992 : CollatzResearch.WordTrace tailWord_764992 prefixEnd_764992 29096932803287125850509 := by
  unfold tailWord_764992
  simp only [CollatzResearch.WordTrace]
  refine ⟨13950775222286054538556615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18601033629714739384742153 13950775222286054538556615)
  ·
    refine ⟨20926162833429081807834923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13950775222286054538556615 20926162833429081807834923)
    ·
      refine ⟨31389244250143622711752385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20926162833429081807834923 31389244250143622711752385)
      ·
        refine ⟨23541933187607717033814289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31389244250143622711752385 23541933187607717033814289)
        ·
          refine ⟨17656449890705787775360717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23541933187607717033814289 17656449890705787775360717)
          ·
            refine ⟨6621168709014670415760269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17656449890705787775360717 6621168709014670415760269)
            ·
              refine ⟨2482938265880501405910101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6621168709014670415760269 2482938265880501405910101)
              ·
                refine ⟨29096932803287125850509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 2482938265880501405910101 29096932803287125850509)
                ·
                  rfl

theorem cell22_764992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 3, 8].length) (baseStart_764992 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_764992 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_764992 prefixEnd_764992 := by exact prefixLift 764992
  have htrace : WordTrace (prefixWord ++ tailWord_764992) baseStart_764992 baseEnd_764992 := by
    simpa [prefixWord, tailWord_764992, baseEnd_764992] using wordTrace_append hprefix tailTrace_764992
  have hstable : (prefixWord ++ tailWord_764992).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_764992).length < 2 ^ (prefixWord ++ tailWord_764992).sum := by decide
  have hdescent : baseEnd_764992 < baseStart_764992 := by decide
  rcases family_descends (prefixWord ++ tailWord_764992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_765026 : List Nat := [3, 3, 2, 2, 1, 2, 2, 7]
def baseStart_765026 : Nat := 118140960795 + 765026 * 2 ^ 59
def prefixEnd_765026 : Nat := 4983230072969 + 3 ^ 40 * 765026 * 2
def baseEnd_765026 : Nat := 29098226013824375256053

theorem tailTrace_765026 : CollatzResearch.WordTrace tailWord_765026 prefixEnd_765026 29098226013824375256053 := by
  unfold tailWord_765026
  simp only [CollatzResearch.WordTrace]
  refine ⟨6975697631612233220962733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18601860350965955255900621 6975697631612233220962733)
  ·
    refine ⟨2615886611854587457861025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6975697631612233220962733 2615886611854587457861025)
    ·
      refine ⟨1961914958890940593395769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2615886611854587457861025 1961914958890940593395769)
      ·
        refine ⟨1471436219168205445046827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1961914958890940593395769 1471436219168205445046827)
        ·
          refine ⟨2207154328752308167570241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1471436219168205445046827 2207154328752308167570241)
          ·
            refine ⟨1655365746564231125677681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2207154328752308167570241 1655365746564231125677681)
            ·
              refine ⟨1241524309923173344258261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1655365746564231125677681 1241524309923173344258261)
              ·
                refine ⟨29098226013824375256053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1241524309923173344258261 29098226013824375256053)
                ·
                  rfl

theorem cell22_765026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 2, 2, 7].length) (baseStart_765026 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_765026 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_765026 prefixEnd_765026 := by exact prefixLift 765026
  have htrace : WordTrace (prefixWord ++ tailWord_765026) baseStart_765026 baseEnd_765026 := by
    simpa [prefixWord, tailWord_765026, baseEnd_765026] using wordTrace_append hprefix tailTrace_765026
  have hstable : (prefixWord ++ tailWord_765026).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_765026).length < 2 ^ (prefixWord ++ tailWord_765026).sum := by decide
  have hdescent : baseEnd_765026 < baseStart_765026 := by decide
  rcases family_descends (prefixWord ++ tailWord_765026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_765086 : List Nat := [4, 3, 1, 1, 2, 1, 1, 1, 1, 7]
def baseStart_765086 : Nat := 118140960795 + 765086 * 2 ^ 59
def prefixEnd_765086 : Nat := 4983230072969 + 3 ^ 40 * 765086 * 2
def baseEnd_765086 : Nat := 261904573350599220804293

theorem tailTrace_765086 : CollatzResearch.WordTrace tailWord_765086 prefixEnd_765086 261904573350599220804293 := by
  unfold tailWord_765086
  simp only [CollatzResearch.WordTrace]
  refine ⟨3488122363278945391379389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 18603319270821042087356741 3488122363278945391379389)
  ·
    refine ⟨1308045886229604521767271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3488122363278945391379389 1308045886229604521767271)
    ·
      refine ⟨1962068829344406782650907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1308045886229604521767271 1962068829344406782650907)
      ·
        refine ⟨2943103244016610173976361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1962068829344406782650907 2943103244016610173976361)
        ·
          refine ⟨2207327433012457630482271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2943103244016610173976361 2207327433012457630482271)
          ·
            refine ⟨3310991149518686445723407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2207327433012457630482271 3310991149518686445723407)
            ·
              refine ⟨4966486724278029668585111, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3310991149518686445723407 4966486724278029668585111)
              ·
                refine ⟨7449730086417044502877667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4966486724278029668585111 7449730086417044502877667)
                ·
                  refine ⟨11174595129625566754316501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7449730086417044502877667 11174595129625566754316501)
                  ·
                    refine ⟨261904573350599220804293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 11174595129625566754316501 261904573350599220804293)
                    ·
                      rfl

theorem cell22_765086_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 1, 1, 1, 1, 7].length) (baseStart_765086 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_765086 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_765086 prefixEnd_765086 := by exact prefixLift 765086
  have htrace : WordTrace (prefixWord ++ tailWord_765086) baseStart_765086 baseEnd_765086 := by
    simpa [prefixWord, tailWord_765086, baseEnd_765086] using wordTrace_append hprefix tailTrace_765086
  have hstable : (prefixWord ++ tailWord_765086).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_765086).length < 2 ^ (prefixWord ++ tailWord_765086).sum := by decide
  have hdescent : baseEnd_765086 < baseStart_765086 := by decide
  rcases family_descends (prefixWord ++ tailWord_765086) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_765118 : List Nat := [4, 2, 1, 1, 3, 2, 1, 3, 1, 4]
def baseStart_765118 : Nat := 118140960795 + 765118 * 2 ^ 59
def prefixEnd_765118 : Nat := 4983230072969 + 3 ^ 40 * 765118 * 2
def baseEnd_765118 : Nat := 261915527604561804004195

theorem tailTrace_765118 : CollatzResearch.WordTrace tailWord_765118 prefixEnd_765118 261915527604561804004195 := by
  unfold tailWord_765118
  simp only [CollatzResearch.WordTrace]
  refine ⟨3488268255264454074525001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 18604097361410421730800005 3488268255264454074525001)
  ·
    refine ⟨2616201191448340555893751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3488268255264454074525001 2616201191448340555893751)
    ·
      refine ⟨3924301787172510833840627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2616201191448340555893751 3924301787172510833840627)
      ·
        refine ⟨5886452680758766250760941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3924301787172510833840627 5886452680758766250760941)
        ·
          refine ⟨2207419755284537344035353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5886452680758766250760941 2207419755284537344035353)
          ·
            refine ⟨1655564816463403008026515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2207419755284537344035353 1655564816463403008026515)
            ·
              refine ⟨2483347224695104512039773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1655564816463403008026515 2483347224695104512039773)
              ·
                refine ⟨931255209260664192014915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2483347224695104512039773 931255209260664192014915)
                ·
                  refine ⟨1396882813890996288022373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 931255209260664192014915 1396882813890996288022373)
                  ·
                    refine ⟨261915527604561804004195, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1396882813890996288022373 261915527604561804004195)
                    ·
                      rfl

theorem cell22_765118_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 2, 1, 3, 1, 4].length) (baseStart_765118 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_765118 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_765118 prefixEnd_765118 := by exact prefixLift 765118
  have htrace : WordTrace (prefixWord ++ tailWord_765118) baseStart_765118 baseEnd_765118 := by
    simpa [prefixWord, tailWord_765118, baseEnd_765118] using wordTrace_append hprefix tailTrace_765118
  have hstable : (prefixWord ++ tailWord_765118).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_765118).length < 2 ^ (prefixWord ++ tailWord_765118).sum := by decide
  have hdescent : baseEnd_765118 < baseStart_765118 := by decide
  rcases family_descends (prefixWord ++ tailWord_765118) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_765122 : List Nat := [3, 5, 1, 1, 2, 2, 1, 2, 5]
def baseStart_765122 : Nat := 118140960795 + 765122 * 2 ^ 59
def prefixEnd_765122 : Nat := 4983230072969 + 3 ^ 40 * 765122 * 2
def baseEnd_765122 : Nat := 87305632295435708968061

theorem tailTrace_765122 : CollatzResearch.WordTrace tailWord_765122 prefixEnd_765122 87305632295435708968061 := by
  unfold tailWord_765122
  simp only [CollatzResearch.WordTrace]
  refine ⟨6976572983525285319836405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18604194622734094186230413 6976572983525285319836405)
  ·
    refine ⟨654053717205495498734663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 6976572983525285319836405 654053717205495498734663)
    ·
      refine ⟨981080575808243248101995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 654053717205495498734663 981080575808243248101995)
      ·
        refine ⟨1471620863712364872152993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 981080575808243248101995 1471620863712364872152993)
        ·
          refine ⟨1103715647784273654114745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1471620863712364872152993 1103715647784273654114745)
          ·
            refine ⟨827786735838205240586059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1103715647784273654114745 827786735838205240586059)
            ·
              refine ⟨1241680103757307860879089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 827786735838205240586059 1241680103757307860879089)
              ·
                refine ⟨931260077817980895659317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1241680103757307860879089 931260077817980895659317)
                ·
                  refine ⟨87305632295435708968061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 931260077817980895659317 87305632295435708968061)
                  ·
                    rfl

theorem cell22_765122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 2, 2, 1, 2, 5].length) (baseStart_765122 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_765122 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_765122 prefixEnd_765122 := by exact prefixLift 765122
  have htrace : WordTrace (prefixWord ++ tailWord_765122) baseStart_765122 baseEnd_765122 := by
    simpa [prefixWord, tailWord_765122, baseEnd_765122] using wordTrace_append hprefix tailTrace_765122
  have hstable : (prefixWord ++ tailWord_765122).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_765122).length < 2 ^ (prefixWord ++ tailWord_765122).sum := by decide
  have hdescent : baseEnd_765122 < baseStart_765122 := by decide
  rcases family_descends (prefixWord ++ tailWord_765122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_765131 : List Nat := [1, 1, 1, 1, 3, 2, 2, 6, 2, 3]
def baseStart_765131 : Nat := 118140960795 + 765131 * 2 ^ 59
def prefixEnd_765131 : Nat := 4983230072969 + 3 ^ 40 * 765131 * 2
def baseEnd_765131 : Nat := 261919977770234103429155

theorem tailTrace_765131 : CollatzResearch.WordTrace tailWord_765131 prefixEnd_765131 261919977770234103429155 := by
  unfold tailWord_765131
  simp only [CollatzResearch.WordTrace]
  refine ⟨27906620191068535816423247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18604413460712357210948831 27906620191068535816423247)
  ·
    refine ⟨41859930286602803724634871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27906620191068535816423247 41859930286602803724634871)
    ·
      refine ⟨62789895429904205586952307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41859930286602803724634871 62789895429904205586952307)
      ·
        refine ⟨94184843144856308380428461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62789895429904205586952307 94184843144856308380428461)
        ·
          refine ⟨35319316179321115642660673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 94184843144856308380428461 35319316179321115642660673)
          ·
            refine ⟨26489487134490836731995505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35319316179321115642660673 26489487134490836731995505)
            ·
              refine ⟨19867115350868127548996629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26489487134490836731995505 19867115350868127548996629)
              ·
                refine ⟨931271032071943478859217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 19867115350868127548996629 931271032071943478859217)
                ·
                  refine ⟨698453274053957609144413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 931271032071943478859217 698453274053957609144413)
                  ·
                    refine ⟨261919977770234103429155, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 698453274053957609144413 261919977770234103429155)
                    ·
                      rfl

theorem cell22_765131_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 2, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 2, 6, 2, 3].length) (baseStart_765131 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_765131 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_765131 prefixEnd_765131 := by exact prefixLift 765131
  have htrace : WordTrace (prefixWord ++ tailWord_765131) baseStart_765131 baseEnd_765131 := by
    simpa [prefixWord, tailWord_765131, baseEnd_765131] using wordTrace_append hprefix tailTrace_765131
  have hstable : (prefixWord ++ tailWord_765131).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_765131).length < 2 ^ (prefixWord ++ tailWord_765131).sum := by decide
  have hdescent : baseEnd_765131 < baseStart_765131 := by decide
  rcases family_descends (prefixWord ++ tailWord_765131) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_765189 : List Nat := [1, 3, 1, 1, 2, 1, 3, 3, 7]
def baseStart_765189 : Nat := 118140960795 + 765189 * 2 ^ 59
def prefixEnd_765189 : Nat := 4983230072969 + 3 ^ 40 * 765189 * 2
def baseEnd_765189 : Nat := 87313277451847095159659

theorem tailTrace_765189 : CollatzResearch.WordTrace tailWord_765189 prefixEnd_765189 87313277451847095159659 := by
  unfold tailWord_765189
  simp only [CollatzResearch.WordTrace]
  refine ⟨27908735624858411722034621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18605823749905607814689747 27908735624858411722034621)
  ·
    refine ⟨10465775859321904395762983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27908735624858411722034621 10465775859321904395762983)
    ·
      refine ⟨15698663788982856593644475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10465775859321904395762983 15698663788982856593644475)
      ·
        refine ⟨23547995683474284890466713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15698663788982856593644475 23547995683474284890466713)
        ·
          refine ⟨17660996762605713667850035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23547995683474284890466713 17660996762605713667850035)
          ·
            refine ⟨26491495143908570501775053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17660996762605713667850035 26491495143908570501775053)
            ·
              refine ⟨9934310678965713938165645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26491495143908570501775053 9934310678965713938165645)
              ·
                refine ⟨3725366504612142726812117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9934310678965713938165645 3725366504612142726812117)
                ·
                  refine ⟨87313277451847095159659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3725366504612142726812117 87313277451847095159659)
                  ·
                    rfl

theorem cell22_765189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 3, 3, 7].length) (baseStart_765189 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_765189 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_765189 prefixEnd_765189 := by exact prefixLift 765189
  have htrace : WordTrace (prefixWord ++ tailWord_765189) baseStart_765189 baseEnd_765189 := by
    simpa [prefixWord, tailWord_765189, baseEnd_765189] using wordTrace_append hprefix tailTrace_765189
  have hstable : (prefixWord ++ tailWord_765189).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_765189).length < 2 ^ (prefixWord ++ tailWord_765189).sum := by decide
  have hdescent : baseEnd_765189 < baseStart_765189 := by decide
  rcases family_descends (prefixWord ++ tailWord_765189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_765287 : List Nat := [1, 1, 5, 1, 4, 2, 2, 1, 1, 4]
def baseStart_765287 : Nat := 118140960795 + 765287 * 2 ^ 59
def prefixEnd_765287 : Nat := 4983230072969 + 3 ^ 40 * 765287 * 2
def baseEnd_765287 : Nat := 261973379758301696528677

theorem tailTrace_765287 : CollatzResearch.WordTrace tailWord_765287 prefixEnd_765287 261973379758301696528677 := by
  unfold tailWord_765287
  simp only [CollatzResearch.WordTrace]
  refine ⟨27912309978503374459102115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18608206652335582972734743 27912309978503374459102115)
  ·
    refine ⟨41868464967755061688653173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27912309978503374459102115 41868464967755061688653173)
    ·
      refine ⟨3925168590727037033311235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 41868464967755061688653173 3925168590727037033311235)
      ·
        refine ⟨5887752886090555549966853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3925168590727037033311235 5887752886090555549966853)
        ·
          refine ⟨1103953666141979165618785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5887752886090555549966853 1103953666141979165618785)
          ·
            refine ⟨827965249606484374214089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1103953666141979165618785 827965249606484374214089)
            ·
              refine ⟨620973937204863280660567, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 827965249606484374214089 620973937204863280660567)
              ·
                refine ⟨931460905807294920990851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 620973937204863280660567 931460905807294920990851)
                ·
                  refine ⟨1397191358710942381486277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 931460905807294920990851 1397191358710942381486277)
                  ·
                    refine ⟨261973379758301696528677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1397191358710942381486277 261973379758301696528677)
                    ·
                      rfl

theorem cell22_765287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 4, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 4, 2, 2, 1, 1, 4].length) (baseStart_765287 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_765287 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_765287 prefixEnd_765287 := by exact prefixLift 765287
  have htrace : WordTrace (prefixWord ++ tailWord_765287) baseStart_765287 baseEnd_765287 := by
    simpa [prefixWord, tailWord_765287, baseEnd_765287] using wordTrace_append hprefix tailTrace_765287
  have hstable : (prefixWord ++ tailWord_765287).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_765287).length < 2 ^ (prefixWord ++ tailWord_765287).sum := by decide
  have hdescent : baseEnd_765287 < baseStart_765287 := by decide
  rcases family_descends (prefixWord ++ tailWord_765287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_765330 : List Nat := [3, 2, 3, 3, 1, 1, 1, 8]
def baseStart_765330 : Nat := 118140960795 + 765330 * 2 ^ 59
def prefixEnd_765330 : Nat := 4983230072969 + 3 ^ 40 * 765330 * 2
def baseEnd_765330 : Nat := 29109788837451546411505

theorem tailTrace_765330 : CollatzResearch.WordTrace tailWord_765330 prefixEnd_765330 29109788837451546411505 := by
  unfold tailWord_765330
  simp only [CollatzResearch.WordTrace]
  refine ⟨6978469579336898200729361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18609252211565061868611629 6978469579336898200729361)
  ·
    refine ⟨5233852184502673650547021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6978469579336898200729361 5233852184502673650547021)
    ·
      refine ⟨1962694569188502618955133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5233852184502673650547021 1962694569188502618955133)
      ·
        refine ⟨736010463445688482108175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1962694569188502618955133 736010463445688482108175)
        ·
          refine ⟨1104015695168532723162263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 736010463445688482108175 1104015695168532723162263)
          ·
            refine ⟨1656023542752799084743395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1104015695168532723162263 1656023542752799084743395)
            ·
              refine ⟨2484035314129198627115093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1656023542752799084743395 2484035314129198627115093)
              ·
                refine ⟨29109788837451546411505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 2484035314129198627115093 29109788837451546411505)
                ·
                  rfl

theorem cell22_765330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 1, 1, 1, 8].length) (baseStart_765330 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_765330 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_765330 prefixEnd_765330 := by exact prefixLift 765330
  have htrace : WordTrace (prefixWord ++ tailWord_765330) baseStart_765330 baseEnd_765330 := by
    simpa [prefixWord, tailWord_765330, baseEnd_765330] using wordTrace_append hprefix tailTrace_765330
  have hstable : (prefixWord ++ tailWord_765330).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_765330).length < 2 ^ (prefixWord ++ tailWord_765330).sum := by decide
  have hdescent : baseEnd_765330 < baseStart_765330 := by decide
  rcases family_descends (prefixWord ++ tailWord_765330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_765356 : List Nat := [2, 2, 1, 1, 1, 1, 4, 1, 4, 5]
def baseStart_765356 : Nat := 118140960795 + 765356 * 2 ^ 59
def prefixEnd_765356 : Nat := 4983230072969 + 3 ^ 40 * 765356 * 2
def baseEnd_765356 : Nat := 261996999868408516553465

theorem tailTrace_765356 : CollatzResearch.WordTrace tailWord_765356 prefixEnd_765356 261996999868408516553465 := by
  unfold tailWord_765356
  simp only [CollatzResearch.WordTrace]
  refine ⟨13957413307626699621681961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18609884410168932828909281 13957413307626699621681961)
  ·
    refine ⟨10468059980720024716261471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13957413307626699621681961 10468059980720024716261471)
    ·
      refine ⟨15702089971080037074392207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10468059980720024716261471 15702089971080037074392207)
      ·
        refine ⟨23553134956620055611588311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15702089971080037074392207 23553134956620055611588311)
        ·
          refine ⟨35329702434930083417382467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23553134956620055611588311 35329702434930083417382467)
          ·
            refine ⟨52994553652395125126073701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35329702434930083417382467 52994553652395125126073701)
            ·
              refine ⟨9936478809824085961138819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 52994553652395125126073701 9936478809824085961138819)
              ·
                refine ⟨14904718214736128941708229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9936478809824085961138819 14904718214736128941708229)
                ·
                  refine ⟨2794634665263024176570293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14904718214736128941708229 2794634665263024176570293)
                  ·
                    refine ⟨261996999868408516553465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2794634665263024176570293 261996999868408516553465)
                    ·
                      rfl

theorem cell22_765356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 5].length) (baseStart_765356 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_765356 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_765356 prefixEnd_765356 := by exact prefixLift 765356
  have htrace : WordTrace (prefixWord ++ tailWord_765356) baseStart_765356 baseEnd_765356 := by
    simpa [prefixWord, tailWord_765356, baseEnd_765356] using wordTrace_append hprefix tailTrace_765356
  have hstable : (prefixWord ++ tailWord_765356).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_765356).length < 2 ^ (prefixWord ++ tailWord_765356).sum := by decide
  have hdescent : baseEnd_765356 < baseStart_765356 := by decide
  rcases family_descends (prefixWord ++ tailWord_765356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_765431 : List Nat := [1, 1, 3, 1, 1, 1, 1, 13]
def baseStart_765431 : Nat := 118140960795 + 765431 * 2 ^ 59
def prefixEnd_765431 : Nat := 4983230072969 + 3 ^ 40 * 765431 * 2
def baseEnd_765431 : Nat := 29113630433459257880915

theorem tailTrace_765431 : CollatzResearch.WordTrace tailWord_765431 prefixEnd_765431 29113630433459257880915 := by
  unfold tailWord_765431
  simp only [CollatzResearch.WordTrace]
  refine ⟨27917562089981687052344147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18611708059987791368229431 27917562089981687052344147)
  ·
    refine ⟨41876343134972530578516221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27917562089981687052344147 41876343134972530578516221)
    ·
      refine ⟨15703628675614698966943583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 41876343134972530578516221 15703628675614698966943583)
      ·
        refine ⟨23555443013422048450415375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15703628675614698966943583 23555443013422048450415375)
        ·
          refine ⟨35333164520133072675623063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23555443013422048450415375 35333164520133072675623063)
          ·
            refine ⟨52999746780199609013434595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35333164520133072675623063 52999746780199609013434595)
            ·
              refine ⟨79499620170299413520151893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52999746780199609013434595 79499620170299413520151893)
              ·
                refine ⟨29113630433459257880915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 13 79499620170299413520151893 29113630433459257880915)
                ·
                  rfl

theorem cell22_765431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 13].length) (baseStart_765431 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_765431 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_765431 prefixEnd_765431 := by exact prefixLift 765431
  have htrace : WordTrace (prefixWord ++ tailWord_765431) baseStart_765431 baseEnd_765431 := by
    simpa [prefixWord, tailWord_765431, baseEnd_765431] using wordTrace_append hprefix tailTrace_765431
  have hstable : (prefixWord ++ tailWord_765431).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_765431).length < 2 ^ (prefixWord ++ tailWord_765431).sum := by decide
  have hdescent : baseEnd_765431 < baseStart_765431 := by decide
  rcases family_descends (prefixWord ++ tailWord_765431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_765450 : List Nat := [3, 1, 2, 2, 2, 2, 3, 1, 2, 4]
def baseStart_765450 : Nat := 118140960795 + 765450 * 2 ^ 59
def prefixEnd_765450 : Nat := 4983230072969 + 3 ^ 40 * 765450 * 2
def baseEnd_765450 : Nat := 262029177989423604703177

theorem tailTrace_765450 : CollatzResearch.WordTrace tailWord_765450 prefixEnd_765450 262029177989423604703177 := by
  unfold tailWord_765450
  simp only [CollatzResearch.WordTrace]
  refine ⟨6979563769228213324321451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18612170051275235531523869 6979563769228213324321451)
  ·
    refine ⟨10469345653842319986482177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6979563769228213324321451 10469345653842319986482177)
    ·
      refine ⟨7852009240381739989861633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10469345653842319986482177 7852009240381739989861633)
      ·
        refine ⟨5889006930286304992396225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7852009240381739989861633 5889006930286304992396225)
        ·
          refine ⟨4416755197714728744297169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5889006930286304992396225 4416755197714728744297169)
          ·
            refine ⟨3312566398286046558222877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4416755197714728744297169 3312566398286046558222877)
            ·
              refine ⟨1242212399357267459333579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3312566398286046558222877 1242212399357267459333579)
              ·
                refine ⟨1863318599035901189000369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1242212399357267459333579 1863318599035901189000369)
                ·
                  refine ⟨1397488949276925891750277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1863318599035901189000369 1397488949276925891750277)
                  ·
                    refine ⟨262029177989423604703177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1397488949276925891750277 262029177989423604703177)
                    ·
                      rfl

theorem cell22_765450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 2, 3, 1, 2, 4].length) (baseStart_765450 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_765450 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_765450 prefixEnd_765450 := by exact prefixLift 765450
  have htrace : WordTrace (prefixWord ++ tailWord_765450) baseStart_765450 baseEnd_765450 := by
    simpa [prefixWord, tailWord_765450, baseEnd_765450] using wordTrace_append hprefix tailTrace_765450
  have hstable : (prefixWord ++ tailWord_765450).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_765450).length < 2 ^ (prefixWord ++ tailWord_765450).sum := by decide
  have hdescent : baseEnd_765450 < baseStart_765450 := by decide
  rcases family_descends (prefixWord ++ tailWord_765450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_765544 : List Nat := [2, 1, 4, 3, 1, 3, 2, 1, 5]
def baseStart_765544 : Nat := 118140960795 + 765544 * 2 ^ 59
def prefixEnd_765544 : Nat := 4983230072969 + 3 ^ 40 * 765544 * 2
def baseEnd_765544 : Nat := 87353785370146230950963

theorem tailTrace_765544 : CollatzResearch.WordTrace tailWord_765544 prefixEnd_765544 87353785370146230950963 := by
  unfold tailWord_765544
  simp only [CollatzResearch.WordTrace]
  refine ⟨13960841769286153675603843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18614455692381538234138457 13960841769286153675603843)
  ·
    refine ⟨20941262653929230513405765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13960841769286153675603843 20941262653929230513405765)
    ·
      refine ⟨3926486747611730721263581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 20941262653929230513405765 3926486747611730721263581)
      ·
        refine ⟨1472432530354399020473843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3926486747611730721263581 1472432530354399020473843)
        ·
          refine ⟨2208648795531598530710765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1472432530354399020473843 2208648795531598530710765)
          ·
            refine ⟨828243298324349449016537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2208648795531598530710765 828243298324349449016537)
            ·
              refine ⟨621182473743262086762403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 828243298324349449016537 621182473743262086762403)
              ·
                refine ⟨931773710614893130143605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 621182473743262086762403 931773710614893130143605)
                ·
                  refine ⟨87353785370146230950963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 931773710614893130143605 87353785370146230950963)
                  ·
                    rfl

theorem cell22_765544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 3, 2, 1, 5].length) (baseStart_765544 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_765544 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_765544 prefixEnd_765544 := by exact prefixLift 765544
  have htrace : WordTrace (prefixWord ++ tailWord_765544) baseStart_765544 baseEnd_765544 := by
    simpa [prefixWord, tailWord_765544, baseEnd_765544] using wordTrace_append hprefix tailTrace_765544
  have hstable : (prefixWord ++ tailWord_765544).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_765544).length < 2 ^ (prefixWord ++ tailWord_765544).sum := by decide
  have hdescent : baseEnd_765544 < baseStart_765544 := by decide
  rcases family_descends (prefixWord ++ tailWord_765544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_765553 : List Nat := [1, 2, 2, 2, 1, 1, 1, 2, 5, 5]
def baseStart_765553 : Nat := 118140960795 + 765553 * 2 ^ 59
def prefixEnd_765553 : Nat := 4983230072969 + 3 ^ 40 * 765553 * 2
def baseEnd_765553 : Nat := 262064436994365669377861

theorem tailTrace_765553 : CollatzResearch.WordTrace tailWord_765553 prefixEnd_765553 262064436994365669377861 := by
  unfold tailWord_765553
  simp only [CollatzResearch.WordTrace]
  refine ⟨27922011795539701888285313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18614674530359801258856875 27922011795539701888285313)
  ·
    refine ⟨20941508846654776416213985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27922011795539701888285313 20941508846654776416213985)
    ·
      refine ⟨15706131634991082312160489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20941508846654776416213985 15706131634991082312160489)
      ·
        refine ⟨11779598726243311734120367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15706131634991082312160489 11779598726243311734120367)
        ·
          refine ⟨17669398089364967601180551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11779598726243311734120367 17669398089364967601180551)
          ·
            refine ⟨26504097134047451401770827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17669398089364967601180551 26504097134047451401770827)
            ·
              refine ⟨39756145701071177102656241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26504097134047451401770827 39756145701071177102656241)
              ·
                refine ⟨29817109275803382826992181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39756145701071177102656241 29817109275803382826992181)
                ·
                  refine ⟨2795353994606567140030517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 29817109275803382826992181 2795353994606567140030517)
                  ·
                    refine ⟨262064436994365669377861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2795353994606567140030517 262064436994365669377861)
                    ·
                      rfl

theorem cell22_765553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 1, 2, 5, 5].length) (baseStart_765553 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_765553 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_765553 prefixEnd_765553 := by exact prefixLift 765553
  have htrace : WordTrace (prefixWord ++ tailWord_765553) baseStart_765553 baseEnd_765553 := by
    simpa [prefixWord, tailWord_765553, baseEnd_765553] using wordTrace_append hprefix tailTrace_765553
  have hstable : (prefixWord ++ tailWord_765553).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_765553).length < 2 ^ (prefixWord ++ tailWord_765553).sum := by decide
  have hdescent : baseEnd_765553 < baseStart_765553 := by decide
  rcases family_descends (prefixWord ++ tailWord_765553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_765557 : List Nat := [1, 3, 4, 2, 1, 2, 1, 1, 3, 4]
def baseStart_765557 : Nat := 118140960795 + 765557 * 2 ^ 59
def prefixEnd_765557 : Nat := 4983230072969 + 3 ^ 40 * 765557 * 2
def baseEnd_765557 : Nat := 262065806276110992277849

theorem tailTrace_765557 : CollatzResearch.WordTrace tailWord_765557 prefixEnd_765557 262065806276110992277849 := by
  unfold tailWord_765557
  simp only [CollatzResearch.WordTrace]
  refine ⟨27922157687525210571430925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18614771791683473714287283 27922157687525210571430925)
  ·
    refine ⟨10470809132821953964286597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27922157687525210571430925 10470809132821953964286597)
    ·
      refine ⟨1963276712404116368303737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 10470809132821953964286597 1963276712404116368303737)
      ·
        refine ⟨1472457534303087276227803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1963276712404116368303737 1472457534303087276227803)
        ·
          refine ⟨2208686301454630914341705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1472457534303087276227803 2208686301454630914341705)
          ·
            refine ⟨1656514726090973185756279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2208686301454630914341705 1656514726090973185756279)
            ·
              refine ⟨2484772089136459778634419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1656514726090973185756279 2484772089136459778634419)
              ·
                refine ⟨3727158133704689667951629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2484772089136459778634419 3727158133704689667951629)
                ·
                  refine ⟨1397684300139258625481861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3727158133704689667951629 1397684300139258625481861)
                  ·
                    refine ⟨262065806276110992277849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1397684300139258625481861 262065806276110992277849)
                    ·
                      rfl

theorem cell22_765557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 2, 1, 1, 3, 4].length) (baseStart_765557 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_765557 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_765557 prefixEnd_765557 := by exact prefixLift 765557
  have htrace : WordTrace (prefixWord ++ tailWord_765557) baseStart_765557 baseEnd_765557 := by
    simpa [prefixWord, tailWord_765557, baseEnd_765557] using wordTrace_append hprefix tailTrace_765557
  have hstable : (prefixWord ++ tailWord_765557).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_765557).length < 2 ^ (prefixWord ++ tailWord_765557).sum := by decide
  have hdescent : baseEnd_765557 < baseStart_765557 := by decide
  rcases family_descends (prefixWord ++ tailWord_765557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_765600 : List Nat := [2, 1, 1, 4, 3, 1, 3, 7]
def baseStart_765600 : Nat := 118140960795 + 765600 * 2 ^ 59
def prefixEnd_765600 : Nat := 4983230072969 + 3 ^ 40 * 765600 * 2
def baseEnd_765600 : Nat := 29120058450541468161413

theorem tailTrace_765600 : CollatzResearch.WordTrace tailWord_765600 prefixEnd_765600 29120058450541468161413 := by
  unfold tailWord_765600
  simp only [CollatzResearch.WordTrace]
  refine ⟨13961863013184714457623127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18615817350912952610164169 13961863013184714457623127)
  ·
    refine ⟨20942794519777071686434691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13961863013184714457623127 20942794519777071686434691)
    ·
      refine ⟨31414191779665607529652037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20942794519777071686434691 31414191779665607529652037)
      ·
        refine ⟨5890160958687301411809757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 31414191779665607529652037 5890160958687301411809757)
        ·
          refine ⟨2208810359507738029428659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5890160958687301411809757 2208810359507738029428659)
          ·
            refine ⟨3313215539261607044142989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2208810359507738029428659 3313215539261607044142989)
            ·
              refine ⟨1242455827223102641553621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3313215539261607044142989 1242455827223102641553621)
              ·
                refine ⟨29120058450541468161413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1242455827223102641553621 29120058450541468161413)
                ·
                  rfl

theorem cell22_765600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 1, 3, 7].length) (baseStart_765600 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_765600 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_765600 prefixEnd_765600 := by exact prefixLift 765600
  have htrace : WordTrace (prefixWord ++ tailWord_765600) baseStart_765600 baseEnd_765600 := by
    simpa [prefixWord, tailWord_765600, baseEnd_765600] using wordTrace_append hprefix tailTrace_765600
  have hstable : (prefixWord ++ tailWord_765600).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_765600).length < 2 ^ (prefixWord ++ tailWord_765600).sum := by decide
  have hdescent : baseEnd_765600 < baseStart_765600 := by decide
  rcases family_descends (prefixWord ++ tailWord_765600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_765638 : List Nat := [6, 1, 2, 1, 1, 1, 3, 2, 2, 3]
def baseStart_765638 : Nat := 118140960795 + 765638 * 2 ^ 59
def prefixEnd_765638 : Nat := 4983230072969 + 3 ^ 40 * 765638 * 2
def baseEnd_765638 : Nat := 262093534231453781002601

theorem tailTrace_765638 : CollatzResearch.WordTrace tailWord_765638 prefixEnd_765638 262093534231453781002601 := by
  unfold tailWord_765638
  simp only [CollatzResearch.WordTrace]
  refine ⟨872659750007242543910299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 18616741333487840936753045 872659750007242543910299)
  ·
    refine ⟨1308989625010863815865449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 872659750007242543910299 1308989625010863815865449)
    ·
      refine ⟨981742218758147861899087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1308989625010863815865449 981742218758147861899087)
      ·
        refine ⟨1472613328137221792848631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 981742218758147861899087 1472613328137221792848631)
        ·
          refine ⟨2208919992205832689272947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1472613328137221792848631 2208919992205832689272947)
          ·
            refine ⟨3313379988308749033909421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2208919992205832689272947 3313379988308749033909421)
            ·
              refine ⟨1242517495615780887716033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3313379988308749033909421 1242517495615780887716033)
              ·
                refine ⟨931888121711835665787025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1242517495615780887716033 931888121711835665787025)
                ·
                  refine ⟨698916091283876749340269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 931888121711835665787025 698916091283876749340269)
                  ·
                    refine ⟨262093534231453781002601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 698916091283876749340269 262093534231453781002601)
                    ·
                      rfl

theorem cell22_765638_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 1, 3, 2, 2, 3].length) (baseStart_765638 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_765638 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_765638 prefixEnd_765638 := by exact prefixLift 765638
  have htrace : WordTrace (prefixWord ++ tailWord_765638) baseStart_765638 baseEnd_765638 := by
    simpa [prefixWord, tailWord_765638, baseEnd_765638] using wordTrace_append hprefix tailTrace_765638
  have hstable : (prefixWord ++ tailWord_765638).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_765638).length < 2 ^ (prefixWord ++ tailWord_765638).sum := by decide
  have hdescent : baseEnd_765638 < baseStart_765638 := by decide
  rcases family_descends (prefixWord ++ tailWord_765638) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_765649 : List Nat := [1, 2, 2, 1, 2, 4, 2, 4, 1, 3]
def baseStart_765649 : Nat := 118140960795 + 765649 * 2 ^ 59
def prefixEnd_765649 : Nat := 4983230072969 + 3 ^ 40 * 765649 * 2
def baseEnd_765649 : Nat := 262097299756253418977567

theorem tailTrace_765649 : CollatzResearch.WordTrace tailWord_765649 prefixEnd_765649 262097299756253418977567 := by
  unfold tailWord_765649
  simp only [CollatzResearch.WordTrace]
  refine ⟨27925513203191910283780001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18617008802127940189186667 27925513203191910283780001)
  ·
    refine ⟨20944134902393932712835001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27925513203191910283780001 20944134902393932712835001)
    ·
      refine ⟨15708101176795449534626251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20944134902393932712835001 15708101176795449534626251)
      ·
        refine ⟨23562151765193174301939377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15708101176795449534626251 23562151765193174301939377)
        ·
          refine ⟨17671613823894880726454533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23562151765193174301939377 17671613823894880726454533)
          ·
            refine ⟨3313427591980290136210225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 17671613823894880726454533 3313427591980290136210225)
            ·
              refine ⟨2485070693985217602157669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3313427591980290136210225 2485070693985217602157669)
              ·
                refine ⟨465950755122228300404563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2485070693985217602157669 465950755122228300404563)
                ·
                  refine ⟨698926132683342450606845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 465950755122228300404563 698926132683342450606845)
                  ·
                    refine ⟨262097299756253418977567, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 698926132683342450606845 262097299756253418977567)
                    ·
                      rfl

theorem cell22_765649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 4, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 4, 2, 4, 1, 3].length) (baseStart_765649 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_765649 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_765649 prefixEnd_765649 := by exact prefixLift 765649
  have htrace : WordTrace (prefixWord ++ tailWord_765649) baseStart_765649 baseEnd_765649 := by
    simpa [prefixWord, tailWord_765649, baseEnd_765649] using wordTrace_append hprefix tailTrace_765649
  have hstable : (prefixWord ++ tailWord_765649).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_765649).length < 2 ^ (prefixWord ++ tailWord_765649).sum := by decide
  have hdescent : baseEnd_765649 < baseStart_765649 := by decide
  rcases family_descends (prefixWord ++ tailWord_765649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_765675 : List Nat := [1, 1, 1, 1, 2, 4, 2, 3, 3, 4]
def baseStart_765675 : Nat := 118140960795 + 765675 * 2 ^ 59
def prefixEnd_765675 : Nat := 4983230072969 + 3 ^ 40 * 765675 * 2
def baseEnd_765675 : Nat := 262106200087598017827487

theorem tailTrace_765675 : CollatzResearch.WordTrace tailWord_765675 prefixEnd_765675 262106200087598017827487 := by
  unfold tailWord_765675
  simp only [CollatzResearch.WordTrace]
  refine ⟨27926461501097716724226479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18617641000731811149484319 27926461501097716724226479)
  ·
    refine ⟨41889692251646575086339719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27926461501097716724226479 41889692251646575086339719)
    ·
      refine ⟨62834538377469862629509579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41889692251646575086339719 62834538377469862629509579)
      ·
        refine ⟨94251807566204793944264369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62834538377469862629509579 94251807566204793944264369)
        ·
          refine ⟨70688855674653595458198277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 94251807566204793944264369 70688855674653595458198277)
          ·
            refine ⟨13254160438997549148412177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 70688855674653595458198277 13254160438997549148412177)
            ·
              refine ⟨9940620329248161861309133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13254160438997549148412177 9940620329248161861309133)
              ·
                refine ⟨3727732623468060697990925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9940620329248161861309133 3727732623468060697990925)
                ·
                  refine ⟨1397899733800522761746597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3727732623468060697990925 1397899733800522761746597)
                  ·
                    refine ⟨262106200087598017827487, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1397899733800522761746597 262106200087598017827487)
                    ·
                      rfl

theorem cell22_765675_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 2, 3, 3, 4].length) (baseStart_765675 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_765675 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_765675 prefixEnd_765675 := by exact prefixLift 765675
  have htrace : WordTrace (prefixWord ++ tailWord_765675) baseStart_765675 baseEnd_765675 := by
    simpa [prefixWord, tailWord_765675, baseEnd_765675] using wordTrace_append hprefix tailTrace_765675
  have hstable : (prefixWord ++ tailWord_765675).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_765675).length < 2 ^ (prefixWord ++ tailWord_765675).sum := by decide
  have hdescent : baseEnd_765675 < baseStart_765675 := by decide
  rcases family_descends (prefixWord ++ tailWord_765675) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_765692 : List Nat := [2, 2, 2, 1, 3, 1, 1, 5, 1, 4]
def baseStart_765692 : Nat := 118140960795 + 765692 * 2 ^ 59
def prefixEnd_765692 : Nat := 4983230072969 + 3 ^ 40 * 765692 * 2
def baseEnd_765692 : Nat := 262112019535015640152435

theorem tailTrace_765692 : CollatzResearch.WordTrace tailWord_765692 prefixEnd_765692 262112019535015640152435 := by
  unfold tailWord_765692
  simp only [CollatzResearch.WordTrace]
  refine ⟨13963540771018064313797665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18618054361357419085063553 13963540771018064313797665)
  ·
    refine ⟨10472655578263548235348249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13963540771018064313797665 10472655578263548235348249)
    ·
      refine ⟨7854491683697661176511187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10472655578263548235348249 7854491683697661176511187)
      ·
        refine ⟨11781737525546491764766781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7854491683697661176511187 11781737525546491764766781)
        ·
          refine ⟨4418151572079934411787543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11781737525546491764766781 4418151572079934411787543)
          ·
            refine ⟨6627227358119901617681315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4418151572079934411787543 6627227358119901617681315)
            ·
              refine ⟨9940841037179852426521973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6627227358119901617681315 9940841037179852426521973)
              ·
                refine ⟨931953847235611164986435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 9940841037179852426521973 931953847235611164986435)
                ·
                  refine ⟨1397930770853416747479653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 931953847235611164986435 1397930770853416747479653)
                  ·
                    refine ⟨262112019535015640152435, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1397930770853416747479653 262112019535015640152435)
                    ·
                      rfl

theorem cell22_765692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 1, 5, 1, 4].length) (baseStart_765692 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_765692 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_765692 prefixEnd_765692 := by exact prefixLift 765692
  have htrace : WordTrace (prefixWord ++ tailWord_765692) baseStart_765692 baseEnd_765692 := by
    simpa [prefixWord, tailWord_765692, baseEnd_765692] using wordTrace_append hprefix tailTrace_765692
  have hstable : (prefixWord ++ tailWord_765692).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_765692).length < 2 ^ (prefixWord ++ tailWord_765692).sum := by decide
  have hdescent : baseEnd_765692 < baseStart_765692 := by decide
  rcases family_descends (prefixWord ++ tailWord_765692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_765707 : List Nat := [1, 1, 1, 1, 5, 1, 2, 6, 4]
def baseStart_765707 : Nat := 118140960795 + 765707 * 2 ^ 59
def prefixEnd_765707 : Nat := 4983230072969 + 3 ^ 40 * 765707 * 2
def baseEnd_765707 : Nat := 87372384780520200342463

theorem tailTrace_765707 : CollatzResearch.WordTrace tailWord_765707 prefixEnd_765707 87372384780520200342463 := by
  unfold tailWord_765707
  simp only [CollatzResearch.WordTrace]
  refine ⟨27927628636981786189391375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18618419091321190792927583 27927628636981786189391375)
  ·
    refine ⟨41891442955472679284087063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27927628636981786189391375 41891442955472679284087063)
    ·
      refine ⟨62837164433209018926130595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41891442955472679284087063 62837164433209018926130595)
      ·
        refine ⟨94255746649813528389195893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62837164433209018926130595 94255746649813528389195893)
        ·
          refine ⟨8836476248420018286487115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 94255746649813528389195893 8836476248420018286487115)
          ·
            refine ⟨13254714372630027429730673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8836476248420018286487115 13254714372630027429730673)
            ·
              refine ⟨9941035779472520572298005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13254714372630027429730673 9941035779472520572298005)
              ·
                refine ⟨465986052162774401826469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 9941035779472520572298005 465986052162774401826469)
                ·
                  refine ⟨87372384780520200342463, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 465986052162774401826469 87372384780520200342463)
                  ·
                    rfl

theorem cell22_765707_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 2, 6, 4].length) (baseStart_765707 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_765707 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_765707 prefixEnd_765707 := by exact prefixLift 765707
  have htrace : WordTrace (prefixWord ++ tailWord_765707) baseStart_765707 baseEnd_765707 := by
    simpa [prefixWord, tailWord_765707, baseEnd_765707] using wordTrace_append hprefix tailTrace_765707
  have hstable : (prefixWord ++ tailWord_765707).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_765707).length < 2 ^ (prefixWord ++ tailWord_765707).sum := by decide
  have hdescent : baseEnd_765707 < baseStart_765707 := by decide
  rcases family_descends (prefixWord ++ tailWord_765707) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_765720 : List Nat := [2, 1, 2, 3, 1, 1, 2, 1, 3, 6]
def baseStart_765720 : Nat := 118140960795 + 765720 * 2 ^ 59
def prefixEnd_765720 : Nat := 4983230072969 + 3 ^ 40 * 765720 * 2
def baseEnd_765720 : Nat := 262121604507232900452349

theorem tailTrace_765720 : CollatzResearch.WordTrace tailWord_765720 prefixEnd_765720 262121604507232900452349 := by
  unfold tailWord_765720
  simp only [CollatzResearch.WordTrace]
  refine ⟨13964051392967344704807307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18618735190623126273076409 13964051392967344704807307)
  ·
    refine ⟨20946077089451017057210961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13964051392967344704807307 20946077089451017057210961)
    ·
      refine ⟨15709557817088262792908221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20946077089451017057210961 15709557817088262792908221)
      ·
        refine ⟨5891084181408098547340583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15709557817088262792908221 5891084181408098547340583)
        ·
          refine ⟨8836626272112147821010875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5891084181408098547340583 8836626272112147821010875)
          ·
            refine ⟨13254939408168221731516313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8836626272112147821010875 13254939408168221731516313)
            ·
              refine ⟨9941204556126166298637235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13254939408168221731516313 9941204556126166298637235)
              ·
                refine ⟨14911806834189249447955853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9941204556126166298637235 14911806834189249447955853)
                ·
                  refine ⟨5591927562820968542983445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14911806834189249447955853 5591927562820968542983445)
                  ·
                    refine ⟨262121604507232900452349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5591927562820968542983445 262121604507232900452349)
                    ·
                      rfl

theorem cell22_765720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 2, 1, 3, 6].length) (baseStart_765720 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_765720 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_765720 prefixEnd_765720 := by exact prefixLift 765720
  have htrace : WordTrace (prefixWord ++ tailWord_765720) baseStart_765720 baseEnd_765720 := by
    simpa [prefixWord, tailWord_765720, baseEnd_765720] using wordTrace_append hprefix tailTrace_765720
  have hstable : (prefixWord ++ tailWord_765720).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_765720).length < 2 ^ (prefixWord ++ tailWord_765720).sum := by decide
  have hdescent : baseEnd_765720 < baseStart_765720 := by decide
  rcases family_descends (prefixWord ++ tailWord_765720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_765758 : List Nat := [4, 2, 1, 2, 2, 3, 2, 2, 4]
def baseStart_765758 : Nat := 118140960795 + 765758 * 2 ^ 59
def prefixEnd_765758 : Nat := 4983230072969 + 3 ^ 40 * 765758 * 2
def baseEnd_765758 : Nat := 87378204227937822667411

theorem tailTrace_765758 : CollatzResearch.WordTrace tailWord_765758 prefixEnd_765758 87378204227937822667411 := by
  unfold tailWord_765758
  simp only [CollatzResearch.WordTrace]
  refine ⟨3491186094974627737437241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 18619659173198014599665285 3491186094974627737437241)
  ·
    refine ⟨2618389571230970803077931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3491186094974627737437241 2618389571230970803077931)
    ·
      refine ⟨3927584356846456204616897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2618389571230970803077931 3927584356846456204616897)
      ·
        refine ⟨2945688267634842153462673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3927584356846456204616897 2945688267634842153462673)
        ·
          refine ⟨2209266200726131615097005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2945688267634842153462673 2209266200726131615097005)
          ·
            refine ⟨828474825272299355661377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2209266200726131615097005 828474825272299355661377)
            ·
              refine ⟨621356118954224516746033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 828474825272299355661377 621356118954224516746033)
              ·
                refine ⟨466017089215668387559525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 621356118954224516746033 466017089215668387559525)
                ·
                  refine ⟨87378204227937822667411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 466017089215668387559525 87378204227937822667411)
                  ·
                    rfl

theorem cell22_765758_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 3, 2, 2, 4].length) (baseStart_765758 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_765758 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_765758 prefixEnd_765758 := by exact prefixLift 765758
  have htrace : WordTrace (prefixWord ++ tailWord_765758) baseStart_765758 baseEnd_765758 := by
    simpa [prefixWord, tailWord_765758, baseEnd_765758] using wordTrace_append hprefix tailTrace_765758
  have hstable : (prefixWord ++ tailWord_765758).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_765758).length < 2 ^ (prefixWord ++ tailWord_765758).sum := by decide
  have hdescent : baseEnd_765758 < baseStart_765758 := by decide
  rcases family_descends (prefixWord ++ tailWord_765758) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_765765 : List Nat := [1, 3, 1, 1, 1, 2, 3, 1, 1, 8]
def baseStart_765765 : Nat := 118140960795 + 765765 * 2 ^ 59
def prefixEnd_765765 : Nat := 4983230072969 + 3 ^ 40 * 765765 * 2
def baseEnd_765765 : Nat := 262137008926867783077211

theorem tailTrace_765765 : CollatzResearch.WordTrace tailWord_765765 prefixEnd_765765 262137008926867783077211 := by
  unfold tailWord_765765
  simp only [CollatzResearch.WordTrace]
  refine ⟨27929744070771662095002749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18619829380514441396668499 27929744070771662095002749)
  ·
    refine ⟨10473654026539373285626031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27929744070771662095002749 10473654026539373285626031)
    ·
      refine ⟨15710481039809059928439047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10473654026539373285626031 15710481039809059928439047)
      ·
        refine ⟨23565721559713589892658571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15710481039809059928439047 23565721559713589892658571)
        ·
          refine ⟨35348582339570384838987857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23565721559713589892658571 35348582339570384838987857)
          ·
            refine ⟨26511436754677788629240893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35348582339570384838987857 26511436754677788629240893)
            ·
              refine ⟨9941788783004170735965335, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26511436754677788629240893 9941788783004170735965335)
              ·
                refine ⟨14912683174506256103948003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9941788783004170735965335 14912683174506256103948003)
                ·
                  refine ⟨22369024761759384155922005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14912683174506256103948003 22369024761759384155922005)
                  ·
                    refine ⟨262137008926867783077211, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 22369024761759384155922005 262137008926867783077211)
                    ·
                      rfl

theorem cell22_765765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 3, 1, 1, 8].length) (baseStart_765765 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_765765 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_765765 prefixEnd_765765 := by exact prefixLift 765765
  have htrace : WordTrace (prefixWord ++ tailWord_765765) baseStart_765765 baseEnd_765765 := by
    simpa [prefixWord, tailWord_765765, baseEnd_765765] using wordTrace_append hprefix tailTrace_765765
  have hstable : (prefixWord ++ tailWord_765765).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_765765).length < 2 ^ (prefixWord ++ tailWord_765765).sum := by decide
  have hdescent : baseEnd_765765 < baseStart_765765 := by decide
  rcases family_descends (prefixWord ++ tailWord_765765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_765788 : List Nat := [2, 2, 4, 2, 3, 1, 1, 1, 2, 4]
def baseStart_765788 : Nat := 118140960795 + 765788 * 2 ^ 59
def prefixEnd_765788 : Nat := 4983230072969 + 3 ^ 40 * 765788 * 2
def baseEnd_765788 : Nat := 262144882296903389752141

theorem tailTrace_765788 : CollatzResearch.WordTrace tailWord_765788 prefixEnd_765788 262144882296903389752141 := by
  unfold tailWord_765788
  simp only [CollatzResearch.WordTrace]
  refine ⟨13965291474844168511545009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18620388633125558015393345 13965291474844168511545009)
  ·
    refine ⟨10473968606133126383658757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13965291474844168511545009 10473968606133126383658757)
    ·
      refine ⟨1963869113649961196936017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 10473968606133126383658757 1963869113649961196936017)
      ·
        refine ⟨1472901835237470897702013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1963869113649961196936017 1472901835237470897702013)
        ·
          refine ⟨552338188214051586638255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1472901835237470897702013 552338188214051586638255)
          ·
            refine ⟨828507282321077379957383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 552338188214051586638255 828507282321077379957383)
            ·
              refine ⟨1242760923481616069936075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 828507282321077379957383 1242760923481616069936075)
              ·
                refine ⟨1864141385222424104904113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1242760923481616069936075 1864141385222424104904113)
                ·
                  refine ⟨1398106038916818078678085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1864141385222424104904113 1398106038916818078678085)
                  ·
                    refine ⟨262144882296903389752141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1398106038916818078678085 262144882296903389752141)
                    ·
                      rfl

theorem cell22_765788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 3, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 3, 1, 1, 1, 2, 4].length) (baseStart_765788 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_765788 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_765788 prefixEnd_765788 := by exact prefixLift 765788
  have htrace : WordTrace (prefixWord ++ tailWord_765788) baseStart_765788 baseEnd_765788 := by
    simpa [prefixWord, tailWord_765788, baseEnd_765788] using wordTrace_append hprefix tailTrace_765788
  have hstable : (prefixWord ++ tailWord_765788).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_765788).length < 2 ^ (prefixWord ++ tailWord_765788).sum := by decide
  have hdescent : baseEnd_765788 < baseStart_765788 := by decide
  rcases family_descends (prefixWord ++ tailWord_765788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_765831 : List Nat := [1, 1, 4, 2, 4, 1, 3, 1, 5]
def baseStart_765831 : Nat := 118140960795 + 765831 * 2 ^ 59
def prefixEnd_765831 : Nat := 4983230072969 + 3 ^ 40 * 765831 * 2
def baseEnd_765831 : Nat := 87386534025221870309003

theorem tailTrace_765831 : CollatzResearch.WordTrace tailWord_765831 prefixEnd_765831 87386534025221870309003 := by
  unfold tailWord_765831
  simp only [CollatzResearch.WordTrace]
  refine ⟨27932151288532555366905347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18621434192355036911270231 27932151288532555366905347)
  ·
    refine ⟨41898226932798833050358021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27932151288532555366905347 41898226932798833050358021)
    ·
      refine ⟨7855917549899781196942129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 41898226932798833050358021 7855917549899781196942129)
      ·
        refine ⟨5891938162424835897706597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7855917549899781196942129 5891938162424835897706597)
        ·
          refine ⟨1104738405454656730819987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5891938162424835897706597 1104738405454656730819987)
          ·
            refine ⟨1657107608181985096229981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1104738405454656730819987 1657107608181985096229981)
            ·
              refine ⟨621415353068244411086243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1657107608181985096229981 621415353068244411086243)
              ·
                refine ⟨932123029602366616629365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 621415353068244411086243 932123029602366616629365)
                ·
                  refine ⟨87386534025221870309003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 932123029602366616629365 87386534025221870309003)
                  ·
                    rfl

theorem cell22_765831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 4, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 4, 1, 3, 1, 5].length) (baseStart_765831 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_765831 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_765831 prefixEnd_765831 := by exact prefixLift 765831
  have htrace : WordTrace (prefixWord ++ tailWord_765831) baseStart_765831 baseEnd_765831 := by
    simpa [prefixWord, tailWord_765831, baseEnd_765831] using wordTrace_append hprefix tailTrace_765831
  have hstable : (prefixWord ++ tailWord_765831).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_765831).length < 2 ^ (prefixWord ++ tailWord_765831).sum := by decide
  have hdescent : baseEnd_765831 < baseStart_765831 := by decide
  rcases family_descends (prefixWord ++ tailWord_765831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_765887 : List Nat := [1, 1, 2, 2, 2, 1, 6, 7]
def baseStart_765887 : Nat := 118140960795 + 765887 * 2 ^ 59
def prefixEnd_765887 : Nat := 4983230072969 + 3 ^ 40 * 765887 * 2
def baseEnd_765887 : Nat := 29130974668900014614093

theorem tailTrace_765887 : CollatzResearch.WordTrace tailWord_765887 prefixEnd_765887 29130974668900014614093 := by
  unfold tailWord_765887
  simp only [CollatzResearch.WordTrace]
  refine ⟨27934193776329676930943915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18622795850886451287295943 27934193776329676930943915)
  ·
    refine ⟨41901290664494515396415873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27934193776329676930943915 41901290664494515396415873)
    ·
      refine ⟨31425967998370886547311905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41901290664494515396415873 31425967998370886547311905)
      ·
        refine ⟨23569475998778164910483929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31425967998370886547311905 23569475998778164910483929)
        ·
          refine ⟨17677106999083623682862947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23569475998778164910483929 17677106999083623682862947)
          ·
            refine ⟨26515660498625435524294421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17677106999083623682862947 26515660498625435524294421)
            ·
              refine ⟨1242921585873067290201301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 26515660498625435524294421 1242921585873067290201301)
              ·
                refine ⟨29130974668900014614093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1242921585873067290201301 29130974668900014614093)
                ·
                  rfl

theorem cell22_765887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 6, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 6, 7].length) (baseStart_765887 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_765887 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_765887 prefixEnd_765887 := by exact prefixLift 765887
  have htrace : WordTrace (prefixWord ++ tailWord_765887) baseStart_765887 baseEnd_765887 := by
    simpa [prefixWord, tailWord_765887, baseEnd_765887] using wordTrace_append hprefix tailTrace_765887
  have hstable : (prefixWord ++ tailWord_765887).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_765887).length < 2 ^ (prefixWord ++ tailWord_765887).sum := by decide
  have hdescent : baseEnd_765887 < baseStart_765887 := by decide
  rcases family_descends (prefixWord ++ tailWord_765887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_765932 : List Nat := [2, 2, 1, 1, 2, 1, 1, 5, 7]
def baseStart_765932 : Nat := 118140960795 + 765932 * 2 ^ 59
def prefixEnd_765932 : Nat := 4983230072969 + 3 ^ 40 * 765932 * 2
def baseEnd_765932 : Nat := 87398058813245004717233

theorem tailTrace_765932 : CollatzResearch.WordTrace tailWord_765932 prefixEnd_765932 87398058813245004717233 := by
  unfold tailWord_765932
  simp only [CollatzResearch.WordTrace]
  refine ⟨13967917530583324808166025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18623890040777766410888033 13967917530583324808166025)
  ·
    refine ⟨10475938147937493606124519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13967917530583324808166025 10475938147937493606124519)
    ·
      refine ⟨15713907221906240409186779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10475938147937493606124519 15713907221906240409186779)
      ·
        refine ⟨23570860832859360613780169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15713907221906240409186779 23570860832859360613780169)
        ·
          refine ⟨17678145624644520460335127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23570860832859360613780169 17678145624644520460335127)
          ·
            refine ⟨26517218436966780690502691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17678145624644520460335127 26517218436966780690502691)
            ·
              refine ⟨39775827655450171035754037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26517218436966780690502691 39775827655450171035754037)
              ·
                refine ⟨3728983842698453534601941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 39775827655450171035754037 3728983842698453534601941)
                ·
                  refine ⟨87398058813245004717233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3728983842698453534601941 87398058813245004717233)
                  ·
                    rfl

theorem cell22_765932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 7].length) (baseStart_765932 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_765932 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_765932 prefixEnd_765932 := by exact prefixLift 765932
  have htrace : WordTrace (prefixWord ++ tailWord_765932) baseStart_765932 baseEnd_765932 := by
    simpa [prefixWord, tailWord_765932, baseEnd_765932] using wordTrace_append hprefix tailTrace_765932
  have hstable : (prefixWord ++ tailWord_765932).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_765932).length < 2 ^ (prefixWord ++ tailWord_765932).sum := by decide
  have hdescent : baseEnd_765932 < baseStart_765932 := by decide
  rcases family_descends (prefixWord ++ tailWord_765932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_765934 : List Nat := [4, 1, 2, 1, 3, 1, 1, 1, 2, 6]
def baseStart_765934 : Nat := 118140960795 + 765934 * 2 ^ 59
def prefixEnd_765934 : Nat := 4983230072969 + 3 ^ 40 * 765934 * 2
def baseEnd_765934 : Nat := 262194861080607675601693

theorem tailTrace_765934 : CollatzResearch.WordTrace tailWord_765934 prefixEnd_765934 262194861080607675601693 := by
  unfold tailWord_765934
  simp only [CollatzResearch.WordTrace]
  refine ⟨3491988500894925494738107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 18623938671439602638603237 3491988500894925494738107)
  ·
    refine ⟨5237982751342388242107161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3491988500894925494738107 5237982751342388242107161)
    ·
      refine ⟨3928487063506791181580371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5237982751342388242107161 3928487063506791181580371)
      ·
        refine ⟨5892730595260186772370557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3928487063506791181580371 5892730595260186772370557)
        ·
          refine ⟨2209773973222570039638959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5892730595260186772370557 2209773973222570039638959)
          ·
            refine ⟨3314660959833855059458439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2209773973222570039638959 3314660959833855059458439)
            ·
              refine ⟨4971991439750782589187659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3314660959833855059458439 4971991439750782589187659)
              ·
                refine ⟨7457987159626173883781489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4971991439750782589187659 7457987159626173883781489)
                ·
                  refine ⟨5593490369719630412836117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7457987159626173883781489 5593490369719630412836117)
                  ·
                    refine ⟨262194861080607675601693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5593490369719630412836117 262194861080607675601693)
                    ·
                      rfl

theorem cell22_765934_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 1, 1, 1, 2, 6].length) (baseStart_765934 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_765934 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_765934 prefixEnd_765934 := by exact prefixLift 765934
  have htrace : WordTrace (prefixWord ++ tailWord_765934) baseStart_765934 baseEnd_765934 := by
    simpa [prefixWord, tailWord_765934, baseEnd_765934] using wordTrace_append hprefix tailTrace_765934
  have hstable : (prefixWord ++ tailWord_765934).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_765934).length < 2 ^ (prefixWord ++ tailWord_765934).sum := by decide
  have hdescent : baseEnd_765934 < baseStart_765934 := by decide
  rcases family_descends (prefixWord ++ tailWord_765934) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_765947 : List Nat := [1, 1, 1, 1, 1, 3, 5, 1, 1, 7]
def baseStart_765947 : Nat := 118140960795 + 765947 * 2 ^ 59
def prefixEnd_765947 : Nat := 4983230072969 + 3 ^ 40 * 765947 * 2
def baseEnd_765947 : Nat := 262199311246279975026653

theorem tailTrace_765947 : CollatzResearch.WordTrace tailWord_765947 prefixEnd_765947 262199311246279975026653 := by
  unfold tailWord_765947
  simp only [CollatzResearch.WordTrace]
  refine ⟨27936382156112307178128095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18624254770741538118752063 27936382156112307178128095)
  ·
    refine ⟨41904573234168460767192143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27936382156112307178128095 41904573234168460767192143)
    ·
      refine ⟨62856859851252691150788215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41904573234168460767192143 62856859851252691150788215)
      ·
        refine ⟨94285289776879036726182323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62856859851252691150788215 94285289776879036726182323)
        ·
          refine ⟨141427934665318555089273485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 94285289776879036726182323 141427934665318555089273485)
          ·
            refine ⟨53035475499494458158477557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 141427934665318555089273485 53035475499494458158477557)
            ·
              refine ⟨4972075828077605452357271, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 53035475499494458158477557 4972075828077605452357271)
              ·
                refine ⟨7458113742116408178535907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4972075828077605452357271 7458113742116408178535907)
                ·
                  refine ⟨11187170613174612267803861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7458113742116408178535907 11187170613174612267803861)
                  ·
                    refine ⟨262199311246279975026653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 11187170613174612267803861 262199311246279975026653)
                    ·
                      rfl

theorem cell22_765947_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 5, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 5, 1, 1, 7].length) (baseStart_765947 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_765947 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_765947 prefixEnd_765947 := by exact prefixLift 765947
  have htrace : WordTrace (prefixWord ++ tailWord_765947) baseStart_765947 baseEnd_765947 := by
    simpa [prefixWord, tailWord_765947, baseEnd_765947] using wordTrace_append hprefix tailTrace_765947
  have hstable : (prefixWord ++ tailWord_765947).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_765947).length < 2 ^ (prefixWord ++ tailWord_765947).sum := by decide
  have hdescent : baseEnd_765947 < baseStart_765947 := by decide
  rcases family_descends (prefixWord ++ tailWord_765947) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_765949 : List Nat := [1, 4, 1, 1, 1, 2, 4, 3, 5]
def baseStart_765949 : Nat := 118140960795 + 765949 * 2 ^ 59
def prefixEnd_765949 : Nat := 4983230072969 + 3 ^ 40 * 765949 * 2
def baseEnd_765949 : Nat := 87399998629050878825549

theorem tailTrace_765949 : CollatzResearch.WordTrace tailWord_765949 prefixEnd_765949 87399998629050878825549 := by
  unfold tailWord_765949
  simp only [CollatzResearch.WordTrace]
  refine ⟨27936455102105061519700901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18624303401403374346467267 27936455102105061519700901)
  ·
    refine ⟨5238085331644699034943919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 27936455102105061519700901 5238085331644699034943919)
    ·
      refine ⟨7857127997467048552415879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5238085331644699034943919 7857127997467048552415879)
      ·
        refine ⟨11785691996200572828623819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7857127997467048552415879 11785691996200572828623819)
        ·
          refine ⟨17678537994300859242935729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11785691996200572828623819 17678537994300859242935729)
          ·
            refine ⟨13258903495725644432201797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17678537994300859242935729 13258903495725644432201797)
            ·
              refine ⟨2486044405448558331037837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13258903495725644432201797 2486044405448558331037837)
              ·
                refine ⟨932266652043209374139189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2486044405448558331037837 932266652043209374139189)
                ·
                  refine ⟨87399998629050878825549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 932266652043209374139189 87399998629050878825549)
                  ·
                    rfl

theorem cell22_765949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 4, 3, 5].length) (baseStart_765949 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_765949 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_765949 prefixEnd_765949 := by exact prefixLift 765949
  have htrace : WordTrace (prefixWord ++ tailWord_765949) baseStart_765949 baseEnd_765949 := by
    simpa [prefixWord, tailWord_765949, baseEnd_765949] using wordTrace_append hprefix tailTrace_765949
  have hstable : (prefixWord ++ tailWord_765949).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_765949).length < 2 ^ (prefixWord ++ tailWord_765949).sum := by decide
  have hdescent : baseEnd_765949 < baseStart_765949 := by decide
  rcases family_descends (prefixWord ++ tailWord_765949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_765977 : List Nat := [1, 2, 1, 2, 1, 1, 3, 1, 10]
def baseStart_765977 : Nat := 118140960795 + 765977 * 2 ^ 59
def prefixEnd_765977 : Nat := 4983230072969 + 3 ^ 40 * 765977 * 2
def baseEnd_765977 : Nat := 87403193619789965592187

theorem tailTrace_765977 : CollatzResearch.WordTrace tailWord_765977 prefixEnd_765977 87403193619789965592187 := by
  unfold tailWord_765977
  simp only [CollatzResearch.WordTrace]
  refine ⟨27937476346003622301720185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18624984230669081534480123 27937476346003622301720185)
  ·
    refine ⟨20953107259502716726290139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27937476346003622301720185 20953107259502716726290139)
    ·
      refine ⟨31429660889254075089435209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20953107259502716726290139 31429660889254075089435209)
      ·
        refine ⟨23572245666940556317076407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31429660889254075089435209 23572245666940556317076407)
        ·
          refine ⟨35358368500410834475614611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23572245666940556317076407 35358368500410834475614611)
          ·
            refine ⟨53037552750616251713421917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35358368500410834475614611 53037552750616251713421917)
            ·
              refine ⟨19889082281481094392533219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 53037552750616251713421917 19889082281481094392533219)
              ·
                refine ⟨29833623422221641588799829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19889082281481094392533219 29833623422221641588799829)
                ·
                  refine ⟨87403193619789965592187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 29833623422221641588799829 87403193619789965592187)
                  ·
                    rfl

theorem cell22_765977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 3, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 3, 1, 10].length) (baseStart_765977 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_765977 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_765977 prefixEnd_765977 := by exact prefixLift 765977
  have htrace : WordTrace (prefixWord ++ tailWord_765977) baseStart_765977 baseEnd_765977 := by
    simpa [prefixWord, tailWord_765977, baseEnd_765977] using wordTrace_append hprefix tailTrace_765977
  have hstable : (prefixWord ++ tailWord_765977).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_765977).length < 2 ^ (prefixWord ++ tailWord_765977).sum := by decide
  have hdescent : baseEnd_765977 < baseStart_765977 := by decide
  rcases family_descends (prefixWord ++ tailWord_765977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_766060 : List Nat := [2, 2, 1, 1, 3, 5, 2, 1, 2, 3]
def baseStart_766060 : Nat := 118140960795 + 766060 * 2 ^ 59
def prefixEnd_766060 : Nat := 4983230072969 + 3 ^ 40 * 766060 * 2
def baseEnd_766060 : Nat := 262237993455585346951307

theorem tailTrace_766060 : CollatzResearch.WordTrace tailWord_766060 prefixEnd_766060 262237993455585346951307 := by
  unfold tailWord_766060
  simp only [CollatzResearch.WordTrace]
  refine ⟨13970251802351463738495817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18627002403135284984661089 13970251802351463738495817)
  ·
    refine ⟨10477688851763597803871863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13970251802351463738495817 10477688851763597803871863)
    ·
      refine ⟨15716533277645396705807795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10477688851763597803871863 15716533277645396705807795)
      ·
        refine ⟨23574799916468095058711693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15716533277645396705807795 23574799916468095058711693)
        ·
          refine ⟨8840549968675535647016885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23574799916468095058711693 8840549968675535647016885)
          ·
            refine ⟨828801559563331466907833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 8840549968675535647016885 828801559563331466907833)
            ·
              refine ⟨621601169672498600180875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 828801559563331466907833 621601169672498600180875)
              ·
                refine ⟨932401754508747900271313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 621601169672498600180875 932401754508747900271313)
                ·
                  refine ⟨699301315881560925203485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 932401754508747900271313 699301315881560925203485)
                  ·
                    refine ⟨262237993455585346951307, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 699301315881560925203485 262237993455585346951307)
                    ·
                      rfl

theorem cell22_766060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 2, 3].length) (baseStart_766060 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_766060 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_766060 prefixEnd_766060 := by exact prefixLift 766060
  have htrace : WordTrace (prefixWord ++ tailWord_766060) baseStart_766060 baseEnd_766060 := by
    simpa [prefixWord, tailWord_766060, baseEnd_766060] using wordTrace_append hprefix tailTrace_766060
  have hstable : (prefixWord ++ tailWord_766060).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_766060).length < 2 ^ (prefixWord ++ tailWord_766060).sum := by decide
  have hdescent : baseEnd_766060 < baseStart_766060 := by decide
  rcases family_descends (prefixWord ++ tailWord_766060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_766099 : List Nat := [1, 1, 1, 2, 1, 2, 3, 4, 2, 5]
def baseStart_766099 : Nat := 118140960795 + 766099 * 2 ^ 59
def prefixEnd_766099 : Nat := 4983230072969 + 3 ^ 40 * 766099 * 2
def baseEnd_766099 : Nat := 262251343952602245226187

theorem tailTrace_766099 : CollatzResearch.WordTrace tailWord_766099 prefixEnd_766099 262251343952602245226187 := by
  unfold tailWord_766099
  simp only [CollatzResearch.WordTrace]
  refine ⟨27941926051561637137661351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18627950701041091425107567 27941926051561637137661351)
  ·
    refine ⟨41912889077342455706492027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27941926051561637137661351 41912889077342455706492027)
    ·
      refine ⟨62869333616013683559738041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41912889077342455706492027 62869333616013683559738041)
      ·
        refine ⟨47152000212010262669803531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62869333616013683559738041 47152000212010262669803531)
        ·
          refine ⟨70728000318015394004705297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47152000212010262669803531 70728000318015394004705297)
          ·
            refine ⟨53046000238511545503528973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 70728000318015394004705297 53046000238511545503528973)
            ·
              refine ⟨19892250089441829563823365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 53046000238511545503528973 19892250089441829563823365)
              ·
                refine ⟨3729796891770343043216881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19892250089441829563823365 3729796891770343043216881)
                ·
                  refine ⟨2797347668827757282412661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3729796891770343043216881 2797347668827757282412661)
                  ·
                    refine ⟨262251343952602245226187, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2797347668827757282412661 262251343952602245226187)
                    ·
                      rfl

theorem cell22_766099_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 3, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 3, 4, 2, 5].length) (baseStart_766099 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_766099 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_766099 prefixEnd_766099 := by exact prefixLift 766099
  have htrace : WordTrace (prefixWord ++ tailWord_766099) baseStart_766099 baseEnd_766099 := by
    simpa [prefixWord, tailWord_766099, baseEnd_766099] using wordTrace_append hprefix tailTrace_766099
  have hstable : (prefixWord ++ tailWord_766099).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_766099).length < 2 ^ (prefixWord ++ tailWord_766099).sum := by decide
  have hdescent : baseEnd_766099 < baseStart_766099 := by decide
  rcases family_descends (prefixWord ++ tailWord_766099) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_766101 : List Nat := [1, 3, 2, 1, 1, 1, 6, 2, 5]
def baseStart_766101 : Nat := 118140960795 + 766101 * 2 ^ 59
def prefixEnd_766101 : Nat := 4983230072969 + 3 ^ 40 * 766101 * 2
def baseEnd_766101 : Nat := 87417342864491635558727

theorem tailTrace_766101 : CollatzResearch.WordTrace tailWord_766101 prefixEnd_766101 87417342864491635558727 := by
  unfold tailWord_766101
  simp only [CollatzResearch.WordTrace]
  refine ⟨27941998997554391479234157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18627999331702927652822771 27941998997554391479234157)
  ·
    refine ⟨10478249624082896804712809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27941998997554391479234157 10478249624082896804712809)
    ·
      refine ⟨7858687218062172603534607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10478249624082896804712809 7858687218062172603534607)
      ·
        refine ⟨11788030827093258905301911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7858687218062172603534607 11788030827093258905301911)
        ·
          refine ⟨17682046240639888357952867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11788030827093258905301911 17682046240639888357952867)
          ·
            refine ⟨26523069360959832536929301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17682046240639888357952867 26523069360959832536929301)
            ·
              refine ⟨1243268876294992150168561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 26523069360959832536929301 1243268876294992150168561)
              ·
                refine ⟨932451657221244112626421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1243268876294992150168561 932451657221244112626421)
                ·
                  refine ⟨87417342864491635558727, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 932451657221244112626421 87417342864491635558727)
                  ·
                    rfl

theorem cell22_766101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 6, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 6, 2, 5].length) (baseStart_766101 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_766101 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_766101 prefixEnd_766101 := by exact prefixLift 766101
  have htrace : WordTrace (prefixWord ++ tailWord_766101) baseStart_766101 baseEnd_766101 := by
    simpa [prefixWord, tailWord_766101, baseEnd_766101] using wordTrace_append hprefix tailTrace_766101
  have hstable : (prefixWord ++ tailWord_766101).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_766101).length < 2 ^ (prefixWord ++ tailWord_766101).sum := by decide
  have hdescent : baseEnd_766101 < baseStart_766101 := by decide
  rcases family_descends (prefixWord ++ tailWord_766101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_766131 : List Nat := [1, 1, 1, 2, 3, 2, 1, 6, 1, 4]
def baseStart_766131 : Nat := 118140960795 + 766131 * 2 ^ 59
def prefixEnd_766131 : Nat := 4983230072969 + 3 ^ 40 * 766131 * 2
def baseEnd_766131 : Nat := 262262298206564828426089

theorem tailTrace_766131 : CollatzResearch.WordTrace tailWord_766131 prefixEnd_766131 262262298206564828426089 := by
  unfold tailWord_766131
  simp only [CollatzResearch.WordTrace]
  refine ⟨27943093187445706602826247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18628728791630471068550831 27943093187445706602826247)
  ·
    refine ⟨41914639781168559904239371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27943093187445706602826247 41914639781168559904239371)
    ·
      refine ⟨62871959671752839856359057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41914639781168559904239371 62871959671752839856359057)
      ·
        refine ⟨47153969753814629892269293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62871959671752839856359057 47153969753814629892269293)
        ·
          refine ⟨17682738657680486209600985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 47153969753814629892269293 17682738657680486209600985)
          ·
            refine ⟨13262053993260364657200739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17682738657680486209600985 13262053993260364657200739)
            ·
              refine ⟨19893080989890546985801109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13262053993260364657200739 19893080989890546985801109)
              ·
                refine ⟨932488171401119389959427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 19893080989890546985801109 932488171401119389959427)
                ·
                  refine ⟨1398732257101679084939141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 932488171401119389959427 1398732257101679084939141)
                  ·
                    refine ⟨262262298206564828426089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1398732257101679084939141 262262298206564828426089)
                    ·
                      rfl

theorem cell22_766131_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 1, 6, 1, 4].length) (baseStart_766131 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_766131 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_766131 prefixEnd_766131 := by exact prefixLift 766131
  have htrace : WordTrace (prefixWord ++ tailWord_766131) baseStart_766131 baseEnd_766131 := by
    simpa [prefixWord, tailWord_766131, baseEnd_766131] using wordTrace_append hprefix tailTrace_766131
  have hstable : (prefixWord ++ tailWord_766131).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_766131).length < 2 ^ (prefixWord ++ tailWord_766131).sum := by decide
  have hdescent : baseEnd_766131 < baseStart_766131 := by decide
  rcases family_descends (prefixWord ++ tailWord_766131) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_766191 : List Nat := [1, 1, 2, 1, 6, 2, 1, 8]
def baseStart_766191 : Nat := 118140960795 + 766191 * 2 ^ 59
def prefixEnd_766191 : Nat := 4983230072969 + 3 ^ 40 * 766191 * 2
def baseEnd_766191 : Nat := 29142537492527185769545

theorem tailTrace_766191 : CollatzResearch.WordTrace tailWord_766191 prefixEnd_766191 29142537492527185769545 := by
  unfold tailWord_766191
  simp only [CollatzResearch.WordTrace]
  refine ⟨27945281567228336850010427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18630187711485557900006951 27945281567228336850010427)
  ·
    refine ⟨41917922350842505275015641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27945281567228336850010427 41917922350842505275015641)
    ·
      refine ⟨31438441763131878956261731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41917922350842505275015641 31438441763131878956261731)
      ·
        refine ⟨47157662644697818434392597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31438441763131878956261731 47157662644697818434392597)
        ·
          refine ⟨2210515436470210239112153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 47157662644697818434392597 2210515436470210239112153)
          ·
            refine ⟨1657886577352657679334115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2210515436470210239112153 1657886577352657679334115)
            ·
              refine ⟨2486829866028986519001173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1657886577352657679334115 2486829866028986519001173)
              ·
                refine ⟨29142537492527185769545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 2486829866028986519001173 29142537492527185769545)
                ·
                  rfl

theorem cell22_766191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 2, 1, 8].length) (baseStart_766191 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_766191 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_766191 prefixEnd_766191 := by exact prefixLift 766191
  have htrace : WordTrace (prefixWord ++ tailWord_766191) baseStart_766191 baseEnd_766191 := by
    simpa [prefixWord, tailWord_766191, baseEnd_766191] using wordTrace_append hprefix tailTrace_766191
  have hstable : (prefixWord ++ tailWord_766191).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_766191).length < 2 ^ (prefixWord ++ tailWord_766191).sum := by decide
  have hdescent : baseEnd_766191 < baseStart_766191 := by decide
  rcases family_descends (prefixWord ++ tailWord_766191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_766210 : List Nat := [3, 4, 1, 1, 2, 2, 1, 2, 2, 4]
def baseStart_766210 : Nat := 118140960795 + 766210 * 2 ^ 59
def prefixEnd_766210 : Nat := 4983230072969 + 3 ^ 40 * 766210 * 2
def baseEnd_766210 : Nat := 262289341521034955700847

theorem tailTrace_766210 : CollatzResearch.WordTrace tailWord_766210 prefixEnd_766210 262289341521034955700847 := by
  unfold tailWord_766210
  simp only [CollatzResearch.WordTrace]
  refine ⟨6986493638539875773738021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18630649702773002063301389 6986493638539875773738021)
  ·
    refine ⟨1309967557226226707575879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 6986493638539875773738021 1309967557226226707575879)
    ·
      refine ⟨1964951335839340061363819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1309967557226226707575879 1964951335839340061363819)
      ·
        refine ⟨2947427003759010092045729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1964951335839340061363819 2947427003759010092045729)
        ·
          refine ⟨2210570252819257569034297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2947427003759010092045729 2210570252819257569034297)
          ·
            refine ⟨1657927689614443176775723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2210570252819257569034297 1657927689614443176775723)
            ·
              refine ⟨2486891534421664765163585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1657927689614443176775723 2486891534421664765163585)
              ·
                refine ⟨1865168650816248573872689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2486891534421664765163585 1865168650816248573872689)
                ·
                  refine ⟨1398876488112186430404517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1865168650816248573872689 1398876488112186430404517)
                  ·
                    refine ⟨262289341521034955700847, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1398876488112186430404517 262289341521034955700847)
                    ·
                      rfl

theorem cell22_766210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 2, 1, 2, 2, 4].length) (baseStart_766210 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_766210 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_766210 prefixEnd_766210 := by exact prefixLift 766210
  have htrace : WordTrace (prefixWord ++ tailWord_766210) baseStart_766210 baseEnd_766210 := by
    simpa [prefixWord, tailWord_766210, baseEnd_766210] using wordTrace_append hprefix tailTrace_766210
  have hstable : (prefixWord ++ tailWord_766210).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_766210).length < 2 ^ (prefixWord ++ tailWord_766210).sum := by decide
  have hdescent : baseEnd_766210 < baseStart_766210 := by decide
  rcases family_descends (prefixWord ++ tailWord_766210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_766270 : List Nat := [4, 2, 1, 2, 1, 3, 2, 2, 5]
def baseStart_766270 : Nat := 118140960795 + 766270 * 2 ^ 59
def prefixEnd_766270 : Nat := 4983230072969 + 3 ^ 40 * 766270 * 2
def baseEnd_766270 : Nat := 87436626915738266400221

theorem tailTrace_766270 : CollatzResearch.WordTrace tailWord_766270 prefixEnd_766270 87436626915738266400221 := by
  unfold tailWord_766270
  simp only [CollatzResearch.WordTrace]
  refine ⟨3493520366742766667767033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 18632108622628088894757509 3493520366742766667767033)
  ·
    refine ⟨2620140275057075000825275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3493520366742766667767033 2620140275057075000825275)
    ·
      refine ⟨3930210412585612501237913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2620140275057075000825275 3930210412585612501237913)
      ·
        refine ⟨2947657809439209375928435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3930210412585612501237913 2947657809439209375928435)
        ·
          refine ⟨4421486714158814063892653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2947657809439209375928435 4421486714158814063892653)
          ·
            refine ⟨1658057517809555273959745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4421486714158814063892653 1658057517809555273959745)
            ·
              refine ⟨1243543138357166455469809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1658057517809555273959745 1243543138357166455469809)
              ·
                refine ⟨932657353767874841602357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1243543138357166455469809 932657353767874841602357)
                ·
                  refine ⟨87436626915738266400221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 932657353767874841602357 87436626915738266400221)
                  ·
                    rfl

theorem cell22_766270_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 3, 2, 2, 5].length) (baseStart_766270 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_766270 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_766270 prefixEnd_766270 := by exact prefixLift 766270
  have htrace : WordTrace (prefixWord ++ tailWord_766270) baseStart_766270 baseEnd_766270 := by
    simpa [prefixWord, tailWord_766270, baseEnd_766270] using wordTrace_append hprefix tailTrace_766270
  have hstable : (prefixWord ++ tailWord_766270).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_766270).length < 2 ^ (prefixWord ++ tailWord_766270).sum := by decide
  have hdescent : baseEnd_766270 < baseStart_766270 := by decide
  rcases family_descends (prefixWord ++ tailWord_766270) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_766281 : List Nat := [1, 2, 1, 1, 2, 3, 1, 5, 6]
def baseStart_766281 : Nat := 118140960795 + 766281 * 2 ^ 59
def prefixEnd_766281 : Nat := 4983230072969 + 3 ^ 40 * 766281 * 2
def baseEnd_766281 : Nat := 87437882090671479058543

theorem tailTrace_766281 : CollatzResearch.WordTrace tailWord_766281 prefixEnd_766281 87437882090671479058543 := by
  unfold tailWord_766281
  simp only [CollatzResearch.WordTrace]
  refine ⟨27948564136902282220786697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18632376091268188147191131 27948564136902282220786697)
  ·
    refine ⟨20961423102676711665590023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27948564136902282220786697 20961423102676711665590023)
    ·
      refine ⟨31442134654015067498385035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20961423102676711665590023 31442134654015067498385035)
      ·
        refine ⟨47163201981022601247577553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31442134654015067498385035 47163201981022601247577553)
        ·
          refine ⟨35372401485766950935683165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47163201981022601247577553 35372401485766950935683165)
          ·
            refine ⟨13264650557162606600881187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35372401485766950935683165 13264650557162606600881187)
            ·
              refine ⟨19896975835743909901321781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13264650557162606600881187 19896975835743909901321781)
              ·
                refine ⟨1865341484600991553248917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 19896975835743909901321781 1865341484600991553248917)
                ·
                  refine ⟨87437882090671479058543, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1865341484600991553248917 87437882090671479058543)
                  ·
                    rfl

theorem cell22_766281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 1, 5, 6].length) (baseStart_766281 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_766281 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_766281 prefixEnd_766281 := by exact prefixLift 766281
  have htrace : WordTrace (prefixWord ++ tailWord_766281) baseStart_766281 baseEnd_766281 := by
    simpa [prefixWord, tailWord_766281, baseEnd_766281] using wordTrace_append hprefix tailTrace_766281
  have hstable : (prefixWord ++ tailWord_766281).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_766281).length < 2 ^ (prefixWord ++ tailWord_766281).sum := by decide
  have hdescent : baseEnd_766281 < baseStart_766281 := by decide
  rcases family_descends (prefixWord ++ tailWord_766281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_766313 : List Nat := [1, 2, 1, 1, 1, 3, 4, 2, 4, 3]
def baseStart_766313 : Nat := 118140960795 + 766313 * 2 ^ 59
def prefixEnd_766313 : Nat := 4983230072969 + 3 ^ 40 * 766313 * 2
def baseEnd_766313 : Nat := 262324600525977020375531

theorem tailTrace_766313 : CollatzResearch.WordTrace tailWord_766313 prefixEnd_766313 262324600525977020375531 := by
  unfold tailWord_766313
  simp only [CollatzResearch.WordTrace]
  refine ⟨27949731272786351685951593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18633154181857567790634395 27949731272786351685951593)
  ·
    refine ⟨20962298454589763764463695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27949731272786351685951593 20962298454589763764463695)
    ·
      refine ⟨31443447681884645646695543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20962298454589763764463695 31443447681884645646695543)
      ·
        refine ⟨47165171522826968470043315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31443447681884645646695543 47165171522826968470043315)
        ·
          refine ⟨70747757284240452705064973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47165171522826968470043315 70747757284240452705064973)
          ·
            refine ⟨26530408981590169764399365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 70747757284240452705064973 26530408981590169764399365)
            ·
              refine ⟨4974451684048156830824881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 26530408981590169764399365 4974451684048156830824881)
              ·
                refine ⟨3730838763036117623118661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4974451684048156830824881 3730838763036117623118661)
                ·
                  refine ⟨699532268069272054334749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3730838763036117623118661 699532268069272054334749)
                  ·
                    refine ⟨262324600525977020375531, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 699532268069272054334749 262324600525977020375531)
                    ·
                      rfl

theorem cell22_766313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 4, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 4, 2, 4, 3].length) (baseStart_766313 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_766313 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_766313 prefixEnd_766313 := by exact prefixLift 766313
  have htrace : WordTrace (prefixWord ++ tailWord_766313) baseStart_766313 baseEnd_766313 := by
    simpa [prefixWord, tailWord_766313, baseEnd_766313] using wordTrace_append hprefix tailTrace_766313
  have hstable : (prefixWord ++ tailWord_766313).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_766313).length < 2 ^ (prefixWord ++ tailWord_766313).sum := by decide
  have hdescent : baseEnd_766313 < baseStart_766313 := by decide
  rcases family_descends (prefixWord ++ tailWord_766313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_766347 : List Nat := [1, 1, 1, 1, 4, 5, 3, 1, 2, 3]
def baseStart_766347 : Nat := 118140960795 + 766347 * 2 ^ 59
def prefixEnd_766347 : Nat := 4983230072969 + 3 ^ 40 * 766347 * 2
def baseEnd_766347 : Nat := 262336239420812265025427

theorem tailTrace_766347 : CollatzResearch.WordTrace tailWord_766347 prefixEnd_766347 262336239420812265025427 := by
  unfold tailWord_766347
  simp only [CollatzResearch.WordTrace]
  refine ⟨27950971354663175492689295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18633980903108783661792863 27950971354663175492689295)
  ·
    refine ⟨41926457031994763239033943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27950971354663175492689295 41926457031994763239033943)
    ·
      refine ⟨62889685547992144858550915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41926457031994763239033943 62889685547992144858550915)
      ·
        refine ⟨94334528321988217287826373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62889685547992144858550915 94334528321988217287826373)
        ·
          refine ⟨17687724060372790741467445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 94334528321988217287826373 17687724060372790741467445)
          ·
            refine ⟨1658224130659949132012573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 17687724060372790741467445 1658224130659949132012573)
            ·
              refine ⟨621834048997480924504715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1658224130659949132012573 621834048997480924504715)
              ·
                refine ⟨932751073496221386757073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 621834048997480924504715 932751073496221386757073)
                ·
                  refine ⟨699563305122166040067805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 932751073496221386757073 699563305122166040067805)
                  ·
                    refine ⟨262336239420812265025427, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 699563305122166040067805 262336239420812265025427)
                    ·
                      rfl

theorem cell22_766347_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 5, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 5, 3, 1, 2, 3].length) (baseStart_766347 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_766347 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_766347 prefixEnd_766347 := by exact prefixLift 766347
  have htrace : WordTrace (prefixWord ++ tailWord_766347) baseStart_766347 baseEnd_766347 := by
    simpa [prefixWord, tailWord_766347, baseEnd_766347] using wordTrace_append hprefix tailTrace_766347
  have hstable : (prefixWord ++ tailWord_766347).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_766347).length < 2 ^ (prefixWord ++ tailWord_766347).sum := by decide
  have hdescent : baseEnd_766347 < baseStart_766347 := by decide
  rcases family_descends (prefixWord ++ tailWord_766347) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_766360 : List Nat := [2, 1, 2, 5, 1, 1, 4, 6]
def baseStart_766360 : Nat := 118140960795 + 766360 * 2 ^ 59
def prefixEnd_766360 : Nat := 4983230072969 + 3 ^ 40 * 766360 * 2
def baseEnd_766360 : Nat := 29148965509609396050043

theorem tailTrace_766360 : CollatzResearch.WordTrace tailWord_766360 prefixEnd_766360 29148965509609396050043 := by
  unfold tailWord_766360
  simp only [CollatzResearch.WordTrace]
  refine ⟨13975722751808039356456267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18634297002410719141941689 13975722751808039356456267)
  ·
    refine ⟨20963584127712059034684401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13975722751808039356456267 20963584127712059034684401)
    ·
      refine ⟨15722688095784044276013301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20963584127712059034684401 15722688095784044276013301)
      ·
        refine ⟨1474002008979754150876247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 15722688095784044276013301 1474002008979754150876247)
        ·
          refine ⟨2211003013469631226314371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1474002008979754150876247 2211003013469631226314371)
          ·
            refine ⟨3316504520204446839471557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2211003013469631226314371 3316504520204446839471557)
            ·
              refine ⟨621844597538333782400917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3316504520204446839471557 621844597538333782400917)
              ·
                refine ⟨29148965509609396050043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 621844597538333782400917 29148965509609396050043)
                ·
                  rfl

theorem cell22_766360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 1, 4, 6].length) (baseStart_766360 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_766360 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_766360 prefixEnd_766360 := by exact prefixLift 766360
  have htrace : WordTrace (prefixWord ++ tailWord_766360) baseStart_766360 baseEnd_766360 := by
    simpa [prefixWord, tailWord_766360, baseEnd_766360] using wordTrace_append hprefix tailTrace_766360
  have hstable : (prefixWord ++ tailWord_766360).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_766360).length < 2 ^ (prefixWord ++ tailWord_766360).sum := by decide
  have hdescent : baseEnd_766360 < baseStart_766360 := by decide
  rcases family_descends (prefixWord ++ tailWord_766360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_766448 : List Nat := [2, 1, 1, 1, 3, 3, 1, 2, 3, 5]
def baseStart_766448 : Nat := 118140960795 + 766448 * 2 ^ 59
def prefixEnd_766448 : Nat := 4983230072969 + 3 ^ 40 * 766448 * 2
def baseEnd_766448 : Nat := 262370813784881668250117

theorem tailTrace_766448 : CollatzResearch.WordTrace tailWord_766448 prefixEnd_766448 262370813784881668250117 := by
  unfold tailWord_766448
  simp only [CollatzResearch.WordTrace]
  refine ⟨13977327563648634871057999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18636436751531513161410665 13977327563648634871057999)
  ·
    refine ⟨20965991345472952306586999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13977327563648634871057999 20965991345472952306586999)
    ·
      refine ⟨31448987018209428459880499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20965991345472952306586999 31448987018209428459880499)
      ·
        refine ⟨47173480527314142689820749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31448987018209428459880499 47173480527314142689820749)
        ·
          refine ⟨17690055197742803508682781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 47173480527314142689820749 17690055197742803508682781)
          ·
            refine ⟨6633770699153551315756043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17690055197742803508682781 6633770699153551315756043)
            ·
              refine ⟨9950656048730326973634065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6633770699153551315756043 9950656048730326973634065)
              ·
                refine ⟨7462992036547745230225549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9950656048730326973634065 7462992036547745230225549)
                ·
                  refine ⟨2798622013705404461334581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7462992036547745230225549 2798622013705404461334581)
                  ·
                    refine ⟨262370813784881668250117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2798622013705404461334581 262370813784881668250117)
                    ·
                      rfl

theorem cell22_766448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 1, 2, 3, 5].length) (baseStart_766448 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_766448 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_766448 prefixEnd_766448 := by exact prefixLift 766448
  have htrace : WordTrace (prefixWord ++ tailWord_766448) baseStart_766448 baseEnd_766448 := by
    simpa [prefixWord, tailWord_766448, baseEnd_766448] using wordTrace_append hprefix tailTrace_766448
  have hstable : (prefixWord ++ tailWord_766448).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_766448).length < 2 ^ (prefixWord ++ tailWord_766448).sum := by decide
  have hdescent : baseEnd_766448 < baseStart_766448 := by decide
  rcases family_descends (prefixWord ++ tailWord_766448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_766463 : List Nat := [1, 1, 2, 2, 1, 2, 4, 2, 1, 6]
def baseStart_766463 : Nat := 118140960795 + 766463 * 2 ^ 59
def prefixEnd_766463 : Nat := 4983230072969 + 3 ^ 40 * 766463 * 2
def baseEnd_766463 : Nat := 262375948591426629125071

theorem tailTrace_766463 : CollatzResearch.WordTrace tailWord_766463 prefixEnd_766463 262375948591426629125071 := by
  unfold tailWord_766463
  simp only [CollatzResearch.WordTrace]
  refine ⟨27955202222242927303912043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18636801481495284869274695 27955202222242927303912043)
  ·
    refine ⟨41932803333364390955868065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27955202222242927303912043 41932803333364390955868065)
    ·
      refine ⟨31449602500023293216901049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41932803333364390955868065 31449602500023293216901049)
      ·
        refine ⟨23587201875017469912675787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31449602500023293216901049 23587201875017469912675787)
        ·
          refine ⟨35380802812526204869013681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23587201875017469912675787 35380802812526204869013681)
          ·
            refine ⟨26535602109394653651760261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35380802812526204869013681 26535602109394653651760261)
            ·
              refine ⟨4975425395511497559705049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 26535602109394653651760261 4975425395511497559705049)
              ·
                refine ⟨3731569046633623169778787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4975425395511497559705049 3731569046633623169778787)
                ·
                  refine ⟨5597353569950434754668181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3731569046633623169778787 5597353569950434754668181)
                  ·
                    refine ⟨262375948591426629125071, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5597353569950434754668181 262375948591426629125071)
                    ·
                      rfl

theorem cell22_766463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 4, 2, 1, 6].length) (baseStart_766463 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_766463 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_766463 prefixEnd_766463 := by exact prefixLift 766463
  have htrace : WordTrace (prefixWord ++ tailWord_766463) baseStart_766463 baseEnd_766463 := by
    simpa [prefixWord, tailWord_766463, baseEnd_766463] using wordTrace_append hprefix tailTrace_766463
  have hstable : (prefixWord ++ tailWord_766463).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_766463).length < 2 ^ (prefixWord ++ tailWord_766463).sum := by decide
  have hdescent : baseEnd_766463 < baseStart_766463 := by decide
  rcases family_descends (prefixWord ++ tailWord_766463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_766465 : List Nat := [1, 2, 4, 1, 3, 1, 1, 3, 1, 5]
def baseStart_766465 : Nat := 118140960795 + 766465 * 2 ^ 59
def prefixEnd_766465 : Nat := 4983230072969 + 3 ^ 40 * 766465 * 2
def baseEnd_766465 : Nat := 262376633232299290575065

theorem tailTrace_766465 : CollatzResearch.WordTrace tailWord_766465 prefixEnd_766465 262376633232299290575065 := by
  unfold tailWord_766465
  simp only [CollatzResearch.WordTrace]
  refine ⟨27955275168235681645484849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18636850112157121096989899 27955275168235681645484849)
  ·
    refine ⟨20966456376176761234113637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27955275168235681645484849 20966456376176761234113637)
    ·
      refine ⟨3931210570533142731396307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 20966456376176761234113637 3931210570533142731396307)
      ·
        refine ⟨5896815855799714097094461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3931210570533142731396307 5896815855799714097094461)
        ·
          refine ⟨2211305945924892786410423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5896815855799714097094461 2211305945924892786410423)
          ·
            refine ⟨3316958918887339179615635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2211305945924892786410423 3316958918887339179615635)
            ·
              refine ⟨4975438378331008769423453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3316958918887339179615635 4975438378331008769423453)
              ·
                refine ⟨1865789391874128288533795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4975438378331008769423453 1865789391874128288533795)
                ·
                  refine ⟨2798684087811192432800693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1865789391874128288533795 2798684087811192432800693)
                  ·
                    refine ⟨262376633232299290575065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2798684087811192432800693 262376633232299290575065)
                    ·
                      rfl

theorem cell22_766465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 1, 1, 3, 1, 5].length) (baseStart_766465 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_766465 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_766465 prefixEnd_766465 := by exact prefixLift 766465
  have htrace : WordTrace (prefixWord ++ tailWord_766465) baseStart_766465 baseEnd_766465 := by
    simpa [prefixWord, tailWord_766465, baseEnd_766465] using wordTrace_append hprefix tailTrace_766465
  have hstable : (prefixWord ++ tailWord_766465).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_766465).length < 2 ^ (prefixWord ++ tailWord_766465).sum := by decide
  have hdescent : baseEnd_766465 < baseStart_766465 := by decide
  rcases family_descends (prefixWord ++ tailWord_766465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_766484 : List Nat := [2, 4, 3, 1, 1, 1, 1, 5, 4]
def baseStart_766484 : Nat := 118140960795 + 766484 * 2 ^ 59
def prefixEnd_766484 : Nat := 4983230072969 + 3 ^ 40 * 766484 * 2
def baseEnd_766484 : Nat := 87461045773529858116669

theorem tailTrace_766484 : CollatzResearch.WordTrace tailWord_766484 prefixEnd_766484 87461045773529858116669 := by
  unfold tailWord_766484
  simp only [CollatzResearch.WordTrace]
  refine ⟨13977984077583423945213253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18637312103444565260284337 13977984077583423945213253)
  ·
    refine ⟨2620872014546891989727485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 13977984077583423945213253 2620872014546891989727485)
    ·
      refine ⟨982827005455084496147807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2620872014546891989727485 982827005455084496147807)
      ·
        refine ⟨1474240508182626744221711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 982827005455084496147807 1474240508182626744221711)
        ·
          refine ⟨2211360762273940116332567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1474240508182626744221711 2211360762273940116332567)
          ·
            refine ⟨3317041143410910174498851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2211360762273940116332567 3317041143410910174498851)
            ·
              refine ⟨4975561715116365261748277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3317041143410910174498851 4975561715116365261748277)
              ·
                refine ⟨466458910792159243288901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 4975561715116365261748277 466458910792159243288901)
                ·
                  refine ⟨87461045773529858116669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 466458910792159243288901 87461045773529858116669)
                  ·
                    rfl

theorem cell22_766484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 1, 1, 5, 4].length) (baseStart_766484 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_766484 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_766484 prefixEnd_766484 := by exact prefixLift 766484
  have htrace : WordTrace (prefixWord ++ tailWord_766484) baseStart_766484 baseEnd_766484 := by
    simpa [prefixWord, tailWord_766484, baseEnd_766484] using wordTrace_append hprefix tailTrace_766484
  have hstable : (prefixWord ++ tailWord_766484).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_766484).length < 2 ^ (prefixWord ++ tailWord_766484).sum := by decide
  have hdescent : baseEnd_766484 < baseStart_766484 := by decide
  rcases family_descends (prefixWord ++ tailWord_766484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_766499 : List Nat := [1, 1, 1, 4, 4, 3, 1, 2, 2, 3]
def baseStart_766499 : Nat := 118140960795 + 766499 * 2 ^ 59
def prefixEnd_766499 : Nat := 4983230072969 + 3 ^ 40 * 766499 * 2
def baseEnd_766499 : Nat := 262388272127134535224961

theorem tailTrace_766499 : CollatzResearch.WordTrace tailWord_766499 prefixEnd_766499 262388272127134535224961 := by
  unfold tailWord_766499
  simp only [CollatzResearch.WordTrace]
  refine ⟨27956515250112505452222551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18637676833408336968148367 27956515250112505452222551)
  ·
    refine ⟨41934772875168758178333827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27956515250112505452222551 41934772875168758178333827)
    ·
      refine ⟨62902159312753137267500741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41934772875168758178333827 62902159312753137267500741)
      ·
        refine ⟨11794154871141213237656389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 62902159312753137267500741 11794154871141213237656389)
        ·
          refine ⟨2211404038338977482060573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11794154871141213237656389 2211404038338977482060573)
          ·
            refine ⟨829276514377116555772715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2211404038338977482060573 829276514377116555772715)
            ·
              refine ⟨1243914771565674833659073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 829276514377116555772715 1243914771565674833659073)
              ·
                refine ⟨932936078674256125244305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1243914771565674833659073 932936078674256125244305)
                ·
                  refine ⟨699702059005692093933229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 932936078674256125244305 699702059005692093933229)
                  ·
                    refine ⟨262388272127134535224961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 699702059005692093933229 262388272127134535224961)
                    ·
                      rfl

theorem cell22_766499_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 3, 1, 2, 2, 3].length) (baseStart_766499 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_766499 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_766499 prefixEnd_766499 := by exact prefixLift 766499
  have htrace : WordTrace (prefixWord ++ tailWord_766499) baseStart_766499 baseEnd_766499 := by
    simpa [prefixWord, tailWord_766499, baseEnd_766499] using wordTrace_append hprefix tailTrace_766499
  have hstable : (prefixWord ++ tailWord_766499).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_766499).length < 2 ^ (prefixWord ++ tailWord_766499).sum := by decide
  have hdescent : baseEnd_766499 < baseStart_766499 := by decide
  rcases family_descends (prefixWord ++ tailWord_766499) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_766508 : List Nat := [2, 2, 1, 1, 1, 2, 1, 3, 1, 8]
def baseStart_766508 : Nat := 118140960795 + 766508 * 2 ^ 59
def prefixEnd_766508 : Nat := 4983230072969 + 3 ^ 40 * 766508 * 2
def baseEnd_766508 : Nat := 262391353011061511749933

theorem tailTrace_766508 : CollatzResearch.WordTrace tailWord_766508 prefixEnd_766508 262391353011061511749933 := by
  unfold tailWord_766508
  simp only [CollatzResearch.WordTrace]
  refine ⟨13978421753539949994650089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18637895671386599992866785 13978421753539949994650089)
  ·
    refine ⟨10483816315154962495987567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13978421753539949994650089 10483816315154962495987567)
    ·
      refine ⟨15725724472732443743981351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10483816315154962495987567 15725724472732443743981351)
      ·
        refine ⟨23588586709098665615972027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15725724472732443743981351 23588586709098665615972027)
        ·
          refine ⟨35382880063647998423958041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23588586709098665615972027 35382880063647998423958041)
          ·
            refine ⟨26537160047735998817968531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35382880063647998423958041 26537160047735998817968531)
            ·
              refine ⟨39805740071603998226952797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26537160047735998817968531 39805740071603998226952797)
              ·
                refine ⟨14927152526851499335107299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 39805740071603998226952797 14927152526851499335107299)
                ·
                  refine ⟨22390728790277249002660949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14927152526851499335107299 22390728790277249002660949)
                  ·
                    refine ⟨262391353011061511749933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 22390728790277249002660949 262391353011061511749933)
                    ·
                      rfl

theorem cell22_766508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 8].length) (baseStart_766508 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_766508 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_766508 prefixEnd_766508 := by exact prefixLift 766508
  have htrace : WordTrace (prefixWord ++ tailWord_766508) baseStart_766508 baseEnd_766508 := by
    simpa [prefixWord, tailWord_766508, baseEnd_766508] using wordTrace_append hprefix tailTrace_766508
  have hstable : (prefixWord ++ tailWord_766508).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_766508).length < 2 ^ (prefixWord ++ tailWord_766508).sum := by decide
  have hdescent : baseEnd_766508 < baseStart_766508 := by decide
  rcases family_descends (prefixWord ++ tailWord_766508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_766516 : List Nat := [2, 5, 1, 3, 1, 2, 1, 1, 1, 5]
def baseStart_766516 : Nat := 118140960795 + 766516 * 2 ^ 59
def prefixEnd_766516 : Nat := 4983230072969 + 3 ^ 40 * 766516 * 2
def baseEnd_766516 : Nat := 262394091574552157549909

theorem tailTrace_766516 : CollatzResearch.WordTrace tailWord_766516 prefixEnd_766516 262394091574552157549909 := by
  unfold tailWord_766516
  simp only [CollatzResearch.WordTrace]
  refine ⟨13978567645525458677795701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18638090194033944903727601 13978567645525458677795701)
  ·
    refine ⟨1310490716768011751043347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 13978567645525458677795701 1310490716768011751043347)
    ·
      refine ⟨1965736075152017626565021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1310490716768011751043347 1965736075152017626565021)
      ·
        refine ⟨737151028182006609961883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1965736075152017626565021 737151028182006609961883)
        ·
          refine ⟨1105726542273009914942825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 737151028182006609961883 1105726542273009914942825)
          ·
            refine ⟨829294906704757436207119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1105726542273009914942825 829294906704757436207119)
            ·
              refine ⟨1243942360057136154310679, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 829294906704757436207119 1243942360057136154310679)
              ·
                refine ⟨1865913540085704231466019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1243942360057136154310679 1865913540085704231466019)
                ·
                  refine ⟨2798870310128556347199029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1865913540085704231466019 2798870310128556347199029)
                  ·
                    refine ⟨262394091574552157549909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2798870310128556347199029 262394091574552157549909)
                    ·
                      rfl

theorem cell22_766516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 1, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 1, 2, 1, 1, 1, 5].length) (baseStart_766516 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_766516 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_766516 prefixEnd_766516 := by exact prefixLift 766516
  have htrace : WordTrace (prefixWord ++ tailWord_766516) baseStart_766516 baseEnd_766516 := by
    simpa [prefixWord, tailWord_766516, baseEnd_766516] using wordTrace_append hprefix tailTrace_766516
  have hstable : (prefixWord ++ tailWord_766516).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_766516).length < 2 ^ (prefixWord ++ tailWord_766516).sum := by decide
  have hdescent : baseEnd_766516 < baseStart_766516 := by decide
  rcases family_descends (prefixWord ++ tailWord_766516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_766561 : List Nat := [1, 2, 3, 1, 1, 5, 3, 2, 1, 3]
def baseStart_766561 : Nat := 118140960795 + 766561 * 2 ^ 59
def prefixEnd_766561 : Nat := 4983230072969 + 3 ^ 40 * 766561 * 2
def baseEnd_766561 : Nat := 262409495994187040174771

theorem tailTrace_766561 : CollatzResearch.WordTrace tailWord_766561 prefixEnd_766561 262409495994187040174771 := by
  unfold tailWord_766561
  simp only [CollatzResearch.WordTrace]
  refine ⟨27958776575887890040979537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18639184383925260027319691 27958776575887890040979537)
  ·
    refine ⟨20969082431915917530734653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27958776575887890040979537 20969082431915917530734653)
    ·
      refine ⟨7863405911968469074025495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20969082431915917530734653 7863405911968469074025495)
      ·
        refine ⟨11795108867952703611038243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7863405911968469074025495 11795108867952703611038243)
        ·
          refine ⟨17692663301929055416557365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11795108867952703611038243 17692663301929055416557365)
          ·
            refine ⟨1658687184555848945302253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 17692663301929055416557365 1658687184555848945302253)
            ·
              refine ⟨622007694208443354488345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1658687184555848945302253 622007694208443354488345)
              ·
                refine ⟨466505770656332515866259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 622007694208443354488345 466505770656332515866259)
                ·
                  refine ⟨699758655984498773799389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 466505770656332515866259 699758655984498773799389)
                  ·
                    refine ⟨262409495994187040174771, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 699758655984498773799389 262409495994187040174771)
                    ·
                      rfl

theorem cell22_766561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 5, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 5, 3, 2, 1, 3].length) (baseStart_766561 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_766561 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_766561 prefixEnd_766561 := by exact prefixLift 766561
  have htrace : WordTrace (prefixWord ++ tailWord_766561) baseStart_766561 baseEnd_766561 := by
    simpa [prefixWord, tailWord_766561, baseEnd_766561] using wordTrace_append hprefix tailTrace_766561
  have hstable : (prefixWord ++ tailWord_766561).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_766561).length < 2 ^ (prefixWord ++ tailWord_766561).sum := by decide
  have hdescent : baseEnd_766561 < baseStart_766561 := by decide
  rcases family_descends (prefixWord ++ tailWord_766561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_766574 : List Nat := [4, 1, 2, 2, 2, 1, 4, 1, 5]
def baseStart_766574 : Nat := 118140960795 + 766574 * 2 ^ 59
def prefixEnd_766574 : Nat := 4983230072969 + 3 ^ 40 * 766574 * 2
def baseEnd_766574 : Nat := 87471315386619779866577

theorem tailTrace_766574 : CollatzResearch.WordTrace tailWord_766574 prefixEnd_766574 87471315386619779866577 := by
  unfold tailWord_766574
  simp only [CollatzResearch.WordTrace]
  refine ⟨3494906340605099157650347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 18639500483227195507468517 3494906340605099157650347)
  ·
    refine ⟨5242359510907648736475521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3494906340605099157650347 5242359510907648736475521)
    ·
      refine ⟨3931769633180736552356641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5242359510907648736475521 3931769633180736552356641)
      ·
        refine ⟨2948827224885552414267481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3931769633180736552356641 2948827224885552414267481)
        ·
          refine ⟨2211620418664164310700611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2948827224885552414267481 2211620418664164310700611)
          ·
            refine ⟨3317430627996246466050917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2211620418664164310700611 3317430627996246466050917)
            ·
              refine ⟨622018242749296212384547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3317430627996246466050917 622018242749296212384547)
              ·
                refine ⟨933027364123944318576821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 622018242749296212384547 933027364123944318576821)
                ·
                  refine ⟨87471315386619779866577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 933027364123944318576821 87471315386619779866577)
                  ·
                    rfl

theorem cell22_766574_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 1, 4, 1, 5].length) (baseStart_766574 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_766574 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_766574 prefixEnd_766574 := by exact prefixLift 766574
  have htrace : WordTrace (prefixWord ++ tailWord_766574) baseStart_766574 baseEnd_766574 := by
    simpa [prefixWord, tailWord_766574, baseEnd_766574] using wordTrace_append hprefix tailTrace_766574
  have hstable : (prefixWord ++ tailWord_766574).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_766574).length < 2 ^ (prefixWord ++ tailWord_766574).sum := by decide
  have hdescent : baseEnd_766574 < baseStart_766574 := by decide
  rcases family_descends (prefixWord ++ tailWord_766574) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_766679 : List Nat := [1, 1, 3, 2, 1, 5, 2, 1, 3, 3]
def baseStart_766679 : Nat := 118140960795 + 766679 * 2 ^ 59
def prefixEnd_766679 : Nat := 4983230072969 + 3 ^ 40 * 766679 * 2
def baseEnd_766679 : Nat := 262449889805674065724409

theorem tailTrace_766679 : CollatzResearch.WordTrace tailWord_766679 prefixEnd_766679 262449889805674065724409 := by
  unfold tailWord_766679
  simp only [CollatzResearch.WordTrace]
  refine ⟨27963080389460396193775091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18642053592973597462516727 27963080389460396193775091)
  ·
    refine ⟨41944620584190594290662637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27963080389460396193775091 41944620584190594290662637)
    ·
      refine ⟨15729232719071472858998489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 41944620584190594290662637 15729232719071472858998489)
      ·
        refine ⟨11796924539303604644248867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15729232719071472858998489 11796924539303604644248867)
        ·
          refine ⟨17695386808955406966373301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11796924539303604644248867 17695386808955406966373301)
          ·
            refine ⟨1658942513339569403097497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 17695386808955406966373301 1658942513339569403097497)
            ·
              refine ⟨1244206885004677052323123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1658942513339569403097497 1244206885004677052323123)
              ·
                refine ⟨1866310327507015578484685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1244206885004677052323123 1866310327507015578484685)
                ·
                  refine ⟨699866372815130841931757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1866310327507015578484685 699866372815130841931757)
                  ·
                    refine ⟨262449889805674065724409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 699866372815130841931757 262449889805674065724409)
                    ·
                      rfl

theorem cell22_766679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 5, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 5, 2, 1, 3, 3].length) (baseStart_766679 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_766679 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_766679 prefixEnd_766679 := by exact prefixLift 766679
  have htrace : WordTrace (prefixWord ++ tailWord_766679) baseStart_766679 baseEnd_766679 := by
    simpa [prefixWord, tailWord_766679, baseEnd_766679] using wordTrace_append hprefix tailTrace_766679
  have hstable : (prefixWord ++ tailWord_766679).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_766679).length < 2 ^ (prefixWord ++ tailWord_766679).sum := by decide
  have hdescent : baseEnd_766679 < baseStart_766679 := by decide
  rcases family_descends (prefixWord ++ tailWord_766679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_766737 : List Nat := [1, 2, 2, 1, 1, 3, 5, 1, 6]
def baseStart_766737 : Nat := 118140960795 + 766737 * 2 ^ 59
def prefixEnd_766737 : Nat := 4983230072969 + 3 ^ 40 * 766737 * 2
def baseEnd_766737 : Nat := 87489914796993749258077

theorem tailTrace_766737 : CollatzResearch.WordTrace tailWord_766737 prefixEnd_766737 87489914796993749258077 := by
  unfold tailWord_766737
  simp only [CollatzResearch.WordTrace]
  refine ⟨27965195823250272099386465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18643463882166848066257643 27965195823250272099386465)
  ·
    refine ⟨20973896867437704074539849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27965195823250272099386465 20973896867437704074539849)
    ·
      refine ⟨15730422650578278055904887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20973896867437704074539849 15730422650578278055904887)
      ·
        refine ⟨23595633975867417083857331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15730422650578278055904887 23595633975867417083857331)
        ·
          refine ⟨35393450963801125625785997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23595633975867417083857331 35393450963801125625785997)
          ·
            refine ⟨13272544111425422109669749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35393450963801125625785997 13272544111425422109669749)
            ·
              refine ⟨1244301010446133322781539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 13272544111425422109669749 1244301010446133322781539)
              ·
                refine ⟨1866451515669199984172309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1244301010446133322781539 1866451515669199984172309)
                ·
                  refine ⟨87489914796993749258077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1866451515669199984172309 87489914796993749258077)
                  ·
                    rfl

theorem cell22_766737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 5, 1, 6].length) (baseStart_766737 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_766737 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_766737 prefixEnd_766737 := by exact prefixLift 766737
  have htrace : WordTrace (prefixWord ++ tailWord_766737) baseStart_766737 baseEnd_766737 := by
    simpa [prefixWord, tailWord_766737, baseEnd_766737] using wordTrace_append hprefix tailTrace_766737
  have hstable : (prefixWord ++ tailWord_766737).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_766737).length < 2 ^ (prefixWord ++ tailWord_766737).sum := by decide
  have hdescent : baseEnd_766737 < baseStart_766737 := by decide
  rcases family_descends (prefixWord ++ tailWord_766737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_766743 : List Nat := [1, 1, 3, 4, 4, 1, 2, 1, 5]
def baseStart_766743 : Nat := 118140960795 + 766743 * 2 ^ 59
def prefixEnd_766743 : Nat := 4983230072969 + 3 ^ 40 * 766743 * 2
def baseEnd_766743 : Nat := 87490599437866410708071

theorem tailTrace_766743 : CollatzResearch.WordTrace tailWord_766743 prefixEnd_766743 87490599437866410708071 := by
  unfold tailWord_766743
  simp only [CollatzResearch.WordTrace]
  refine ⟨27965414661228535124104883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18643609774152356749403255 27965414661228535124104883)
  ·
    refine ⟨41948121991842802686157325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27965414661228535124104883 41948121991842802686157325)
    ·
      refine ⟨15730545746941051007308997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 41948121991842802686157325 15730545746941051007308997)
      ·
        refine ⟨2949477327551447063870437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 15730545746941051007308997 2949477327551447063870437)
        ·
          refine ⟨553026998915896324475707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2949477327551447063870437 553026998915896324475707)
          ·
            refine ⟨829540498373844486713561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 553026998915896324475707 829540498373844486713561)
            ·
              refine ⟨622155373780383365035171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 829540498373844486713561 622155373780383365035171)
              ·
                refine ⟨933233060670575047552757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 622155373780383365035171 933233060670575047552757)
                ·
                  refine ⟨87490599437866410708071, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 933233060670575047552757 87490599437866410708071)
                  ·
                    rfl

theorem cell22_766743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 4, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 4, 1, 2, 1, 5].length) (baseStart_766743 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_766743 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_766743 prefixEnd_766743 := by exact prefixLift 766743
  have htrace : WordTrace (prefixWord ++ tailWord_766743) baseStart_766743 baseEnd_766743 := by
    simpa [prefixWord, tailWord_766743, baseEnd_766743] using wordTrace_append hprefix tailTrace_766743
  have hstable : (prefixWord ++ tailWord_766743).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_766743).length < 2 ^ (prefixWord ++ tailWord_766743).sum := by decide
  have hdescent : baseEnd_766743 < baseStart_766743 := by decide
  rcases family_descends (prefixWord ++ tailWord_766743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_766782 : List Nat := [4, 2, 1, 2, 13]
def baseStart_766782 : Nat := 118140960795 + 766782 * 2 ^ 59
def prefixEnd_766782 : Nat := 4983230072969 + 3 ^ 40 * 766782 * 2
def baseEnd_766782 : Nat := 1080185797574551976951

theorem tailTrace_766782 : CollatzResearch.WordTrace tailWord_766782 prefixEnd_766782 1080185797574551976951 := by
  unfold tailWord_766782
  simp only [CollatzResearch.WordTrace]
  refine ⟨3495854638510905598096825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 18644558072058163189849733 3495854638510905598096825)
  ·
    refine ⟨2621890978883179198572619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3495854638510905598096825 2621890978883179198572619)
    ·
      refine ⟨3932836468324768797858929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2621890978883179198572619 3932836468324768797858929)
      ·
        refine ⟨2949627351243576598394197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3932836468324768797858929 2949627351243576598394197)
        ·
          refine ⟨1080185797574551976951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 13 2949627351243576598394197 1080185797574551976951)
          ·
            rfl

theorem cell22_766782_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 13].length) (baseStart_766782 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_766782 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_766782 prefixEnd_766782 := by exact prefixLift 766782
  have htrace : WordTrace (prefixWord ++ tailWord_766782) baseStart_766782 baseEnd_766782 := by
    simpa [prefixWord, tailWord_766782, baseEnd_766782] using wordTrace_append hprefix tailTrace_766782
  have hstable : (prefixWord ++ tailWord_766782).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_766782).length < 2 ^ (prefixWord ++ tailWord_766782).sum := by decide
  have hdescent : baseEnd_766782 < baseStart_766782 := by decide
  rcases family_descends (prefixWord ++ tailWord_766782) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_766818 : List Nat := [3, 3, 2, 1, 3, 2, 1, 1, 2, 4]
def baseStart_766818 : Nat := 118140960795 + 766818 * 2 ^ 59
def prefixEnd_766818 : Nat := 4983230072969 + 3 ^ 40 * 766818 * 2
def baseEnd_766818 : Nat := 262497472346324036498983

theorem tailTrace_766818 : CollatzResearch.WordTrace tailWord_766818 prefixEnd_766818 262497472346324036498983 := by
  unfold tailWord_766818
  simp only [CollatzResearch.WordTrace]
  refine ⟨6992037533989205733271277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18645433423971215288723405 6992037533989205733271277)
  ·
    refine ⟨2622014075245952149976729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6992037533989205733271277 2622014075245952149976729)
    ·
      refine ⟨1966510556434464112482547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2622014075245952149976729 1966510556434464112482547)
      ·
        refine ⟨2949765834651696168723821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1966510556434464112482547 2949765834651696168723821)
        ·
          refine ⟨1106162187994386063271433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2949765834651696168723821 1106162187994386063271433)
          ·
            refine ⟨829621640995789547453575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1106162187994386063271433 829621640995789547453575)
            ·
              refine ⟨1244432461493684321180363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 829621640995789547453575 1244432461493684321180363)
              ·
                refine ⟨1866648692240526481770545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1244432461493684321180363 1866648692240526481770545)
                ·
                  refine ⟨1399986519180394861327909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1866648692240526481770545 1399986519180394861327909)
                  ·
                    refine ⟨262497472346324036498983, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1399986519180394861327909 262497472346324036498983)
                    ·
                      rfl

theorem cell22_766818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 3, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 3, 2, 1, 1, 2, 4].length) (baseStart_766818 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_766818 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_766818 prefixEnd_766818 := by exact prefixLift 766818
  have htrace : WordTrace (prefixWord ++ tailWord_766818) baseStart_766818 baseEnd_766818 := by
    simpa [prefixWord, tailWord_766818, baseEnd_766818] using wordTrace_append hprefix tailTrace_766818
  have hstable : (prefixWord ++ tailWord_766818).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_766818).length < 2 ^ (prefixWord ++ tailWord_766818).sum := by decide
  have hdescent : baseEnd_766818 < baseStart_766818 := by decide
  rcases family_descends (prefixWord ++ tailWord_766818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_766936 : List Nat := [2, 1, 2, 2, 2, 4, 2, 1, 2, 4]
def baseStart_766936 : Nat := 118140960795 + 766936 * 2 ^ 59
def prefixEnd_766936 : Nat := 4983230072969 + 3 ^ 40 * 766936 * 2
def baseEnd_766936 : Nat := 262537866157811062048621

theorem tailTrace_766936 : CollatzResearch.WordTrace tailWord_766936 prefixEnd_766936 262537866157811062048621 := by
  unfold tailWord_766936
  simp only [CollatzResearch.WordTrace]
  refine ⟨13986226974764664542940331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18648302633019552723920441 13986226974764664542940331)
  ·
    refine ⟨20979340462146996814410497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13986226974764664542940331 20979340462146996814410497)
    ·
      refine ⟨15734505346610247610807873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20979340462146996814410497 15734505346610247610807873)
      ·
        refine ⟨11800879009957685708105905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15734505346610247610807873 11800879009957685708105905)
        ·
          refine ⟨8850659257468264281079429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11800879009957685708105905 8850659257468264281079429)
          ·
            refine ⟨1659498610775299552702393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8850659257468264281079429 1659498610775299552702393)
            ·
              refine ⟨1244623958081474664526795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1659498610775299552702393 1244623958081474664526795)
              ·
                refine ⟨1866935937122211996790193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1244623958081474664526795 1866935937122211996790193)
                ·
                  refine ⟨1400201952841658997592645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1866935937122211996790193 1400201952841658997592645)
                  ·
                    refine ⟨262537866157811062048621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1400201952841658997592645 262537866157811062048621)
                    ·
                      rfl

theorem cell22_766936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 4, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 4, 2, 1, 2, 4].length) (baseStart_766936 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_766936 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_766936 prefixEnd_766936 := by exact prefixLift 766936
  have htrace : WordTrace (prefixWord ++ tailWord_766936) baseStart_766936 baseEnd_766936 := by
    simpa [prefixWord, tailWord_766936, baseEnd_766936] using wordTrace_append hprefix tailTrace_766936
  have hstable : (prefixWord ++ tailWord_766936).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_766936).length < 2 ^ (prefixWord ++ tailWord_766936).sum := by decide
  have hdescent : baseEnd_766936 < baseStart_766936 := by decide
  rcases family_descends (prefixWord ++ tailWord_766936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_767000 : List Nat := [2, 1, 2, 3, 2, 3, 2, 3, 1, 3]
def baseStart_767000 : Nat := 118140960795 + 767000 * 2 ^ 59
def prefixEnd_767000 : Nat := 4983230072969 + 3 ^ 40 * 767000 * 2
def baseEnd_767000 : Nat := 262559774665736228448425

theorem tailTrace_767000 : CollatzResearch.WordTrace tailWord_767000 prefixEnd_767000 262559774665736228448425 := by
  unfold tailWord_767000
  simp only [CollatzResearch.WordTrace]
  refine ⟨13987394110648734008105227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18649858814198312010806969 13987394110648734008105227)
  ·
    refine ⟨20981091165973101012157841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13987394110648734008105227 20981091165973101012157841)
    ·
      refine ⟨15735818374479825759118381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20981091165973101012157841 15735818374479825759118381)
      ·
        refine ⟨5900931890429934659669393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15735818374479825759118381 5900931890429934659669393)
        ·
          refine ⟨4425698917822450994752045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5900931890429934659669393 4425698917822450994752045)
          ·
            refine ⟨1659637094183419123032017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4425698917822450994752045 1659637094183419123032017)
            ·
              refine ⟨1244727820637564342274013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1659637094183419123032017 1244727820637564342274013)
              ·
                refine ⟨466772932739086628352755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1244727820637564342274013 466772932739086628352755)
                ·
                  refine ⟨700159399108629942529133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 466772932739086628352755 700159399108629942529133)
                  ·
                    refine ⟨262559774665736228448425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 700159399108629942529133 262559774665736228448425)
                    ·
                      rfl

theorem cell22_767000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 3, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 3, 2, 3, 1, 3].length) (baseStart_767000 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_767000 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_767000 prefixEnd_767000 := by exact prefixLift 767000
  have htrace : WordTrace (prefixWord ++ tailWord_767000) baseStart_767000 baseEnd_767000 := by
    simpa [prefixWord, tailWord_767000, baseEnd_767000] using wordTrace_append hprefix tailTrace_767000
  have hstable : (prefixWord ++ tailWord_767000).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_767000).length < 2 ^ (prefixWord ++ tailWord_767000).sum := by decide
  have hdescent : baseEnd_767000 < baseStart_767000 := by decide
  rcases family_descends (prefixWord ++ tailWord_767000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_767028 : List Nat := [2, 5, 1, 2, 1, 1, 2, 1, 2, 5]
def baseStart_767028 : Nat := 118140960795 + 767028 * 2 ^ 59
def prefixEnd_767028 : Nat := 4983230072969 + 3 ^ 40 * 767028 * 2
def baseEnd_767028 : Nat := 262569359637953488748339

theorem tailTrace_767028 : CollatzResearch.WordTrace tailWord_767028 prefixEnd_767028 262569359637953488748339 := by
  unfold tailWord_767028
  simp only [CollatzResearch.WordTrace]
  refine ⟨13987904732598014399114869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18650539643464019198819825 13987904732598014399114869)
  ·
    refine ⟨1311366068681063849917019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 13987904732598014399114869 1311366068681063849917019)
    ·
      refine ⟨1967049103021595774875529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1311366068681063849917019 1967049103021595774875529)
      ·
        refine ⟨1475286827266196831156647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1967049103021595774875529 1475286827266196831156647)
        ·
          refine ⟨2212930240899295246734971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1475286827266196831156647 2212930240899295246734971)
          ·
            refine ⟨3319395361348942870102457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2212930240899295246734971 3319395361348942870102457)
            ·
              refine ⟨2489546521011707152576843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3319395361348942870102457 2489546521011707152576843)
              ·
                refine ⟨3734319781517560728865265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2489546521011707152576843 3734319781517560728865265)
                ·
                  refine ⟨2800739836138170546648949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3734319781517560728865265 2800739836138170546648949)
                  ·
                    refine ⟨262569359637953488748339, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2800739836138170546648949 262569359637953488748339)
                    ·
                      rfl

theorem cell22_767028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 1, 2, 1, 2, 5].length) (baseStart_767028 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_767028 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_767028 prefixEnd_767028 := by exact prefixLift 767028
  have htrace : WordTrace (prefixWord ++ tailWord_767028) baseStart_767028 baseEnd_767028 := by
    simpa [prefixWord, tailWord_767028, baseEnd_767028] using wordTrace_append hprefix tailTrace_767028
  have hstable : (prefixWord ++ tailWord_767028).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_767028).length < 2 ^ (prefixWord ++ tailWord_767028).sum := by decide
  have hdescent : baseEnd_767028 < baseStart_767028 := by decide
  rcases family_descends (prefixWord ++ tailWord_767028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_767030 : List Nat := [5, 1, 2, 1, 1, 3, 3, 1, 5]
def baseStart_767030 : Nat := 118140960795 + 767030 * 2 ^ 59
def prefixEnd_767030 : Nat := 4983230072969 + 3 ^ 40 * 767030 * 2
def baseEnd_767030 : Nat := 87523348092942050066111

theorem tailTrace_767030 : CollatzResearch.WordTrace tailWord_767030 prefixEnd_767030 87523348092942050066111 := by
  unfold tailWord_767030
  simp only [CollatzResearch.WordTrace]
  refine ⟨1748492650699298946237659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 18650588274125855426535029 1748492650699298946237659)
  ·
    refine ⟨2622738976048948419356489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1748492650699298946237659 2622738976048948419356489)
    ·
      refine ⟨1967054232036711314517367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2622738976048948419356489 1967054232036711314517367)
      ·
        refine ⟨2950581348055066971776051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1967054232036711314517367 2950581348055066971776051)
        ·
          refine ⟨4425872022082600457664077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2950581348055066971776051 4425872022082600457664077)
          ·
            refine ⟨1659702008280975171624029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4425872022082600457664077 1659702008280975171624029)
            ·
              refine ⟨622388253105365689359011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1659702008280975171624029 622388253105365689359011)
              ·
                refine ⟨933582379658048534038517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 622388253105365689359011 933582379658048534038517)
                ·
                  refine ⟨87523348092942050066111, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 933582379658048534038517 87523348092942050066111)
                  ·
                    rfl

theorem cell22_767030_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 3, 3, 1, 5].length) (baseStart_767030 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_767030 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_767030 prefixEnd_767030 := by exact prefixLift 767030
  have htrace : WordTrace (prefixWord ++ tailWord_767030) baseStart_767030 baseEnd_767030 := by
    simpa [prefixWord, tailWord_767030, baseEnd_767030] using wordTrace_append hprefix tailTrace_767030
  have hstable : (prefixWord ++ tailWord_767030).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_767030).length < 2 ^ (prefixWord ++ tailWord_767030).sum := by decide
  have hdescent : baseEnd_767030 < baseStart_767030 := by decide
  rcases family_descends (prefixWord ++ tailWord_767030) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_767071 : List Nat := [1, 1, 2, 3, 1, 1, 5, 2, 2, 4]
def baseStart_767071 : Nat := 118140960795 + 767071 * 2 ^ 59
def prefixEnd_767071 : Nat := 4983230072969 + 3 ^ 40 * 767071 * 2
def baseEnd_767071 : Nat := 262584079416715709923207

theorem tailTrace_767071 : CollatzResearch.WordTrace tailWord_767071 prefixEnd_767071 262584079416715709923207 := by
  unfold tailWord_767071
  simp only [CollatzResearch.WordTrace]
  refine ⟨27977377804040247142045067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18651585202693498094696711 27977377804040247142045067)
  ·
    refine ⟨41966066706060370713067601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27977377804040247142045067 41966066706060370713067601)
    ·
      refine ⟨31474550029545278034800701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41966066706060370713067601 31474550029545278034800701)
      ·
        refine ⟨11802956261079479263050263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31474550029545278034800701 11802956261079479263050263)
        ·
          refine ⟨17704434391619218894575395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11802956261079479263050263 17704434391619218894575395)
          ·
            refine ⟨26556651587428828341863093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17704434391619218894575395 26556651587428828341863093)
            ·
              refine ⟨2489686086321452657049665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 26556651587428828341863093 2489686086321452657049665)
              ·
                refine ⟨1867264564741089492787249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2489686086321452657049665 1867264564741089492787249)
                ·
                  refine ⟨1400448423555817119590437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1867264564741089492787249 1400448423555817119590437)
                  ·
                    refine ⟨262584079416715709923207, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1400448423555817119590437 262584079416715709923207)
                    ·
                      rfl

theorem cell22_767071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 5, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 5, 2, 2, 4].length) (baseStart_767071 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_767071 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_767071 prefixEnd_767071 := by exact prefixLift 767071
  have htrace : WordTrace (prefixWord ++ tailWord_767071) baseStart_767071 baseEnd_767071 := by
    simpa [prefixWord, tailWord_767071, baseEnd_767071] using wordTrace_append hprefix tailTrace_767071
  have hstable : (prefixWord ++ tailWord_767071).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_767071).length < 2 ^ (prefixWord ++ tailWord_767071).sum := by decide
  have hdescent : baseEnd_767071 < baseStart_767071 := by decide
  rcases family_descends (prefixWord ++ tailWord_767071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_767086 : List Nat := [4, 1, 2, 2, 1, 2, 1, 9]
def baseStart_767086 : Nat := 118140960795 + 767086 * 2 ^ 59
def prefixEnd_767086 : Nat := 4983230072969 + 3 ^ 40 * 767086 * 2
def baseEnd_767086 : Nat := 29176579358140074533129

theorem tailTrace_767086 : CollatzResearch.WordTrace tailWord_767086 prefixEnd_767086 29176579358140074533129 := by
  unfold tailWord_767086
  simp only [CollatzResearch.WordTrace]
  refine ⟨3497240612373238087980139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 18651949932657269802560741 3497240612373238087980139)
  ·
    refine ⟨5245860918559857131970209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3497240612373238087980139 5245860918559857131970209)
    ·
      refine ⟨3934395688919892848977657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5245860918559857131970209 3934395688919892848977657)
      ·
        refine ⟨2950796766689919636733243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3934395688919892848977657 2950796766689919636733243)
        ·
          refine ⟨4426195150034879455099865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2950796766689919636733243 4426195150034879455099865)
          ·
            refine ⟨3319646362526159591324899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4426195150034879455099865 3319646362526159591324899)
            ·
              refine ⟨4979469543789239386987349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3319646362526159591324899 4979469543789239386987349)
              ·
                refine ⟨29176579358140074533129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 4979469543789239386987349 29176579358140074533129)
                ·
                  rfl

theorem cell22_767086_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 2, 1, 9].length) (baseStart_767086 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_767086 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_767086 prefixEnd_767086 := by exact prefixLift 767086
  have htrace : WordTrace (prefixWord ++ tailWord_767086) baseStart_767086 baseEnd_767086 := by
    simpa [prefixWord, tailWord_767086, baseEnd_767086] using wordTrace_append hprefix tailTrace_767086
  have hstable : (prefixWord ++ tailWord_767086).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_767086).length < 2 ^ (prefixWord ++ tailWord_767086).sum := by decide
  have hdescent : baseEnd_767086 < baseStart_767086 := by decide
  rcases family_descends (prefixWord ++ tailWord_767086) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_767169 : List Nat := [1, 2, 6, 1, 1, 2, 2, 3, 1, 3]
def baseStart_767169 : Nat := 118140960795 + 767169 * 2 ^ 59
def prefixEnd_767169 : Nat := 4983230072969 + 3 ^ 40 * 767169 * 2
def baseEnd_767169 : Nat := 262617626819476120972907

theorem tailTrace_767169 : CollatzResearch.WordTrace tailWord_767169 prefixEnd_767169 262617626819476120972907 := by
  unfold tailWord_767169
  simp only [CollatzResearch.WordTrace]
  refine ⟨27980952157685209879112561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18653968105123473252741707 27980952157685209879112561)
  ·
    refine ⟨20985714118263907409334421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27980952157685209879112561 20985714118263907409334421)
    ·
      refine ⟨983705349293620659812551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 20985714118263907409334421 983705349293620659812551)
      ·
        refine ⟨1475558023940430989718827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 983705349293620659812551 1475558023940430989718827)
        ·
          refine ⟨2213337035910646484578241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1475558023940430989718827 2213337035910646484578241)
          ·
            refine ⟨1660002776932984863433681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2213337035910646484578241 1660002776932984863433681)
            ·
              refine ⟨1245002082699738647575261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1660002776932984863433681 1245002082699738647575261)
              ·
                refine ⟨466875781012401992840723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1245002082699738647575261 466875781012401992840723)
                ·
                  refine ⟨700313671518602989261085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 466875781012401992840723 700313671518602989261085)
                  ·
                    refine ⟨262617626819476120972907, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 700313671518602989261085 262617626819476120972907)
                    ·
                      rfl

theorem cell22_767169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 2, 2, 3, 1, 3].length) (baseStart_767169 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_767169 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_767169 prefixEnd_767169 := by exact prefixLift 767169
  have htrace : WordTrace (prefixWord ++ tailWord_767169) baseStart_767169 baseEnd_767169 := by
    simpa [prefixWord, tailWord_767169, baseEnd_767169] using wordTrace_append hprefix tailTrace_767169
  have hstable : (prefixWord ++ tailWord_767169).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_767169).length < 2 ^ (prefixWord ++ tailWord_767169).sum := by decide
  have hdescent : baseEnd_767169 < baseStart_767169 := by decide
  rcases family_descends (prefixWord ++ tailWord_767169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_767182 : List Nat := [4, 1, 1, 1, 6, 1, 1, 2, 5]
def baseStart_767182 : Nat := 118140960795 + 767182 * 2 ^ 59
def prefixEnd_767182 : Nat := 4983230072969 + 3 ^ 40 * 767182 * 2
def baseEnd_767182 : Nat := 87540692328382806799289

theorem tailTrace_767182 : CollatzResearch.WordTrace tailWord_767182 prefixEnd_767182 87540692328382806799289 := by
  unfold tailWord_767182
  simp only [CollatzResearch.WordTrace]
  refine ⟨3497678288329764137416975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 18654284204425408732890533 3497678288329764137416975)
  ·
    refine ⟨5246517432494646206125463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3497678288329764137416975 5246517432494646206125463)
    ·
      refine ⟨7869776148741969309188195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5246517432494646206125463 7869776148741969309188195)
      ·
        refine ⟨11804664223112953963782293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7869776148741969309188195 11804664223112953963782293)
        ·
          refine ⟨553343635458419717052295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 11804664223112953963782293 553343635458419717052295)
          ·
            refine ⟨830015453187629575578443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 553343635458419717052295 830015453187629575578443)
            ·
              refine ⟨1245023179781444363367665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 830015453187629575578443 1245023179781444363367665)
              ·
                refine ⟨933767384836083272525749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1245023179781444363367665 933767384836083272525749)
                ·
                  refine ⟨87540692328382806799289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 933767384836083272525749 87540692328382806799289)
                  ·
                    rfl

theorem cell22_767182_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 6, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 6, 1, 1, 2, 5].length) (baseStart_767182 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_767182 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_767182 prefixEnd_767182 := by exact prefixLift 767182
  have htrace : WordTrace (prefixWord ++ tailWord_767182) baseStart_767182 baseEnd_767182 := by
    simpa [prefixWord, tailWord_767182, baseEnd_767182] using wordTrace_append hprefix tailTrace_767182
  have hstable : (prefixWord ++ tailWord_767182).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_767182).length < 2 ^ (prefixWord ++ tailWord_767182).sum := by decide
  have hdescent : baseEnd_767182 < baseStart_767182 := by decide
  rcases family_descends (prefixWord ++ tailWord_767182) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_767191 : List Nat := [1, 1, 3, 2, 1, 2, 2, 2, 3, 5]
def baseStart_767191 : Nat := 118140960795 + 767191 * 2 ^ 59
def prefixEnd_767191 : Nat := 4983230072969 + 3 ^ 40 * 767191 * 2
def baseEnd_767191 : Nat := 262625157869075396922839

theorem tailTrace_767191 : CollatzResearch.WordTrace tailWord_767191 prefixEnd_767191 262625157869075396922839 := by
  unfold tailWord_767191
  simp only [CollatzResearch.WordTrace]
  refine ⟨27981754563605507636413427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18654503042403671757608951 27981754563605507636413427)
  ·
    refine ⟨41972631845408261454620141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27981754563605507636413427 41972631845408261454620141)
    ·
      refine ⟨15739736942028098045482553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 41972631845408261454620141 15739736942028098045482553)
      ·
        refine ⟨11804802706521073534111915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15739736942028098045482553 11804802706521073534111915)
        ·
          refine ⟨17707204059781610301167873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11804802706521073534111915 17707204059781610301167873)
          ·
            refine ⟨13280403044836207725875905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17707204059781610301167873 13280403044836207725875905)
            ·
              refine ⟨9960302283627155794406929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13280403044836207725875905 9960302283627155794406929)
              ·
                refine ⟨7470226712720366845805197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9960302283627155794406929 7470226712720366845805197)
                ·
                  refine ⟨2801335017270137567176949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7470226712720366845805197 2801335017270137567176949)
                  ·
                    refine ⟨262625157869075396922839, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2801335017270137567176949 262625157869075396922839)
                    ·
                      rfl

theorem cell22_767191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 2, 2, 3, 5].length) (baseStart_767191 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_767191 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_767191 prefixEnd_767191 := by exact prefixLift 767191
  have htrace : WordTrace (prefixWord ++ tailWord_767191) baseStart_767191 baseEnd_767191 := by
    simpa [prefixWord, tailWord_767191, baseEnd_767191] using wordTrace_append hprefix tailTrace_767191
  have hstable : (prefixWord ++ tailWord_767191).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_767191).length < 2 ^ (prefixWord ++ tailWord_767191).sum := by decide
  have hdescent : baseEnd_767191 < baseStart_767191 := by decide
  rcases family_descends (prefixWord ++ tailWord_767191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_767220 : List Nat := [2, 6, 1, 2, 2, 1, 1, 3, 1, 3]
def baseStart_767220 : Nat := 118140960795 + 767220 * 2 ^ 59
def prefixEnd_767220 : Nat := 4983230072969 + 3 ^ 40 * 767220 * 2
def baseEnd_767220 : Nat := 262635085161728987947751

theorem tailTrace_767220 : CollatzResearch.WordTrace tailWord_767220 prefixEnd_767220 262635085161728987947751 := by
  unfold tailWord_767220
  simp only [CollatzResearch.WordTrace]
  refine ⟨13991406140250222794609557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18655208187000297059479409 13991406140250222794609557)
  ·
    refine ⟨655847162824229193497323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 13991406140250222794609557 655847162824229193497323)
    ·
      refine ⟨983770744236343790245985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 655847162824229193497323 983770744236343790245985)
      ·
        refine ⟨737828058177257842684489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 983770744236343790245985 737828058177257842684489)
        ·
          refine ⟨553371043632943382013367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 737828058177257842684489 553371043632943382013367)
          ·
            refine ⟨830056565449415073020051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 553371043632943382013367 830056565449415073020051)
            ·
              refine ⟨1245084848174122609530077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 830056565449415073020051 1245084848174122609530077)
              ·
                refine ⟨466906818065295978573779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1245084848174122609530077 466906818065295978573779)
                ·
                  refine ⟨700360227097943967860669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 466906818065295978573779 700360227097943967860669)
                  ·
                    refine ⟨262635085161728987947751, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 700360227097943967860669 262635085161728987947751)
                    ·
                      rfl

theorem cell22_767220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 2, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 2, 1, 1, 3, 1, 3].length) (baseStart_767220 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_767220 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_767220 prefixEnd_767220 := by exact prefixLift 767220
  have htrace : WordTrace (prefixWord ++ tailWord_767220) baseStart_767220 baseEnd_767220 := by
    simpa [prefixWord, tailWord_767220, baseEnd_767220] using wordTrace_append hprefix tailTrace_767220
  have hstable : (prefixWord ++ tailWord_767220).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_767220).length < 2 ^ (prefixWord ++ tailWord_767220).sum := by decide
  have hdescent : baseEnd_767220 < baseStart_767220 := by decide
  rcases family_descends (prefixWord ++ tailWord_767220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_767240 : List Nat := [2, 1, 3, 2, 4, 1, 1, 2, 2, 4]
def baseStart_767240 : Nat := 118140960795 + 767240 * 2 ^ 59
def prefixEnd_767240 : Nat := 4983230072969 + 3 ^ 40 * 767240 * 2
def baseEnd_767240 : Nat := 262641931570455602447689

theorem tailTrace_767240 : CollatzResearch.WordTrace tailWord_767240 prefixEnd_767240 262641931570455602447689 := by
  unfold tailWord_767240
  simp only [CollatzResearch.WordTrace]
  refine ⟨13991770870213994502473587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18655694493618659336631449 13991770870213994502473587)
  ·
    refine ⟨20987656305320991753710381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13991770870213994502473587 20987656305320991753710381)
    ·
      refine ⟨7870371114495371907641393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20987656305320991753710381 7870371114495371907641393)
      ·
        refine ⟨5902778335871528930731045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7870371114495371907641393 5902778335871528930731045)
        ·
          refine ⟨1106770937975911674512071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5902778335871528930731045 1106770937975911674512071)
          ·
            refine ⟨1660156406963867511768107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1106770937975911674512071 1660156406963867511768107)
            ·
              refine ⟨2490234610445801267652161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1660156406963867511768107 2490234610445801267652161)
              ·
                refine ⟨1867675957834350950739121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2490234610445801267652161 1867675957834350950739121)
                ·
                  refine ⟨1400756968375763213054341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1867675957834350950739121 1400756968375763213054341)
                  ·
                    refine ⟨262641931570455602447689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1400756968375763213054341 262641931570455602447689)
                    ·
                      rfl

theorem cell22_767240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 4, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 4, 1, 1, 2, 2, 4].length) (baseStart_767240 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_767240 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_767240 prefixEnd_767240 := by exact prefixLift 767240
  have htrace : WordTrace (prefixWord ++ tailWord_767240) baseStart_767240 baseEnd_767240 := by
    simpa [prefixWord, tailWord_767240, baseEnd_767240] using wordTrace_append hprefix tailTrace_767240
  have hstable : (prefixWord ++ tailWord_767240).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_767240).length < 2 ^ (prefixWord ++ tailWord_767240).sum := by decide
  have hdescent : baseEnd_767240 < baseStart_767240 := by decide
  rcases family_descends (prefixWord ++ tailWord_767240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_767313 : List Nat := [1, 2, 2, 1, 4, 1, 1, 1, 5, 4]
def baseStart_767313 : Nat := 118140960795 + 767313 * 2 ^ 59
def prefixEnd_767313 : Nat := 4983230072969 + 3 ^ 40 * 767313 * 2
def baseEnd_767313 : Nat := 262666920962307745372465

theorem tailTrace_767313 : CollatzResearch.WordTrace tailWord_767313 prefixEnd_767313 262666920962307745372465 := by
  unfold tailWord_767313
  simp only [CollatzResearch.WordTrace]
  refine ⟨27986204269163522472354593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18657469512775681648236395 27986204269163522472354593)
  ·
    refine ⟨20989653201872641854265945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27986204269163522472354593 20989653201872641854265945)
    ·
      refine ⟨15742239901404481390699459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20989653201872641854265945 15742239901404481390699459)
      ·
        refine ⟨23613359852106722086049189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15742239901404481390699459 23613359852106722086049189)
        ·
          refine ⟨4427504972270010391134223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 23613359852106722086049189 4427504972270010391134223)
          ·
            refine ⟨6641257458405015586701335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4427504972270010391134223 6641257458405015586701335)
            ·
              refine ⟨9961886187607523380052003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6641257458405015586701335 9961886187607523380052003)
              ·
                refine ⟨14942829281411285070078005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9961886187607523380052003 14942829281411285070078005)
                ·
                  refine ⟨1400890245132307975319813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 14942829281411285070078005 1400890245132307975319813)
                  ·
                    refine ⟨262666920962307745372465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1400890245132307975319813 262666920962307745372465)
                    ·
                      rfl

theorem cell22_767313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 1, 1, 5, 4].length) (baseStart_767313 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_767313 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_767313 prefixEnd_767313 := by exact prefixLift 767313
  have htrace : WordTrace (prefixWord ++ tailWord_767313) baseStart_767313 baseEnd_767313 := by
    simpa [prefixWord, tailWord_767313, baseEnd_767313] using wordTrace_append hprefix tailTrace_767313
  have hstable : (prefixWord ++ tailWord_767313).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_767313).length < 2 ^ (prefixWord ++ tailWord_767313).sum := by decide
  have hdescent : baseEnd_767313 < baseStart_767313 := by decide
  rcases family_descends (prefixWord ++ tailWord_767313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_767328 : List Nat := [2, 1, 1, 3, 4, 1, 1, 1, 8]
def baseStart_767328 : Nat := 118140960795 + 767328 * 2 ^ 59
def prefixEnd_767328 : Nat := 4983230072969 + 3 ^ 40 * 767328 * 2
def baseEnd_767328 : Nat := 87557351922950902082473

theorem tailTrace_767328 : CollatzResearch.WordTrace tailWord_767328 prefixEnd_767328 87557351922950902082473 := by
  unfold tailWord_767328
  simp only [CollatzResearch.WordTrace]
  refine ⟨13993375682054590017075319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18657834242739453356100425 13993375682054590017075319)
  ·
    refine ⟨20990063523081885025612979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13993375682054590017075319 20990063523081885025612979)
    ·
      refine ⟨31485095284622827538419469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20990063523081885025612979 31485095284622827538419469)
      ·
        refine ⟨11806910731733560326907301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31485095284622827538419469 11806910731733560326907301)
        ·
          refine ⟨2213795762200042561295119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11806910731733560326907301 2213795762200042561295119)
          ·
            refine ⟨3320693643300063841942679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2213795762200042561295119 3320693643300063841942679)
            ·
              refine ⟨4981040464950095762914019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3320693643300063841942679 4981040464950095762914019)
              ·
                refine ⟨7471560697425143644371029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4981040464950095762914019 7471560697425143644371029)
                ·
                  refine ⟨87557351922950902082473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 7471560697425143644371029 87557351922950902082473)
                  ·
                    rfl

theorem cell22_767328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 1, 1, 1, 8].length) (baseStart_767328 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_767328 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_767328 prefixEnd_767328 := by exact prefixLift 767328
  have htrace : WordTrace (prefixWord ++ tailWord_767328) baseStart_767328 baseEnd_767328 := by
    simpa [prefixWord, tailWord_767328, baseEnd_767328] using wordTrace_append hprefix tailTrace_767328
  have hstable : (prefixWord ++ tailWord_767328).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_767328).length < 2 ^ (prefixWord ++ tailWord_767328).sum := by decide
  have hdescent : baseEnd_767328 < baseStart_767328 := by decide
  rcases family_descends (prefixWord ++ tailWord_767328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_767330 : List Nat := [3, 3, 2, 1, 1, 1, 1, 3, 3, 4]
def baseStart_767330 : Nat := 118140960795 + 767330 * 2 ^ 59
def prefixEnd_767330 : Nat := 4983230072969 + 3 ^ 40 * 767330 * 2
def baseEnd_767330 : Nat := 262672740409725367697413

theorem tailTrace_767330 : CollatzResearch.WordTrace tailWord_767330 prefixEnd_767330 262672740409725367697413 := by
  unfold tailWord_767330
  simp only [CollatzResearch.WordTrace]
  refine ⟨6996706077525483593930861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18657882873401289583815629 6996706077525483593930861)
  ·
    refine ⟨2623764779072056347724073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6996706077525483593930861 2623764779072056347724073)
    ·
      refine ⟨1967823584304042260793055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2623764779072056347724073 1967823584304042260793055)
      ·
        refine ⟨2951735376456063391189583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1967823584304042260793055 2951735376456063391189583)
        ·
          refine ⟨4427603064684095086784375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2951735376456063391189583 4427603064684095086784375)
          ·
            refine ⟨6641404597026142630176563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4427603064684095086784375 6641404597026142630176563)
            ·
              refine ⟨9962106895539213945264845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6641404597026142630176563 9962106895539213945264845)
              ·
                refine ⟨3735790085827205229474317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9962106895539213945264845 3735790085827205229474317)
                ·
                  refine ⟨1400921282185201961052869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3735790085827205229474317 1400921282185201961052869)
                  ·
                    refine ⟨262672740409725367697413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1400921282185201961052869 262672740409725367697413)
                    ·
                      rfl

theorem cell22_767330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 1, 3, 3, 4].length) (baseStart_767330 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_767330 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_767330 prefixEnd_767330 := by exact prefixLift 767330
  have htrace : WordTrace (prefixWord ++ tailWord_767330) baseStart_767330 baseEnd_767330 := by
    simpa [prefixWord, tailWord_767330, baseEnd_767330] using wordTrace_append hprefix tailTrace_767330
  have hstable : (prefixWord ++ tailWord_767330).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_767330).length < 2 ^ (prefixWord ++ tailWord_767330).sum := by decide
  have hdescent : baseEnd_767330 < baseStart_767330 := by decide
  rcases family_descends (prefixWord ++ tailWord_767330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_767343 : List Nat := [1, 1, 2, 1, 3, 1, 3, 4, 1, 5]
def baseStart_767343 : Nat := 118140960795 + 767343 * 2 ^ 59
def prefixEnd_767343 : Nat := 4983230072969 + 3 ^ 40 * 767343 * 2
def baseEnd_767343 : Nat := 262677190575397667122373

theorem tailTrace_767343 : CollatzResearch.WordTrace tailWord_767343 prefixEnd_767343 262677190575397667122373 := by
  unfold tailWord_767343
  simp only [CollatzResearch.WordTrace]
  refine ⟨27987298459054837595946683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18658198972703225063964455 27987298459054837595946683)
  ·
    refine ⟨41980947688582256393920025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27987298459054837595946683 41980947688582256393920025)
    ·
      refine ⟨31485710766436692295440019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41980947688582256393920025 31485710766436692295440019)
      ·
        refine ⟨47228566149655038443160029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31485710766436692295440019 47228566149655038443160029)
        ·
          refine ⟨17710712306120639416185011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 47228566149655038443160029 17710712306120639416185011)
          ·
            refine ⟨26566068459180959124277517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17710712306120639416185011 26566068459180959124277517)
            ·
              refine ⟨9962275672192859671604069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26566068459180959124277517 9962275672192859671604069)
              ·
                refine ⟨1867926688536161188425763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9962275672192859671604069 1867926688536161188425763)
                ·
                  refine ⟨2801890032804241782638645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1867926688536161188425763 2801890032804241782638645)
                  ·
                    refine ⟨262677190575397667122373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2801890032804241782638645 262677190575397667122373)
                    ·
                      rfl

theorem cell22_767343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 3, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 3, 4, 1, 5].length) (baseStart_767343 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_767343 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_767343 prefixEnd_767343 := by exact prefixLift 767343
  have htrace : WordTrace (prefixWord ++ tailWord_767343) baseStart_767343 baseEnd_767343 := by
    simpa [prefixWord, tailWord_767343, baseEnd_767343] using wordTrace_append hprefix tailTrace_767343
  have hstable : (prefixWord ++ tailWord_767343).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_767343).length < 2 ^ (prefixWord ++ tailWord_767343).sum := by decide
  have hdescent : baseEnd_767343 < baseStart_767343 := by decide
  rcases family_descends (prefixWord ++ tailWord_767343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_767345 : List Nat := [1, 2, 2, 2, 1, 2, 3, 5, 4]
def baseStart_767345 : Nat := 118140960795 + 767345 * 2 ^ 59
def prefixEnd_767345 : Nat := 4983230072969 + 3 ^ 40 * 767345 * 2
def baseEnd_767345 : Nat := 87559291738756776190789

theorem tailTrace_767345 : CollatzResearch.WordTrace tailWord_767345 prefixEnd_767345 87559291738756776190789 := by
  unfold tailWord_767345
  simp only [CollatzResearch.WordTrace]
  refine ⟨27987371405047591937519489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18658247603365061291679659 27987371405047591937519489)
  ·
    refine ⟨20990528553785693953139617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27987371405047591937519489 20990528553785693953139617)
    ·
      refine ⟨15742896415339270464854713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20990528553785693953139617 15742896415339270464854713)
      ·
        refine ⟨11807172311504452848641035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15742896415339270464854713 11807172311504452848641035)
        ·
          refine ⟨17710758467256679272961553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11807172311504452848641035 17710758467256679272961553)
          ·
            refine ⟨13283068850442509454721165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17710758467256679272961553 13283068850442509454721165)
            ·
              refine ⟨4981150818915941045520437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13283068850442509454721165 4981150818915941045520437)
              ·
                refine ⟨466982889273369473017541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 4981150818915941045520437 466982889273369473017541)
                ·
                  refine ⟨87559291738756776190789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 466982889273369473017541 87559291738756776190789)
                  ·
                    rfl

theorem cell22_767345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 3, 5, 4].length) (baseStart_767345 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_767345 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_767345 prefixEnd_767345 := by exact prefixLift 767345
  have htrace : WordTrace (prefixWord ++ tailWord_767345) baseStart_767345 baseEnd_767345 := by
    simpa [prefixWord, tailWord_767345, baseEnd_767345] using wordTrace_append hprefix tailTrace_767345
  have hstable : (prefixWord ++ tailWord_767345).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_767345).length < 2 ^ (prefixWord ++ tailWord_767345).sum := by decide
  have hdescent : baseEnd_767345 < baseStart_767345 := by decide
  rcases family_descends (prefixWord ++ tailWord_767345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_767362 : List Nat := [3, 4, 2, 1, 1, 1, 1, 3, 6]
def baseStart_767362 : Nat := 118140960795 + 767362 * 2 ^ 59
def prefixEnd_767362 : Nat := 4983230072969 + 3 ^ 40 * 767362 * 2
def baseEnd_767362 : Nat := 87561231554562650299105

theorem tailTrace_767362 : CollatzResearch.WordTrace tailWord_767362 prefixEnd_767362 87561231554562650299105 := by
  unfold tailWord_767362
  simp only [CollatzResearch.WordTrace]
  refine ⟨6996997861496500960222085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18658660963990669227258893 6996997861496500960222085)
  ·
    refine ⟨1311937099030593930041641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 6996997861496500960222085 1311937099030593930041641)
    ·
      refine ⟨983952824272945447531231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1311937099030593930041641 983952824272945447531231)
      ·
        refine ⟨1475929236409418171296847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 983952824272945447531231 1475929236409418171296847)
        ·
          refine ⟨2213893854614127256945271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1475929236409418171296847 2213893854614127256945271)
          ·
            refine ⟨3320840781921190885417907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2213893854614127256945271 3320840781921190885417907)
            ·
              refine ⟨4981261172881786328126861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3320840781921190885417907 4981261172881786328126861)
              ·
                refine ⟨1867972939830669873047573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4981261172881786328126861 1867972939830669873047573)
                ·
                  refine ⟨87561231554562650299105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1867972939830669873047573 87561231554562650299105)
                  ·
                    rfl

theorem cell22_767362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 1, 1, 3, 6].length) (baseStart_767362 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_767362 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_767362 prefixEnd_767362 := by exact prefixLift 767362
  have htrace : WordTrace (prefixWord ++ tailWord_767362) baseStart_767362 baseEnd_767362 := by
    simpa [prefixWord, tailWord_767362, baseEnd_767362] using wordTrace_append hprefix tailTrace_767362
  have hstable : (prefixWord ++ tailWord_767362).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_767362).length < 2 ^ (prefixWord ++ tailWord_767362).sum := by decide
  have hdescent : baseEnd_767362 < baseStart_767362 := by decide
  rcases family_descends (prefixWord ++ tailWord_767362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_767433 : List Nat := [1, 2, 1, 1, 2, 1, 3, 3, 1, 7]
def baseStart_767433 : Nat := 118140960795 + 767433 * 2 ^ 59
def prefixEnd_767433 : Nat := 4983230072969 + 3 ^ 40 * 767433 * 2
def baseEnd_767433 : Nat := 262707999414667432372097

theorem tailTrace_767433 : CollatzResearch.WordTrace tailWord_767433 prefixEnd_767433 262707999414667432372097 := by
  unfold tailWord_767433
  simp only [CollatzResearch.WordTrace]
  refine ⟨27990581028728782966722953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18660387352485855311148635 27990581028728782966722953)
  ·
    refine ⟨20992935771546587225042215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27990581028728782966722953 20992935771546587225042215)
    ·
      refine ⟨31489403657319880837563323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20992935771546587225042215 31489403657319880837563323)
      ·
        refine ⟨47234105485979821256344985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31489403657319880837563323 47234105485979821256344985)
        ·
          refine ⟨35425579114484865942258739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47234105485979821256344985 35425579114484865942258739)
          ·
            refine ⟨53138368671727298913388109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35425579114484865942258739 53138368671727298913388109)
            ·
              refine ⟨19926888251897737092520541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 53138368671727298913388109 19926888251897737092520541)
              ·
                refine ⟨7472583094461651409695203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19926888251897737092520541 7472583094461651409695203)
                ·
                  refine ⟨11208874641692477114542805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7472583094461651409695203 11208874641692477114542805)
                  ·
                    refine ⟨262707999414667432372097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 11208874641692477114542805 262707999414667432372097)
                    ·
                      rfl

theorem cell22_767433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 3, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 3, 3, 1, 7].length) (baseStart_767433 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_767433 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_767433 prefixEnd_767433 := by exact prefixLift 767433
  have htrace : WordTrace (prefixWord ++ tailWord_767433) baseStart_767433 baseEnd_767433 := by
    simpa [prefixWord, tailWord_767433, baseEnd_767433] using wordTrace_append hprefix tailTrace_767433
  have hstable : (prefixWord ++ tailWord_767433).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_767433).length < 2 ^ (prefixWord ++ tailWord_767433).sum := by decide
  have hdescent : baseEnd_767433 < baseStart_767433 := by decide
  rcases family_descends (prefixWord ++ tailWord_767433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_767469 : List Nat := [1, 5, 1, 3, 2, 1, 2, 2, 5]
def baseStart_767469 : Nat := 118140960795 + 767469 * 2 ^ 59
def prefixEnd_767469 : Nat := 4983230072969 + 3 ^ 40 * 767469 * 2
def baseEnd_767469 : Nat := 87573440983458446157329

theorem tailTrace_767469 : CollatzResearch.WordTrace tailWord_767469 prefixEnd_767469 87573440983458446157329 := by
  unfold tailWord_767469
  simp only [CollatzResearch.WordTrace]
  refine ⟨27991894056598361115033461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18661262704398907410022307 27991894056598361115033461)
  ·
    refine ⟨2624240067806096354534387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 27991894056598361115033461 2624240067806096354534387)
    ·
      refine ⟨3936360101709144531801581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2624240067806096354534387 3936360101709144531801581)
      ·
        refine ⟨1476135038140929199425593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3936360101709144531801581 1476135038140929199425593)
        ·
          refine ⟨1107101278605696899569195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1476135038140929199425593 1107101278605696899569195)
          ·
            refine ⟨1660651917908545349353793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1107101278605696899569195 1660651917908545349353793)
            ·
              refine ⟨1245488938431409012015345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1660651917908545349353793 1245488938431409012015345)
              ·
                refine ⟨934116703823556759011509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1245488938431409012015345 934116703823556759011509)
                ·
                  refine ⟨87573440983458446157329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 934116703823556759011509 87573440983458446157329)
                  ·
                    rfl

theorem cell22_767469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 2, 1, 2, 2, 5].length) (baseStart_767469 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_767469 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_767469 prefixEnd_767469 := by exact prefixLift 767469
  have htrace : WordTrace (prefixWord ++ tailWord_767469) baseStart_767469 baseEnd_767469 := by
    simpa [prefixWord, tailWord_767469, baseEnd_767469] using wordTrace_append hprefix tailTrace_767469
  have hstable : (prefixWord ++ tailWord_767469).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_767469).length < 2 ^ (prefixWord ++ tailWord_767469).sum := by decide
  have hdescent : baseEnd_767469 < baseStart_767469 := by decide
  rcases family_descends (prefixWord ++ tailWord_767469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_767557 : List Nat := [1, 3, 1, 1, 1, 4, 1, 4, 3, 3]
def baseStart_767557 : Nat := 118140960795 + 767557 * 2 ^ 59
def prefixEnd_767557 : Nat := 4983230072969 + 3 ^ 40 * 767557 * 2
def baseEnd_767557 : Nat := 262750447148772442271717

theorem tailTrace_767557 : CollatzResearch.WordTrace tailWord_767557 prefixEnd_767557 262750447148772442271717 := by
  unfold tailWord_767557
  simp only [CollatzResearch.WordTrace]
  refine ⟨27995103680279552144236925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18663402453519701429491283 27995103680279552144236925)
  ·
    refine ⟨10498163880104832054088847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27995103680279552144236925 10498163880104832054088847)
    ·
      refine ⟨15747245820157248081133271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10498163880104832054088847 15747245820157248081133271)
      ·
        refine ⟨23620868730235872121699907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15747245820157248081133271 23620868730235872121699907)
        ·
          refine ⟨35431303095353808182549861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23620868730235872121699907 35431303095353808182549861)
          ·
            refine ⟨6643369330378839034228099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 35431303095353808182549861 6643369330378839034228099)
            ·
              refine ⟨9965053995568258551342149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6643369330378839034228099 9965053995568258551342149)
              ·
                refine ⟨1868447624169048478376653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9965053995568258551342149 1868447624169048478376653)
                ·
                  refine ⟨700667859063393179391245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1868447624169048478376653 700667859063393179391245)
                  ·
                    refine ⟨262750447148772442271717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 700667859063393179391245 262750447148772442271717)
                    ·
                      rfl

theorem cell22_767557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 1, 4, 3, 3].length) (baseStart_767557 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_767557 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_767557 prefixEnd_767557 := by exact prefixLift 767557
  have htrace : WordTrace (prefixWord ++ tailWord_767557) baseStart_767557 baseEnd_767557 := by
    simpa [prefixWord, tailWord_767557, baseEnd_767557] using wordTrace_append hprefix tailTrace_767557
  have hstable : (prefixWord ++ tailWord_767557).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_767557).length < 2 ^ (prefixWord ++ tailWord_767557).sum := by decide
  have hdescent : baseEnd_767557 < baseStart_767557 := by decide
  rcases family_descends (prefixWord ++ tailWord_767557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_767559 : List Nat := [1, 1, 4, 1, 5, 2, 2, 6]
def baseStart_767559 : Nat := 118140960795 + 767559 * 2 ^ 59
def prefixEnd_767559 : Nat := 4983230072969 + 3 ^ 40 * 767559 * 2
def baseEnd_767559 : Nat := 29194570198849455969079

theorem tailTrace_767559 : CollatzResearch.WordTrace tailWord_767559 prefixEnd_767559 29194570198849455969079 := by
  unfold tailWord_767559
  simp only [CollatzResearch.WordTrace]
  refine ⟨27995176626272306485809731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18663451084181537657206487 27995176626272306485809731)
  ·
    refine ⟨41992764939408459728714597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27995176626272306485809731 41992764939408459728714597)
    ·
      refine ⟨7873643426139086199133987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 41992764939408459728714597 7873643426139086199133987)
      ·
        refine ⟨11810465139208629298700981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7873643426139086199133987 11810465139208629298700981)
        ·
          refine ⟨1107231106800808996753217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 11810465139208629298700981 1107231106800808996753217)
          ·
            refine ⟨830423330100606747564913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1107231106800808996753217 830423330100606747564913)
            ·
              refine ⟨622817497575455060673685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 830423330100606747564913 622817497575455060673685)
              ·
                refine ⟨29194570198849455969079, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 622817497575455060673685 29194570198849455969079)
                ·
                  rfl

theorem cell22_767559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 5, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 5, 2, 2, 6].length) (baseStart_767559 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_767559 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_767559 prefixEnd_767559 := by exact prefixLift 767559
  have htrace : WordTrace (prefixWord ++ tailWord_767559) baseStart_767559 baseEnd_767559 := by
    simpa [prefixWord, tailWord_767559, baseEnd_767559] using wordTrace_append hprefix tailTrace_767559
  have hstable : (prefixWord ++ tailWord_767559).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_767559).length < 2 ^ (prefixWord ++ tailWord_767559).sum := by decide
  have hdescent : baseEnd_767559 < baseStart_767559 := by decide
  rcases family_descends (prefixWord ++ tailWord_767559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_767664 : List Nat := [2, 1, 1, 1, 2, 1, 6, 3, 2, 3]
def baseStart_767664 : Nat := 118140960795 + 767664 * 2 ^ 59
def prefixEnd_767664 : Nat := 4983230072969 + 3 ^ 40 * 767664 * 2
def baseEnd_767664 : Nat := 262787075435459829846389

theorem tailTrace_767664 : CollatzResearch.WordTrace tailWord_767664 prefixEnd_767664 262787075435459829846389 := by
  unfold tailWord_767664
  simp only [CollatzResearch.WordTrace]
  refine ⟨13999503145445954709191023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18666004193927939612254697 13999503145445954709191023)
  ·
    refine ⟨20999254718168932063786535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13999503145445954709191023 20999254718168932063786535)
    ·
      refine ⟨31498882077253398095679803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20999254718168932063786535 31498882077253398095679803)
      ·
        refine ⟨47248323115880097143519705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31498882077253398095679803 47248323115880097143519705)
        ·
          refine ⟨35436242336910072857639779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47248323115880097143519705 35436242336910072857639779)
          ·
            refine ⟨53154363505365109286459669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35436242336910072857639779 53154363505365109286459669)
            ·
              refine ⟨2491610789313989497802797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 53154363505365109286459669 2491610789313989497802797)
              ·
                refine ⟨934354045992746061676049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2491610789313989497802797 934354045992746061676049)
                ·
                  refine ⟨700765534494559546257037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 934354045992746061676049 700765534494559546257037)
                  ·
                    refine ⟨262787075435459829846389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 700765534494559546257037 262787075435459829846389)
                    ·
                      rfl

theorem cell22_767664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 6, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 6, 3, 2, 3].length) (baseStart_767664 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_767664 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_767664 prefixEnd_767664 := by exact prefixLift 767664
  have htrace : WordTrace (prefixWord ++ tailWord_767664) baseStart_767664 baseEnd_767664 := by
    simpa [prefixWord, tailWord_767664, baseEnd_767664] using wordTrace_append hprefix tailTrace_767664
  have hstable : (prefixWord ++ tailWord_767664).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_767664).length < 2 ^ (prefixWord ++ tailWord_767664).sum := by decide
  have hdescent : baseEnd_767664 < baseStart_767664 := by decide
  rcases family_descends (prefixWord ++ tailWord_767664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_767698 : List Nat := [3, 2, 2, 2, 2, 3, 1, 2, 2, 3]
def baseStart_767698 : Nat := 118140960795 + 767698 * 2 ^ 59
def prefixEnd_767698 : Nat := 4983230072969 + 3 ^ 40 * 767698 * 2
def baseEnd_767698 : Nat := 262798714330295074496285

theorem tailTrace_767698 : CollatzResearch.WordTrace tailWord_767698 prefixEnd_767698 262798714330295074496285 := by
  unfold tailWord_767698
  simp only [CollatzResearch.WordTrace]
  refine ⟨7000061593192183306279937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18666830915179155483413165 7000061593192183306279937)
  ·
    refine ⟨5250046194894137479709953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7000061593192183306279937 5250046194894137479709953)
    ·
      refine ⟨3937534646170603109782465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5250046194894137479709953 3937534646170603109782465)
      ·
        refine ⟨2953150984627952332336849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3937534646170603109782465 2953150984627952332336849)
        ·
          refine ⟨2214863238470964249252637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2953150984627952332336849 2214863238470964249252637)
          ·
            refine ⟨830573714426611593469739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2214863238470964249252637 830573714426611593469739)
            ·
              refine ⟨1245860571639917390204609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 830573714426611593469739 1245860571639917390204609)
              ·
                refine ⟨934395428729938042653457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1245860571639917390204609 934395428729938042653457)
                ·
                  refine ⟨700796571547453531990093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 934395428729938042653457 700796571547453531990093)
                  ·
                    refine ⟨262798714330295074496285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 700796571547453531990093 262798714330295074496285)
                    ·
                      rfl

theorem cell22_767698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 3, 1, 2, 2, 3].length) (baseStart_767698 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_767698 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_767698 prefixEnd_767698 := by exact prefixLift 767698
  have htrace : WordTrace (prefixWord ++ tailWord_767698) baseStart_767698 baseEnd_767698 := by
    simpa [prefixWord, tailWord_767698, baseEnd_767698] using wordTrace_append hprefix tailTrace_767698
  have hstable : (prefixWord ++ tailWord_767698).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_767698).length < 2 ^ (prefixWord ++ tailWord_767698).sum := by decide
  have hdescent : baseEnd_767698 < baseStart_767698 := by decide
  rcases family_descends (prefixWord ++ tailWord_767698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_767799 : List Nat := [1, 1, 3, 1, 2, 1, 2, 4, 4, 3]
def baseStart_767799 : Nat := 118140960795 + 767799 * 2 ^ 59
def prefixEnd_767799 : Nat := 4983230072969 + 3 ^ 40 * 767799 * 2
def baseEnd_767799 : Nat := 262833288694364477720975

theorem tailTrace_767799 : CollatzResearch.WordTrace tailWord_767799 prefixEnd_767799 262833288694364477720975 := by
  unfold tailWord_767799
  simp only [CollatzResearch.WordTrace]
  refine ⟨28003930145402827474546451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18669286763601884983030967 28003930145402827474546451)
  ·
    refine ⟨42005895218104241211819677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28003930145402827474546451 42005895218104241211819677)
    ·
      refine ⟨15752210706789090454432379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 42005895218104241211819677 15752210706789090454432379)
      ·
        refine ⟨23628316060183635681648569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15752210706789090454432379 23628316060183635681648569)
        ·
          refine ⟨17721237045137726761236427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23628316060183635681648569 17721237045137726761236427)
          ·
            refine ⟨26581855567706590141854641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17721237045137726761236427 26581855567706590141854641)
            ·
              refine ⟨19936391675779942606390981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26581855567706590141854641 19936391675779942606390981)
              ·
                refine ⟨3738073439208739238698309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19936391675779942606390981 3738073439208739238698309)
                ·
                  refine ⟨700888769851638607255933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3738073439208739238698309 700888769851638607255933)
                  ·
                    refine ⟨262833288694364477720975, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 700888769851638607255933 262833288694364477720975)
                    ·
                      rfl

theorem cell22_767799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 2, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 2, 4, 4, 3].length) (baseStart_767799 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_767799 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_767799 prefixEnd_767799 := by exact prefixLift 767799
  have htrace : WordTrace (prefixWord ++ tailWord_767799) baseStart_767799 baseEnd_767799 := by
    simpa [prefixWord, tailWord_767799, baseEnd_767799] using wordTrace_append hprefix tailTrace_767799
  have hstable : (prefixWord ++ tailWord_767799).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_767799).length < 2 ^ (prefixWord ++ tailWord_767799).sum := by decide
  have hdescent : baseEnd_767799 < baseStart_767799 := by decide
  rcases family_descends (prefixWord ++ tailWord_767799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_767816 : List Nat := [2, 1, 3, 1, 1, 4, 1, 4, 2, 3]
def baseStart_767816 : Nat := 118140960795 + 767816 * 2 ^ 59
def prefixEnd_767816 : Nat := 4983230072969 + 3 ^ 40 * 767816 * 2
def baseEnd_767816 : Nat := 262839108141782100045923

theorem tailTrace_767816 : CollatzResearch.WordTrace tailWord_767816 prefixEnd_767816 262839108141782100045923 := by
  unfold tailWord_767816
  simp only [CollatzResearch.WordTrace]
  refine ⟨14002275093170619688957651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18669700124227492918610201 14002275093170619688957651)
  ·
    refine ⟨21003412639755929533436477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14002275093170619688957651 21003412639755929533436477)
    ·
      refine ⟨7876279739908473575038679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21003412639755929533436477 7876279739908473575038679)
      ·
        refine ⟨11814419609862710362558019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7876279739908473575038679 11814419609862710362558019)
        ·
          refine ⟨17721629414794065543837029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11814419609862710362558019 17721629414794065543837029)
          ·
            refine ⟨3322805515273887289469443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 17721629414794065543837029 3322805515273887289469443)
            ·
              refine ⟨4984208272910830934204165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3322805515273887289469443 4984208272910830934204165)
              ·
                refine ⟨934539051170780800163281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4984208272910830934204165 934539051170780800163281)
                ·
                  refine ⟨700904288378085600122461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 934539051170780800163281 700904288378085600122461)
                  ·
                    refine ⟨262839108141782100045923, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 700904288378085600122461 262839108141782100045923)
                    ·
                      rfl

theorem cell22_767816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 4, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 4, 1, 4, 2, 3].length) (baseStart_767816 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_767816 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_767816 prefixEnd_767816 := by exact prefixLift 767816
  have htrace : WordTrace (prefixWord ++ tailWord_767816) baseStart_767816 baseEnd_767816 := by
    simpa [prefixWord, tailWord_767816, baseEnd_767816] using wordTrace_append hprefix tailTrace_767816
  have hstable : (prefixWord ++ tailWord_767816).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_767816).length < 2 ^ (prefixWord ++ tailWord_767816).sum := by decide
  have hdescent : baseEnd_767816 < baseStart_767816 := by decide
  rcases family_descends (prefixWord ++ tailWord_767816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_767827 : List Nat := [1, 1, 1, 2, 1, 1, 3, 1, 4, 7]
def baseStart_767827 : Nat := 118140960795 + 767827 * 2 ^ 59
def prefixEnd_767827 : Nat := 4983230072969 + 3 ^ 40 * 767827 * 2
def baseEnd_767827 : Nat := 262842873666581738020889

theorem tailTrace_767827 : CollatzResearch.WordTrace tailWord_767827 prefixEnd_767827 262842873666581738020889 := by
  unfold tailWord_767827
  simp only [CollatzResearch.WordTrace]
  refine ⟨28004951389301388256565735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18669967592867592171043823 28004951389301388256565735)
  ·
    refine ⟨42007427083952082384848603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28004951389301388256565735 42007427083952082384848603)
    ·
      refine ⟨63011140625928123577272905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42007427083952082384848603 63011140625928123577272905)
      ·
        refine ⟨47258355469446092682954679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63011140625928123577272905 47258355469446092682954679)
        ·
          refine ⟨70887533204169139024432019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47258355469446092682954679 70887533204169139024432019)
          ·
            refine ⟨106331299806253708536648029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 70887533204169139024432019 106331299806253708536648029)
            ·
              refine ⟨39874237427345140701243011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 106331299806253708536648029 39874237427345140701243011)
              ·
                refine ⟨59811356141017711051864517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39874237427345140701243011 59811356141017711051864517)
                ·
                  refine ⟨11214629276440820822224597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 59811356141017711051864517 11214629276440820822224597)
                  ·
                    refine ⟨262842873666581738020889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 11214629276440820822224597 262842873666581738020889)
                    ·
                      rfl

theorem cell22_767827_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 3, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 3, 1, 4, 7].length) (baseStart_767827 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_767827 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_767827 prefixEnd_767827 := by exact prefixLift 767827
  have htrace : WordTrace (prefixWord ++ tailWord_767827) baseStart_767827 baseEnd_767827 := by
    simpa [prefixWord, tailWord_767827, baseEnd_767827] using wordTrace_append hprefix tailTrace_767827
  have hstable : (prefixWord ++ tailWord_767827).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_767827).length < 2 ^ (prefixWord ++ tailWord_767827).sum := by decide
  have hdescent : baseEnd_767827 < baseStart_767827 := by decide
  rcases family_descends (prefixWord ++ tailWord_767827) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_767829 : List Nat := [1, 3, 2, 2, 2, 2, 3, 7]
def baseStart_767829 : Nat := 118140960795 + 767829 * 2 ^ 59
def prefixEnd_767829 : Nat := 4983230072969 + 3 ^ 40 * 767829 * 2
def baseEnd_767829 : Nat := 29204839811939377718987

theorem tailTrace_767829 : CollatzResearch.WordTrace tailWord_767829 prefixEnd_767829 29204839811939377718987 := by
  unfold tailWord_767829
  simp only [CollatzResearch.WordTrace]
  refine ⟨28005024335294142598138541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18670016223529428398759027 28005024335294142598138541)
  ·
    refine ⟨10501884125735303474301953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28005024335294142598138541 10501884125735303474301953)
    ·
      refine ⟨7876413094301477605726465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10501884125735303474301953 7876413094301477605726465)
      ·
        refine ⟨5907309820726108204294849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7876413094301477605726465 5907309820726108204294849)
        ·
          refine ⟨4430482365544581153221137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5907309820726108204294849 4430482365544581153221137)
          ·
            refine ⟨3322861774158435864915853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4430482365544581153221137 3322861774158435864915853)
            ·
              refine ⟨1246073165309413449343445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3322861774158435864915853 1246073165309413449343445)
              ·
                refine ⟨29204839811939377718987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1246073165309413449343445 29204839811939377718987)
                ·
                  rfl

theorem cell22_767829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 2, 3, 7].length) (baseStart_767829 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_767829 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_767829 prefixEnd_767829 := by exact prefixLift 767829
  have htrace : WordTrace (prefixWord ++ tailWord_767829) baseStart_767829 baseEnd_767829 := by
    simpa [prefixWord, tailWord_767829, baseEnd_767829] using wordTrace_append hprefix tailTrace_767829
  have hstable : (prefixWord ++ tailWord_767829).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_767829).length < 2 ^ (prefixWord ++ tailWord_767829).sum := by decide
  have hdescent : baseEnd_767829 < baseStart_767829 := by decide
  rcases family_descends (prefixWord ++ tailWord_767829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_767861 : List Nat := [1, 3, 4, 1, 1, 1, 1, 2, 5, 3]
def baseStart_767861 : Nat := 118140960795 + 767861 * 2 ^ 59
def prefixEnd_767861 : Nat := 4983230072969 + 3 ^ 40 * 767861 * 2
def baseEnd_767861 : Nat := 262854512561416982670785

theorem tailTrace_767861 : CollatzResearch.WordTrace tailWord_767861 prefixEnd_767861 262854512561416982670785 := by
  unfold tailWord_767861
  simp only [CollatzResearch.WordTrace]
  refine ⟨28006191471178212063303437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18670794314118808042202291 28006191471178212063303437)
  ·
    refine ⟨10502321801691829523738789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28006191471178212063303437 10502321801691829523738789)
    ·
      refine ⟨1969185337817218035701023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 10502321801691829523738789 1969185337817218035701023)
      ·
        refine ⟨2953778006725827053551535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1969185337817218035701023 2953778006725827053551535)
        ·
          refine ⟨4430667010088740580327303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2953778006725827053551535 4430667010088740580327303)
          ·
            refine ⟨6646000515133110870490955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4430667010088740580327303 6646000515133110870490955)
            ·
              refine ⟨9969000772699666305736433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6646000515133110870490955 9969000772699666305736433)
              ·
                refine ⟨7476750579524749729302325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9969000772699666305736433 7476750579524749729302325)
                ·
                  refine ⟨700945366830445287122093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 7476750579524749729302325 700945366830445287122093)
                  ·
                    refine ⟨262854512561416982670785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 700945366830445287122093 262854512561416982670785)
                    ·
                      rfl

theorem cell22_767861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 1, 2, 5, 3].length) (baseStart_767861 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_767861 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_767861 prefixEnd_767861 := by exact prefixLift 767861
  have htrace : WordTrace (prefixWord ++ tailWord_767861) baseStart_767861 baseEnd_767861 := by
    simpa [prefixWord, tailWord_767861, baseEnd_767861] using wordTrace_append hprefix tailTrace_767861
  have hstable : (prefixWord ++ tailWord_767861).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_767861).length < 2 ^ (prefixWord ++ tailWord_767861).sum := by decide
  have hdescent : baseEnd_767861 < baseStart_767861 := by decide
  rcases family_descends (prefixWord ++ tailWord_767861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_767889 : List Nat := [1, 2, 2, 1, 1, 1, 6, 1, 2, 5]
def baseStart_767889 : Nat := 118140960795 + 767889 * 2 ^ 59
def prefixEnd_767889 : Nat := 4983230072969 + 3 ^ 40 * 767889 * 2
def baseEnd_767889 : Nat := 262864097533634242970699

theorem tailTrace_767889 : CollatzResearch.WordTrace tailWord_767889 prefixEnd_767889 262864097533634242970699 := by
  unfold tailWord_767889
  simp only [CollatzResearch.WordTrace]
  refine ⟨28007212715076772845322721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18671475143384515230215147 28007212715076772845322721)
  ·
    refine ⟨21005409536307579633992041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28007212715076772845322721 21005409536307579633992041)
    ·
      refine ⟨15754057152230684725494031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21005409536307579633992041 15754057152230684725494031)
      ·
        refine ⟨23631085728346027088241047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15754057152230684725494031 23631085728346027088241047)
        ·
          refine ⟨35446628592519040632361571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23631085728346027088241047 35446628592519040632361571)
          ·
            refine ⟨53169942888778560948542357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35446628592519040632361571 53169942888778560948542357)
            ·
              refine ⟨2492341072911495044462923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 53169942888778560948542357 2492341072911495044462923)
              ·
                refine ⟨3738511609367242566694385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2492341072911495044462923 3738511609367242566694385)
                ·
                  refine ⟨2803883707025431925020789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3738511609367242566694385 2803883707025431925020789)
                  ·
                    refine ⟨262864097533634242970699, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2803883707025431925020789 262864097533634242970699)
                    ·
                      rfl

theorem cell22_767889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 5].length) (baseStart_767889 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_767889 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_767889 prefixEnd_767889 := by exact prefixLift 767889
  have htrace : WordTrace (prefixWord ++ tailWord_767889) baseStart_767889 baseEnd_767889 := by
    simpa [prefixWord, tailWord_767889, baseEnd_767889] using wordTrace_append hprefix tailTrace_767889
  have hstable : (prefixWord ++ tailWord_767889).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_767889).length < 2 ^ (prefixWord ++ tailWord_767889).sum := by decide
  have hdescent : baseEnd_767889 < baseStart_767889 := by decide
  rcases family_descends (prefixWord ++ tailWord_767889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_767981 : List Nat := [1, 5, 1, 4, 11]
def baseStart_767981 : Nat := 118140960795 + 767981 * 2 ^ 59
def prefixEnd_767981 : Nat := 4983230072969 + 3 ^ 40 * 767981 * 2
def baseEnd_767981 : Nat := 1081874860138998640619

theorem tailTrace_767981 : CollatzResearch.WordTrace tailWord_767981 prefixEnd_767981 1081874860138998640619 := by
  unfold tailWord_767981
  simp only [CollatzResearch.WordTrace]
  refine ⟨28010568230743472557671797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18673712153828981705114531 28010568230743472557671797)
  ·
    refine ⟨2625990771632200552281731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 28010568230743472557671797 2625990771632200552281731)
    ·
      refine ⟨3938986157448300828422597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2625990771632200552281731 3938986157448300828422597)
      ·
        refine ⟨738559904521556405329237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3938986157448300828422597 738559904521556405329237)
        ·
          refine ⟨1081874860138998640619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 11 738559904521556405329237 1081874860138998640619)
          ·
            rfl

theorem cell22_767981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 11].length) (baseStart_767981 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_767981 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_767981 prefixEnd_767981 := by exact prefixLift 767981
  have htrace : WordTrace (prefixWord ++ tailWord_767981) baseStart_767981 baseEnd_767981 := by
    simpa [prefixWord, tailWord_767981, baseEnd_767981] using wordTrace_append hprefix tailTrace_767981
  have hstable : (prefixWord ++ tailWord_767981).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_767981).length < 2 ^ (prefixWord ++ tailWord_767981).sum := by decide
  have hdescent : baseEnd_767981 < baseStart_767981 := by decide
  rcases family_descends (prefixWord ++ tailWord_767981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_767985 : List Nat := [1, 2, 2, 2, 5, 1, 2, 2, 2, 3]
def baseStart_767985 : Nat := 118140960795 + 767985 * 2 ^ 59
def prefixEnd_767985 : Nat := 4983230072969 + 3 ^ 40 * 767985 * 2
def baseEnd_767985 : Nat := 262896960295521992570405

theorem tailTrace_767985 : CollatzResearch.WordTrace tailWord_767985 prefixEnd_767985 262896960295521992570405 := by
  unfold tailWord_767985
  simp only [CollatzResearch.WordTrace]
  refine ⟨28010714122728981240817409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18673809415152654160544939 28010714122728981240817409)
  ·
    refine ⟨21008035592046735930613057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28010714122728981240817409 21008035592046735930613057)
    ·
      refine ⟨15756026694035051947959793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21008035592046735930613057 15756026694035051947959793)
      ·
        refine ⟨11817020020526288960969845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15756026694035051947959793 11817020020526288960969845)
        ·
          refine ⟨1107845626924339590090923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 11817020020526288960969845 1107845626924339590090923)
          ·
            refine ⟨1661768440386509385136385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1107845626924339590090923 1661768440386509385136385)
            ·
              refine ⟨1246326330289882038852289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1661768440386509385136385 1246326330289882038852289)
              ·
                refine ⟨934744747717411529139217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1246326330289882038852289 934744747717411529139217)
                ·
                  refine ⟨701058560788058646854413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 934744747717411529139217 701058560788058646854413)
                  ·
                    refine ⟨262896960295521992570405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 701058560788058646854413 262896960295521992570405)
                    ·
                      rfl

theorem cell22_767985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 5, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 5, 1, 2, 2, 2, 3].length) (baseStart_767985 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_767985 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_767985 prefixEnd_767985 := by exact prefixLift 767985
  have htrace : WordTrace (prefixWord ++ tailWord_767985) baseStart_767985 baseEnd_767985 := by
    simpa [prefixWord, tailWord_767985, baseEnd_767985] using wordTrace_append hprefix tailTrace_767985
  have hstable : (prefixWord ++ tailWord_767985).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_767985).length < 2 ^ (prefixWord ++ tailWord_767985).sum := by decide
  have hdescent : baseEnd_767985 < baseStart_767985 := by decide
  rcases family_descends (prefixWord ++ tailWord_767985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_767998 : List Nat := [4, 2, 2, 2, 1, 1, 3, 7]
def baseStart_767998 : Nat := 118140960795 + 767998 * 2 ^ 59
def prefixEnd_767998 : Nat := 4983230072969 + 3 ^ 40 * 767998 * 2
def baseEnd_767998 : Nat := 29211267829021587999485

theorem tailTrace_767998 : CollatzResearch.WordTrace tailWord_767998 prefixEnd_767998 29211267829021587999485 := by
  unfold tailWord_767998
  simp only [CollatzResearch.WordTrace]
  refine ⟨3501398533960235557630081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 18674125514454589640693765 3501398533960235557630081)
  ·
    refine ⟨2626048900470176668222561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3501398533960235557630081 2626048900470176668222561)
    ·
      refine ⟨1969536675352632501166921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2626048900470176668222561 1969536675352632501166921)
      ·
        refine ⟨1477152506514474375875191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1969536675352632501166921 1477152506514474375875191)
        ·
          refine ⟨2215728759771711563812787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1477152506514474375875191 2215728759771711563812787)
          ·
            refine ⟨3323593139657567345719181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2215728759771711563812787 3323593139657567345719181)
            ·
              refine ⟨1246347427371587754644693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3323593139657567345719181 1246347427371587754644693)
              ·
                refine ⟨29211267829021587999485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1246347427371587754644693 29211267829021587999485)
                ·
                  rfl

theorem cell22_767998_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 1, 3, 7].length) (baseStart_767998 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_767998 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_767998 prefixEnd_767998 := by exact prefixLift 767998
  have htrace : WordTrace (prefixWord ++ tailWord_767998) baseStart_767998 baseEnd_767998 := by
    simpa [prefixWord, tailWord_767998, baseEnd_767998] using wordTrace_append hprefix tailTrace_767998
  have hstable : (prefixWord ++ tailWord_767998).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_767998).length < 2 ^ (prefixWord ++ tailWord_767998).sum := by decide
  have hdescent : baseEnd_767998 < baseStart_767998 := by decide
  rcases family_descends (prefixWord ++ tailWord_767998) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_768009 : List Nat := [1, 2, 1, 1, 3, 1, 1, 1, 11]
def baseStart_768009 : Nat := 118140960795 + 768009 * 2 ^ 59
def prefixEnd_768009 : Nat := 4983230072969 + 3 ^ 40 * 768009 * 2
def baseEnd_768009 : Nat := 87635058661997976656777

theorem tailTrace_768009 : CollatzResearch.WordTrace tailWord_768009 prefixEnd_768009 87635058661997976656777 := by
  unfold tailWord_768009
  simp only [CollatzResearch.WordTrace]
  refine ⟨28011589474642033339691081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18674392983094688893127387 28011589474642033339691081)
  ·
    refine ⟨21008692105981525004768311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28011589474642033339691081 21008692105981525004768311)
    ·
      refine ⟨31513038158972287507152467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21008692105981525004768311 31513038158972287507152467)
      ·
        refine ⟨47269557238458431260728701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31513038158972287507152467 47269557238458431260728701)
        ·
          refine ⟨17726083964421911722773263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 47269557238458431260728701 17726083964421911722773263)
          ·
            refine ⟨26589125946632867584159895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17726083964421911722773263 26589125946632867584159895)
            ·
              refine ⟨39883688919949301376239843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26589125946632867584159895 39883688919949301376239843)
              ·
                refine ⟨59825533379923952064359765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39883688919949301376239843 59825533379923952064359765)
                ·
                  refine ⟨87635058661997976656777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 11 59825533379923952064359765 87635058661997976656777)
                  ·
                    rfl

theorem cell22_768009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 1, 1, 11].length) (baseStart_768009 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_768009 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_768009 prefixEnd_768009 := by exact prefixLift 768009
  have htrace : WordTrace (prefixWord ++ tailWord_768009) baseStart_768009 baseEnd_768009 := by
    simpa [prefixWord, tailWord_768009, baseEnd_768009] using wordTrace_append hprefix tailTrace_768009
  have hstable : (prefixWord ++ tailWord_768009).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_768009).length < 2 ^ (prefixWord ++ tailWord_768009).sum := by decide
  have hdescent : baseEnd_768009 < baseStart_768009 := by decide
  rcases family_descends (prefixWord ++ tailWord_768009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_768071 : List Nat := [1, 1, 4, 1, 3, 1, 1, 4, 6]
def baseStart_768071 : Nat := 118140960795 + 768071 * 2 ^ 59
def prefixEnd_768071 : Nat := 4983230072969 + 3 ^ 40 * 768071 * 2
def baseEnd_768071 : Nat := 87642133284348811640047

theorem tailTrace_768071 : CollatzResearch.WordTrace tailWord_768071 prefixEnd_768071 87642133284348811640047 := by
  unfold tailWord_768071
  simp only [CollatzResearch.WordTrace]
  refine ⟨28013850800417417928448067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18675900533611611952298711 28013850800417417928448067)
  ·
    refine ⟨42020776200626126892672101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28013850800417417928448067 42020776200626126892672101)
    ·
      refine ⟨7878895537617398792376019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 42020776200626126892672101 7878895537617398792376019)
      ·
        refine ⟨11818343306426098188564029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7878895537617398792376019 11818343306426098188564029)
        ·
          refine ⟨4431878739909786820711511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11818343306426098188564029 4431878739909786820711511)
          ·
            refine ⟨6647818109864680231067267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4431878739909786820711511 6647818109864680231067267)
            ·
              refine ⟨9971727164797020346600901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6647818109864680231067267 9971727164797020346600901)
              ·
                refine ⟨1869698843399441314987669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9971727164797020346600901 1869698843399441314987669)
                ·
                  refine ⟨87642133284348811640047, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1869698843399441314987669 87642133284348811640047)
                  ·
                    rfl

theorem cell22_768071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 1, 4, 6].length) (baseStart_768071 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_768071 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_768071 prefixEnd_768071 := by exact prefixLift 768071
  have htrace : WordTrace (prefixWord ++ tailWord_768071) baseStart_768071 baseEnd_768071 := by
    simpa [prefixWord, tailWord_768071, baseEnd_768071] using wordTrace_append hprefix tailTrace_768071
  have hstable : (prefixWord ++ tailWord_768071).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_768071).length < 2 ^ (prefixWord ++ tailWord_768071).sum := by decide
  have hdescent : baseEnd_768071 < baseStart_768071 := by decide
  rcases family_descends (prefixWord ++ tailWord_768071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_768073 : List Nat := [1, 2, 1, 1, 2, 2, 6, 2, 1, 4]
def baseStart_768073 : Nat := 118140960795 + 768073 * 2 ^ 59
def prefixEnd_768073 : Nat := 4983230072969 + 3 ^ 40 * 768073 * 2
def baseEnd_768073 : Nat := 262927084493919096370135

theorem tailTrace_768073 : CollatzResearch.WordTrace tailWord_768073 prefixEnd_768073 262927084493919096370135 := by
  unfold tailWord_768073
  simp only [CollatzResearch.WordTrace]
  refine ⟨28013923746410172270020873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18675949164273448180013915 28013923746410172270020873)
  ·
    refine ⟨21010442809807629202515655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28013923746410172270020873 21010442809807629202515655)
    ·
      refine ⟨31515664214711443803773483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21010442809807629202515655 31515664214711443803773483)
      ·
        refine ⟨47273496322067165705660225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31515664214711443803773483 47273496322067165705660225)
        ·
          refine ⟨35455122241550374279245169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47273496322067165705660225 35455122241550374279245169)
          ·
            refine ⟨26591341681162780709433877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35455122241550374279245169 26591341681162780709433877)
            ·
              refine ⟨1246469141304505345754713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 26591341681162780709433877 1246469141304505345754713)
              ·
                refine ⟨934851855978379009316035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1246469141304505345754713 934851855978379009316035)
                ·
                  refine ⟨1402277783967568513974053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 934851855978379009316035 1402277783967568513974053)
                  ·
                    refine ⟨262927084493919096370135, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1402277783967568513974053 262927084493919096370135)
                    ·
                      rfl

theorem cell22_768073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 6, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 6, 2, 1, 4].length) (baseStart_768073 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_768073 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_768073 prefixEnd_768073 := by exact prefixLift 768073
  have htrace : WordTrace (prefixWord ++ tailWord_768073) baseStart_768073 baseEnd_768073 := by
    simpa [prefixWord, tailWord_768073, baseEnd_768073] using wordTrace_append hprefix tailTrace_768073
  have hstable : (prefixWord ++ tailWord_768073).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_768073).length < 2 ^ (prefixWord ++ tailWord_768073).sum := by decide
  have hdescent : baseEnd_768073 < baseStart_768073 := by decide
  rcases family_descends (prefixWord ++ tailWord_768073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_768103 : List Nat := [1, 1, 5, 1, 1, 2, 1, 3, 4, 3]
def baseStart_768103 : Nat := 118140960795 + 768103 * 2 ^ 59
def prefixEnd_768103 : Nat := 4983230072969 + 3 ^ 40 * 768103 * 2
def baseEnd_768103 : Nat := 262937354107009018120043

theorem tailTrace_768103 : CollatzResearch.WordTrace tailWord_768103 prefixEnd_768103 262937354107009018120043 := by
  unfold tailWord_768103
  simp only [CollatzResearch.WordTrace]
  refine ⟨28015017936301487393612963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18676678624200991595741975 28015017936301487393612963)
  ·
    refine ⟨42022526904452231090419445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28015017936301487393612963 42022526904452231090419445)
    ·
      refine ⟨3939611897292396664726823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 42022526904452231090419445 3939611897292396664726823)
      ·
        refine ⟨5909417845938594997090235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3939611897292396664726823 5909417845938594997090235)
        ·
          refine ⟨8864126768907892495635353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5909417845938594997090235 8864126768907892495635353)
          ·
            refine ⟨6648095076680919371726515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8864126768907892495635353 6648095076680919371726515)
            ·
              refine ⟨9972142615021379057589773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6648095076680919371726515 9972142615021379057589773)
              ·
                refine ⟨3739553480633017146596165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9972142615021379057589773 3739553480633017146596165)
                ·
                  refine ⟨701166277618690714986781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3739553480633017146596165 701166277618690714986781)
                  ·
                    refine ⟨262937354107009018120043, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 701166277618690714986781 262937354107009018120043)
                    ·
                      rfl

theorem cell22_768103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 1, 3, 4, 3].length) (baseStart_768103 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_768103 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_768103 prefixEnd_768103 := by exact prefixLift 768103
  have htrace : WordTrace (prefixWord ++ tailWord_768103) baseStart_768103 baseEnd_768103 := by
    simpa [prefixWord, tailWord_768103, baseEnd_768103] using wordTrace_append hprefix tailTrace_768103
  have hstable : (prefixWord ++ tailWord_768103).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_768103).length < 2 ^ (prefixWord ++ tailWord_768103).sum := by decide
  have hdescent : baseEnd_768103 < baseStart_768103 := by decide
  rcases family_descends (prefixWord ++ tailWord_768103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_768105 : List Nat := [1, 2, 1, 1, 1, 5, 5, 2, 4]
def baseStart_768105 : Nat := 118140960795 + 768105 * 2 ^ 59
def prefixEnd_768105 : Nat := 4983230072969 + 3 ^ 40 * 768105 * 2
def baseEnd_768105 : Nat := 87646012915960559856679

theorem tailTrace_768105 : CollatzResearch.WordTrace tailWord_768105 prefixEnd_768105 87646012915960559856679 := by
  unfold tailWord_768105
  simp only [CollatzResearch.WordTrace]
  refine ⟨28015090882294241735185769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18676727254862827823457179 28015090882294241735185769)
  ·
    refine ⟨21011318161720681301389327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28015090882294241735185769 21011318161720681301389327)
    ·
      refine ⟨31516977242581021952083991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21011318161720681301389327 31516977242581021952083991)
      ·
        refine ⟨47275465863871532928125987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31516977242581021952083991 47275465863871532928125987)
        ·
          refine ⟨70913198795807299392188981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47275465863871532928125987 70913198795807299392188981)
          ·
            refine ⟨6648112387106934318017717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 70913198795807299392188981 6648112387106934318017717)
            ·
              refine ⟨623260536291275092314161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 6648112387106934318017717 623260536291275092314161)
              ·
                refine ⟨467445402218456319235621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 623260536291275092314161 467445402218456319235621)
                ·
                  refine ⟨87646012915960559856679, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 467445402218456319235621 87646012915960559856679)
                  ·
                    rfl

theorem cell22_768105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 5, 2, 4].length) (baseStart_768105 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_768105 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_768105 prefixEnd_768105 := by exact prefixLift 768105
  have htrace : WordTrace (prefixWord ++ tailWord_768105) baseStart_768105 baseEnd_768105 := by
    simpa [prefixWord, tailWord_768105, baseEnd_768105] using wordTrace_append hprefix tailTrace_768105
  have hstable : (prefixWord ++ tailWord_768105).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_768105).length < 2 ^ (prefixWord ++ tailWord_768105).sum := by decide
  have hdescent : baseEnd_768105 < baseStart_768105 := by decide
  rcases family_descends (prefixWord ++ tailWord_768105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_768167 : List Nat := [1, 1, 6, 2, 3, 1, 1, 7]
def baseStart_768167 : Nat := 118140960795 + 768167 * 2 ^ 59
def prefixEnd_768167 : Nat := 4983230072969 + 3 ^ 40 * 768167 * 2
def baseEnd_768167 : Nat := 29217695846103798279983

theorem tailTrace_768167 : CollatzResearch.WordTrace tailWord_768167 prefixEnd_768167 29217695846103798279983 := by
  unfold tailWord_768167
  simp only [CollatzResearch.WordTrace]
  refine ⟨28017352208069626323942755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18678234805379750882628503 28017352208069626323942755)
  ·
    refine ⟨42026028312104439485914133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28017352208069626323942755 42026028312104439485914133)
    ·
      refine ⟨1969970077129895600902225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 42026028312104439485914133 1969970077129895600902225)
      ·
        refine ⟨1477477557847421700676669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1969970077129895600902225 1477477557847421700676669)
        ·
          refine ⟨554054084192783137753751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1477477557847421700676669 554054084192783137753751)
          ·
            refine ⟨831081126289174706630627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 554054084192783137753751 831081126289174706630627)
            ·
              refine ⟨1246621689433762059945941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 831081126289174706630627 1246621689433762059945941)
              ·
                refine ⟨29217695846103798279983, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1246621689433762059945941 29217695846103798279983)
                ·
                  rfl

theorem cell22_768167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 3, 1, 1, 7].length) (baseStart_768167 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_768167 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_768167 prefixEnd_768167 := by exact prefixLift 768167
  have htrace : WordTrace (prefixWord ++ tailWord_768167) baseStart_768167 baseEnd_768167 := by
    simpa [prefixWord, tailWord_768167, baseEnd_768167] using wordTrace_append hprefix tailTrace_768167
  have hstable : (prefixWord ++ tailWord_768167).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_768167).length < 2 ^ (prefixWord ++ tailWord_768167).sum := by decide
  have hdescent : baseEnd_768167 < baseStart_768167 := by decide
  rcases family_descends (prefixWord ++ tailWord_768167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_768178 : List Nat := [3, 2, 1, 1, 1, 3, 1, 5, 5]
def baseStart_768178 : Nat := 118140960795 + 768178 * 2 ^ 59
def prefixEnd_768178 : Nat := 4983230072969 + 3 ^ 40 * 768178 * 2
def baseEnd_768178 : Nat := 87654342713244607498271

theorem tailTrace_768178 : CollatzResearch.WordTrace tailWord_768178 prefixEnd_768178 87654342713244607498271 := by
  unfold tailWord_768178
  simp only [CollatzResearch.WordTrace]
  refine ⟨7004438352757443800648297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18678502274019850135062125 7004438352757443800648297)
  ·
    refine ⟨5253328764568082850486223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7004438352757443800648297 5253328764568082850486223)
    ·
      refine ⟨7879993146852124275729335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5253328764568082850486223 7879993146852124275729335)
      ·
        refine ⟨11819989720278186413594003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7879993146852124275729335 11819989720278186413594003)
        ·
          refine ⟨17729984580417279620391005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11819989720278186413594003 17729984580417279620391005)
          ·
            refine ⟨6648744217656479857646627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17729984580417279620391005 6648744217656479857646627)
            ·
              refine ⟨9973116326484719786469941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6648744217656479857646627 9973116326484719786469941)
              ·
                refine ⟨934979655607942479981557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 9973116326484719786469941 934979655607942479981557)
                ·
                  refine ⟨87654342713244607498271, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 934979655607942479981557 87654342713244607498271)
                  ·
                    rfl

theorem cell22_768178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 1, 5, 5].length) (baseStart_768178 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_768178 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_768178 prefixEnd_768178 := by exact prefixLift 768178
  have htrace : WordTrace (prefixWord ++ tailWord_768178) baseStart_768178 baseEnd_768178 := by
    simpa [prefixWord, tailWord_768178, baseEnd_768178] using wordTrace_append hprefix tailTrace_768178
  have hstable : (prefixWord ++ tailWord_768178).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_768178).length < 2 ^ (prefixWord ++ tailWord_768178).sum := by decide
  have hdescent : baseEnd_768178 < baseStart_768178 := by decide
  rcases family_descends (prefixWord ++ tailWord_768178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_768242 : List Nat := [3, 2, 1, 3, 2, 2, 2, 2, 1, 4]
def baseStart_768242 : Nat := 118140960795 + 768242 * 2 ^ 59
def prefixEnd_768242 : Nat := 4983230072969 + 3 ^ 40 * 768242 * 2
def baseEnd_768242 : Nat := 262984936647658988894617

theorem tailTrace_768242 : CollatzResearch.WordTrace tailWord_768242 prefixEnd_768242 262984936647658988894617 := by
  unfold tailWord_768242
  simp only [CollatzResearch.WordTrace]
  refine ⟨7005021920699478533230745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18680058455198609421948653 7005021920699478533230745)
  ·
    refine ⟨5253766440524608899923059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7005021920699478533230745 5253766440524608899923059)
    ·
      refine ⟨7880649660786913349884589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5253766440524608899923059 7880649660786913349884589)
      ·
        refine ⟨2955243622795092506206721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7880649660786913349884589 2955243622795092506206721)
        ·
          refine ⟨2216432717096319379655041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2955243622795092506206721 2216432717096319379655041)
          ·
            refine ⟨1662324537822239534741281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2216432717096319379655041 1662324537822239534741281)
            ·
              refine ⟨1246743403366679651055961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1662324537822239534741281 1246743403366679651055961)
              ·
                refine ⟨935057552525009738291971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1246743403366679651055961 935057552525009738291971)
                ·
                  refine ⟨1402586328787514607437957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 935057552525009738291971 1402586328787514607437957)
                  ·
                    refine ⟨262984936647658988894617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1402586328787514607437957 262984936647658988894617)
                    ·
                      rfl

theorem cell22_768242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 2, 2, 2, 1, 4].length) (baseStart_768242 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_768242 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_768242 prefixEnd_768242 := by exact prefixLift 768242
  have htrace : WordTrace (prefixWord ++ tailWord_768242) baseStart_768242 baseEnd_768242 := by
    simpa [prefixWord, tailWord_768242, baseEnd_768242] using wordTrace_append hprefix tailTrace_768242
  have hstable : (prefixWord ++ tailWord_768242).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_768242).length < 2 ^ (prefixWord ++ tailWord_768242).sum := by decide
  have hdescent : baseEnd_768242 < baseStart_768242 := by decide
  rcases family_descends (prefixWord ++ tailWord_768242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_768253 : List Nat := [1, 4, 1, 1, 1, 1, 1, 2, 6, 4]
def baseStart_768253 : Nat := 118140960795 + 768253 * 2 ^ 59
def prefixEnd_768253 : Nat := 4983230072969 + 3 ^ 40 * 768253 * 2
def baseEnd_768253 : Nat := 262988702172458626869583

theorem tailTrace_768253 : CollatzResearch.WordTrace tailWord_768253 prefixEnd_768253 262988702172458626869583 := by
  unfold tailWord_768253
  simp only [CollatzResearch.WordTrace]
  refine ⟨28020488885758063011573413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18680325923838708674382275 28020488885758063011573413)
  ·
    refine ⟨5253841666079636814670015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 28020488885758063011573413 5253841666079636814670015)
    ·
      refine ⟨7880762499119455222005023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5253841666079636814670015 7880762499119455222005023)
      ·
        refine ⟨11821143748679182833007535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7880762499119455222005023 11821143748679182833007535)
        ·
          refine ⟨17731715623018774249511303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11821143748679182833007535 17731715623018774249511303)
          ·
            refine ⟨26597573434528161374266955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17731715623018774249511303 26597573434528161374266955)
            ·
              refine ⟨39896360151792242061400433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26597573434528161374266955 39896360151792242061400433)
              ·
                refine ⟨29922270113844181546050325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39896360151792242061400433 29922270113844181546050325)
                ·
                  refine ⟨1402606411586446009971109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 29922270113844181546050325 1402606411586446009971109)
                  ·
                    refine ⟨262988702172458626869583, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1402606411586446009971109 262988702172458626869583)
                    ·
                      rfl

theorem cell22_768253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 1, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 1, 2, 6, 4].length) (baseStart_768253 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_768253 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_768253 prefixEnd_768253 := by exact prefixLift 768253
  have htrace : WordTrace (prefixWord ++ tailWord_768253) baseStart_768253 baseEnd_768253 := by
    simpa [prefixWord, tailWord_768253, baseEnd_768253] using wordTrace_append hprefix tailTrace_768253
  have hstable : (prefixWord ++ tailWord_768253).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_768253).length < 2 ^ (prefixWord ++ tailWord_768253).sum := by decide
  have hdescent : baseEnd_768253 < baseStart_768253 := by decide
  rcases family_descends (prefixWord ++ tailWord_768253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_768270 : List Nat := [4, 1, 1, 2, 1, 2, 3, 2, 2, 4]
def baseStart_768270 : Nat := 118140960795 + 768270 * 2 ^ 59
def prefixEnd_768270 : Nat := 4983230072969 + 3 ^ 40 * 768270 * 2
def baseEnd_768270 : Nat := 262994521619876249194531

theorem tailTrace_768270 : CollatzResearch.WordTrace tailWord_768270 prefixEnd_768270 262994521619876249194531 := by
  unfold tailWord_768270
  simp only [CollatzResearch.WordTrace]
  refine ⟨3502638615837059364367783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 18680739284464316609961509 3502638615837059364367783)
  ·
    refine ⟨5253957923755589046551675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3502638615837059364367783 5253957923755589046551675)
    ·
      refine ⟨7880936885633383569827513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5253957923755589046551675 7880936885633383569827513)
      ·
        refine ⟨5910702664225037677370635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7880936885633383569827513 5910702664225037677370635)
        ·
          refine ⟨8866053996337556516055953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5910702664225037677370635 8866053996337556516055953)
          ·
            refine ⟨6649540497253167387041965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8866053996337556516055953 6649540497253167387041965)
            ·
              refine ⟨2493577686469937770140737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6649540497253167387041965 2493577686469937770140737)
              ·
                refine ⟨1870183264852453327605553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2493577686469937770140737 1870183264852453327605553)
                ·
                  refine ⟨1402637448639339995704165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1870183264852453327605553 1402637448639339995704165)
                  ·
                    refine ⟨262994521619876249194531, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1402637448639339995704165 262994521619876249194531)
                    ·
                      rfl

theorem cell22_768270_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 3, 2, 2, 4].length) (baseStart_768270 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_768270 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_768270 prefixEnd_768270 := by exact prefixLift 768270
  have htrace : WordTrace (prefixWord ++ tailWord_768270) baseStart_768270 baseEnd_768270 := by
    simpa [prefixWord, tailWord_768270, baseEnd_768270] using wordTrace_append hprefix tailTrace_768270
  have hstable : (prefixWord ++ tailWord_768270).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_768270).length < 2 ^ (prefixWord ++ tailWord_768270).sum := by decide
  have hdescent : baseEnd_768270 < baseStart_768270 := by decide
  rcases family_descends (prefixWord ++ tailWord_768270) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_768300 : List Nat := [2, 2, 1, 1, 1, 3, 2, 4, 3, 3]
def baseStart_768300 : Nat := 118140960795 + 768300 * 2 ^ 59
def prefixEnd_768300 : Nat := 4983230072969 + 3 ^ 40 * 768300 * 2
def baseEnd_768300 : Nat := 263004791232966170944439

theorem tailTrace_768300 : CollatzResearch.WordTrace tailWord_768300 prefixEnd_768300 263004791232966170944439 := by
  unfold tailWord_768300
  simp only [CollatzResearch.WordTrace]
  refine ⟨14011101558293895019267177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18681468744391860025689569 14011101558293895019267177)
  ·
    refine ⟨10508326168720421264450383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14011101558293895019267177 10508326168720421264450383)
    ·
      refine ⟨15762489253080631896675575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10508326168720421264450383 15762489253080631896675575)
      ·
        refine ⟨23643733879620947845013363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15762489253080631896675575 23643733879620947845013363)
        ·
          refine ⟨35465600819431421767520045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23643733879620947845013363 35465600819431421767520045)
          ·
            refine ⟨13299600307286783162820017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35465600819431421767520045 13299600307286783162820017)
            ·
              refine ⟨9974700230465087372115013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13299600307286783162820017 9974700230465087372115013)
              ·
                refine ⟨1870256293212203882271565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9974700230465087372115013 1870256293212203882271565)
                ·
                  refine ⟨701346109954576455851837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1870256293212203882271565 701346109954576455851837)
                  ·
                    refine ⟨263004791232966170944439, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 701346109954576455851837 263004791232966170944439)
                    ·
                      rfl

theorem cell22_768300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 3, 3].length) (baseStart_768300 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_768300 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_768300 prefixEnd_768300 := by exact prefixLift 768300
  have htrace : WordTrace (prefixWord ++ tailWord_768300) baseStart_768300 baseEnd_768300 := by
    simpa [prefixWord, tailWord_768300, baseEnd_768300] using wordTrace_append hprefix tailTrace_768300
  have hstable : (prefixWord ++ tailWord_768300).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_768300).length < 2 ^ (prefixWord ++ tailWord_768300).sum := by decide
  have hdescent : baseEnd_768300 < baseStart_768300 := by decide
  rcases family_descends (prefixWord ++ tailWord_768300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_768392 : List Nat := [2, 1, 3, 3, 1, 1, 1, 6, 4]
def baseStart_768392 : Nat := 118140960795 + 768392 * 2 ^ 59
def prefixEnd_768392 : Nat := 4983230072969 + 3 ^ 40 * 768392 * 2
def baseEnd_768392 : Nat := 87678761571036199214719

theorem tailTrace_768392 : CollatzResearch.WordTrace tailWord_768392 prefixEnd_768392 87678761571036199214719 := by
  unfold tailWord_768392
  simp only [CollatzResearch.WordTrace]
  refine ⟨14012779316127244875441715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18683705754836326500588953 14012779316127244875441715)
  ·
    refine ⟨21019168974190867313162573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14012779316127244875441715 21019168974190867313162573)
    ·
      refine ⟨7882188365321575242435965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21019168974190867313162573 7882188365321575242435965)
      ·
        refine ⟨2955820636995590715913487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7882188365321575242435965 2955820636995590715913487)
        ·
          refine ⟨4433730955493386073870231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2955820636995590715913487 4433730955493386073870231)
          ·
            refine ⟨6650596433240079110805347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4433730955493386073870231 6650596433240079110805347)
            ·
              refine ⟨9975894649860118666208021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6650596433240079110805347 9975894649860118666208021)
              ·
                refine ⟨467620061712193062478501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 9975894649860118666208021 467620061712193062478501)
                ·
                  refine ⟨87678761571036199214719, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 467620061712193062478501 87678761571036199214719)
                  ·
                    rfl

theorem cell22_768392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 1, 6, 4].length) (baseStart_768392 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_768392 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_768392 prefixEnd_768392 := by exact prefixLift 768392
  have htrace : WordTrace (prefixWord ++ tailWord_768392) baseStart_768392 baseEnd_768392 := by
    simpa [prefixWord, tailWord_768392, baseEnd_768392] using wordTrace_append hprefix tailTrace_768392
  have hstable : (prefixWord ++ tailWord_768392).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_768392).length < 2 ^ (prefixWord ++ tailWord_768392).sum := by decide
  have hdescent : baseEnd_768392 < baseStart_768392 := by decide
  rcases family_descends (prefixWord ++ tailWord_768392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_768407 : List Nat := [1, 1, 3, 3, 1, 1, 2, 5, 2, 3]
def baseStart_768407 : Nat := 118140960795 + 768407 * 2 ^ 59
def prefixEnd_768407 : Nat := 4983230072969 + 3 ^ 40 * 768407 * 2
def baseEnd_768407 : Nat := 263041419519653558519111

theorem tailTrace_768407 : CollatzResearch.WordTrace tailWord_768407 prefixEnd_768407 263041419519653558519111 := by
  unfold tailWord_768407
  simp only [CollatzResearch.WordTrace]
  refine ⟨28026105727200147312679475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18684070484800098208452983 28026105727200147312679475)
  ·
    refine ⟨42039158590800220969019213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28026105727200147312679475 42039158590800220969019213)
    ·
      refine ⟨15764684471550082863382205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 42039158590800220969019213 15764684471550082863382205)
      ·
        refine ⟨5911756676831281073768327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15764684471550082863382205 5911756676831281073768327)
        ·
          refine ⟨8867635015246921610652491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5911756676831281073768327 8867635015246921610652491)
          ·
            refine ⟨13301452522870382415978737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8867635015246921610652491 13301452522870382415978737)
            ·
              refine ⟨9976089392152786811984053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13301452522870382415978737 9976089392152786811984053)
              ·
                refine ⟨935258380514323763623505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 9976089392152786811984053 935258380514323763623505)
                ·
                  refine ⟨701443785385742822717629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 935258380514323763623505 701443785385742822717629)
                  ·
                    refine ⟨263041419519653558519111, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 701443785385742822717629 263041419519653558519111)
                    ·
                      rfl

theorem cell22_768407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 2, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 2, 5, 2, 3].length) (baseStart_768407 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_768407 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_768407 prefixEnd_768407 := by exact prefixLift 768407
  have htrace : WordTrace (prefixWord ++ tailWord_768407) baseStart_768407 baseEnd_768407 := by
    simpa [prefixWord, tailWord_768407, baseEnd_768407] using wordTrace_append hprefix tailTrace_768407
  have hstable : (prefixWord ++ tailWord_768407).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_768407).length < 2 ^ (prefixWord ++ tailWord_768407).sum := by decide
  have hdescent : baseEnd_768407 < baseStart_768407 := by decide
  rcases family_descends (prefixWord ++ tailWord_768407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_768424 : List Nat := [2, 1, 6, 1, 1, 1, 1, 2, 4, 3]
def baseStart_768424 : Nat := 118140960795 + 768424 * 2 ^ 59
def prefixEnd_768424 : Nat := 4983230072969 + 3 ^ 40 * 768424 * 2
def baseEnd_768424 : Nat := 263047238967071180844059

theorem tailTrace_768424 : CollatzResearch.WordTrace tailWord_768424 prefixEnd_768424 263047238967071180844059 := by
  unfold tailWord_768424
  simp only [CollatzResearch.WordTrace]
  refine ⟨14013362884069279608024163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18684483845425706144032217 14013362884069279608024163)
  ·
    refine ⟨21020044326103919412036245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14013362884069279608024163 21020044326103919412036245)
    ·
      refine ⟨985314577786121222439199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 21020044326103919412036245 985314577786121222439199)
      ·
        refine ⟨1477971866679181833658799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 985314577786121222439199 1477971866679181833658799)
        ·
          refine ⟨2216957800018772750488199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1477971866679181833658799 2216957800018772750488199)
          ·
            refine ⟨3325436700028159125732299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2216957800018772750488199 3325436700028159125732299)
            ·
              refine ⟨4988155050042238688598449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3325436700028159125732299 4988155050042238688598449)
              ·
                refine ⟨3741116287531679016448837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4988155050042238688598449 3741116287531679016448837)
                ·
                  refine ⟨701459303912189815584157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3741116287531679016448837 701459303912189815584157)
                  ·
                    refine ⟨263047238967071180844059, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 701459303912189815584157 263047238967071180844059)
                    ·
                      rfl

theorem cell22_768424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 1, 1, 2, 4, 3].length) (baseStart_768424 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_768424 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_768424 prefixEnd_768424 := by exact prefixLift 768424
  have htrace : WordTrace (prefixWord ++ tailWord_768424) baseStart_768424 baseEnd_768424 := by
    simpa [prefixWord, tailWord_768424, baseEnd_768424] using wordTrace_append hprefix tailTrace_768424
  have hstable : (prefixWord ++ tailWord_768424).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_768424).length < 2 ^ (prefixWord ++ tailWord_768424).sum := by decide
  have hdescent : baseEnd_768424 < baseStart_768424 := by decide
  rcases family_descends (prefixWord ++ tailWord_768424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_768437 : List Nat := [1, 3, 3, 2, 3, 2, 8]
def baseStart_768437 : Nat := 118140960795 + 768437 * 2 ^ 59
def prefixEnd_768437 : Nat := 4983230072969 + 3 ^ 40 * 768437 * 2
def baseEnd_768437 : Nat := 9742655153064573343297

theorem tailTrace_768437 : CollatzResearch.WordTrace tailWord_768437 prefixEnd_768437 9742655153064573343297 := by
  unfold tailWord_768437
  simp only [CollatzResearch.WordTrace]
  refine ⟨28027199917091462436271565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18684799944727641624181043 28027199917091462436271565)
  ·
    refine ⟨10510199968909298413601837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28027199917091462436271565 10510199968909298413601837)
    ·
      refine ⟨3941324988340986905100689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10510199968909298413601837 3941324988340986905100689)
      ·
        refine ⟨2955993741255740178825517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3941324988340986905100689 2955993741255740178825517)
        ·
          refine ⟨1108497652970902567059569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2955993741255740178825517 1108497652970902567059569)
          ·
            refine ⟨831373239728176925294677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1108497652970902567059569 831373239728176925294677)
            ·
              refine ⟨9742655153064573343297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 831373239728176925294677 9742655153064573343297)
              ·
                rfl

theorem cell22_768437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 3, 2, 8].length) (baseStart_768437 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_768437 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_768437 prefixEnd_768437 := by exact prefixLift 768437
  have htrace : WordTrace (prefixWord ++ tailWord_768437) baseStart_768437 baseEnd_768437 := by
    simpa [prefixWord, tailWord_768437, baseEnd_768437] using wordTrace_append hprefix tailTrace_768437
  have hstable : (prefixWord ++ tailWord_768437).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_768437).length < 2 ^ (prefixWord ++ tailWord_768437).sum := by decide
  have hdescent : baseEnd_768437 < baseStart_768437 := by decide
  rcases family_descends (prefixWord ++ tailWord_768437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_768580 : List Nat := [2, 3, 5, 1, 1, 1, 2, 2, 1, 4]
def baseStart_768580 : Nat := 118140960795 + 768580 * 2 ^ 59
def prefixEnd_768580 : Nat := 4983230072969 + 3 ^ 40 * 768580 * 2
def baseEnd_768580 : Nat := 263100640955138773943581

theorem tailTrace_768580 : CollatzResearch.WordTrace tailWord_768580 prefixEnd_768580 263100640955138773943581 := by
  unfold tailWord_768580
  simp only [CollatzResearch.WordTrace]
  refine ⟨14016207777786698929363597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18688277037048931905818129 14016207777786698929363597)
  ·
    refine ⟨5256077916670012098511349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14016207777786698929363597 5256077916670012098511349)
    ·
      refine ⟨492757304687813634235439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 5256077916670012098511349 492757304687813634235439)
      ·
        refine ⟨739135957031720451353159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 492757304687813634235439 739135957031720451353159)
        ·
          refine ⟨1108703935547580677029739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 739135957031720451353159 1108703935547580677029739)
          ·
            refine ⟨1663055903321371015544609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1108703935547580677029739 1663055903321371015544609)
            ·
              refine ⟨1247291927491028261658457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1663055903321371015544609 1247291927491028261658457)
              ·
                refine ⟨935468945618271196243843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1247291927491028261658457 935468945618271196243843)
                ·
                  refine ⟨1403203418427406794365765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 935468945618271196243843 1403203418427406794365765)
                  ·
                    refine ⟨263100640955138773943581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1403203418427406794365765 263100640955138773943581)
                    ·
                      rfl

theorem cell22_768580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 1, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 1, 1, 2, 2, 1, 4].length) (baseStart_768580 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_768580 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_768580 prefixEnd_768580 := by exact prefixLift 768580
  have htrace : WordTrace (prefixWord ++ tailWord_768580) baseStart_768580 baseEnd_768580 := by
    simpa [prefixWord, tailWord_768580, baseEnd_768580] using wordTrace_append hprefix tailTrace_768580
  have hstable : (prefixWord ++ tailWord_768580).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_768580).length < 2 ^ (prefixWord ++ tailWord_768580).sum := by decide
  have hdescent : baseEnd_768580 < baseStart_768580 := by decide
  rcases family_descends (prefixWord ++ tailWord_768580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_768589 : List Nat := [1, 6, 1, 1, 2, 2, 1, 8]
def baseStart_768589 : Nat := 118140960795 + 768589 * 2 ^ 59
def prefixEnd_768589 : Nat := 4983230072969 + 3 ^ 40 * 768589 * 2
def baseEnd_768589 : Nat := 29233746871007305607617

theorem tailTrace_768589 : CollatzResearch.WordTrace tailWord_768589 prefixEnd_768589 29233746871007305607617 := by
  unfold tailWord_768589
  simp only [CollatzResearch.WordTrace]
  refine ⟨28032743812540792395804821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18688495875027194930536547 28032743812540792395804821)
  ·
    refine ⟨1314034866212849643553351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 28032743812540792395804821 1314034866212849643553351)
    ·
      refine ⟨1971052299319274465330027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1314034866212849643553351 1971052299319274465330027)
      ·
        refine ⟨2956578448978911697995041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1971052299319274465330027 2956578448978911697995041)
        ·
          refine ⟨2217433836734183773496281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2956578448978911697995041 2217433836734183773496281)
          ·
            refine ⟨1663075377550637830122211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2217433836734183773496281 1663075377550637830122211)
            ·
              refine ⟨2494613066325956745183317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1663075377550637830122211 2494613066325956745183317)
              ·
                refine ⟨29233746871007305607617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 2494613066325956745183317 29233746871007305607617)
                ·
                  rfl

theorem cell22_768589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 2, 1, 8].length) (baseStart_768589 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_768589 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_768589 prefixEnd_768589 := by exact prefixLift 768589
  have htrace : WordTrace (prefixWord ++ tailWord_768589) baseStart_768589 baseEnd_768589 := by
    simpa [prefixWord, tailWord_768589, baseEnd_768589] using wordTrace_append hprefix tailTrace_768589
  have hstable : (prefixWord ++ tailWord_768589).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_768589).length < 2 ^ (prefixWord ++ tailWord_768589).sum := by decide
  have hdescent : baseEnd_768589 < baseStart_768589 := by decide
  rcases family_descends (prefixWord ++ tailWord_768589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_768617 : List Nat := [1, 2, 1, 1, 1, 4, 1, 6, 5]
def baseStart_768617 : Nat := 118140960795 + 768617 * 2 ^ 59
def prefixEnd_768617 : Nat := 4983230072969 + 3 ^ 40 * 768617 * 2
def baseEnd_768617 : Nat := 87704435603761003589489

theorem tailTrace_768617 : CollatzResearch.WordTrace tailWord_768617 prefixEnd_768617 87704435603761003589489 := by
  unfold tailWord_768617
  simp only [CollatzResearch.WordTrace]
  refine ⟨28033765056439353177824105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18689176704292902118549403 28033765056439353177824105)
  ·
    refine ⟨21025323792329514883368079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28033765056439353177824105 21025323792329514883368079)
    ·
      refine ⟨31537985688494272325052119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21025323792329514883368079 31537985688494272325052119)
      ·
        refine ⟨47306978532741408487578179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31537985688494272325052119 47306978532741408487578179)
        ·
          refine ⟨70960467799112112731367269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47306978532741408487578179 70960467799112112731367269)
          ·
            refine ⟨13305087712333521137131363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 70960467799112112731367269 13305087712333521137131363)
            ·
              refine ⟨19957631568500281705697045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13305087712333521137131363 19957631568500281705697045)
              ·
                refine ⟨935513979773450704954549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 19957631568500281705697045 935513979773450704954549)
                ·
                  refine ⟨87704435603761003589489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 935513979773450704954549 87704435603761003589489)
                  ·
                    rfl

theorem cell22_768617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 1, 6, 5].length) (baseStart_768617 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_768617 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_768617 prefixEnd_768617 := by exact prefixLift 768617
  have htrace : WordTrace (prefixWord ++ tailWord_768617) baseStart_768617 baseEnd_768617 := by
    simpa [prefixWord, tailWord_768617, baseEnd_768617] using wordTrace_append hprefix tailTrace_768617
  have hstable : (prefixWord ++ tailWord_768617).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_768617).length < 2 ^ (prefixWord ++ tailWord_768617).sum := by decide
  have hdescent : baseEnd_768617 < baseStart_768617 := by decide
  rcases family_descends (prefixWord ++ tailWord_768617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_768621 : List Nat := [1, 5, 1, 1, 3, 1, 3, 1, 3, 3]
def baseStart_768621 : Nat := 118140960795 + 768621 * 2 ^ 59
def prefixEnd_768621 : Nat := 4983230072969 + 3 ^ 40 * 768621 * 2
def baseEnd_768621 : Nat := 263114676093028333668455

theorem tailTrace_768621 : CollatzResearch.WordTrace tailWord_768621 prefixEnd_768621 263114676093028333668455 := by
  unfold tailWord_768621
  simp only [CollatzResearch.WordTrace]
  refine ⟨28033910948424861860969717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18689273965616574573979811 28033910948424861860969717)
  ·
    refine ⟨2628179151414830799465911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 28033910948424861860969717 2628179151414830799465911)
    ·
      refine ⟨3942268727122246199198867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2628179151414830799465911 3942268727122246199198867)
      ·
        refine ⟨5913403090683369298798301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3942268727122246199198867 5913403090683369298798301)
        ·
          refine ⟨2217526159006263487049363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5913403090683369298798301 2217526159006263487049363)
          ·
            refine ⟨3326289238509395230574045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2217526159006263487049363 3326289238509395230574045)
            ·
              refine ⟨1247358464441023211465267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3326289238509395230574045 1247358464441023211465267)
              ·
                refine ⟨1871037696661534817197901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1247358464441023211465267 1871037696661534817197901)
                ·
                  refine ⟨701639136248075556449213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1871037696661534817197901 701639136248075556449213)
                  ·
                    refine ⟨263114676093028333668455, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 701639136248075556449213 263114676093028333668455)
                    ·
                      rfl

theorem cell22_768621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 1, 3, 1, 3, 3].length) (baseStart_768621 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_768621 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_768621 prefixEnd_768621 := by exact prefixLift 768621
  have htrace : WordTrace (prefixWord ++ tailWord_768621) baseStart_768621 baseEnd_768621 := by
    simpa [prefixWord, tailWord_768621, baseEnd_768621] using wordTrace_append hprefix tailTrace_768621
  have hstable : (prefixWord ++ tailWord_768621).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_768621).length < 2 ^ (prefixWord ++ tailWord_768621).sum := by decide
  have hdescent : baseEnd_768621 < baseStart_768621 := by decide
  rcases family_descends (prefixWord ++ tailWord_768621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_768672 : List Nat := [2, 1, 1, 4, 5, 1, 2, 2, 1, 3]
def baseStart_768672 : Nat := 118140960795 + 768672 * 2 ^ 59
def prefixEnd_768672 : Nat := 4983230072969 + 3 ^ 40 * 768672 * 2
def baseEnd_768672 : Nat := 263132134435281200643299

theorem tailTrace_768672 : CollatzResearch.WordTrace tailWord_768672 prefixEnd_768672 263132134435281200643299 := by
  unfold tailWord_768672
  simp only [CollatzResearch.WordTrace]
  refine ⟨14017885535620048785538135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18690514047493398380717513 14017885535620048785538135)
  ·
    refine ⟨21026828303430073178307203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14017885535620048785538135 21026828303430073178307203)
    ·
      refine ⟨31540242455145109767460805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21026828303430073178307203 31540242455145109767460805)
      ·
        refine ⟨5913795460339708081398901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 31540242455145109767460805 5913795460339708081398901)
        ·
          refine ⟨554418324406847632631147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 5913795460339708081398901 554418324406847632631147)
          ·
            refine ⟨831627486610271448946721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 554418324406847632631147 831627486610271448946721)
            ·
              refine ⟨623720614957703586710041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 831627486610271448946721 623720614957703586710041)
              ·
                refine ⟨467790461218277690032531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 623720614957703586710041 467790461218277690032531)
                ·
                  refine ⟨701685691827416535048797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 467790461218277690032531 701685691827416535048797)
                  ·
                    refine ⟨263132134435281200643299, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 701685691827416535048797 263132134435281200643299)
                    ·
                      rfl

theorem cell22_768672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 5, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 5, 1, 2, 2, 1, 3].length) (baseStart_768672 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_768672 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_768672 prefixEnd_768672 := by exact prefixLift 768672
  have htrace : WordTrace (prefixWord ++ tailWord_768672) baseStart_768672 baseEnd_768672 := by
    simpa [prefixWord, tailWord_768672, baseEnd_768672] using wordTrace_append hprefix tailTrace_768672
  have hstable : (prefixWord ++ tailWord_768672).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_768672).length < 2 ^ (prefixWord ++ tailWord_768672).sum := by decide
  have hdescent : baseEnd_768672 < baseStart_768672 := by decide
  rcases family_descends (prefixWord ++ tailWord_768672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_768677 : List Nat := [1, 3, 1, 2, 1, 2, 1, 1, 5, 5]
def baseStart_768677 : Nat := 118140960795 + 768677 * 2 ^ 59
def prefixEnd_768677 : Nat := 4983230072969 + 3 ^ 40 * 768677 * 2
def baseEnd_768677 : Nat := 263133846037462854268283

theorem tailTrace_768677 : CollatzResearch.WordTrace tailWord_768677 prefixEnd_768677 263133846037462854268283 := by
  unfold tailWord_768677
  simp only [CollatzResearch.WordTrace]
  refine ⟨28035953436221983425008285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18690635624147988950005523 28035953436221983425008285)
  ·
    refine ⟨10513482538583243784378107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28035953436221983425008285 10513482538583243784378107)
    ·
      refine ⟨15770223807874865676567161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10513482538583243784378107 15770223807874865676567161)
      ·
        refine ⟨11827667855906149257425371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15770223807874865676567161 11827667855906149257425371)
        ·
          refine ⟨17741501783859223886138057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11827667855906149257425371 17741501783859223886138057)
          ·
            refine ⟨13306126337894417914603543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17741501783859223886138057 13306126337894417914603543)
            ·
              refine ⟨19959189506841626871905315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13306126337894417914603543 19959189506841626871905315)
              ·
                refine ⟨29938784260262440307857973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19959189506841626871905315 29938784260262440307857973)
                ·
                  refine ⟨2806761024399603778861685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 29938784260262440307857973 2806761024399603778861685)
                  ·
                    refine ⟨263133846037462854268283, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2806761024399603778861685 263133846037462854268283)
                    ·
                      rfl

theorem cell22_768677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 1, 1, 5, 5].length) (baseStart_768677 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_768677 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_768677 prefixEnd_768677 := by exact prefixLift 768677
  have htrace : WordTrace (prefixWord ++ tailWord_768677) baseStart_768677 baseEnd_768677 := by
    simpa [prefixWord, tailWord_768677, baseEnd_768677] using wordTrace_append hprefix tailTrace_768677
  have hstable : (prefixWord ++ tailWord_768677).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_768677).length < 2 ^ (prefixWord ++ tailWord_768677).sum := by decide
  have hdescent : baseEnd_768677 < baseStart_768677 := by decide
  rcases family_descends (prefixWord ++ tailWord_768677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_768728 : List Nat := [2, 1, 2, 2, 3, 4, 1, 2, 2, 3]
def baseStart_768728 : Nat := 118140960795 + 768728 * 2 ^ 59
def prefixEnd_768728 : Nat := 4983230072969 + 3 ^ 40 * 768728 * 2
def baseEnd_768728 : Nat := 263151304379715721243127

theorem tailTrace_768728 : CollatzResearch.WordTrace tailWord_768728 prefixEnd_768728 263151304379715721243127 := by
  unfold tailWord_768728
  simp only [CollatzResearch.WordTrace]
  refine ⟨14018906779518609567557419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18691875706024812756743225 14018906779518609567557419)
  ·
    refine ⟨21028360169277914351336129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14018906779518609567557419 21028360169277914351336129)
    ·
      refine ⟨15771270126958435763502097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21028360169277914351336129 15771270126958435763502097)
      ·
        refine ⟨11828452595218826822626573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15771270126958435763502097 11828452595218826822626573)
        ·
          refine ⟨4435669723207060058484965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11828452595218826822626573 4435669723207060058484965)
          ·
            refine ⟨831688073101323760965931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4435669723207060058484965 831688073101323760965931)
            ·
              refine ⟨1247532109651985641448897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 831688073101323760965931 1247532109651985641448897)
              ·
                refine ⟨935649082238989231086673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1247532109651985641448897 935649082238989231086673)
                ·
                  refine ⟨701736811679241923315005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 935649082238989231086673 701736811679241923315005)
                  ·
                    refine ⟨263151304379715721243127, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 701736811679241923315005 263151304379715721243127)
                    ·
                      rfl

theorem cell22_768728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 4, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 4, 1, 2, 2, 3].length) (baseStart_768728 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_768728 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_768728 prefixEnd_768728 := by exact prefixLift 768728
  have htrace : WordTrace (prefixWord ++ tailWord_768728) baseStart_768728 baseEnd_768728 := by
    simpa [prefixWord, tailWord_768728, baseEnd_768728] using wordTrace_append hprefix tailTrace_768728
  have hstable : (prefixWord ++ tailWord_768728).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_768728).length < 2 ^ (prefixWord ++ tailWord_768728).sum := by decide
  have hdescent : baseEnd_768728 < baseStart_768728 := by decide
  rcases family_descends (prefixWord ++ tailWord_768728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_768846 : List Nat := [4, 1, 1, 1, 1, 1, 1, 5, 4, 3]
def baseStart_768846 : Nat := 118140960795 + 768846 * 2 ^ 59
def prefixEnd_768846 : Nat := 4983230072969 + 3 ^ 40 * 768846 * 2
def baseEnd_768846 : Nat := 263191698191202746792765

theorem tailTrace_768846 : CollatzResearch.WordTrace tailWord_768846 prefixEnd_768846 263191698191202746792765 := by
  unfold tailWord_768846
  simp only [CollatzResearch.WordTrace]
  refine ⟨3505264671576215660988799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 18694744915073150191940261 3505264671576215660988799)
  ·
    refine ⟨5257897007364323491483199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3505264671576215660988799 5257897007364323491483199)
    ·
      refine ⟨7886845511046485237224799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5257897007364323491483199 7886845511046485237224799)
      ·
        refine ⟨11830268266569727855837199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7886845511046485237224799 11830268266569727855837199)
        ·
          refine ⟨17745402399854591783755799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11830268266569727855837199 17745402399854591783755799)
          ·
            refine ⟨26618103599781887675633699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17745402399854591783755799 26618103599781887675633699)
            ·
              refine ⟨39927155399672831513450549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26618103599781887675633699 39927155399672831513450549)
              ·
                refine ⟨3743170818719327954385989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 39927155399672831513450549 3743170818719327954385989)
                ·
                  refine ⟨701844528509873991447373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3743170818719327954385989 701844528509873991447373)
                  ·
                    refine ⟨263191698191202746792765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 701844528509873991447373 263191698191202746792765)
                    ·
                      rfl

theorem cell22_768846_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 1, 5, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 1, 5, 4, 3].length) (baseStart_768846 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_768846 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_768846 prefixEnd_768846 := by exact prefixLift 768846
  have htrace : WordTrace (prefixWord ++ tailWord_768846) baseStart_768846 baseEnd_768846 := by
    simpa [prefixWord, tailWord_768846, baseEnd_768846] using wordTrace_append hprefix tailTrace_768846
  have hstable : (prefixWord ++ tailWord_768846).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_768846).length < 2 ^ (prefixWord ++ tailWord_768846).sum := by decide
  have hdescent : baseEnd_768846 < baseStart_768846 := by decide
  rcases family_descends (prefixWord ++ tailWord_768846) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_768848 : List Nat := [2, 1, 1, 1, 1, 4, 6, 2, 4]
def baseStart_768848 : Nat := 118140960795 + 768848 * 2 ^ 59
def prefixEnd_768848 : Nat := 4983230072969 + 3 ^ 40 * 768848 * 2
def baseEnd_768848 : Nat := 87730794277358469414253

theorem tailTrace_768848 : CollatzResearch.WordTrace tailWord_768848 prefixEnd_768848 87730794277358469414253 := by
  unfold tailWord_768848
  simp only [CollatzResearch.WordTrace]
  refine ⟨14021095159301239814741599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18694793545734986419655465 14021095159301239814741599)
  ·
    refine ⟨21031642738951859722112399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14021095159301239814741599 21031642738951859722112399)
    ·
      refine ⟨31547464108427789583168599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21031642738951859722112399 31547464108427789583168599)
      ·
        refine ⟨47321196162641684374752899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31547464108427789583168599 47321196162641684374752899)
        ·
          refine ⟨70981794243962526562129349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47321196162641684374752899 70981794243962526562129349)
          ·
            refine ⟨13309086420742973730399253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 70981794243962526562129349 13309086420742973730399253)
            ·
              refine ⟨623863425972326893612465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 13309086420742973730399253 623863425972326893612465)
              ·
                refine ⟨467897569479245170209349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 623863425972326893612465 467897569479245170209349)
                ·
                  refine ⟨87730794277358469414253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 467897569479245170209349 87730794277358469414253)
                  ·
                    rfl

theorem cell22_768848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 6, 2, 4].length) (baseStart_768848 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_768848 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_768848 prefixEnd_768848 := by exact prefixLift 768848
  have htrace : WordTrace (prefixWord ++ tailWord_768848) baseStart_768848 baseEnd_768848 := by
    simpa [prefixWord, tailWord_768848, baseEnd_768848] using wordTrace_append hprefix tailTrace_768848
  have hstable : (prefixWord ++ tailWord_768848).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_768848).length < 2 ^ (prefixWord ++ tailWord_768848).sum := by decide
  have hdescent : baseEnd_768848 < baseStart_768848 := by decide
  rcases family_descends (prefixWord ++ tailWord_768848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_768876 : List Nat := [2, 2, 1, 1, 4, 1, 5, 6]
def baseStart_768876 : Nat := 118140960795 + 768876 * 2 ^ 59
def prefixEnd_768876 : Nat := 4983230072969 + 3 ^ 40 * 768876 * 2
def baseEnd_768876 : Nat := 29244663089365852060297

theorem tailTrace_768876 : CollatzResearch.WordTrace tailWord_768876 prefixEnd_768876 29244663089365852060297 := by
  unfold tailWord_768876
  simp only [CollatzResearch.WordTrace]
  refine ⟨14021605781250520205751241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18695474375000693607668321 14021605781250520205751241)
  ·
    refine ⟨10516204335937890154313431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14021605781250520205751241 10516204335937890154313431)
    ·
      refine ⟨15774306503906835231470147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10516204335937890154313431 15774306503906835231470147)
      ·
        refine ⟨23661459755860252847205221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15774306503906835231470147 23661459755860252847205221)
        ·
          refine ⟨4436523704223797408850979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 23661459755860252847205221 4436523704223797408850979)
          ·
            refine ⟨6654785556335696113276469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4436523704223797408850979 6654785556335696113276469)
            ·
              refine ⟨623886145906471510619669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 6654785556335696113276469 623886145906471510619669)
              ·
                refine ⟨29244663089365852060297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 623886145906471510619669 29244663089365852060297)
                ·
                  rfl

theorem cell22_768876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 5, 6].length) (baseStart_768876 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_768876 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_768876 prefixEnd_768876 := by exact prefixLift 768876
  have htrace : WordTrace (prefixWord ++ tailWord_768876) baseStart_768876 baseEnd_768876 := by
    simpa [prefixWord, tailWord_768876, baseEnd_768876] using wordTrace_append hprefix tailTrace_768876
  have hstable : (prefixWord ++ tailWord_768876).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_768876).length < 2 ^ (prefixWord ++ tailWord_768876).sum := by decide
  have hdescent : baseEnd_768876 < baseStart_768876 := by decide
  rcases family_descends (prefixWord ++ tailWord_768876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_768878 : List Nat := [4, 1, 2, 3, 2, 1, 1, 1, 1, 6]
def baseStart_768878 : Nat := 118140960795 + 768878 * 2 ^ 59
def prefixEnd_768878 : Nat := 4983230072969 + 3 ^ 40 * 768878 * 2
def baseEnd_768878 : Nat := 263202652445165329992667

theorem tailTrace_768878 : CollatzResearch.WordTrace tailWord_768878 prefixEnd_768878 263202652445165329992667 := by
  unfold tailWord_768878
  simp only [CollatzResearch.WordTrace]
  refine ⟨3505410563561724344134411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 18695523005662529835383525 3505410563561724344134411)
  ·
    refine ⟨5258115845342586516201617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3505410563561724344134411 5258115845342586516201617)
    ·
      refine ⟨3943586884006939887151213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5258115845342586516201617 3943586884006939887151213)
      ·
        refine ⟨1478845081502602457681705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3943586884006939887151213 1478845081502602457681705)
        ·
          refine ⟨1109133811126951843261279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1478845081502602457681705 1109133811126951843261279)
          ·
            refine ⟨1663700716690427764891919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1109133811126951843261279 1663700716690427764891919)
            ·
              refine ⟨2495551075035641647337879, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1663700716690427764891919 2495551075035641647337879)
              ·
                refine ⟨3743326612553462471006819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2495551075035641647337879 3743326612553462471006819)
                ·
                  refine ⟨5614989918830193706510229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3743326612553462471006819 5614989918830193706510229)
                  ·
                    refine ⟨263202652445165329992667, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5614989918830193706510229 263202652445165329992667)
                    ·
                      rfl

theorem cell22_768878_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 2, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 2, 1, 1, 1, 1, 6].length) (baseStart_768878 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_768878 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_768878 prefixEnd_768878 := by exact prefixLift 768878
  have htrace : WordTrace (prefixWord ++ tailWord_768878) baseStart_768878 baseEnd_768878 := by
    simpa [prefixWord, tailWord_768878, baseEnd_768878] using wordTrace_append hprefix tailTrace_768878
  have hstable : (prefixWord ++ tailWord_768878).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_768878).length < 2 ^ (prefixWord ++ tailWord_768878).sum := by decide
  have hdescent : baseEnd_768878 < baseStart_768878 := by decide
  rcases family_descends (prefixWord ++ tailWord_768878) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_768985 : List Nat := [1, 2, 1, 2, 5, 3, 1, 2, 1, 4]
def baseStart_768985 : Nat := 118140960795 + 768985 * 2 ^ 59
def prefixEnd_768985 : Nat := 4983230072969 + 3 ^ 40 * 768985 * 2
def baseEnd_768985 : Nat := 263239280731852717567339

theorem tailTrace_768985 : CollatzResearch.WordTrace tailWord_768985 prefixEnd_768985 263239280731852717567339 := by
  unfold tailWord_768985
  simp only [CollatzResearch.WordTrace]
  refine ⟨28047187119106152027220409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18698124746070768018146939 28047187119106152027220409)
  ·
    refine ⟨21035390339329614020415307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28047187119106152027220409 21035390339329614020415307)
    ·
      refine ⟨31553085508994421030622961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21035390339329614020415307 31553085508994421030622961)
      ·
        refine ⟨23664814131745815772967221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31553085508994421030622961 23664814131745815772967221)
        ·
          refine ⟨2218576324851170228715677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 23664814131745815772967221 2218576324851170228715677)
          ·
            refine ⟨831966121819188835768379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2218576324851170228715677 831966121819188835768379)
            ·
              refine ⟨1247949182728783253652569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 831966121819188835768379 1247949182728783253652569)
              ·
                refine ⟨935961887046587440239427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1247949182728783253652569 935961887046587440239427)
                ·
                  refine ⟨1403942830569881160359141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 935961887046587440239427 1403942830569881160359141)
                  ·
                    refine ⟨263239280731852717567339, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1403942830569881160359141 263239280731852717567339)
                    ·
                      rfl

theorem cell22_768985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 3, 1, 2, 1, 4].length) (baseStart_768985 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_768985 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_768985 prefixEnd_768985 := by exact prefixLift 768985
  have htrace : WordTrace (prefixWord ++ tailWord_768985) baseStart_768985 baseEnd_768985 := by
    simpa [prefixWord, tailWord_768985, baseEnd_768985] using wordTrace_append hprefix tailTrace_768985
  have hstable : (prefixWord ++ tailWord_768985).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_768985).length < 2 ^ (prefixWord ++ tailWord_768985).sum := by decide
  have hdescent : baseEnd_768985 < baseStart_768985 := by decide
  rcases family_descends (prefixWord ++ tailWord_768985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_769131 : List Nat := [1, 1, 1, 1, 2, 2, 1, 1, 2, 10]
def baseStart_769131 : Nat := 118140960795 + 769131 * 2 ^ 59
def prefixEnd_769131 : Nat := 4983230072969 + 3 ^ 40 * 769131 * 2
def baseEnd_769131 : Nat := 263289259515557003416891

theorem tailTrace_769131 : CollatzResearch.WordTrace tailWord_769131 prefixEnd_769131 263289259515557003416891 := by
  unfold tailWord_769131
  simp only [CollatzResearch.WordTrace]
  refine ⟨28052512176577218962035247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18701674784384812641356831 28052512176577218962035247)
  ·
    refine ⟨42078768264865828443052871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28052512176577218962035247 42078768264865828443052871)
    ·
      refine ⟨63118152397298742664579307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42078768264865828443052871 63118152397298742664579307)
      ·
        refine ⟨94677228595948113996868961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63118152397298742664579307 94677228595948113996868961)
        ·
          refine ⟨71007921446961085497651721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 94677228595948113996868961 71007921446961085497651721)
          ·
            refine ⟨53255941085220814123238791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 71007921446961085497651721 53255941085220814123238791)
            ·
              refine ⟨79883911627831221184858187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53255941085220814123238791 79883911627831221184858187)
              ·
                refine ⟨119825867441746831777287281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 79883911627831221184858187 119825867441746831777287281)
                ·
                  refine ⟨89869400581310123832965461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 119825867441746831777287281 89869400581310123832965461)
                  ·
                    refine ⟨263289259515557003416891, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 89869400581310123832965461 263289259515557003416891)
                    ·
                      rfl

theorem cell22_769131_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 1, 2, 10].length) (baseStart_769131 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_769131 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_769131 prefixEnd_769131 := by exact prefixLift 769131
  have htrace : WordTrace (prefixWord ++ tailWord_769131) baseStart_769131 baseEnd_769131 := by
    simpa [prefixWord, tailWord_769131, baseEnd_769131] using wordTrace_append hprefix tailTrace_769131
  have hstable : (prefixWord ++ tailWord_769131).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_769131).length < 2 ^ (prefixWord ++ tailWord_769131).sum := by decide
  have hdescent : baseEnd_769131 < baseStart_769131 := by decide
  rcases family_descends (prefixWord ++ tailWord_769131) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_769141 : List Nat := [1, 3, 4, 3, 2, 1, 2, 1, 5]
def baseStart_769141 : Nat := 118140960795 + 769141 * 2 ^ 59
def prefixEnd_769141 : Nat := 4983230072969 + 3 ^ 40 * 769141 * 2
def baseEnd_769141 : Nat := 87764227573306770222287

theorem tailTrace_769141 : CollatzResearch.WordTrace tailWord_769141 prefixEnd_769141 87764227573306770222287 := by
  unfold tailWord_769141
  simp only [CollatzResearch.WordTrace]
  refine ⟨28052876906540990669899277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18701917937693993779932851 28052876906540990669899277)
  ·
    refine ⟨10519828839952871501212229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28052876906540990669899277 10519828839952871501212229)
    ·
      refine ⟨1972467907491163406477293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 10519828839952871501212229 1972467907491163406477293)
      ·
        refine ⟨739675465309186277428985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1972467907491163406477293 739675465309186277428985)
        ·
          refine ⟨554756598981889708071739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 739675465309186277428985 554756598981889708071739)
          ·
            refine ⟨832134898472834562107609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 554756598981889708071739 832134898472834562107609)
            ·
              refine ⟨624101173854625921580707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 832134898472834562107609 624101173854625921580707)
              ·
                refine ⟨936151760781938882371061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 624101173854625921580707 936151760781938882371061)
                ·
                  refine ⟨87764227573306770222287, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 936151760781938882371061 87764227573306770222287)
                  ·
                    rfl

theorem cell22_769141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 2, 1, 2, 1, 5].length) (baseStart_769141 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_769141 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_769141 prefixEnd_769141 := by exact prefixLift 769141
  have htrace : WordTrace (prefixWord ++ tailWord_769141) baseStart_769141 baseEnd_769141 := by
    simpa [prefixWord, tailWord_769141, baseEnd_769141] using wordTrace_append hprefix tailTrace_769141
  have hstable : (prefixWord ++ tailWord_769141).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_769141).length < 2 ^ (prefixWord ++ tailWord_769141).sum := by decide
  have hdescent : baseEnd_769141 < baseStart_769141 := by decide
  rcases family_descends (prefixWord ++ tailWord_769141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_769148 : List Nat := [2, 2, 2, 1, 1, 3, 1, 2, 4, 4]
def baseStart_769148 : Nat := 118140960795 + 769148 * 2 ^ 59
def prefixEnd_769148 : Nat := 4983230072969 + 3 ^ 40 * 769148 * 2
def baseEnd_769148 : Nat := 263295078962974625741839

theorem tailTrace_769148 : CollatzResearch.WordTrace tailWord_769148 prefixEnd_769148 263295078962974625741839 := by
  unfold tailWord_769148
  simp only [CollatzResearch.WordTrace]
  refine ⟨14026566108757815432702049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18702088145010420576936065 14026566108757815432702049)
  ·
    refine ⟨10519924581568361574526537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14026566108757815432702049 10519924581568361574526537)
    ·
      refine ⟨7889943436176271180894903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10519924581568361574526537 7889943436176271180894903)
      ·
        refine ⟨11834915154264406771342355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7889943436176271180894903 11834915154264406771342355)
        ·
          refine ⟨17752372731396610157013533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11834915154264406771342355 17752372731396610157013533)
          ·
            refine ⟨6657139774273728808880075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17752372731396610157013533 6657139774273728808880075)
            ·
              refine ⟨9985709661410593213320113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6657139774273728808880075 9985709661410593213320113)
              ·
                refine ⟨7489282246057944909990085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9985709661410593213320113 7489282246057944909990085)
                ·
                  refine ⟨1404240421135864670623141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7489282246057944909990085 1404240421135864670623141)
                  ·
                    refine ⟨263295078962974625741839, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1404240421135864670623141 263295078962974625741839)
                    ·
                      rfl

theorem cell22_769148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 1, 2, 4, 4].length) (baseStart_769148 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_769148 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_769148 prefixEnd_769148 := by exact prefixLift 769148
  have htrace : WordTrace (prefixWord ++ tailWord_769148) baseStart_769148 baseEnd_769148 := by
    simpa [prefixWord, tailWord_769148, baseEnd_769148] using wordTrace_append hprefix tailTrace_769148
  have hstable : (prefixWord ++ tailWord_769148).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_769148).length < 2 ^ (prefixWord ++ tailWord_769148).sum := by decide
  have hdescent : baseEnd_769148 < baseStart_769148 := by decide
  rcases family_descends (prefixWord ++ tailWord_769148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_769182 : List Nat := [4, 3, 1, 1, 2, 1, 2, 2, 2, 4]
def baseStart_769182 : Nat := 118140960795 + 769182 * 2 ^ 59
def prefixEnd_769182 : Nat := 4983230072969 + 3 ^ 40 * 769182 * 2
def baseEnd_769182 : Nat := 263306717857809870391735

theorem tailTrace_769182 : CollatzResearch.WordTrace tailWord_769182 prefixEnd_769182 263306717857809870391735 := by
  unfold tailWord_769182
  simp only [CollatzResearch.WordTrace]
  refine ⟨3506796537424056834017725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 18702914866261636448094533 3506796537424056834017725)
  ·
    refine ⟨1315048701534021312756647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3506796537424056834017725 1315048701534021312756647)
    ·
      refine ⟨1972573052301031969134971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1315048701534021312756647 1972573052301031969134971)
      ·
        refine ⟨2958859578451547953702457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1972573052301031969134971 2958859578451547953702457)
        ·
          refine ⟨2219144683838660965276843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2958859578451547953702457 2219144683838660965276843)
          ·
            refine ⟨3328717025757991447915265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2219144683838660965276843 3328717025757991447915265)
            ·
              refine ⟨2496537769318493585936449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3328717025757991447915265 2496537769318493585936449)
              ·
                refine ⟨1872403326988870189452337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2496537769318493585936449 1872403326988870189452337)
                ·
                  refine ⟨1404302495241652642089253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1872403326988870189452337 1404302495241652642089253)
                  ·
                    refine ⟨263306717857809870391735, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1404302495241652642089253 263306717857809870391735)
                    ·
                      rfl

theorem cell22_769182_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 1, 2, 2, 2, 4].length) (baseStart_769182 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_769182 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_769182 prefixEnd_769182 := by exact prefixLift 769182
  have htrace : WordTrace (prefixWord ++ tailWord_769182) baseStart_769182 baseEnd_769182 := by
    simpa [prefixWord, tailWord_769182, baseEnd_769182] using wordTrace_append hprefix tailTrace_769182
  have hstable : (prefixWord ++ tailWord_769182).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_769182).length < 2 ^ (prefixWord ++ tailWord_769182).sum := by decide
  have hdescent : baseEnd_769182 < baseStart_769182 := by decide
  rcases family_descends (prefixWord ++ tailWord_769182) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_769186 : List Nat := [3, 3, 1, 3, 2, 2, 2, 2, 4]
def baseStart_769186 : Nat := 118140960795 + 769186 * 2 ^ 59
def prefixEnd_769186 : Nat := 4983230072969 + 3 ^ 40 * 769186 * 2
def baseEnd_769186 : Nat := 87769362379851731097241

theorem tailTrace_769186 : CollatzResearch.WordTrace tailWord_769186 prefixEnd_769186 87769362379851731097241 := by
  unfold tailWord_769186
  simp only [CollatzResearch.WordTrace]
  refine ⟨7013629547844490838821853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18703012127585308903524941 7013629547844490838821853)
  ·
    refine ⟨2630111080441684064558195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7013629547844490838821853 2630111080441684064558195)
    ·
      refine ⟨3945166620662526096837293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2630111080441684064558195 3945166620662526096837293)
      ·
        refine ⟨1479437482748447286313985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3945166620662526096837293 1479437482748447286313985)
        ·
          refine ⟨1109578112061335464735489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1479437482748447286313985 1109578112061335464735489)
          ·
            refine ⟨832183584046001598551617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1109578112061335464735489 832183584046001598551617)
            ·
              refine ⟨624137688034501198913713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 832183584046001598551617 624137688034501198913713)
              ·
                refine ⟨468103266025875899185285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 624137688034501198913713 468103266025875899185285)
                ·
                  refine ⟨87769362379851731097241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 468103266025875899185285 87769362379851731097241)
                  ·
                    rfl

theorem cell22_769186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 2, 2, 2, 2, 4].length) (baseStart_769186 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_769186 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_769186 prefixEnd_769186 := by exact prefixLift 769186
  have htrace : WordTrace (prefixWord ++ tailWord_769186) baseStart_769186 baseEnd_769186 := by
    simpa [prefixWord, tailWord_769186, baseEnd_769186] using wordTrace_append hprefix tailTrace_769186
  have hstable : (prefixWord ++ tailWord_769186).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_769186).length < 2 ^ (prefixWord ++ tailWord_769186).sum := by decide
  have hdescent : baseEnd_769186 < baseStart_769186 := by decide
  rcases family_descends (prefixWord ++ tailWord_769186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_769197 : List Nat := [1, 5, 2, 1, 3, 2, 1, 7]
def baseStart_769197 : Nat := 118140960795 + 769197 * 2 ^ 59
def prefixEnd_769197 : Nat := 4983230072969 + 3 ^ 40 * 769197 * 2
def baseEnd_769197 : Nat := 29256872518261647918521

theorem tailTrace_769197 : CollatzResearch.WordTrace tailWord_769197 prefixEnd_769197 29256872518261647918521 := by
  unfold tailWord_769197
  simp only [CollatzResearch.WordTrace]
  refine ⟨28054919394338112233937845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18703279596225408155958563 28054919394338112233937845)
  ·
    refine ⟨2630148693219198021931673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 28054919394338112233937845 2630148693219198021931673)
    ·
      refine ⟨1972611519914398516448755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2630148693219198021931673 1972611519914398516448755)
      ·
        refine ⟨2958917279871597774673133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1972611519914398516448755 2958917279871597774673133)
        ·
          refine ⟨1109593979951849165502425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2958917279871597774673133 1109593979951849165502425)
          ·
            refine ⟨832195484963886874126819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1109593979951849165502425 832195484963886874126819)
            ·
              refine ⟨1248293227445830311190229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 832195484963886874126819 1248293227445830311190229)
              ·
                refine ⟨29256872518261647918521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1248293227445830311190229 29256872518261647918521)
                ·
                  rfl

theorem cell22_769197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 3, 2, 1, 7].length) (baseStart_769197 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_769197 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_769197 prefixEnd_769197 := by exact prefixLift 769197
  have htrace : WordTrace (prefixWord ++ tailWord_769197) baseStart_769197 baseEnd_769197 := by
    simpa [prefixWord, tailWord_769197, baseEnd_769197] using wordTrace_append hprefix tailTrace_769197
  have hstable : (prefixWord ++ tailWord_769197).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_769197).length < 2 ^ (prefixWord ++ tailWord_769197).sum := by decide
  have hdescent : baseEnd_769197 < baseStart_769197 := by decide
  rcases family_descends (prefixWord ++ tailWord_769197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_769212 : List Nat := [2, 2, 2, 3, 2, 2, 1, 2, 3, 3]
def baseStart_769212 : Nat := 118140960795 + 769212 * 2 ^ 59
def prefixEnd_769212 : Nat := 4983230072969 + 3 ^ 40 * 769212 * 2
def baseEnd_769212 : Nat := 263316987470899792141643

theorem tailTrace_769212 : CollatzResearch.WordTrace tailWord_769212 prefixEnd_769212 263316987470899792141643 := by
  unfold tailWord_769212
  simp only [CollatzResearch.WordTrace]
  refine ⟨14027733244641884897866945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18703644326189179863822593 14027733244641884897866945)
  ·
    refine ⟨10520799933481413673400209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14027733244641884897866945 10520799933481413673400209)
    ·
      refine ⟨7890599950111060255050157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10520799933481413673400209 7890599950111060255050157)
      ·
        refine ⟨2958974981291647595643809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7890599950111060255050157 2958974981291647595643809)
        ·
          refine ⟨2219231235968735696732857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2958974981291647595643809 2219231235968735696732857)
          ·
            refine ⟨1664423426976551772549643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2219231235968735696732857 1664423426976551772549643)
            ·
              refine ⟨2496635140464827658824465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1664423426976551772549643 2496635140464827658824465)
              ·
                refine ⟨1872476355348620744118349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2496635140464827658824465 1872476355348620744118349)
                ·
                  refine ⟨702178633255732779044381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1872476355348620744118349 702178633255732779044381)
                  ·
                    refine ⟨263316987470899792141643, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 702178633255732779044381 263316987470899792141643)
                    ·
                      rfl

theorem cell22_769212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 2, 1, 2, 3, 3].length) (baseStart_769212 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_769212 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_769212 prefixEnd_769212 := by exact prefixLift 769212
  have htrace : WordTrace (prefixWord ++ tailWord_769212) baseStart_769212 baseEnd_769212 := by
    simpa [prefixWord, tailWord_769212, baseEnd_769212] using wordTrace_append hprefix tailTrace_769212
  have hstable : (prefixWord ++ tailWord_769212).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_769212).length < 2 ^ (prefixWord ++ tailWord_769212).sum := by decide
  have hdescent : baseEnd_769212 < baseStart_769212 := by decide
  rcases family_descends (prefixWord ++ tailWord_769212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_769285 : List Nat := [1, 3, 1, 1, 2, 1, 3, 1, 6, 3]
def baseStart_769285 : Nat := 118140960795 + 769285 * 2 ^ 59
def prefixEnd_769285 : Nat := 4983230072969 + 3 ^ 40 * 769285 * 2
def baseEnd_769285 : Nat := 263341976862751935066419

theorem tailTrace_769285 : CollatzResearch.WordTrace tailWord_769285 prefixEnd_769285 263341976862751935066419 := by
  unfold tailWord_769285
  simp only [CollatzResearch.WordTrace]
  refine ⟨28058129018019303263141309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18705419345346202175427539 28058129018019303263141309)
  ·
    refine ⟨10521798381757238723677991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28058129018019303263141309 10521798381757238723677991)
    ·
      refine ⟨15782697572635858085516987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10521798381757238723677991 15782697572635858085516987)
      ·
        refine ⟨23674046358953787128275481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15782697572635858085516987 23674046358953787128275481)
        ·
          refine ⟨17755534769215340346206611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23674046358953787128275481 17755534769215340346206611)
          ·
            refine ⟨26633302153823010519309917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17755534769215340346206611 26633302153823010519309917)
            ·
              refine ⟨9987488307683628944741219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26633302153823010519309917 9987488307683628944741219)
              ·
                refine ⟨14981232461525443417111829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9987488307683628944741219 14981232461525443417111829)
                ·
                  refine ⟨702245271634005160177117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 14981232461525443417111829 702245271634005160177117)
                  ·
                    refine ⟨263341976862751935066419, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 702245271634005160177117 263341976862751935066419)
                    ·
                      rfl

theorem cell22_769285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 3, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 3, 1, 6, 3].length) (baseStart_769285 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_769285 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_769285 prefixEnd_769285 := by exact prefixLift 769285
  have htrace : WordTrace (prefixWord ++ tailWord_769285) baseStart_769285 baseEnd_769285 := by
    simpa [prefixWord, tailWord_769285, baseEnd_769285] using wordTrace_append hprefix tailTrace_769285
  have hstable : (prefixWord ++ tailWord_769285).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_769285).length < 2 ^ (prefixWord ++ tailWord_769285).sum := by decide
  have hdescent : baseEnd_769285 < baseStart_769285 := by decide
  rcases family_descends (prefixWord ++ tailWord_769285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_769304 : List Nat := [2, 1, 2, 3, 1, 4, 3, 2, 4]
def baseStart_769304 : Nat := 118140960795 + 769304 * 2 ^ 59
def prefixEnd_769304 : Nat := 4983230072969 + 3 ^ 40 * 769304 * 2
def baseEnd_769304 : Nat := 87782826983680739613787

theorem tailTrace_769304 : CollatzResearch.WordTrace tailWord_769304 prefixEnd_769304 87782826983680739613787 := by
  unfold tailWord_769304
  simp only [CollatzResearch.WordTrace]
  refine ⟨14029411002475234754041483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18705881336633646338721977 14029411002475234754041483)
  ·
    refine ⟨21044116503712852131062225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14029411002475234754041483 21044116503712852131062225)
    ·
      refine ⟨15783087377784639098296669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21044116503712852131062225 15783087377784639098296669)
      ·
        refine ⟨5918657766669239661861251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15783087377784639098296669 5918657766669239661861251)
        ·
          refine ⟨8877986650003859492791877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5918657766669239661861251 8877986650003859492791877)
          ·
            refine ⟨1664622496875723654898477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8877986650003859492791877 1664622496875723654898477)
            ·
              refine ⟨624233436328396370586929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1664622496875723654898477 624233436328396370586929)
              ·
                refine ⟨468175077246297277940197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 624233436328396370586929 468175077246297277940197)
                ·
                  refine ⟨87782826983680739613787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 468175077246297277940197 87782826983680739613787)
                  ·
                    rfl

theorem cell22_769304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 4, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 4, 3, 2, 4].length) (baseStart_769304 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_769304 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_769304 prefixEnd_769304 := by exact prefixLift 769304
  have htrace : WordTrace (prefixWord ++ tailWord_769304) baseStart_769304 baseEnd_769304 := by
    simpa [prefixWord, tailWord_769304, baseEnd_769304] using wordTrace_append hprefix tailTrace_769304
  have hstable : (prefixWord ++ tailWord_769304).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_769304).length < 2 ^ (prefixWord ++ tailWord_769304).sum := by decide
  have hdescent : baseEnd_769304 < baseStart_769304 := by decide
  rcases family_descends (prefixWord ++ tailWord_769304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_769315 : List Nat := [1, 1, 1, 4, 2, 4, 2, 7]
def baseStart_769315 : Nat := 118140960795 + 769315 * 2 ^ 59
def prefixEnd_769315 : Nat := 4983230072969 + 3 ^ 40 * 769315 * 2
def baseEnd_769315 : Nat := 29261360719537984090703

theorem tailTrace_769315 : CollatzResearch.WordTrace tailWord_769315 prefixEnd_769315 29261360719537984090703 := by
  unfold tailWord_769315
  simp only [CollatzResearch.WordTrace]
  refine ⟨28059223207910618386733399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18706148805273745591155599 28059223207910618386733399)
  ·
    refine ⟨42088834811865927580100099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28059223207910618386733399 42088834811865927580100099)
    ·
      refine ⟨63133252217798891370150149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42088834811865927580100099 63133252217798891370150149)
      ·
        refine ⟨11837484790837292131903153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 63133252217798891370150149 11837484790837292131903153)
        ·
          refine ⟨8878113593127969098927365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11837484790837292131903153 8878113593127969098927365)
          ·
            refine ⟨1664646298711494206048881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8878113593127969098927365 1664646298711494206048881)
            ·
              refine ⟨1248484724033620654536661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1664646298711494206048881 1248484724033620654536661)
              ·
                refine ⟨29261360719537984090703, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1248484724033620654536661 29261360719537984090703)
                ·
                  rfl

theorem cell22_769315_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 4, 2, 7].length) (baseStart_769315 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_769315 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_769315 prefixEnd_769315 := by exact prefixLift 769315
  have htrace : WordTrace (prefixWord ++ tailWord_769315) baseStart_769315 baseEnd_769315 := by
    simpa [prefixWord, tailWord_769315, baseEnd_769315] using wordTrace_append hprefix tailTrace_769315
  have hstable : (prefixWord ++ tailWord_769315).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_769315).length < 2 ^ (prefixWord ++ tailWord_769315).sum := by decide
  have hdescent : baseEnd_769315 < baseStart_769315 := by decide
  rcases family_descends (prefixWord ++ tailWord_769315) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_769405 : List Nat := [1, 4, 1, 1, 2, 2, 1, 2, 8]
def baseStart_769405 : Nat := 118140960795 + 769405 * 2 ^ 59
def prefixEnd_769405 : Nat := 4983230072969 + 3 ^ 40 * 769405 * 2
def baseEnd_769405 : Nat := 87794351771703874022017

theorem tailTrace_769405 : CollatzResearch.WordTrace tailWord_769405 prefixEnd_769405 87794351771703874022017 := by
  unfold tailWord_769405
  simp only [CollatzResearch.WordTrace]
  refine ⟨28062505777584563757509669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18708337185056375838339779 28062505777584563757509669)
  ·
    refine ⟨5261719833297105704533063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 28062505777584563757509669 5261719833297105704533063)
    ·
      refine ⟨7892579749945658556799595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5261719833297105704533063 7892579749945658556799595)
      ·
        refine ⟨11838869624918487835199393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7892579749945658556799595 11838869624918487835199393)
        ·
          refine ⟨8879152218688865876399545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11838869624918487835199393 8879152218688865876399545)
          ·
            refine ⟨6659364164016649407299659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8879152218688865876399545 6659364164016649407299659)
            ·
              refine ⟨9989046246024974110949489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6659364164016649407299659 9989046246024974110949489)
              ·
                refine ⟨7491784684518730583212117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9989046246024974110949489 7491784684518730583212117)
                ·
                  refine ⟨87794351771703874022017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 7491784684518730583212117 87794351771703874022017)
                  ·
                    rfl

theorem cell22_769405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 1, 2, 8].length) (baseStart_769405 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_769405 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_769405 prefixEnd_769405 := by exact prefixLift 769405
  have htrace : WordTrace (prefixWord ++ tailWord_769405) baseStart_769405 baseEnd_769405 := by
    simpa [prefixWord, tailWord_769405, baseEnd_769405] using wordTrace_append hprefix tailTrace_769405
  have hstable : (prefixWord ++ tailWord_769405).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_769405).length < 2 ^ (prefixWord ++ tailWord_769405).sum := by decide
  have hdescent : baseEnd_769405 < baseStart_769405 := by decide
  rcases family_descends (prefixWord ++ tailWord_769405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_769533 : List Nat := [1, 4, 1, 1, 1, 4, 4, 2, 1, 3]
def baseStart_769533 : Nat := 118140960795 + 769533 * 2 ^ 59
def prefixEnd_769533 : Nat := 4983230072969 + 3 ^ 40 * 769533 * 2
def baseEnd_769533 : Nat := 263426872330961954865659

theorem tailTrace_769533 : CollatzResearch.WordTrace tailWord_769533 prefixEnd_769533 263426872330961954865659 := by
  unfold tailWord_769533
  simp only [CollatzResearch.WordTrace]
  refine ⟨28067174321120841618169253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18711449547413894412112835 28067174321120841618169253)
  ·
    refine ⟨5262595185210157803406735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 28067174321120841618169253 5262595185210157803406735)
    ·
      refine ⟨7893892777815236705110103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5262595185210157803406735 7893892777815236705110103)
      ·
        refine ⟨11840839166722855057665155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7893892777815236705110103 11840839166722855057665155)
        ·
          refine ⟨17761258750084282586497733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11840839166722855057665155 17761258750084282586497733)
          ·
            refine ⟨3330236015640802984968325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 17761258750084282586497733 3330236015640802984968325)
            ·
              refine ⟨624419252932650559681561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3330236015640802984968325 624419252932650559681561)
              ·
                refine ⟨468314439699487919761171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 624419252932650559681561 468314439699487919761171)
                ·
                  refine ⟨702471659549231879641757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 468314439699487919761171 702471659549231879641757)
                  ·
                    refine ⟨263426872330961954865659, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 702471659549231879641757 263426872330961954865659)
                    ·
                      rfl

theorem cell22_769533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 4, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 4, 4, 2, 1, 3].length) (baseStart_769533 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_769533 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_769533 prefixEnd_769533 := by exact prefixLift 769533
  have htrace : WordTrace (prefixWord ++ tailWord_769533) baseStart_769533 baseEnd_769533 := by
    simpa [prefixWord, tailWord_769533, baseEnd_769533] using wordTrace_append hprefix tailTrace_769533
  have hstable : (prefixWord ++ tailWord_769533).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_769533).length < 2 ^ (prefixWord ++ tailWord_769533).sum := by decide
  have hdescent : baseEnd_769533 < baseStart_769533 := by decide
  rcases family_descends (prefixWord ++ tailWord_769533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_769557 : List Nat := [1, 3, 2, 1, 3, 2, 1, 1, 8]
def baseStart_769557 : Nat := 118140960795 + 769557 * 2 ^ 59
def prefixEnd_769557 : Nat := 4983230072969 + 3 ^ 40 * 769557 * 2
def baseEnd_769557 : Nat := 87811696007144630755195

theorem tailTrace_769557 : CollatzResearch.WordTrace tailWord_769557 prefixEnd_769557 87811696007144630755195 := by
  unfold tailWord_769557
  simp only [CollatzResearch.WordTrace]
  refine ⟨28068049673033893717042925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18712033115355929144695283 28068049673033893717042925)
  ·
    refine ⟨10525518627387710143891097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28068049673033893717042925 10525518627387710143891097)
    ·
      refine ⟨7894138970540782607918323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10525518627387710143891097 7894138970540782607918323)
      ·
        refine ⟨11841208455811173911877485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7894138970540782607918323 11841208455811173911877485)
        ·
          refine ⟨4440453170929190216954057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11841208455811173911877485 4440453170929190216954057)
          ·
            refine ⟨3330339878196892662715543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4440453170929190216954057 3330339878196892662715543)
            ·
              refine ⟨4995509817295338994073315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3330339878196892662715543 4995509817295338994073315)
              ·
                refine ⟨7493264725943008491109973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4995509817295338994073315 7493264725943008491109973)
                ·
                  refine ⟨87811696007144630755195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 7493264725943008491109973 87811696007144630755195)
                  ·
                    rfl

theorem cell22_769557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 2, 1, 1, 8].length) (baseStart_769557 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_769557 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_769557 prefixEnd_769557 := by exact prefixLift 769557
  have htrace : WordTrace (prefixWord ++ tailWord_769557) baseStart_769557 baseEnd_769557 := by
    simpa [prefixWord, tailWord_769557, baseEnd_769557] using wordTrace_append hprefix tailTrace_769557
  have hstable : (prefixWord ++ tailWord_769557).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_769557).length < 2 ^ (prefixWord ++ tailWord_769557).sum := by decide
  have hdescent : baseEnd_769557 < baseStart_769557 := by decide
  rcases family_descends (prefixWord ++ tailWord_769557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_769617 : List Nat := [1, 2, 2, 1, 3, 2, 1, 1, 2, 7]
def baseStart_769617 : Nat := 118140960795 + 769617 * 2 ^ 59
def prefixEnd_769617 : Nat := 4983230072969 + 3 ^ 40 * 769617 * 2
def baseEnd_769617 : Nat := 263455627247613735765401

theorem tailTrace_769617 : CollatzResearch.WordTrace tailWord_769617 prefixEnd_769617 263455627247613735765401 := by
  unfold tailWord_769617
  simp only [CollatzResearch.WordTrace]
  refine ⟨28070238052816523964227105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18713492035211015976151403 28070238052816523964227105)
  ·
    refine ⟨21052678539612392973170329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28070238052816523964227105 21052678539612392973170329)
    ·
      refine ⟨15789508904709294729877747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21052678539612392973170329 15789508904709294729877747)
      ·
        refine ⟨23684263357063942094816621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15789508904709294729877747 23684263357063942094816621)
        ·
          refine ⟨8881598758898978285556233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23684263357063942094816621 8881598758898978285556233)
          ·
            refine ⟨6661199069174233714167175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8881598758898978285556233 6661199069174233714167175)
            ·
              refine ⟨9991798603761350571250763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6661199069174233714167175 9991798603761350571250763)
              ·
                refine ⟨14987697905642025856876145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9991798603761350571250763 14987697905642025856876145)
                ·
                  refine ⟨11240773429231519392657109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14987697905642025856876145 11240773429231519392657109)
                  ·
                    refine ⟨263455627247613735765401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 11240773429231519392657109 263455627247613735765401)
                    ·
                      rfl

theorem cell22_769617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 1, 1, 2, 7].length) (baseStart_769617 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_769617 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_769617 prefixEnd_769617 := by exact prefixLift 769617
  have htrace : WordTrace (prefixWord ++ tailWord_769617) baseStart_769617 baseEnd_769617 := by
    simpa [prefixWord, tailWord_769617, baseEnd_769617] using wordTrace_append hprefix tailTrace_769617
  have hstable : (prefixWord ++ tailWord_769617).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_769617).length < 2 ^ (prefixWord ++ tailWord_769617).sum := by decide
  have hdescent : baseEnd_769617 < baseStart_769617 := by decide
  rcases family_descends (prefixWord ++ tailWord_769617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_769632 : List Nat := [2, 1, 1, 3, 2, 1, 1, 2, 1, 8]
def baseStart_769632 : Nat := 118140960795 + 769632 * 2 ^ 59
def prefixEnd_769632 : Nat := 4983230072969 + 3 ^ 40 * 769632 * 2
def baseEnd_769632 : Nat := 263460762054158696640355

theorem tailTrace_769632 : CollatzResearch.WordTrace tailWord_769632 prefixEnd_769632 263460762054158696640355 := by
  unfold tailWord_769632
  simp only [CollatzResearch.WordTrace]
  refine ⟨14035392573881090763011575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18713856765174787684015433 14035392573881090763011575)
  ·
    refine ⟨21053088860821636144517363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14035392573881090763011575 21053088860821636144517363)
    ·
      refine ⟨31579633291232454216776045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21053088860821636144517363 31579633291232454216776045)
      ·
        refine ⟨11842362484212170331291017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31579633291232454216776045 11842362484212170331291017)
        ·
          refine ⟨8881771863159127748468263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11842362484212170331291017 8881771863159127748468263)
          ·
            refine ⟨13322657794738691622702395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8881771863159127748468263 13322657794738691622702395)
            ·
              refine ⟨19983986692108037434053593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13322657794738691622702395 19983986692108037434053593)
              ·
                refine ⟨14987990019081028075540195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19983986692108037434053593 14987990019081028075540195)
                ·
                  refine ⟨22481985028621542113310293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14987990019081028075540195 22481985028621542113310293)
                  ·
                    refine ⟨263460762054158696640355, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 22481985028621542113310293 263460762054158696640355)
                    ·
                      rfl

theorem cell22_769632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 1, 2, 1, 8].length) (baseStart_769632 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_769632 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_769632 prefixEnd_769632 := by exact prefixLift 769632
  have htrace : WordTrace (prefixWord ++ tailWord_769632) baseStart_769632 baseEnd_769632 := by
    simpa [prefixWord, tailWord_769632, baseEnd_769632] using wordTrace_append hprefix tailTrace_769632
  have hstable : (prefixWord ++ tailWord_769632).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_769632).length < 2 ^ (prefixWord ++ tailWord_769632).sum := by decide
  have hdescent : baseEnd_769632 < baseStart_769632 := by decide
  rcases family_descends (prefixWord ++ tailWord_769632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_769664 : List Nat := [2, 1, 1, 2, 1, 4, 3, 3, 5]
def baseStart_769664 : Nat := 118140960795 + 769664 * 2 ^ 59
def prefixEnd_769664 : Nat := 4983230072969 + 3 ^ 40 * 769664 * 2
def baseEnd_769664 : Nat := 87823905436040426613419

theorem tailTrace_769664 : CollatzResearch.WordTrace tailWord_769664 prefixEnd_769664 87823905436040426613419 := by
  unfold tailWord_769664
  simp only [CollatzResearch.WordTrace]
  refine ⟨14035976141823125495594023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18714634855764167327458697 14035976141823125495594023)
  ·
    refine ⟨21053964212734688243391035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14035976141823125495594023 21053964212734688243391035)
    ·
      refine ⟨31580946319102032365086553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21053964212734688243391035 31580946319102032365086553)
      ·
        refine ⟨23685709739326524273814915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31580946319102032365086553 23685709739326524273814915)
        ·
          refine ⟨35528564608989786410722373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23685709739326524273814915 35528564608989786410722373)
          ·
            refine ⟨6661605864185584952010445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 35528564608989786410722373 6661605864185584952010445)
            ·
              refine ⟨2498102199069594357003917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6661605864185584952010445 2498102199069594357003917)
              ·
                refine ⟨936788324651097883876469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2498102199069594357003917 936788324651097883876469)
                ·
                  refine ⟨87823905436040426613419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 936788324651097883876469 87823905436040426613419)
                  ·
                    rfl

theorem cell22_769664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 3, 3, 5].length) (baseStart_769664 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_769664 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_769664 prefixEnd_769664 := by exact prefixLift 769664
  have htrace : WordTrace (prefixWord ++ tailWord_769664) baseStart_769664 baseEnd_769664 := by
    simpa [prefixWord, tailWord_769664, baseEnd_769664] using wordTrace_append hprefix tailTrace_769664
  have hstable : (prefixWord ++ tailWord_769664).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_769664).length < 2 ^ (prefixWord ++ tailWord_769664).sum := by decide
  have hdescent : baseEnd_769664 < baseStart_769664 := by decide
  rcases family_descends (prefixWord ++ tailWord_769664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_769726 : List Nat := [4, 2, 1, 1, 2, 3, 1, 2, 6]
def baseStart_769726 : Nat := 118140960795 + 769726 * 2 ^ 59
def prefixEnd_769726 : Nat := 4983230072969 + 3 ^ 40 * 769726 * 2
def baseEnd_769726 : Nat := 87830980058391261596689

theorem tailTrace_769726 : CollatzResearch.WordTrace tailWord_769726 prefixEnd_769726 87830980058391261596689 := by
  unfold tailWord_769726
  simp only [CollatzResearch.WordTrace]
  refine ⟨3509276701177704447493129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 18716142406281090386630021 3509276701177704447493129)
  ·
    refine ⟨2631957525883278335619847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3509276701177704447493129 2631957525883278335619847)
    ·
      refine ⟨3947936288824917503429771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2631957525883278335619847 3947936288824917503429771)
      ·
        refine ⟨5921904433237376255144657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3947936288824917503429771 5921904433237376255144657)
        ·
          refine ⟨4441428324928032191358493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5921904433237376255144657 4441428324928032191358493)
          ·
            refine ⟨1665535621848012071759435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4441428324928032191358493 1665535621848012071759435)
            ·
              refine ⟨2498303432772018107639153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1665535621848012071759435 2498303432772018107639153)
              ·
                refine ⟨1873727574579013580729365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2498303432772018107639153 1873727574579013580729365)
                ·
                  refine ⟨87830980058391261596689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1873727574579013580729365 87830980058391261596689)
                  ·
                    rfl

theorem cell22_769726_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 3, 1, 2, 6].length) (baseStart_769726 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_769726 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_769726 prefixEnd_769726 := by exact prefixLift 769726
  have htrace : WordTrace (prefixWord ++ tailWord_769726) baseStart_769726 baseEnd_769726 := by
    simpa [prefixWord, tailWord_769726, baseEnd_769726] using wordTrace_append hprefix tailTrace_769726
  have hstable : (prefixWord ++ tailWord_769726).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_769726).length < 2 ^ (prefixWord ++ tailWord_769726).sum := by decide
  have hdescent : baseEnd_769726 < baseStart_769726 := by decide
  rcases family_descends (prefixWord ++ tailWord_769726) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_769754 : List Nat := [3, 1, 1, 2, 2, 4, 9]
def baseStart_769754 : Nat := 118140960795 + 769754 * 2 ^ 59
def prefixEnd_769754 : Nat := 4983230072969 + 3 ^ 40 * 769754 * 2
def baseEnd_769754 : Nat := 9759352783236705373703

theorem tailTrace_769754 : CollatzResearch.WordTrace tailWord_769754 prefixEnd_769754 9759352783236705373703 := by
  unfold tailWord_769754
  simp only [CollatzResearch.WordTrace]
  refine ⟨7018808713330049090491079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18716823235546797574642877 7018808713330049090491079)
  ·
    refine ⟨10528213069995073635736619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7018808713330049090491079 10528213069995073635736619)
    ·
      refine ⟨15792319604992610453604929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10528213069995073635736619 15792319604992610453604929)
      ·
        refine ⟨11844239703744457840203697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15792319604992610453604929 11844239703744457840203697)
        ·
          refine ⟨8883179777808343380152773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11844239703744457840203697 8883179777808343380152773)
          ·
            refine ⟨1665596208339064383778645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8883179777808343380152773 1665596208339064383778645)
            ·
              refine ⟨9759352783236705373703, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 1665596208339064383778645 9759352783236705373703)
              ·
                rfl

theorem cell22_769754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 4, 9].length) (baseStart_769754 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_769754 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_769754 prefixEnd_769754 := by exact prefixLift 769754
  have htrace : WordTrace (prefixWord ++ tailWord_769754) baseStart_769754 baseEnd_769754 := by
    simpa [prefixWord, tailWord_769754, baseEnd_769754] using wordTrace_append hprefix tailTrace_769754
  have hstable : (prefixWord ++ tailWord_769754).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_769754).length < 2 ^ (prefixWord ++ tailWord_769754).sum := by decide
  have hdescent : baseEnd_769754 < baseStart_769754 := by decide
  rcases family_descends (prefixWord ++ tailWord_769754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_769927 : List Nat := [1, 1, 4, 2, 4, 2, 1, 2, 2, 3]
def baseStart_769927 : Nat := 118140960795 + 769927 * 2 ^ 59
def prefixEnd_769927 : Nat := 4983230072969 + 3 ^ 40 * 769927 * 2
def baseEnd_769927 : Nat := 263561746582876260514451

theorem tailTrace_769927 : CollatzResearch.WordTrace tailWord_769927 prefixEnd_769927 263561746582876260514451 := by
  unfold tailWord_769927
  simp only [CollatzResearch.WordTrace]
  refine ⟨28081544681693446908012035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18721029787795631272008023 28081544681693446908012035)
  ·
    refine ⟨42122317022540170362018053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28081544681693446908012035 42122317022540170362018053)
    ·
      refine ⟨7897934441726281942878385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 42122317022540170362018053 7897934441726281942878385)
      ·
        refine ⟨5923450831294711457158789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7897934441726281942878385 5923450831294711457158789)
        ·
          refine ⟨1110647030867758398217273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5923450831294711457158789 1110647030867758398217273)
          ·
            refine ⟨832985273150818798662955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1110647030867758398217273 832985273150818798662955)
            ·
              refine ⟨1249477909726228197994433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 832985273150818798662955 1249477909726228197994433)
              ·
                refine ⟨937108432294671148495825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1249477909726228197994433 937108432294671148495825)
                ·
                  refine ⟨702831324221003361371869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 937108432294671148495825 702831324221003361371869)
                  ·
                    refine ⟨263561746582876260514451, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 702831324221003361371869 263561746582876260514451)
                    ·
                      rfl

theorem cell22_769927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 4, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 4, 2, 1, 2, 2, 3].length) (baseStart_769927 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_769927 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_769927 prefixEnd_769927 := by exact prefixLift 769927
  have htrace : WordTrace (prefixWord ++ tailWord_769927) baseStart_769927 baseEnd_769927 := by
    simpa [prefixWord, tailWord_769927, baseEnd_769927] using wordTrace_append hprefix tailTrace_769927
  have hstable : (prefixWord ++ tailWord_769927).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_769927).length < 2 ^ (prefixWord ++ tailWord_769927).sum := by decide
  have hdescent : baseEnd_769927 < baseStart_769927 := by decide
  rcases family_descends (prefixWord ++ tailWord_769927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_769944 : List Nat := [2, 1, 2, 6, 1, 1, 3, 1, 2, 3]
def baseStart_769944 : Nat := 118140960795 + 769944 * 2 ^ 59
def prefixEnd_769944 : Nat := 4983230072969 + 3 ^ 40 * 769944 * 2
def baseEnd_769944 : Nat := 263567566030293882839399

theorem tailTrace_769944 : CollatzResearch.WordTrace tailWord_769944 prefixEnd_769944 263567566030293882839399 := by
  unfold tailWord_769944
  simp only [CollatzResearch.WordTrace]
  refine ⟨14041082361315929405690443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18721443148421239207587257 14041082361315929405690443)
  ·
    refine ⟨21061623541973894108535665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14041082361315929405690443 21061623541973894108535665)
    ·
      refine ⟨15796217656480420581401749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21061623541973894108535665 15796217656480420581401749)
      ·
        refine ⟨740447702647519714753207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 15796217656480420581401749 740447702647519714753207)
        ·
          refine ⟨1110671553971279572129811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 740447702647519714753207 1110671553971279572129811)
          ·
            refine ⟨1666007330956919358194717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1110671553971279572129811 1666007330956919358194717)
            ·
              refine ⟨624752749108844759323019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1666007330956919358194717 624752749108844759323019)
              ·
                refine ⟨937129123663267138984529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 624752749108844759323019 937129123663267138984529)
                ·
                  refine ⟨702846842747450354238397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 937129123663267138984529 702846842747450354238397)
                  ·
                    refine ⟨263567566030293882839399, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 702846842747450354238397 263567566030293882839399)
                    ·
                      rfl

theorem cell22_769944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 1, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 1, 1, 3, 1, 2, 3].length) (baseStart_769944 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_769944 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_769944 prefixEnd_769944 := by exact prefixLift 769944
  have htrace : WordTrace (prefixWord ++ tailWord_769944) baseStart_769944 baseEnd_769944 := by
    simpa [prefixWord, tailWord_769944, baseEnd_769944] using wordTrace_append hprefix tailTrace_769944
  have hstable : (prefixWord ++ tailWord_769944).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_769944).length < 2 ^ (prefixWord ++ tailWord_769944).sum := by decide
  have hdescent : baseEnd_769944 < baseStart_769944 := by decide
  rcases family_descends (prefixWord ++ tailWord_769944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_769998 : List Nat := [4, 1, 1, 1, 2, 2, 2, 2, 3, 4]
def baseStart_769998 : Nat := 118140960795 + 769998 * 2 ^ 59
def prefixEnd_769998 : Nat := 4983230072969 + 3 ^ 40 * 769998 * 2
def baseEnd_769998 : Nat := 263586051333855741989233

theorem tailTrace_769998 : CollatzResearch.WordTrace tailWord_769998 prefixEnd_769998 263586051333855741989233 := by
  unfold tailWord_769998
  simp only [CollatzResearch.WordTrace]
  refine ⟨3510516783054528254230831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 18722756176290817355897765 3510516783054528254230831)
  ·
    refine ⟨5265775174581792381346247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3510516783054528254230831 5265775174581792381346247)
    ·
      refine ⟨7898662761872688572019371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5265775174581792381346247 7898662761872688572019371)
      ·
        refine ⟨11847994142809032858029057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7898662761872688572019371 11847994142809032858029057)
        ·
          refine ⟨8885995607106774643521793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11847994142809032858029057 8885995607106774643521793)
          ·
            refine ⟨6664496705330080982641345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8885995607106774643521793 6664496705330080982641345)
            ·
              refine ⟨4998372528997560736981009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6664496705330080982641345 4998372528997560736981009)
              ·
                refine ⟨3748779396748170552735757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4998372528997560736981009 3748779396748170552735757)
                ·
                  refine ⟨1405792273780563957275909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3748779396748170552735757 1405792273780563957275909)
                  ·
                    refine ⟨263586051333855741989233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1405792273780563957275909 263586051333855741989233)
                    ·
                      rfl

theorem cell22_769998_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 2, 2, 3, 4].length) (baseStart_769998 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_769998 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_769998 prefixEnd_769998 := by exact prefixLift 769998
  have htrace : WordTrace (prefixWord ++ tailWord_769998) baseStart_769998 baseEnd_769998 := by
    simpa [prefixWord, tailWord_769998, baseEnd_769998] using wordTrace_append hprefix tailTrace_769998
  have hstable : (prefixWord ++ tailWord_769998).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_769998).length < 2 ^ (prefixWord ++ tailWord_769998).sum := by decide
  have hdescent : baseEnd_769998 < baseStart_769998 := by decide
  rcases family_descends (prefixWord ++ tailWord_769998) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_770015 : List Nat := [1, 1, 2, 3, 4, 1, 3, 2, 1, 4]
def baseStart_770015 : Nat := 118140960795 + 770015 * 2 ^ 59
def prefixEnd_770015 : Nat := 4983230072969 + 3 ^ 40 * 770015 * 2
def baseEnd_770015 : Nat := 263591870781273364314181

theorem tailTrace_770015 : CollatzResearch.WordTrace tailWord_770015 prefixEnd_770015 263591870781273364314181 := by
  unfold tailWord_770015
  simp only [CollatzResearch.WordTrace]
  refine ⟨28084754305374637937215499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18723169536916425291476999 28084754305374637937215499)
  ·
    refine ⟨42127131458061956905823249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28084754305374637937215499 42127131458061956905823249)
    ·
      refine ⟨31595348593546467679367437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42127131458061956905823249 31595348593546467679367437)
      ·
        refine ⟨11848255722579925379762789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31595348593546467679367437 11848255722579925379762789)
        ·
          refine ⟨2221547947983736008705523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11848255722579925379762789 2221547947983736008705523)
          ·
            refine ⟨3332321921975604013058285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2221547947983736008705523 3332321921975604013058285)
            ·
              refine ⟨1249620720740851504896857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3332321921975604013058285 1249620720740851504896857)
              ·
                refine ⟨937215540555638628672643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1249620720740851504896857 937215540555638628672643)
                ·
                  refine ⟨1405823310833457943008965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 937215540555638628672643 1405823310833457943008965)
                  ·
                    refine ⟨263591870781273364314181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1405823310833457943008965 263591870781273364314181)
                    ·
                      rfl

theorem cell22_770015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 1, 3, 2, 1, 4].length) (baseStart_770015 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_770015 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_770015 prefixEnd_770015 := by exact prefixLift 770015
  have htrace : WordTrace (prefixWord ++ tailWord_770015) baseStart_770015 baseEnd_770015 := by
    simpa [prefixWord, tailWord_770015, baseEnd_770015] using wordTrace_append hprefix tailTrace_770015
  have hstable : (prefixWord ++ tailWord_770015).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_770015).length < 2 ^ (prefixWord ++ tailWord_770015).sum := by decide
  have hdescent : baseEnd_770015 < baseStart_770015 := by decide
  rcases family_descends (prefixWord ++ tailWord_770015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_770028 : List Nat := [2, 2, 1, 1, 2, 1, 1, 3, 6, 3]
def baseStart_770028 : Nat := 118140960795 + 770028 * 2 ^ 59
def prefixEnd_770028 : Nat := 4983230072969 + 3 ^ 40 * 770028 * 2
def baseEnd_770028 : Nat := 263596320946945663739141

theorem tailTrace_770028 : CollatzResearch.WordTrace tailWord_770028 prefixEnd_770028 263596320946945663739141 := by
  unfold tailWord_770028
  simp only [CollatzResearch.WordTrace]
  refine ⟨14042614227163770578719369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18723485636218360771625825 14042614227163770578719369)
  ·
    refine ⟨10531960670372827934039527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14042614227163770578719369 10531960670372827934039527)
    ·
      refine ⟨15797941005559241901059291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10531960670372827934039527 15797941005559241901059291)
      ·
        refine ⟨23696911508338862851588937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15797941005559241901059291 23696911508338862851588937)
        ·
          refine ⟨17772683631254147138691703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23696911508338862851588937 17772683631254147138691703)
          ·
            refine ⟨26659025446881220708037555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17772683631254147138691703 26659025446881220708037555)
            ·
              refine ⟨39988538170321831062056333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26659025446881220708037555 39988538170321831062056333)
              ·
                refine ⟨14995701813870686648271125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 39988538170321831062056333 14995701813870686648271125)
                ·
                  refine ⟨702923522525188436637709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 14995701813870686648271125 702923522525188436637709)
                  ·
                    refine ⟨263596320946945663739141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 702923522525188436637709 263596320946945663739141)
                    ·
                      rfl

theorem cell22_770028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 6, 3].length) (baseStart_770028 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_770028 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_770028 prefixEnd_770028 := by exact prefixLift 770028
  have htrace : WordTrace (prefixWord ++ tailWord_770028) baseStart_770028 baseEnd_770028 := by
    simpa [prefixWord, tailWord_770028, baseEnd_770028] using wordTrace_append hprefix tailTrace_770028
  have hstable : (prefixWord ++ tailWord_770028).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_770028).length < 2 ^ (prefixWord ++ tailWord_770028).sum := by decide
  have hdescent : baseEnd_770028 < baseStart_770028 := by decide
  rcases family_descends (prefixWord ++ tailWord_770028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_770041 : List Nat := [1, 2, 1, 3, 1, 14]
def baseStart_770041 : Nat := 118140960795 + 770041 * 2 ^ 59
def prefixEnd_770041 : Nat := 4983230072969 + 3 ^ 40 * 770041 * 2
def baseEnd_770041 : Nat := 3254330507563184730421

theorem tailTrace_770041 : CollatzResearch.WordTrace tailWord_770041 prefixEnd_770041 3254330507563184730421 := by
  unfold tailWord_770041
  simp only [CollatzResearch.WordTrace]
  refine ⟨28085702603280444377661977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18723801735520296251774651 28085702603280444377661977)
  ·
    refine ⟨21064276952460333283246483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28085702603280444377661977 21064276952460333283246483)
    ·
      refine ⟨31596415428690499924869725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21064276952460333283246483 31596415428690499924869725)
      ·
        refine ⟨11848655785758937471826147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31596415428690499924869725 11848655785758937471826147)
        ·
          refine ⟨17772983678638406207739221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11848655785758937471826147 17772983678638406207739221)
          ·
            refine ⟨3254330507563184730421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 14 17772983678638406207739221 3254330507563184730421)
            ·
              rfl

theorem cell22_770041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 14].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 14].length) (baseStart_770041 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_770041 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_770041 prefixEnd_770041 := by exact prefixLift 770041
  have htrace : WordTrace (prefixWord ++ tailWord_770041) baseStart_770041 baseEnd_770041 := by
    simpa [prefixWord, tailWord_770041, baseEnd_770041] using wordTrace_append hprefix tailTrace_770041
  have hstable : (prefixWord ++ tailWord_770041).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_770041).length < 2 ^ (prefixWord ++ tailWord_770041).sum := by decide
  have hdescent : baseEnd_770041 < baseStart_770041 := by decide
  rcases family_descends (prefixWord ++ tailWord_770041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_770043 : List Nat := [1, 1, 1, 1, 1, 3, 6, 2, 2, 4]
def baseStart_770043 : Nat := 118140960795 + 770043 * 2 ^ 59
def prefixEnd_770043 : Nat := 4983230072969 + 3 ^ 40 * 770043 * 2
def baseEnd_770043 : Nat := 263601455753490624614095

theorem tailTrace_770043 : CollatzResearch.WordTrace tailWord_770043 prefixEnd_770043 263601455753490624614095 := by
  unfold tailWord_770043
  simp only [CollatzResearch.WordTrace]
  refine ⟨28085775549273198719234783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18723850366182132479489855 28085775549273198719234783)
  ·
    refine ⟨42128663323909798078852175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28085775549273198719234783 42128663323909798078852175)
    ·
      refine ⟨63192994985864697118278263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42128663323909798078852175 63192994985864697118278263)
      ·
        refine ⟨94789492478797045677417395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63192994985864697118278263 94789492478797045677417395)
        ·
          refine ⟨142184238718195568516126093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 94789492478797045677417395 142184238718195568516126093)
          ·
            refine ⟨53319089519323338193547285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 142184238718195568516126093 53319089519323338193547285)
            ·
              refine ⟨2499332321218281477822529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 53319089519323338193547285 2499332321218281477822529)
              ·
                refine ⟨1874499240913711108366897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2499332321218281477822529 1874499240913711108366897)
                ·
                  refine ⟨1405874430685283331275173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1874499240913711108366897 1405874430685283331275173)
                  ·
                    refine ⟨263601455753490624614095, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1405874430685283331275173 263601455753490624614095)
                    ·
                      rfl

theorem cell22_770043_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 6, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 6, 2, 2, 4].length) (baseStart_770043 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_770043 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_770043 prefixEnd_770043 := by exact prefixLift 770043
  have htrace : WordTrace (prefixWord ++ tailWord_770043) baseStart_770043 baseEnd_770043 := by
    simpa [prefixWord, tailWord_770043, baseEnd_770043] using wordTrace_append hprefix tailTrace_770043
  have hstable : (prefixWord ++ tailWord_770043).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_770043).length < 2 ^ (prefixWord ++ tailWord_770043).sum := by decide
  have hdescent : baseEnd_770043 < baseStart_770043 := by decide
  rcases family_descends (prefixWord ++ tailWord_770043) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_770045 : List Nat := [1, 4, 1, 1, 1, 2, 3, 4, 2, 3]
def baseStart_770045 : Nat := 118140960795 + 770045 * 2 ^ 59
def prefixEnd_770045 : Nat := 4983230072969 + 3 ^ 40 * 770045 * 2
def baseEnd_770045 : Nat := 263602140394363286064089

theorem tailTrace_770045 : CollatzResearch.WordTrace tailWord_770045 prefixEnd_770045 263602140394363286064089 := by
  unfold tailWord_770045
  simp only [CollatzResearch.WordTrace]
  refine ⟨28085848495265953060807589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18723898996843968707205059 28085848495265953060807589)
  ·
    refine ⟨5266096592862366198901423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 28085848495265953060807589 5266096592862366198901423)
    ·
      refine ⟨7899144889293549298352135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5266096592862366198901423 7899144889293549298352135)
      ·
        refine ⟨11848717333940323947528203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7899144889293549298352135 11848717333940323947528203)
        ·
          refine ⟨17773076000910485921292305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11848717333940323947528203 17773076000910485921292305)
          ·
            refine ⟨13329807000682864440969229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17773076000910485921292305 13329807000682864440969229)
            ·
              refine ⟨4998677625256074165363461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13329807000682864440969229 4998677625256074165363461)
              ·
                refine ⟨937252054735513906005649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4998677625256074165363461 937252054735513906005649)
                ·
                  refine ⟨702939041051635429504237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 937252054735513906005649 702939041051635429504237)
                  ·
                    refine ⟨263602140394363286064089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 702939041051635429504237 263602140394363286064089)
                    ·
                      rfl

theorem cell22_770045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 3, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 3, 4, 2, 3].length) (baseStart_770045 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_770045 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_770045 prefixEnd_770045 := by exact prefixLift 770045
  have htrace : WordTrace (prefixWord ++ tailWord_770045) baseStart_770045 baseEnd_770045 := by
    simpa [prefixWord, tailWord_770045, baseEnd_770045] using wordTrace_append hprefix tailTrace_770045
  have hstable : (prefixWord ++ tailWord_770045).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_770045).length < 2 ^ (prefixWord ++ tailWord_770045).sum := by decide
  have hdescent : baseEnd_770045 < baseStart_770045 := by decide
  rcases family_descends (prefixWord ++ tailWord_770045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_770077 : List Nat := [1, 4, 2, 2, 2, 3, 1, 1, 2, 4]
def baseStart_770077 : Nat := 118140960795 + 770077 * 2 ^ 59
def prefixEnd_770077 : Nat := 4983230072969 + 3 ^ 40 * 770077 * 2
def baseEnd_770077 : Nat := 263613094648325869263991

theorem tailTrace_770077 : CollatzResearch.WordTrace tailWord_770077 prefixEnd_770077 263613094648325869263991 := by
  unfold tailWord_770077
  simp only [CollatzResearch.WordTrace]
  refine ⟨28087015631150022525972485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18724677087433348350648323 28087015631150022525972485)
  ·
    refine ⟨5266315430840629223619841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 28087015631150022525972485 5266315430840629223619841)
    ·
      refine ⟨3949736573130471917714881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5266315430840629223619841 3949736573130471917714881)
      ·
        refine ⟨2962302429847853938286161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3949736573130471917714881 2962302429847853938286161)
        ·
          refine ⟨2221726822385890453714621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2962302429847853938286161 2221726822385890453714621)
          ·
            refine ⟨833147558394708920142983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2221726822385890453714621 833147558394708920142983)
            ·
              refine ⟨1249721337592063380214475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 833147558394708920142983 1249721337592063380214475)
              ·
                refine ⟨1874582006388095070321713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1249721337592063380214475 1874582006388095070321713)
                ·
                  refine ⟨1405936504791071302741285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1874582006388095070321713 1405936504791071302741285)
                  ·
                    refine ⟨263613094648325869263991, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1405936504791071302741285 263613094648325869263991)
                    ·
                      rfl

theorem cell22_770077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 3, 1, 1, 2, 4].length) (baseStart_770077 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_770077 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_770077 prefixEnd_770077 := by exact prefixLift 770077
  have htrace : WordTrace (prefixWord ++ tailWord_770077) baseStart_770077 baseEnd_770077 := by
    simpa [prefixWord, tailWord_770077, baseEnd_770077] using wordTrace_append hprefix tailTrace_770077
  have hstable : (prefixWord ++ tailWord_770077).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_770077).length < 2 ^ (prefixWord ++ tailWord_770077).sum := by decide
  have hdescent : baseEnd_770077 < baseStart_770077 := by decide
  rcases family_descends (prefixWord ++ tailWord_770077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_770141 : List Nat := [1, 4, 4, 1, 1, 1, 3, 3, 1, 3]
def baseStart_770141 : Nat := 118140960795 + 770141 * 2 ^ 59
def prefixEnd_770141 : Nat := 4983230072969 + 3 ^ 40 * 770141 * 2
def baseEnd_770141 : Nat := 263635003156251035663795

theorem tailTrace_770141 : CollatzResearch.WordTrace tailWord_770141 prefixEnd_770141 263635003156251035663795 := by
  unfold tailWord_770141
  simp only [CollatzResearch.WordTrace]
  refine ⟨28089349902918161456302277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18726233268612107637534851 28089349902918161456302277)
  ·
    refine ⟨5266753106797155273056677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 28089349902918161456302277 5266753106797155273056677)
    ·
      refine ⟨987516207524466613698127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5266753106797155273056677 987516207524466613698127)
      ·
        refine ⟨1481274311286699920547191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 987516207524466613698127 1481274311286699920547191)
        ·
          refine ⟨2221911466930049880820787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1481274311286699920547191 2221911466930049880820787)
          ·
            refine ⟨3332867200395074821231181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2221911466930049880820787 3332867200395074821231181)
            ·
              refine ⟨1249825200148153057961693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3332867200395074821231181 1249825200148153057961693)
              ·
                refine ⟨468684450055557396735635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1249825200148153057961693 468684450055557396735635)
                ·
                  refine ⟨703026675083336095103453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 468684450055557396735635 703026675083336095103453)
                  ·
                    refine ⟨263635003156251035663795, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 703026675083336095103453 263635003156251035663795)
                    ·
                      rfl

theorem cell22_770141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 1, 3, 3, 1, 3].length) (baseStart_770141 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_770141 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_770141 prefixEnd_770141 := by exact prefixLift 770141
  have htrace : WordTrace (prefixWord ++ tailWord_770141) baseStart_770141 baseEnd_770141 := by
    simpa [prefixWord, tailWord_770141, baseEnd_770141] using wordTrace_append hprefix tailTrace_770141
  have hstable : (prefixWord ++ tailWord_770141).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_770141).length < 2 ^ (prefixWord ++ tailWord_770141).sum := by decide
  have hdescent : baseEnd_770141 < baseStart_770141 := by decide
  rcases family_descends (prefixWord ++ tailWord_770141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_770148 : List Nat := [2, 3, 1, 1, 2, 1, 2, 2, 8]
def baseStart_770148 : Nat := 118140960795 + 770148 * 2 ^ 59
def prefixEnd_770148 : Nat := 4983230072969 + 3 ^ 40 * 770148 * 2
def baseEnd_770148 : Nat := 87879133133101783579591

theorem tailTrace_770148 : CollatzResearch.WordTrace tailWord_770148 prefixEnd_770148 87879133133101783579591 := by
  unfold tailWord_770148
  simp only [CollatzResearch.WordTrace]
  refine ⟨14044802606946400825903549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18726403475928534434538065 14044802606946400825903549)
  ·
    refine ⟨5266800977604900309713831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14044802606946400825903549 5266800977604900309713831)
    ·
      refine ⟨7900201466407350464570747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5266800977604900309713831 7900201466407350464570747)
      ·
        refine ⟨11850302199611025696856121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7900201466407350464570747 11850302199611025696856121)
        ·
          refine ⟨8887726649708269272642091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11850302199611025696856121 8887726649708269272642091)
          ·
            refine ⟨13331589974562403908963137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8887726649708269272642091 13331589974562403908963137)
            ·
              refine ⟨9998692480921802931722353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13331589974562403908963137 9998692480921802931722353)
              ·
                refine ⟨7499019360691352198791765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9998692480921802931722353 7499019360691352198791765)
                ·
                  refine ⟨87879133133101783579591, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 7499019360691352198791765 87879133133101783579591)
                  ·
                    rfl

theorem cell22_770148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 2, 2, 8].length) (baseStart_770148 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_770148 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_770148 prefixEnd_770148 := by exact prefixLift 770148
  have htrace : WordTrace (prefixWord ++ tailWord_770148) baseStart_770148 baseEnd_770148 := by
    simpa [prefixWord, tailWord_770148, baseEnd_770148] using wordTrace_append hprefix tailTrace_770148
  have hstable : (prefixWord ++ tailWord_770148).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_770148).length < 2 ^ (prefixWord ++ tailWord_770148).sum := by decide
  have hdescent : baseEnd_770148 < baseStart_770148 := by decide
  rcases family_descends (prefixWord ++ tailWord_770148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_770180 : List Nat := [2, 3, 2, 1, 2, 1, 2, 3, 1, 5]
def baseStart_770180 : Nat := 118140960795 + 770180 * 2 ^ 59
def prefixEnd_770180 : Nat := 4983230072969 + 3 ^ 40 * 770180 * 2
def baseEnd_770180 : Nat := 263648353653267933938675

theorem tailTrace_770180 : CollatzResearch.WordTrace tailWord_770180 prefixEnd_770180 263648353653267933938675 := by
  unfold tailWord_770180
  simp only [CollatzResearch.WordTrace]
  refine ⟨14045386174888435558485997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18727181566517914077981329 14045386174888435558485997)
  ·
    refine ⟨5267019815583163334432249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14045386174888435558485997 5267019815583163334432249)
    ·
      refine ⟨3950264861687372500824187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5267019815583163334432249 3950264861687372500824187)
      ·
        refine ⟨5925397292531058751236281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3950264861687372500824187 5925397292531058751236281)
        ·
          refine ⟨4444047969398294063427211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5925397292531058751236281 4444047969398294063427211)
          ·
            refine ⟨6666071954097441095140817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4444047969398294063427211 6666071954097441095140817)
            ·
              refine ⟨4999553965573080821355613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6666071954097441095140817 4999553965573080821355613)
              ·
                refine ⟨1874832737089905308008355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4999553965573080821355613 1874832737089905308008355)
                ·
                  refine ⟨2812249105634857962012533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1874832737089905308008355 2812249105634857962012533)
                  ·
                    refine ⟨263648353653267933938675, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2812249105634857962012533 263648353653267933938675)
                    ·
                      rfl

theorem cell22_770180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 2, 3, 1, 5].length) (baseStart_770180 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_770180 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_770180 prefixEnd_770180 := by exact prefixLift 770180
  have htrace : WordTrace (prefixWord ++ tailWord_770180) baseStart_770180 baseEnd_770180 := by
    simpa [prefixWord, tailWord_770180, baseEnd_770180] using wordTrace_append hprefix tailTrace_770180
  have hstable : (prefixWord ++ tailWord_770180).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_770180).length < 2 ^ (prefixWord ++ tailWord_770180).sum := by decide
  have hdescent : baseEnd_770180 < baseStart_770180 := by decide
  rcases family_descends (prefixWord ++ tailWord_770180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_770184 : List Nat := [2, 1, 3, 4, 1, 3, 1, 2, 1, 4]
def baseStart_770184 : Nat := 118140960795 + 770184 * 2 ^ 59
def prefixEnd_770184 : Nat := 4983230072969 + 3 ^ 40 * 770184 * 2
def baseEnd_770184 : Nat := 263649722935013256838663

theorem tailTrace_770184 : CollatzResearch.WordTrace tailWord_770184 prefixEnd_770184 263649722935013256838663 := by
  unfold tailWord_770184
  simp only [CollatzResearch.WordTrace]
  refine ⟨14045459120881189900058803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18727278827841586533411737 14045459120881189900058803)
  ·
    refine ⟨21068188681321784850088205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14045459120881189900058803 21068188681321784850088205)
    ·
      refine ⟨7900570755495669318783077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21068188681321784850088205 7900570755495669318783077)
      ·
        refine ⟨1481357016655437997271827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 7900570755495669318783077 1481357016655437997271827)
        ·
          refine ⟨2222035524983156995907741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1481357016655437997271827 2222035524983156995907741)
          ·
            refine ⟨833263321868683873465403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2222035524983156995907741 833263321868683873465403)
            ·
              refine ⟨1249894982803025810198105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 833263321868683873465403 1249894982803025810198105)
              ·
                refine ⟨937421237102269357648579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1249894982803025810198105 937421237102269357648579)
                ·
                  refine ⟨1406131855653404036472869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 937421237102269357648579 1406131855653404036472869)
                  ·
                    refine ⟨263649722935013256838663, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1406131855653404036472869 263649722935013256838663)
                    ·
                      rfl

theorem cell22_770184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 3, 1, 2, 1, 4].length) (baseStart_770184 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_770184 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_770184 prefixEnd_770184 := by exact prefixLift 770184
  have htrace : WordTrace (prefixWord ++ tailWord_770184) baseStart_770184 baseEnd_770184 := by
    simpa [prefixWord, tailWord_770184, baseEnd_770184] using wordTrace_append hprefix tailTrace_770184
  have hstable : (prefixWord ++ tailWord_770184).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_770184).length < 2 ^ (prefixWord ++ tailWord_770184).sum := by decide
  have hdescent : baseEnd_770184 < baseStart_770184 := by decide
  rcases family_descends (prefixWord ++ tailWord_770184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_770210 : List Nat := [3, 3, 1, 3, 1, 11]
def baseStart_770210 : Nat := 118140960795 + 770210 * 2 ^ 59
def prefixEnd_770210 : Nat := 4983230072969 + 3 ^ 40 * 770210 * 2
def baseEnd_770210 : Nat := 3255044731683430317143

theorem tailTrace_770210 : CollatzResearch.WordTrace tailWord_770210 prefixEnd_770210 3255044731683430317143 := by
  unfold tailWord_770210
  simp only [CollatzResearch.WordTrace]
  refine ⟨7022966634917046560141021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18727911026445457493709389 7022966634917046560141021)
  ·
    refine ⟨2633612488093892460052883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7022966634917046560141021 2633612488093892460052883)
    ·
      refine ⟨3950418732140838690079325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2633612488093892460052883 3950418732140838690079325)
      ·
        refine ⟨1481407024552814508779747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3950418732140838690079325 1481407024552814508779747)
        ·
          refine ⟨2222110536829221763169621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1481407024552814508779747 2222110536829221763169621)
          ·
            refine ⟨3255044731683430317143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 2222110536829221763169621 3255044731683430317143)
            ·
              rfl

theorem cell22_770210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 11].length) (baseStart_770210 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_770210 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_770210 prefixEnd_770210 := by exact prefixLift 770210
  have htrace : WordTrace (prefixWord ++ tailWord_770210) baseStart_770210 baseEnd_770210 := by
    simpa [prefixWord, tailWord_770210, baseEnd_770210] using wordTrace_append hprefix tailTrace_770210
  have hstable : (prefixWord ++ tailWord_770210).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_770210).length < 2 ^ (prefixWord ++ tailWord_770210).sum := by decide
  have hdescent : baseEnd_770210 < baseStart_770210 := by decide
  rcases family_descends (prefixWord ++ tailWord_770210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_770315 : List Nat := [1, 1, 1, 1, 5, 2, 2, 1, 3, 5]
def baseStart_770315 : Nat := 118140960795 + 770315 * 2 ^ 59
def prefixEnd_770315 : Nat := 4983230072969 + 3 ^ 40 * 770315 * 2
def baseEnd_770315 : Nat := 263694566912172581813261

theorem tailTrace_770315 : CollatzResearch.WordTrace tailWord_770315 prefixEnd_770315 263694566912172581813261 := by
  unfold tailWord_770315
  simp only [CollatzResearch.WordTrace]
  refine ⟨28095696204287789173136399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18730464136191859448757599 28095696204287789173136399)
  ·
    refine ⟨42143544306431683759704599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28095696204287789173136399 42143544306431683759704599)
    ·
      refine ⟨63215316459647525639556899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42143544306431683759704599 63215316459647525639556899)
      ·
        refine ⟨94822974689471288459335349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63215316459647525639556899 94822974689471288459335349)
        ·
          refine ⟨8889653877137933293062689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 94822974689471288459335349 8889653877137933293062689)
          ·
            refine ⟨6667240407853449969797017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8889653877137933293062689 6667240407853449969797017)
            ·
              refine ⟨5000430305890087477347763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6667240407853449969797017 5000430305890087477347763)
              ·
                refine ⟨7500645458835131216021645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5000430305890087477347763 7500645458835131216021645)
                ·
                  refine ⟨2812742047063174206008117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7500645458835131216021645 2812742047063174206008117)
                  ·
                    refine ⟨263694566912172581813261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2812742047063174206008117 263694566912172581813261)
                    ·
                      rfl

theorem cell22_770315_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 2, 1, 3, 5].length) (baseStart_770315 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_770315 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_770315 prefixEnd_770315 := by exact prefixLift 770315
  have htrace : WordTrace (prefixWord ++ tailWord_770315) baseStart_770315 baseEnd_770315 := by
    simpa [prefixWord, tailWord_770315, baseEnd_770315] using wordTrace_append hprefix tailTrace_770315
  have hstable : (prefixWord ++ tailWord_770315).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_770315).length < 2 ^ (prefixWord ++ tailWord_770315).sum := by decide
  have hdescent : baseEnd_770315 < baseStart_770315 := by decide
  rcases family_descends (prefixWord ++ tailWord_770315) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_770360 : List Nat := [2, 1, 2, 1, 3, 1, 2, 1, 2, 7]
def baseStart_770360 : Nat := 118140960795 + 770360 * 2 ^ 59
def prefixEnd_770360 : Nat := 4983230072969 + 3 ^ 40 * 770360 * 2
def baseEnd_770360 : Nat := 263709971331807464438123

theorem tailTrace_770360 : CollatzResearch.WordTrace tailWord_770360 prefixEnd_770360 263709971331807464438123 := by
  unfold tailWord_770360
  simp only [CollatzResearch.WordTrace]
  refine ⟨14048668744562380929262267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18731558326083174572349689 14048668744562380929262267)
  ·
    refine ⟨21073003116843571393893401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14048668744562380929262267 21073003116843571393893401)
    ·
      refine ⟨15804752337632678545420051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21073003116843571393893401 15804752337632678545420051)
      ·
        refine ⟨23707128506449017818130077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15804752337632678545420051 23707128506449017818130077)
        ·
          refine ⟨8890173189918381681798779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23707128506449017818130077 8890173189918381681798779)
          ·
            refine ⟨13335259784877572522698169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8890173189918381681798779 13335259784877572522698169)
            ·
              refine ⟨10001444838658179392023627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13335259784877572522698169 10001444838658179392023627)
              ·
                refine ⟨15002167257987269088035441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10001444838658179392023627 15002167257987269088035441)
                ·
                  refine ⟨11251625443490451816026581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15002167257987269088035441 11251625443490451816026581)
                  ·
                    refine ⟨263709971331807464438123, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 11251625443490451816026581 263709971331807464438123)
                    ·
                      rfl

theorem cell22_770360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 2, 1, 2, 7].length) (baseStart_770360 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_770360 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_770360 prefixEnd_770360 := by exact prefixLift 770360
  have htrace : WordTrace (prefixWord ++ tailWord_770360) baseStart_770360 baseEnd_770360 := by
    simpa [prefixWord, tailWord_770360, baseEnd_770360] using wordTrace_append hprefix tailTrace_770360
  have hstable : (prefixWord ++ tailWord_770360).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_770360).length < 2 ^ (prefixWord ++ tailWord_770360).sum := by decide
  have hdescent : baseEnd_770360 < baseStart_770360 := by decide
  rcases family_descends (prefixWord ++ tailWord_770360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_770396 : List Nat := [2, 2, 4, 3, 1, 2, 1, 7]
def baseStart_770396 : Nat := 118140960795 + 770396 * 2 ^ 59
def prefixEnd_770396 : Nat := 4983230072969 + 3 ^ 40 * 770396 * 2
def baseEnd_770396 : Nat := 29302477207501707837557

theorem tailTrace_770396 : CollatzResearch.WordTrace tailWord_770396 prefixEnd_770396 29302477207501707837557 := by
  unfold tailWord_770396
  simp only [CollatzResearch.WordTrace]
  refine ⟨14049325258497170003417521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18732433677996226671223361 14049325258497170003417521)
  ·
    refine ⟨10536993943872877502563141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14049325258497170003417521 10536993943872877502563141)
    ·
      refine ⟨1975686364476164531730589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 10536993943872877502563141 1975686364476164531730589)
      ·
        refine ⟨740882386678561699398971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1975686364476164531730589 740882386678561699398971)
        ·
          refine ⟨1111323580017842549098457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 740882386678561699398971 1111323580017842549098457)
          ·
            refine ⟨833492685013381911823843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1111323580017842549098457 833492685013381911823843)
            ·
              refine ⟨1250239027520072867735765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 833492685013381911823843 1250239027520072867735765)
              ·
                refine ⟨29302477207501707837557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1250239027520072867735765 29302477207501707837557)
                ·
                  rfl

theorem cell22_770396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 1, 2, 1, 7].length) (baseStart_770396 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_770396 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_770396 prefixEnd_770396 := by exact prefixLift 770396
  have htrace : WordTrace (prefixWord ++ tailWord_770396) baseStart_770396 baseEnd_770396 := by
    simpa [prefixWord, tailWord_770396, baseEnd_770396] using wordTrace_append hprefix tailTrace_770396
  have hstable : (prefixWord ++ tailWord_770396).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_770396).length < 2 ^ (prefixWord ++ tailWord_770396).sum := by decide
  have hdescent : baseEnd_770396 < baseStart_770396 := by decide
  rcases family_descends (prefixWord ++ tailWord_770396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_770471 : List Nat := [1, 1, 6, 1, 1, 3, 2, 2, 1, 4]
def baseStart_770471 : Nat := 118140960795 + 770471 * 2 ^ 59
def prefixEnd_770471 : Nat := 4983230072969 + 3 ^ 40 * 770471 * 2
def baseEnd_770471 : Nat := 263747968900240174912783

theorem tailTrace_770471 : CollatzResearch.WordTrace tailWord_770471 prefixEnd_770471 263747968900240174912783 := by
  unfold tailWord_770471
  simp only [CollatzResearch.WordTrace]
  refine ⟨28101385991722627815815267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18734257327815085210543511 28101385991722627815815267)
  ·
    refine ⟨42152078987583941723722901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28101385991722627815815267 42152078987583941723722901)
    ·
      refine ⟨1975878702542997268299511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 42152078987583941723722901 1975878702542997268299511)
      ·
        refine ⟨2963818053814495902449267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1975878702542997268299511 2963818053814495902449267)
        ·
          refine ⟨4445727080721743853673901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2963818053814495902449267 4445727080721743853673901)
          ·
            refine ⟨1667147655270653945127713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4445727080721743853673901 1667147655270653945127713)
            ·
              refine ⟨1250360741452990458845785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1667147655270653945127713 1250360741452990458845785)
              ·
                refine ⟨937770556089742844134339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1250360741452990458845785 937770556089742844134339)
                ·
                  refine ⟨1406655834134614266201509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 937770556089742844134339 1406655834134614266201509)
                  ·
                    refine ⟨263747968900240174912783, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1406655834134614266201509 263747968900240174912783)
                    ·
                      rfl

theorem cell22_770471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 3, 2, 2, 1, 4].length) (baseStart_770471 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_770471 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_770471 prefixEnd_770471 := by exact prefixLift 770471
  have htrace : WordTrace (prefixWord ++ tailWord_770471) baseStart_770471 baseEnd_770471 := by
    simpa [prefixWord, tailWord_770471, baseEnd_770471] using wordTrace_append hprefix tailTrace_770471
  have hstable : (prefixWord ++ tailWord_770471).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_770471).length < 2 ^ (prefixWord ++ tailWord_770471).sum := by decide
  have hdescent : baseEnd_770471 < baseStart_770471 := by decide
  rcases family_descends (prefixWord ++ tailWord_770471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_770482 : List Nat := [3, 2, 1, 1, 1, 1, 3, 3, 1, 6]
def baseStart_770482 : Nat := 118140960795 + 770482 * 2 ^ 59
def prefixEnd_770482 : Nat := 4983230072969 + 3 ^ 40 * 770482 * 2
def baseEnd_770482 : Nat := 263751734425039812887749

theorem tailTrace_770482 : CollatzResearch.WordTrace tailWord_770482 prefixEnd_770482 263751734425039812887749 := by
  unfold tailWord_770482
  simp only [CollatzResearch.WordTrace]
  refine ⟨7025446798670694173616425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18734524796455184462977133 7025446798670694173616425)
  ·
    refine ⟨5269085099003020630212319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7025446798670694173616425 5269085099003020630212319)
    ·
      refine ⟨7903627648504530945318479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5269085099003020630212319 7903627648504530945318479)
      ·
        refine ⟨11855441472756796417977719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7903627648504530945318479 11855441472756796417977719)
        ·
          refine ⟨17783162209135194626966579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11855441472756796417977719 17783162209135194626966579)
          ·
            refine ⟨26674743313702791940449869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17783162209135194626966579 26674743313702791940449869)
            ·
              refine ⟨10003028742638546977668701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26674743313702791940449869 10003028742638546977668701)
              ·
                refine ⟨3751135778489455116625763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10003028742638546977668701 3751135778489455116625763)
                ·
                  refine ⟨5626703667734182674938645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3751135778489455116625763 5626703667734182674938645)
                  ·
                    refine ⟨263751734425039812887749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5626703667734182674938645 263751734425039812887749)
                    ·
                      rfl

theorem cell22_770482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 3, 3, 1, 6].length) (baseStart_770482 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_770482 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_770482 prefixEnd_770482 := by exact prefixLift 770482
  have htrace : WordTrace (prefixWord ++ tailWord_770482) baseStart_770482 baseEnd_770482 := by
    simpa [prefixWord, tailWord_770482, baseEnd_770482] using wordTrace_append hprefix tailTrace_770482
  have hstable : (prefixWord ++ tailWord_770482).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_770482).length < 2 ^ (prefixWord ++ tailWord_770482).sum := by decide
  have hdescent : baseEnd_770482 < baseStart_770482 := by decide
  rcases family_descends (prefixWord ++ tailWord_770482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_770518 : List Nat := [5, 2, 1, 1, 1, 1, 3, 3, 2, 3]
def baseStart_770518 : Nat := 118140960795 + 770518 * 2 ^ 59
def prefixEnd_770518 : Nat := 4983230072969 + 3 ^ 40 * 770518 * 2
def baseEnd_770518 : Nat := 263764057960747718987639

theorem tailTrace_770518 : CollatzResearch.WordTrace tailWord_770518 prefixEnd_770518 263764057960747718987639 := by
  unfold tailWord_770518
  simp only [CollatzResearch.WordTrace]
  refine ⟨1756443763909522177673513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 18735400148368236561850805 1756443763909522177673513)
  ·
    refine ⟨1317332822932141633255135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1756443763909522177673513 1317332822932141633255135)
    ·
      refine ⟨1975999234398212449882703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1317332822932141633255135 1975999234398212449882703)
      ·
        refine ⟨2963998851597318674824055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1975999234398212449882703 2963998851597318674824055)
        ·
          refine ⟨4445998277395978012236083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2963998851597318674824055 4445998277395978012236083)
          ·
            refine ⟨6668997416093967018354125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4445998277395978012236083 6668997416093967018354125)
            ·
              refine ⟨2500874031035237631882797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6668997416093967018354125 2500874031035237631882797)
              ·
                refine ⟨937827761638214111956049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2500874031035237631882797 937827761638214111956049)
                ·
                  refine ⟨703370821228660583967037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 937827761638214111956049 703370821228660583967037)
                  ·
                    refine ⟨263764057960747718987639, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 703370821228660583967037 263764057960747718987639)
                    ·
                      rfl

theorem cell22_770518_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 3, 3, 2, 3].length) (baseStart_770518 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_770518 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_770518 prefixEnd_770518 := by exact prefixLift 770518
  have htrace : WordTrace (prefixWord ++ tailWord_770518) baseStart_770518 baseEnd_770518 := by
    simpa [prefixWord, tailWord_770518, baseEnd_770518] using wordTrace_append hprefix tailTrace_770518
  have hstable : (prefixWord ++ tailWord_770518).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_770518).length < 2 ^ (prefixWord ++ tailWord_770518).sum := by decide
  have hdescent : baseEnd_770518 < baseStart_770518 := by decide
  rcases family_descends (prefixWord ++ tailWord_770518) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_770529 : List Nat := [1, 2, 3, 1, 2, 2, 2, 1, 5, 3]
def baseStart_770529 : Nat := 118140960795 + 770529 * 2 ^ 59
def prefixEnd_770529 : Nat := 4983230072969 + 3 ^ 40 * 770529 * 2
def baseEnd_770529 : Nat := 263767823485547356962605

theorem tailTrace_770529 : CollatzResearch.WordTrace tailWord_770529 prefixEnd_770529 263767823485547356962605 := by
  unfold tailWord_770529
  simp only [CollatzResearch.WordTrace]
  refine ⟨28103501425512503721426641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18735667617008335814284427 28103501425512503721426641)
  ·
    refine ⟨21077626069134377791069981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28103501425512503721426641 21077626069134377791069981)
    ·
      refine ⟨7904109775925391671651243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21077626069134377791069981 7904109775925391671651243)
      ·
        refine ⟨11856164663888087507476865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7904109775925391671651243 11856164663888087507476865)
        ·
          refine ⟨8892123497916065630607649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11856164663888087507476865 8892123497916065630607649)
          ·
            refine ⟨6669092623437049222955737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8892123497916065630607649 6669092623437049222955737)
            ·
              refine ⟨5001819467577786917216803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6669092623437049222955737 5001819467577786917216803)
              ·
                refine ⟨7502729201366680375825205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5001819467577786917216803 7502729201366680375825205)
                ·
                  refine ⟨703380862628126285233613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 7502729201366680375825205 703380862628126285233613)
                  ·
                    refine ⟨263767823485547356962605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 703380862628126285233613 263767823485547356962605)
                    ·
                      rfl

theorem cell22_770529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 2, 1, 5, 3].length) (baseStart_770529 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_770529 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_770529 prefixEnd_770529 := by exact prefixLift 770529
  have htrace : WordTrace (prefixWord ++ tailWord_770529) baseStart_770529 baseEnd_770529 := by
    simpa [prefixWord, tailWord_770529, baseEnd_770529] using wordTrace_append hprefix tailTrace_770529
  have hstable : (prefixWord ++ tailWord_770529).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_770529).length < 2 ^ (prefixWord ++ tailWord_770529).sum := by decide
  have hdescent : baseEnd_770529 < baseStart_770529 := by decide
  rcases family_descends (prefixWord ++ tailWord_770529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_770559 : List Nat := [1, 1, 2, 2, 1, 2, 6, 2, 5]
def baseStart_770559 : Nat := 118140960795 + 770559 * 2 ^ 59
def prefixEnd_770559 : Nat := 4983230072969 + 3 ^ 40 * 770559 * 2
def baseEnd_770559 : Nat := 87926031032879092904171

theorem tailTrace_770559 : CollatzResearch.WordTrace tailWord_770559 prefixEnd_770559 87926031032879092904171 := by
  unfold tailWord_770559
  simp only [CollatzResearch.WordTrace]
  refine ⟨28104595615403818845018731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18736397076935879230012487 28104595615403818845018731)
  ·
    refine ⟨42156893423105728267528097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28104595615403818845018731 42156893423105728267528097)
    ·
      refine ⟨31617670067329296200646073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42156893423105728267528097 31617670067329296200646073)
      ·
        refine ⟨23713252550496972150484555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31617670067329296200646073 23713252550496972150484555)
        ·
          refine ⟨35569878825745458225726833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23713252550496972150484555 35569878825745458225726833)
          ·
            refine ⟨26677409119309093669295125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35569878825745458225726833 26677409119309093669295125)
            ·
              refine ⟨1250503552467613765748209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 26677409119309093669295125 1250503552467613765748209)
              ·
                refine ⟨937877664350710324311157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1250503552467613765748209 937877664350710324311157)
                ·
                  refine ⟨87926031032879092904171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 937877664350710324311157 87926031032879092904171)
                  ·
                    rfl

theorem cell22_770559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 6, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 6, 2, 5].length) (baseStart_770559 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_770559 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_770559 prefixEnd_770559 := by exact prefixLift 770559
  have htrace : WordTrace (prefixWord ++ tailWord_770559) baseStart_770559 baseEnd_770559 := by
    simpa [prefixWord, tailWord_770559, baseEnd_770559] using wordTrace_append hprefix tailTrace_770559
  have hstable : (prefixWord ++ tailWord_770559).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_770559).length < 2 ^ (prefixWord ++ tailWord_770559).sum := by decide
  have hdescent : baseEnd_770559 < baseStart_770559 := by decide
  rcases family_descends (prefixWord ++ tailWord_770559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_770574 : List Nat := [4, 1, 1, 2, 3, 1, 1, 1, 1, 7]
def baseStart_770574 : Nat := 118140960795 + 770574 * 2 ^ 59
def prefixEnd_770574 : Nat := 4983230072969 + 3 ^ 40 * 770574 * 2
def baseEnd_770574 : Nat := 263783227905182239587467

theorem tailTrace_770574 : CollatzResearch.WordTrace tailWord_770574 prefixEnd_770574 263783227905182239587467 := by
  unfold tailWord_770574
  simp only [CollatzResearch.WordTrace]
  refine ⟨3513142838793684550851847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 18736761806899650937876517 3513142838793684550851847)
  ·
    refine ⟨5269714258190526826277771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3513142838793684550851847 5269714258190526826277771)
    ·
      refine ⟨7904571387285790239416657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5269714258190526826277771 7904571387285790239416657)
      ·
        refine ⟨5928428540464342679562493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7904571387285790239416657 5928428540464342679562493)
        ·
          refine ⟨2223160702674128504835935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5928428540464342679562493 2223160702674128504835935)
          ·
            refine ⟨3334741054011192757253903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2223160702674128504835935 3334741054011192757253903)
            ·
              refine ⟨5002111581016789135880855, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3334741054011192757253903 5002111581016789135880855)
              ·
                refine ⟨7503167371525183703821283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5002111581016789135880855 7503167371525183703821283)
                ·
                  refine ⟨11254751057287775555731925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7503167371525183703821283 11254751057287775555731925)
                  ·
                    refine ⟨263783227905182239587467, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 11254751057287775555731925 263783227905182239587467)
                    ·
                      rfl

theorem cell22_770574_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 1, 1, 1, 1, 7].length) (baseStart_770574 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_770574 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_770574 prefixEnd_770574 := by exact prefixLift 770574
  have htrace : WordTrace (prefixWord ++ tailWord_770574) baseStart_770574 baseEnd_770574 := by
    simpa [prefixWord, tailWord_770574, baseEnd_770574] using wordTrace_append hprefix tailTrace_770574
  have hstable : (prefixWord ++ tailWord_770574).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_770574).length < 2 ^ (prefixWord ++ tailWord_770574).sum := by decide
  have hdescent : baseEnd_770574 < baseStart_770574 := by decide
  rcases family_descends (prefixWord ++ tailWord_770574) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_770621 : List Nat := [1, 4, 1, 3, 2, 2, 2, 1, 6]
def baseStart_770621 : Nat := 118140960795 + 770621 * 2 ^ 59
def prefixEnd_770621 : Nat := 4983230072969 + 3 ^ 40 * 770621 * 2
def baseEnd_770621 : Nat := 87933105655229927887441

theorem tailTrace_770621 : CollatzResearch.WordTrace tailWord_770621 prefixEnd_770621 87933105655229927887441 := by
  unfold tailWord_770621
  simp only [CollatzResearch.WordTrace]
  refine ⟨28106856941179203433775717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18737904627452802289183811 28106856941179203433775717)
  ·
    refine ⟨5270035676471100643832947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 28106856941179203433775717 5270035676471100643832947)
    ·
      refine ⟨7905053514706650965749421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5270035676471100643832947 7905053514706650965749421)
      ·
        refine ⟨2964395068014994112156033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7905053514706650965749421 2964395068014994112156033)
        ·
          refine ⟨2223296301011245584117025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2964395068014994112156033 2223296301011245584117025)
          ·
            refine ⟨1667472225758434188087769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2223296301011245584117025 1667472225758434188087769)
            ·
              refine ⟨1250604169318825641065827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1667472225758434188087769 1250604169318825641065827)
              ·
                refine ⟨1875906253978238461598741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1250604169318825641065827 1875906253978238461598741)
                ·
                  refine ⟨87933105655229927887441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1875906253978238461598741 87933105655229927887441)
                  ·
                    rfl

theorem cell22_770621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 2, 2, 1, 6].length) (baseStart_770621 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_770621 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_770621 prefixEnd_770621 := by exact prefixLift 770621
  have htrace : WordTrace (prefixWord ++ tailWord_770621) baseStart_770621 baseEnd_770621 := by
    simpa [prefixWord, tailWord_770621, baseEnd_770621] using wordTrace_append hprefix tailTrace_770621
  have hstable : (prefixWord ++ tailWord_770621).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_770621).length < 2 ^ (prefixWord ++ tailWord_770621).sum := by decide
  have hdescent : baseEnd_770621 < baseStart_770621 := by decide
  rcases family_descends (prefixWord ++ tailWord_770621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_770634 : List Nat := [3, 1, 2, 1, 1, 4, 1, 2, 1, 6]
def baseStart_770634 : Nat := 118140960795 + 770634 * 2 ^ 59
def prefixEnd_770634 : Nat := 4983230072969 + 3 ^ 40 * 770634 * 2
def baseEnd_770634 : Nat := 263803767131362083087283

theorem tailTrace_770634 : CollatzResearch.WordTrace tailWord_770634 prefixEnd_770634 263803767131362083087283 := by
  unfold tailWord_770634
  simp only [CollatzResearch.WordTrace]
  refine ⟨7026832772533026663499739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18738220726754737769332637 7026832772533026663499739)
  ·
    refine ⟨10540249158799539995249609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7026832772533026663499739 10540249158799539995249609)
    ·
      refine ⟨7905186869099654996437207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10540249158799539995249609 7905186869099654996437207)
      ·
        refine ⟨11857780303649482494655811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7905186869099654996437207 11857780303649482494655811)
        ·
          refine ⟨17786670455474223741983717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11857780303649482494655811 17786670455474223741983717)
          ·
            refine ⟨3335000710401416951621947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 17786670455474223741983717 3335000710401416951621947)
            ·
              refine ⟨5002501065602125427432921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3335000710401416951621947 5002501065602125427432921)
              ·
                refine ⟨3751875799201594070574691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5002501065602125427432921 3751875799201594070574691)
                ·
                  refine ⟨5627813698802391105862037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3751875799201594070574691 5627813698802391105862037)
                  ·
                    refine ⟨263803767131362083087283, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5627813698802391105862037 263803767131362083087283)
                    ·
                      rfl

theorem cell22_770634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 4, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 4, 1, 2, 1, 6].length) (baseStart_770634 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_770634 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_770634 prefixEnd_770634 := by exact prefixLift 770634
  have htrace : WordTrace (prefixWord ++ tailWord_770634) baseStart_770634 baseEnd_770634 := by
    simpa [prefixWord, tailWord_770634, baseEnd_770634] using wordTrace_append hprefix tailTrace_770634
  have hstable : (prefixWord ++ tailWord_770634).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_770634).length < 2 ^ (prefixWord ++ tailWord_770634).sum := by decide
  have hdescent : baseEnd_770634 < baseStart_770634 := by decide
  rcases family_descends (prefixWord ++ tailWord_770634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_770709 : List Nat := [1, 3, 2, 1, 1, 1, 1, 1, 6, 5]
def baseStart_770709 : Nat := 118140960795 + 770709 * 2 ^ 59
def prefixEnd_770709 : Nat := 4983230072969 + 3 ^ 40 * 770709 * 2
def baseEnd_770709 : Nat := 263829441164086887462053

theorem tailTrace_770709 : CollatzResearch.WordTrace tailWord_770709 prefixEnd_770709 263829441164086887462053 := by
  unfold tailWord_770709
  simp only [CollatzResearch.WordTrace]
  refine ⟨28110066564860394462979181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18740044376573596308652787 28110066564860394462979181)
  ·
    refine ⟨10541274961822647923617193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28110066564860394462979181 10541274961822647923617193)
    ·
      refine ⟨7905956221366985942712895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10541274961822647923617193 7905956221366985942712895)
      ·
        refine ⟨11858934332050478914069343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7905956221366985942712895 11858934332050478914069343)
        ·
          refine ⟨17788401498075718371104015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11858934332050478914069343 17788401498075718371104015)
          ·
            refine ⟨26682602247113577556656023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17788401498075718371104015 26682602247113577556656023)
            ·
              refine ⟨40023903370670366334984035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26682602247113577556656023 40023903370670366334984035)
              ·
                refine ⟨60035855056005549502476053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40023903370670366334984035 60035855056005549502476053)
                ·
                  refine ⟨2814180705750260132928565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 60035855056005549502476053 2814180705750260132928565)
                  ·
                    refine ⟨263829441164086887462053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2814180705750260132928565 263829441164086887462053)
                    ·
                      rfl

theorem cell22_770709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 1, 6, 5].length) (baseStart_770709 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_770709 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_770709 prefixEnd_770709 := by exact prefixLift 770709
  have htrace : WordTrace (prefixWord ++ tailWord_770709) baseStart_770709 baseEnd_770709 := by
    simpa [prefixWord, tailWord_770709, baseEnd_770709] using wordTrace_append hprefix tailTrace_770709
  have hstable : (prefixWord ++ tailWord_770709).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_770709).length < 2 ^ (prefixWord ++ tailWord_770709).sum := by decide
  have hdescent : baseEnd_770709 < baseStart_770709 := by decide
  rcases family_descends (prefixWord ++ tailWord_770709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_770756 : List Nat := [2, 3, 3, 1, 1, 2, 1, 1, 8]
def baseStart_770756 : Nat := 118140960795 + 770756 * 2 ^ 59
def prefixEnd_770756 : Nat := 4983230072969 + 3 ^ 40 * 770756 * 2
def baseEnd_770756 : Nat := 87948510074864810512303

theorem tailTrace_770756 : CollatzResearch.WordTrace tailWord_770756 prefixEnd_770756 87948510074864810512303 := by
  unfold tailWord_770756
  simp only [CollatzResearch.WordTrace]
  refine ⟨14055890397845060744970061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18741187197126747659960081 14055890397845060744970061)
  ·
    refine ⟨5270958899191897779363773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14055890397845060744970061 5270958899191897779363773)
    ·
      refine ⟨1976609587196961667261415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5270958899191897779363773 1976609587196961667261415)
      ·
        refine ⟨2964914380795442500892123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1976609587196961667261415 2964914380795442500892123)
        ·
          refine ⟨4447371571193163751338185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2964914380795442500892123 4447371571193163751338185)
          ·
            refine ⟨3335528678394872813503639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4447371571193163751338185 3335528678394872813503639)
            ·
              refine ⟨5003293017592309220255459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3335528678394872813503639 5003293017592309220255459)
              ·
                refine ⟨7504939526388463830383189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5003293017592309220255459 7504939526388463830383189)
                ·
                  refine ⟨87948510074864810512303, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 7504939526388463830383189 87948510074864810512303)
                  ·
                    rfl

theorem cell22_770756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 2, 1, 1, 8].length) (baseStart_770756 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_770756 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_770756 prefixEnd_770756 := by exact prefixLift 770756
  have htrace : WordTrace (prefixWord ++ tailWord_770756) baseStart_770756 baseEnd_770756 := by
    simpa [prefixWord, tailWord_770756, baseEnd_770756] using wordTrace_append hprefix tailTrace_770756
  have hstable : (prefixWord ++ tailWord_770756).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_770756).length < 2 ^ (prefixWord ++ tailWord_770756).sum := by decide
  have hdescent : baseEnd_770756 < baseStart_770756 := by decide
  rcases family_descends (prefixWord ++ tailWord_770756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_770775 : List Nat := [1, 1, 3, 2, 1, 6, 2, 1, 1, 4]
def baseStart_770775 : Nat := 118140960795 + 770775 * 2 ^ 59
def prefixEnd_770775 : Nat := 4983230072969 + 3 ^ 40 * 770775 * 2
def baseEnd_770775 : Nat := 263852034312884715311851

theorem tailTrace_770775 : CollatzResearch.WordTrace tailWord_770775 prefixEnd_770775 263852034312884715311851 := by
  unfold tailWord_770775
  simp only [CollatzResearch.WordTrace]
  refine ⟨28112473782621287734881779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18741649188414191823254519 28112473782621287734881779)
  ·
    refine ⟨42168710673931931602322669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28112473782621287734881779 42168710673931931602322669)
    ·
      refine ⟨15813266502724474350871001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 42168710673931931602322669 15813266502724474350871001)
      ·
        refine ⟨11859949877043355763153251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15813266502724474350871001 11859949877043355763153251)
        ·
          refine ⟨17789924815565033644729877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11859949877043355763153251 17789924815565033644729877)
          ·
            refine ⟨833902725729610952096713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 17789924815565033644729877 833902725729610952096713)
            ·
              refine ⟨625427044297208214072535, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 833902725729610952096713 625427044297208214072535)
              ·
                refine ⟨938140566445812321108803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 625427044297208214072535 938140566445812321108803)
                ·
                  refine ⟨1407210849668718481663205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 938140566445812321108803 1407210849668718481663205)
                  ·
                    refine ⟨263852034312884715311851, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1407210849668718481663205 263852034312884715311851)
                    ·
                      rfl

theorem cell22_770775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 6, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 6, 2, 1, 1, 4].length) (baseStart_770775 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_770775 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_770775 prefixEnd_770775 := by exact prefixLift 770775
  have htrace : WordTrace (prefixWord ++ tailWord_770775) baseStart_770775 baseEnd_770775 := by
    simpa [prefixWord, tailWord_770775, baseEnd_770775] using wordTrace_append hprefix tailTrace_770775
  have hstable : (prefixWord ++ tailWord_770775).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_770775).length < 2 ^ (prefixWord ++ tailWord_770775).sum := by decide
  have hdescent : baseEnd_770775 < baseStart_770775 := by decide
  rcases family_descends (prefixWord ++ tailWord_770775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_770788 : List Nat := [2, 3, 1, 1, 1, 5, 1, 1, 4, 3]
def baseStart_770788 : Nat := 118140960795 + 770788 * 2 ^ 59
def prefixEnd_770788 : Nat := 4983230072969 + 3 ^ 40 * 770788 * 2
def baseEnd_770788 : Nat := 263856484478557014736811

theorem tailTrace_770788 : CollatzResearch.WordTrace tailWord_770788 prefixEnd_770788 263856484478557014736811 := by
  unfold tailWord_770788
  simp only [CollatzResearch.WordTrace]
  refine ⟨14056473965787095477552509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18741965287716127303403345 14056473965787095477552509)
  ·
    refine ⟨5271177737170160804082191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14056473965787095477552509 5271177737170160804082191)
    ·
      refine ⟨7906766605755241206123287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5271177737170160804082191 7906766605755241206123287)
      ·
        refine ⟨11860149908632861809184931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7906766605755241206123287 11860149908632861809184931)
        ·
          refine ⟨17790224862949292713777397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11860149908632861809184931 17790224862949292713777397)
          ·
            refine ⟨1667833580901496191916631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 17790224862949292713777397 1667833580901496191916631)
            ·
              refine ⟨2501750371352244287874947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1667833580901496191916631 2501750371352244287874947)
              ·
                refine ⟨3752625557028366431812421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2501750371352244287874947 3752625557028366431812421)
                ·
                  refine ⟨703617291942818705964829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3752625557028366431812421 703617291942818705964829)
                  ·
                    refine ⟨263856484478557014736811, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 703617291942818705964829 263856484478557014736811)
                    ·
                      rfl

theorem cell22_770788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 5, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 5, 1, 1, 4, 3].length) (baseStart_770788 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_770788 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_770788 prefixEnd_770788 := by exact prefixLift 770788
  have htrace : WordTrace (prefixWord ++ tailWord_770788) baseStart_770788 baseEnd_770788 := by
    simpa [prefixWord, tailWord_770788, baseEnd_770788] using wordTrace_append hprefix tailTrace_770788
  have hstable : (prefixWord ++ tailWord_770788).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_770788).length < 2 ^ (prefixWord ++ tailWord_770788).sum := by decide
  have hdescent : baseEnd_770788 < baseStart_770788 := by decide
  rcases family_descends (prefixWord ++ tailWord_770788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_770818 : List Nat := [3, 4, 1, 1, 1, 3, 1, 8]
def baseStart_770818 : Nat := 118140960795 + 770818 * 2 ^ 59
def prefixEnd_770818 : Nat := 4983230072969 + 3 ^ 40 * 770818 * 2
def baseEnd_770818 : Nat := 29318528232405215165191

theorem tailTrace_770818 : CollatzResearch.WordTrace tailWord_770818 prefixEnd_770818 29318528232405215165191 := by
  unfold tailWord_770818
  simp only [CollatzResearch.WordTrace]
  refine ⟨7028510530366376519674277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18742694747643670719131405 7028510530366376519674277)
  ·
    refine ⟨1317845724443695597438927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 7028510530366376519674277 1317845724443695597438927)
    ·
      refine ⟨1976768586665543396158391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1317845724443695597438927 1976768586665543396158391)
      ·
        refine ⟨2965152879998315094237587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1976768586665543396158391 2965152879998315094237587)
        ·
          refine ⟨4447729319997472641356381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2965152879998315094237587 4447729319997472641356381)
          ·
            refine ⟨1667898494999052240508643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4447729319997472641356381 1667898494999052240508643)
            ·
              refine ⟨2501847742498578360762965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1667898494999052240508643 2501847742498578360762965)
              ·
                refine ⟨29318528232405215165191, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 2501847742498578360762965 29318528232405215165191)
                ·
                  rfl

theorem cell22_770818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 3, 1, 8].length) (baseStart_770818 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_770818 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_770818 prefixEnd_770818 := by exact prefixLift 770818
  have htrace : WordTrace (prefixWord ++ tailWord_770818) baseStart_770818 baseEnd_770818 := by
    simpa [prefixWord, tailWord_770818, baseEnd_770818] using wordTrace_append hprefix tailTrace_770818
  have hstable : (prefixWord ++ tailWord_770818).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_770818).length < 2 ^ (prefixWord ++ tailWord_770818).sum := by decide
  have hdescent : baseEnd_770818 < baseStart_770818 := by decide
  rcases family_descends (prefixWord ++ tailWord_770818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_770850 : List Nat := [3, 3, 1, 1, 2, 2, 3, 1, 3, 3]
def baseStart_770850 : Nat := 118140960795 + 770850 * 2 ^ 59
def prefixEnd_770850 : Nat := 4983230072969 + 3 ^ 40 * 770850 * 2
def baseEnd_770850 : Nat := 263877708345609519686621

theorem tailTrace_770850 : CollatzResearch.WordTrace tailWord_770850 prefixEnd_770850 263877708345609519686621 := by
  unfold tailWord_770850
  simp only [CollatzResearch.WordTrace]
  refine ⟨7028802314337393885965501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18743472838233050362574669 7028802314337393885965501)
  ·
    refine ⟨2635800867876522707237063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7028802314337393885965501 2635800867876522707237063)
    ·
      refine ⟨3953701301814784060855595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2635800867876522707237063 3953701301814784060855595)
      ·
        refine ⟨5930551952722176091283393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3953701301814784060855595 5930551952722176091283393)
        ·
          refine ⟨4447913964541632068462545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5930551952722176091283393 4447913964541632068462545)
          ·
            refine ⟨3335935473406224051346909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4447913964541632068462545 3335935473406224051346909)
            ·
              refine ⟨1250975802527334019255091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3335935473406224051346909 1250975802527334019255091)
              ·
                refine ⟨1876463703791001028882637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1250975802527334019255091 1876463703791001028882637)
                ·
                  refine ⟨703673888921625385830989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1876463703791001028882637 703673888921625385830989)
                  ·
                    refine ⟨263877708345609519686621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 703673888921625385830989 263877708345609519686621)
                    ·
                      rfl

theorem cell22_770850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 2, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 2, 3, 1, 3, 3].length) (baseStart_770850 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_770850 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_770850 prefixEnd_770850 := by exact prefixLift 770850
  have htrace : WordTrace (prefixWord ++ tailWord_770850) baseStart_770850 baseEnd_770850 := by
    simpa [prefixWord, tailWord_770850, baseEnd_770850] using wordTrace_append hprefix tailTrace_770850
  have hstable : (prefixWord ++ tailWord_770850).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_770850).length < 2 ^ (prefixWord ++ tailWord_770850).sum := by decide
  have hdescent : baseEnd_770850 < baseStart_770850 := by decide
  rcases family_descends (prefixWord ++ tailWord_770850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_771019 : List Nat := [1, 1, 1, 1, 3, 6, 3, 2, 1, 3]
def baseStart_771019 : Nat := 118140960795 + 771019 * 2 ^ 59
def prefixEnd_771019 : Nat := 4983230072969 + 3 ^ 40 * 771019 * 2
def baseEnd_771019 : Nat := 263935560499349412211103

theorem tailTrace_771019 : CollatzResearch.WordTrace tailWord_771019 prefixEnd_771019 263935560499349412211103 := by
  unfold tailWord_771019
  simp only [CollatzResearch.WordTrace]
  refine ⟨28121373193737317406764111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18747582129158211604509407 28121373193737317406764111)
  ·
    refine ⟨42182059790605976110146167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28121373193737317406764111 42182059790605976110146167)
    ·
      refine ⟨63273089685908964165219251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42182059790605976110146167 63273089685908964165219251)
      ·
        refine ⟨94909634528863446247828877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63273089685908964165219251 94909634528863446247828877)
        ·
          refine ⟨35591112948323792342935829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 94909634528863446247828877 35591112948323792342935829)
          ·
            refine ⟨1668333419452677766075117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 35591112948323792342935829 1668333419452677766075117)
            ·
              refine ⟨625625032294754162278169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1668333419452677766075117 625625032294754162278169)
              ·
                refine ⟨469218774221065621708627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 625625032294754162278169 469218774221065621708627)
                ·
                  refine ⟨703828161331598432562941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 469218774221065621708627 703828161331598432562941)
                  ·
                    refine ⟨263935560499349412211103, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 703828161331598432562941 263935560499349412211103)
                    ·
                      rfl

theorem cell22_771019_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 6, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 6, 3, 2, 1, 3].length) (baseStart_771019 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_771019 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_771019 prefixEnd_771019 := by exact prefixLift 771019
  have htrace : WordTrace (prefixWord ++ tailWord_771019) baseStart_771019 baseEnd_771019 := by
    simpa [prefixWord, tailWord_771019, baseEnd_771019] using wordTrace_append hprefix tailTrace_771019
  have hstable : (prefixWord ++ tailWord_771019).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_771019).length < 2 ^ (prefixWord ++ tailWord_771019).sum := by decide
  have hdescent : baseEnd_771019 < baseStart_771019 := by decide
  rcases family_descends (prefixWord ++ tailWord_771019) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_771032 : List Nat := [2, 1, 2, 2, 2, 5, 2, 1, 5]
def baseStart_771032 : Nat := 118140960795 + 771032 * 2 ^ 59
def prefixEnd_771032 : Nat := 4983230072969 + 3 ^ 40 * 771032 * 2
def baseEnd_771032 : Nat := 87980003555007237212021

theorem tailTrace_771032 : CollatzResearch.WordTrace tailWord_771032 prefixEnd_771032 87980003555007237212021 := by
  unfold tailWord_771032
  simp only [CollatzResearch.WordTrace]
  refine ⟨14060923671345110313493675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18747898228460147084658233 14060923671345110313493675)
  ·
    refine ⟨21091385507017665470240513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14060923671345110313493675 21091385507017665470240513)
    ·
      refine ⟨15818539130263249102680385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21091385507017665470240513 15818539130263249102680385)
      ·
        refine ⟨11863904347697436827010289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15818539130263249102680385 11863904347697436827010289)
        ·
          refine ⟨8897928260773077620257717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11863904347697436827010289 8897928260773077620257717)
          ·
            refine ⟨834180774447476026899161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 8897928260773077620257717 834180774447476026899161)
            ·
              refine ⟨625635580835607020174371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 834180774447476026899161 625635580835607020174371)
              ·
                refine ⟨938453371253410530261557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 625635580835607020174371 938453371253410530261557)
                ·
                  refine ⟨87980003555007237212021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 938453371253410530261557 87980003555007237212021)
                  ·
                    rfl

theorem cell22_771032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 5, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 5, 2, 1, 5].length) (baseStart_771032 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_771032 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_771032 prefixEnd_771032 := by exact prefixLift 771032
  have htrace : WordTrace (prefixWord ++ tailWord_771032) baseStart_771032 baseEnd_771032 := by
    simpa [prefixWord, tailWord_771032, baseEnd_771032] using wordTrace_append hprefix tailTrace_771032
  have hstable : (prefixWord ++ tailWord_771032).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_771032).length < 2 ^ (prefixWord ++ tailWord_771032).sum := by decide
  have hdescent : baseEnd_771032 < baseStart_771032 := by decide
  rcases family_descends (prefixWord ++ tailWord_771032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_771043 : List Nat := [1, 1, 1, 6, 1, 1, 2, 1, 8]
def baseStart_771043 : Nat := 118140960795 + 771043 * 2 ^ 59
def prefixEnd_771043 : Nat := 4983230072969 + 3 ^ 40 * 771043 * 2
def baseEnd_771043 : Nat := 87981258729940449870343

theorem tailTrace_771043 : CollatzResearch.WordTrace tailWord_771043 prefixEnd_771043 87981258729940449870343 := by
  unfold tailWord_771043
  simp only [CollatzResearch.WordTrace]
  refine ⟨28122248545650369505637783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18748165697100246337091855 28122248545650369505637783)
  ·
    refine ⟨42183372818475554258456675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28122248545650369505637783 42183372818475554258456675)
    ·
      refine ⟨63275059227713331387685013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42183372818475554258456675 63275059227713331387685013)
      ·
        refine ⟨2966018401299062408797735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 63275059227713331387685013 2966018401299062408797735)
        ·
          refine ⟨4449027601948593613196603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2966018401299062408797735 4449027601948593613196603)
          ·
            refine ⟨6673541402922890419794905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4449027601948593613196603 6673541402922890419794905)
            ·
              refine ⟨5005156052192167814846179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6673541402922890419794905 5005156052192167814846179)
              ·
                refine ⟨7507734078288251722269269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5005156052192167814846179 7507734078288251722269269)
                ·
                  refine ⟨87981258729940449870343, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 7507734078288251722269269 87981258729940449870343)
                  ·
                    rfl

theorem cell22_771043_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 2, 1, 8].length) (baseStart_771043 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_771043 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_771043 prefixEnd_771043 := by exact prefixLift 771043
  have htrace : WordTrace (prefixWord ++ tailWord_771043) baseStart_771043 baseEnd_771043 := by
    simpa [prefixWord, tailWord_771043, baseEnd_771043] using wordTrace_append hprefix tailTrace_771043
  have hstable : (prefixWord ++ tailWord_771043).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_771043).length < 2 ^ (prefixWord ++ tailWord_771043).sum := by decide
  have hdescent : baseEnd_771043 < baseStart_771043 := by decide
  rcases family_descends (prefixWord ++ tailWord_771043) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_771070 : List Nat := [4, 2, 2, 2, 3, 1, 2, 2, 1, 3]
def baseStart_771070 : Nat := 118140960795 + 771070 * 2 ^ 59
def prefixEnd_771070 : Nat := 4983230072969 + 3 ^ 40 * 771070 * 2
def baseEnd_771070 : Nat := 263953018841602279185947

theorem tailTrace_771070 : CollatzResearch.WordTrace tailWord_771070 prefixEnd_771070 263953018841602279185947 := by
  unfold tailWord_771070
  simp only [CollatzResearch.WordTrace]
  refine ⟨3515404164569069139608833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 18748822211035035411247109 3515404164569069139608833)
  ·
    refine ⟨2636553123426801854706625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3515404164569069139608833 2636553123426801854706625)
    ·
      refine ⟨1977414842570101391029969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2636553123426801854706625 1977414842570101391029969)
      ·
        refine ⟨1483061131927576043272477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1977414842570101391029969 1483061131927576043272477)
        ·
          refine ⟨556147924472841016227179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1483061131927576043272477 556147924472841016227179)
          ·
            refine ⟨834221886709261524340769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 556147924472841016227179 834221886709261524340769)
            ·
              refine ⟨625666415031946143255577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 834221886709261524340769 625666415031946143255577)
              ·
                refine ⟨469249811273959607441683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 625666415031946143255577 469249811273959607441683)
                ·
                  refine ⟨703874716910939411162525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 469249811273959607441683 703874716910939411162525)
                  ·
                    refine ⟨263953018841602279185947, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 703874716910939411162525 263953018841602279185947)
                    ·
                      rfl

theorem cell22_771070_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 3, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 3, 1, 2, 2, 1, 3].length) (baseStart_771070 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_771070 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_771070 prefixEnd_771070 := by exact prefixLift 771070
  have htrace : WordTrace (prefixWord ++ tailWord_771070) baseStart_771070 baseEnd_771070 := by
    simpa [prefixWord, tailWord_771070, baseEnd_771070] using wordTrace_append hprefix tailTrace_771070
  have hstable : (prefixWord ++ tailWord_771070).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_771070).length < 2 ^ (prefixWord ++ tailWord_771070).sum := by decide
  have hdescent : baseEnd_771070 < baseStart_771070 := by decide
  rcases family_descends (prefixWord ++ tailWord_771070) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_771107 : List Nat := [1, 1, 1, 4, 3, 4, 1, 1, 2, 4]
def baseStart_771107 : Nat := 118140960795 + 771107 * 2 ^ 59
def prefixEnd_771107 : Nat := 4983230072969 + 3 ^ 40 * 771107 * 2
def baseEnd_771107 : Nat := 263965684697746516010833

theorem tailTrace_771107 : CollatzResearch.WordTrace tailWord_771107 prefixEnd_771107 263965684697746516010833 := by
  unfold tailWord_771107
  simp only [CollatzResearch.WordTrace]
  refine ⟨28124582817418508435967575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18749721878279005623978383 28124582817418508435967575)
  ·
    refine ⟨42186874226127762653951363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28124582817418508435967575 42186874226127762653951363)
    ·
      refine ⟨63280311339191643980927045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42186874226127762653951363 63280311339191643980927045)
      ·
        refine ⟨11865058376098433246423821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 63280311339191643980927045 11865058376098433246423821)
        ·
          refine ⟨4449396891036912467408933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11865058376098433246423821 4449396891036912467408933)
          ·
            refine ⟨834261917069421087639175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4449396891036912467408933 834261917069421087639175)
            ·
              refine ⟨1251392875604131631458763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 834261917069421087639175 1251392875604131631458763)
              ·
                refine ⟨1877089313406197447188145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1251392875604131631458763 1877089313406197447188145)
                ·
                  refine ⟨1407816985054648085391109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1877089313406197447188145 1407816985054648085391109)
                  ·
                    refine ⟨263965684697746516010833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1407816985054648085391109 263965684697746516010833)
                    ·
                      rfl

theorem cell22_771107_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 4, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 4, 1, 1, 2, 4].length) (baseStart_771107 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_771107 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_771107 prefixEnd_771107 := by exact prefixLift 771107
  have htrace : WordTrace (prefixWord ++ tailWord_771107) baseStart_771107 baseEnd_771107 := by
    simpa [prefixWord, tailWord_771107, baseEnd_771107] using wordTrace_append hprefix tailTrace_771107
  have hstable : (prefixWord ++ tailWord_771107).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_771107).length < 2 ^ (prefixWord ++ tailWord_771107).sum := by decide
  have hdescent : baseEnd_771107 < baseStart_771107 := by decide
  rcases family_descends (prefixWord ++ tailWord_771107) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_771120 : List Nat := [2, 1, 1, 1, 2, 4, 1, 2, 5, 3]
def baseStart_771120 : Nat := 118140960795 + 771120 * 2 ^ 59
def prefixEnd_771120 : Nat := 4983230072969 + 3 ^ 40 * 771120 * 2
def baseEnd_771120 : Nat := 263970134863418815435793

theorem tailTrace_771120 : CollatzResearch.WordTrace tailWord_771120 prefixEnd_771120 263970134863418815435793 := by
  unfold tailWord_771120
  simp only [CollatzResearch.WordTrace]
  refine ⟨14062528483185705828095407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18750037977580941104127209 14062528483185705828095407)
  ·
    refine ⟨21093792724778558742143111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14062528483185705828095407 21093792724778558742143111)
    ·
      refine ⟨31640689087167838113214667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21093792724778558742143111 31640689087167838113214667)
      ·
        refine ⟨47461033630751757169822001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31640689087167838113214667 47461033630751757169822001)
        ·
          refine ⟨35595775223063817877366501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47461033630751757169822001 35595775223063817877366501)
          ·
            refine ⟨6674207854324465852006219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 35595775223063817877366501 6674207854324465852006219)
            ·
              refine ⟨10011311781486698778009329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6674207854324465852006219 10011311781486698778009329)
              ·
                refine ⟨7508483836115024083506997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10011311781486698778009329 7508483836115024083506997)
                ·
                  refine ⟨703920359635783507828781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 7508483836115024083506997 703920359635783507828781)
                  ·
                    refine ⟨263970134863418815435793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 703920359635783507828781 263970134863418815435793)
                    ·
                      rfl

theorem cell22_771120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 1, 2, 5, 3].length) (baseStart_771120 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_771120 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_771120 prefixEnd_771120 := by exact prefixLift 771120
  have htrace : WordTrace (prefixWord ++ tailWord_771120) baseStart_771120 baseEnd_771120 := by
    simpa [prefixWord, tailWord_771120, baseEnd_771120] using wordTrace_append hprefix tailTrace_771120
  have hstable : (prefixWord ++ tailWord_771120).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_771120).length < 2 ^ (prefixWord ++ tailWord_771120).sum := by decide
  have hdescent : baseEnd_771120 < baseStart_771120 := by decide
  rcases family_descends (prefixWord ++ tailWord_771120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_771126 : List Nat := [5, 1, 2, 1, 1, 4, 1, 2, 2, 3]
def baseStart_771126 : Nat := 118140960795 + 771126 * 2 ^ 59
def prefixEnd_771126 : Nat := 4983230072969 + 3 ^ 40 * 771126 * 2
def baseEnd_771126 : Nat := 263972188786036799785775

theorem tailTrace_771126 : CollatzResearch.WordTrace tailWord_771126 prefixEnd_771126 263972188786036799785775 := by
  unfold tailWord_771126
  simp only [CollatzResearch.WordTrace]
  refine ⟨1757829737771854667556827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 18750183869566449787272821 1757829737771854667556827)
  ·
    refine ⟨2636744606657782001335241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1757829737771854667556827 2636744606657782001335241)
    ·
      refine ⟨1977558454993336501001431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2636744606657782001335241 1977558454993336501001431)
      ·
        refine ⟨2966337682490004751502147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1977558454993336501001431 2966337682490004751502147)
        ·
          refine ⟨4449506523735007127253221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2966337682490004751502147 4449506523735007127253221)
          ·
            refine ⟨834282473200313836359979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4449506523735007127253221 834282473200313836359979)
            ·
              refine ⟨1251423709800470754539969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 834282473200313836359979 1251423709800470754539969)
              ·
                refine ⟨938567782350353065904977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1251423709800470754539969 938567782350353065904977)
                ·
                  refine ⟨703925836762764799428733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 938567782350353065904977 703925836762764799428733)
                  ·
                    refine ⟨263972188786036799785775, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 703925836762764799428733 263972188786036799785775)
                    ·
                      rfl

theorem cell22_771126_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 4, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 4, 1, 2, 2, 3].length) (baseStart_771126 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_771126 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_771126 prefixEnd_771126 := by exact prefixLift 771126
  have htrace : WordTrace (prefixWord ++ tailWord_771126) baseStart_771126 baseEnd_771126 := by
    simpa [prefixWord, tailWord_771126, baseEnd_771126] using wordTrace_append hprefix tailTrace_771126
  have hstable : (prefixWord ++ tailWord_771126).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_771126).length < 2 ^ (prefixWord ++ tailWord_771126).sum := by decide
  have hdescent : baseEnd_771126 < baseStart_771126 := by decide
  rcases family_descends (prefixWord ++ tailWord_771126) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_771214 : List Nat := [4, 1, 1, 3, 2, 1, 3, 2, 1, 4]
def baseStart_771214 : Nat := 118140960795 + 771214 * 2 ^ 59
def prefixEnd_771214 : Nat := 4983230072969 + 3 ^ 40 * 771214 * 2
def baseEnd_771214 : Nat := 264002312984433903585505

theorem tailTrace_771214 : CollatzResearch.WordTrace tailWord_771214 prefixEnd_771214 264002312984433903585505 := by
  unfold tailWord_771214
  simp only [CollatzResearch.WordTrace]
  refine ⟨3516060678503858213764087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 18752323618687243806741797 3516060678503858213764087)
  ·
    refine ⟨5274091017755787320646131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3516060678503858213764087 5274091017755787320646131)
    ·
      refine ⟨7911136526633680980969197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5274091017755787320646131 7911136526633680980969197)
      ·
        refine ⟨2966676197487630367863449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7911136526633680980969197 2966676197487630367863449)
        ·
          refine ⟨2225007148115722775897587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2966676197487630367863449 2225007148115722775897587)
          ·
            refine ⟨3337510722173584163846381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2225007148115722775897587 3337510722173584163846381)
            ·
              refine ⟨1251566520815094061442393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3337510722173584163846381 1251566520815094061442393)
              ·
                refine ⟨938674890611320546081795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1251566520815094061442393 938674890611320546081795)
                ·
                  refine ⟨1408012335916980819122693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 938674890611320546081795 1408012335916980819122693)
                  ·
                    refine ⟨264002312984433903585505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1408012335916980819122693 264002312984433903585505)
                    ·
                      rfl

theorem cell22_771214_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 1, 3, 2, 1, 4].length) (baseStart_771214 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_771214 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_771214 prefixEnd_771214 := by exact prefixLift 771214
  have htrace : WordTrace (prefixWord ++ tailWord_771214) baseStart_771214 baseEnd_771214 := by
    simpa [prefixWord, tailWord_771214, baseEnd_771214] using wordTrace_append hprefix tailTrace_771214
  have hstable : (prefixWord ++ tailWord_771214).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_771214).length < 2 ^ (prefixWord ++ tailWord_771214).sum := by decide
  have hdescent : baseEnd_771214 < baseStart_771214 := by decide
  rcases family_descends (prefixWord ++ tailWord_771214) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_771231 : List Nat := [1, 1, 2, 6, 2, 1, 3, 1, 1, 4]
def baseStart_771231 : Nat := 118140960795 + 771231 * 2 ^ 59
def prefixEnd_771231 : Nat := 4983230072969 + 3 ^ 40 * 771231 * 2
def baseEnd_771231 : Nat := 264008132431851525910453

theorem tailTrace_771231 : CollatzResearch.WordTrace tailWord_771231 prefixEnd_771231 264008132431851525910453 := by
  unfold tailWord_771231
  simp only [CollatzResearch.WordTrace]
  refine ⟨28129105468969277613481547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18752736979312851742321031 28129105468969277613481547)
  ·
    refine ⟨42193658203453916420222321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28129105468969277613481547 42193658203453916420222321)
    ·
      refine ⟨31645243652590437315166741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42193658203453916420222321 31645243652590437315166741)
      ·
        refine ⟨1483370796215176749148441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 31645243652590437315166741 1483370796215176749148441)
        ·
          refine ⟨1112528097161382561861331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1483370796215176749148441 1112528097161382561861331)
          ·
            refine ⟨1668792145742073842791997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1112528097161382561861331 1668792145742073842791997)
            ·
              refine ⟨625797054653277691046999, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1668792145742073842791997 625797054653277691046999)
              ·
                refine ⟨938695581979916536570499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 625797054653277691046999 938695581979916536570499)
                ·
                  refine ⟨1408043372969874804855749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 938695581979916536570499 1408043372969874804855749)
                  ·
                    refine ⟨264008132431851525910453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1408043372969874804855749 264008132431851525910453)
                    ·
                      rfl

theorem cell22_771231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 2, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 2, 1, 3, 1, 1, 4].length) (baseStart_771231 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_771231 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_771231 prefixEnd_771231 := by exact prefixLift 771231
  have htrace : WordTrace (prefixWord ++ tailWord_771231) baseStart_771231 baseEnd_771231 := by
    simpa [prefixWord, tailWord_771231, baseEnd_771231] using wordTrace_append hprefix tailTrace_771231
  have hstable : (prefixWord ++ tailWord_771231).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_771231).length < 2 ^ (prefixWord ++ tailWord_771231).sum := by decide
  have hdescent : baseEnd_771231 < baseStart_771231 := by decide
  rcases family_descends (prefixWord ++ tailWord_771231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_771257 : List Nat := [1, 2, 1, 4, 1, 5, 1, 7]
def baseStart_771257 : Nat := 118140960795 + 771257 * 2 ^ 59
def prefixEnd_771257 : Nat := 4983230072969 + 3 ^ 40 * 771257 * 2
def baseEnd_771257 : Nat := 29335225862577347195597

theorem tailTrace_771257 : CollatzResearch.WordTrace tailWord_771257 prefixEnd_771257 29335225862577347195597 := by
  unfold tailWord_771257
  simp only [CollatzResearch.WordTrace]
  refine ⟨28130053766875084053928025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18753369177916722702618683 28130053766875084053928025)
  ·
    refine ⟨21097540325156313040446019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28130053766875084053928025 21097540325156313040446019)
    ·
      refine ⟨31646310487734469560669029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21097540325156313040446019 31646310487734469560669029)
      ·
        refine ⟨5933683216450213042625443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 31646310487734469560669029 5933683216450213042625443)
        ·
          refine ⟨8900524824675319563938165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5933683216450213042625443 8900524824675319563938165)
          ·
            refine ⟨834424202313311209119203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 8900524824675319563938165 834424202313311209119203)
            ·
              refine ⟨1251636303469966813678805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 834424202313311209119203 1251636303469966813678805)
              ·
                refine ⟨29335225862577347195597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1251636303469966813678805 29335225862577347195597)
                ·
                  rfl

theorem cell22_771257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 5, 1, 7].length) (baseStart_771257 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_771257 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_771257 prefixEnd_771257 := by exact prefixLift 771257
  have htrace : WordTrace (prefixWord ++ tailWord_771257) baseStart_771257 baseEnd_771257 := by
    simpa [prefixWord, tailWord_771257, baseEnd_771257] using wordTrace_append hprefix tailTrace_771257
  have hstable : (prefixWord ++ tailWord_771257).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_771257).length < 2 ^ (prefixWord ++ tailWord_771257).sum := by decide
  have hdescent : baseEnd_771257 < baseStart_771257 := by decide
  rcases family_descends (prefixWord ++ tailWord_771257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_771272 : List Nat := [2, 1, 3, 1, 2, 1, 3, 1, 5, 3]
def baseStart_771272 : Nat := 118140960795 + 771272 * 2 ^ 59
def prefixEnd_771272 : Nat := 4983230072969 + 3 ^ 40 * 771272 * 2
def baseEnd_771272 : Nat := 264022167569741085635327

theorem tailTrace_771272 : CollatzResearch.WordTrace tailWord_771272 prefixEnd_771272 264022167569741085635327 := by
  unfold tailWord_771272
  simp only [CollatzResearch.WordTrace]
  refine ⟨14065300430910370807862035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18753733907880494410482713 14065300430910370807862035)
  ·
    refine ⟨21097950646365556211793053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14065300430910370807862035 21097950646365556211793053)
    ·
      refine ⟨7911731492387083579422395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21097950646365556211793053 7911731492387083579422395)
      ·
        refine ⟨11867597238580625369133593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7911731492387083579422395 11867597238580625369133593)
        ·
          refine ⟨8900697928935469026850195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11867597238580625369133593 8900697928935469026850195)
          ·
            refine ⟨13351046893403203540275293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8900697928935469026850195 13351046893403203540275293)
            ·
              refine ⟨5006642585026201327603235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13351046893403203540275293 5006642585026201327603235)
              ·
                refine ⟨7509963877539301991404853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5006642585026201327603235 7509963877539301991404853)
                ·
                  refine ⟨704059113519309561694205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 7509963877539301991404853 704059113519309561694205)
                  ·
                    refine ⟨264022167569741085635327, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 704059113519309561694205 264022167569741085635327)
                    ·
                      rfl

theorem cell22_771272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 3, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 3, 1, 5, 3].length) (baseStart_771272 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_771272 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_771272 prefixEnd_771272 := by exact prefixLift 771272
  have htrace : WordTrace (prefixWord ++ tailWord_771272) baseStart_771272 baseEnd_771272 := by
    simpa [prefixWord, tailWord_771272, baseEnd_771272] using wordTrace_append hprefix tailTrace_771272
  have hstable : (prefixWord ++ tailWord_771272).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_771272).length < 2 ^ (prefixWord ++ tailWord_771272).sum := by decide
  have hdescent : baseEnd_771272 < baseStart_771272 := by decide
  rcases family_descends (prefixWord ++ tailWord_771272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_771306 : List Nat := [3, 1, 3, 1, 1, 3, 2, 4, 1, 3]
def baseStart_771306 : Nat := 118140960795 + 771306 * 2 ^ 59
def prefixEnd_771306 : Nat := 4983230072969 + 3 ^ 40 * 771306 * 2
def baseEnd_771306 : Nat := 264033806464576330285223

theorem tailTrace_771306 : CollatzResearch.WordTrace tailWord_771306 prefixEnd_771306 264033806464576330285223 := by
  unfold tailWord_771306
  simp only [CollatzResearch.WordTrace]
  refine ⟨7032960235924391355615443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18754560629131710281641181 7032960235924391355615443)
  ·
    refine ⟨10549440353886587033423165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7032960235924391355615443 10549440353886587033423165)
    ·
      refine ⟨3956040132707470137533687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10549440353886587033423165 3956040132707470137533687)
      ·
        refine ⟨5934060199061205206300531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3956040132707470137533687 5934060199061205206300531)
        ·
          refine ⟨8901090298591807809450797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5934060199061205206300531 8901090298591807809450797)
          ·
            refine ⟨3337908861971927928544049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8901090298591807809450797 3337908861971927928544049)
            ·
              refine ⟨2503431646478945946408037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3337908861971927928544049 2503431646478945946408037)
              ·
                refine ⟨469393433714802364951507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2503431646478945946408037 469393433714802364951507)
                ·
                  refine ⟨704090150572203547427261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 469393433714802364951507 704090150572203547427261)
                  ·
                    refine ⟨264033806464576330285223, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 704090150572203547427261 264033806464576330285223)
                    ·
                      rfl

theorem cell22_771306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 3, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 3, 2, 4, 1, 3].length) (baseStart_771306 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_771306 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_771306 prefixEnd_771306 := by exact prefixLift 771306
  have htrace : WordTrace (prefixWord ++ tailWord_771306) baseStart_771306 baseEnd_771306 := by
    simpa [prefixWord, tailWord_771306, baseEnd_771306] using wordTrace_append hprefix tailTrace_771306
  have hstable : (prefixWord ++ tailWord_771306).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_771306).length < 2 ^ (prefixWord ++ tailWord_771306).sum := by decide
  have hdescent : baseEnd_771306 < baseStart_771306 := by decide
  rcases family_descends (prefixWord ++ tailWord_771306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_771396 : List Nat := [2, 3, 4, 1, 1, 2, 1, 2, 1, 5]
def baseStart_771396 : Nat := 118140960795 + 771396 * 2 ^ 59
def prefixEnd_771396 : Nat := 4983230072969 + 3 ^ 40 * 771396 * 2
def baseEnd_771396 : Nat := 264064615303846095534947

theorem tailTrace_771396 : CollatzResearch.WordTrace tailWord_771396 prefixEnd_771396 264064615303846095534947 := by
  unfold tailWord_771396
  simp only [CollatzResearch.WordTrace]
  refine ⟨14067561756685755396619021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18756749008914340528825361 14067561756685755396619021)
  ·
    refine ⟨5275335658757158273732133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14067561756685755396619021 5275335658757158273732133)
    ·
      refine ⟨989125436016967176324775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5275335658757158273732133 989125436016967176324775)
      ·
        refine ⟨1483688154025450764487163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 989125436016967176324775 1483688154025450764487163)
        ·
          refine ⟨2225532231038176146730745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1483688154025450764487163 2225532231038176146730745)
          ·
            refine ⟨1669149173278632110048059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2225532231038176146730745 1669149173278632110048059)
            ·
              refine ⟨2503723759917948165072089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1669149173278632110048059 2503723759917948165072089)
              ·
                refine ⟨1877792819938461123804067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2503723759917948165072089 1877792819938461123804067)
                ·
                  refine ⟨2816689229907691685706101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1877792819938461123804067 2816689229907691685706101)
                  ·
                    refine ⟨264064615303846095534947, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2816689229907691685706101 264064615303846095534947)
                    ·
                      rfl

theorem cell22_771396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 2, 1, 2, 1, 5].length) (baseStart_771396 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_771396 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_771396 prefixEnd_771396 := by exact prefixLift 771396
  have htrace : WordTrace (prefixWord ++ tailWord_771396) baseStart_771396 baseEnd_771396 := by
    simpa [prefixWord, tailWord_771396, baseEnd_771396] using wordTrace_append hprefix tailTrace_771396
  have hstable : (prefixWord ++ tailWord_771396).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_771396).length < 2 ^ (prefixWord ++ tailWord_771396).sum := by decide
  have hdescent : baseEnd_771396 < baseStart_771396 := by decide
  rcases family_descends (prefixWord ++ tailWord_771396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_771452 : List Nat := [2, 2, 2, 1, 1, 1, 3, 2, 1, 7]
def baseStart_771452 : Nat := 118140960795 + 771452 * 2 ^ 59
def prefixEnd_771452 : Nat := 4983230072969 + 3 ^ 40 * 771452 * 2
def baseEnd_771452 : Nat := 264083785248280616134775

theorem tailTrace_771452 : CollatzResearch.WordTrace tailWord_771452 prefixEnd_771452 264083785248280616134775 := by
  unfold tailWord_771452
  simp only [CollatzResearch.WordTrace]
  refine ⟨14068583000584316178638305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18758110667445754904851073 14068583000584316178638305)
  ·
    refine ⟨10551437250438237133978729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14068583000584316178638305 10551437250438237133978729)
    ·
      refine ⟨7913577937828677850484047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10551437250438237133978729 7913577937828677850484047)
      ·
        refine ⟨11870366906743016775726071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7913577937828677850484047 11870366906743016775726071)
        ·
          refine ⟨17805550360114525163589107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11870366906743016775726071 17805550360114525163589107)
          ·
            refine ⟨26708325540171787745383661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17805550360114525163589107 26708325540171787745383661)
            ·
              refine ⟨10015622077564420404518873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26708325540171787745383661 10015622077564420404518873)
              ·
                refine ⟨7511716558173315303389155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10015622077564420404518873 7511716558173315303389155)
                ·
                  refine ⟨11267574837259972955083733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7511716558173315303389155 11267574837259972955083733)
                  ·
                    refine ⟨264083785248280616134775, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 11267574837259972955083733 264083785248280616134775)
                    ·
                      rfl

theorem cell22_771452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 3, 2, 1, 7].length) (baseStart_771452 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_771452 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_771452 prefixEnd_771452 := by exact prefixLift 771452
  have htrace : WordTrace (prefixWord ++ tailWord_771452) baseStart_771452 baseEnd_771452 := by
    simpa [prefixWord, tailWord_771452, baseEnd_771452] using wordTrace_append hprefix tailTrace_771452
  have hstable : (prefixWord ++ tailWord_771452).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_771452).length < 2 ^ (prefixWord ++ tailWord_771452).sum := by decide
  have hdescent : baseEnd_771452 < baseStart_771452 := by decide
  rcases family_descends (prefixWord ++ tailWord_771452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan22Incremental
