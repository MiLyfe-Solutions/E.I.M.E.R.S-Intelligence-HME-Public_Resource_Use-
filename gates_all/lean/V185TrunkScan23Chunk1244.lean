import V185TrunkScan23Chunk1243

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_7369392 : List Nat := [2, 1, 1, 1, 2, 1, 3, 3, 5, 1, 3]
def baseStart_7369392 : Nat := 118140960795 + 7369392 * 2 ^ 59
def prefixEnd_7369392 : Nat := 4983230072969 + 3 ^ 40 * 7369392 * 2
def baseEnd_7369392 : Nat := 3784040227398336453608789

theorem tailTrace_7369392 : CollatzResearch.WordTrace tailWord_7369392 prefixEnd_7369392 3784040227398336453608789 := by
  unfold tailWord_7369392
  simp only [CollatzResearch.WordTrace]
  refine ⟨134391903858979425398543215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 179189205145305900531390953 134391903858979425398543215)
  ·
    refine ⟨201587855788469138097814823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134391903858979425398543215 201587855788469138097814823)
    ·
      refine ⟨302381783682703707146722235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 201587855788469138097814823 302381783682703707146722235)
      ·
        refine ⟨453572675524055560720083353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 302381783682703707146722235 453572675524055560720083353)
        ·
          refine ⟨340179506643041670540062515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 453572675524055560720083353 340179506643041670540062515)
          ·
            refine ⟨510269259964562505810093773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 340179506643041670540062515 510269259964562505810093773)
            ·
              refine ⟨191350972486710939678785165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 510269259964562505810093773 191350972486710939678785165)
              ·
                refine ⟨71756614682516602379544437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 191350972486710939678785165 71756614682516602379544437)
                ·
                  refine ⟨6727182626485931473082291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 71756614682516602379544437 6727182626485931473082291)
                  ·
                    refine ⟨10090773939728897209623437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6727182626485931473082291 10090773939728897209623437)
                    ·
                      refine ⟨3784040227398336453608789, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10090773939728897209623437 3784040227398336453608789)
                      ·
                        rfl

theorem cell23_7369392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 3, 3, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 3, 3, 5, 1, 3].length) (baseStart_7369392 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7369392 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7369392 prefixEnd_7369392 := by exact prefixLift 7369392
  have htrace : WordTrace (prefixWord ++ tailWord_7369392) baseStart_7369392 baseEnd_7369392 := by
    simpa [prefixWord, tailWord_7369392, baseEnd_7369392] using wordTrace_append hprefix tailTrace_7369392
  have hstable : (prefixWord ++ tailWord_7369392).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7369392).length < 2 ^ (prefixWord ++ tailWord_7369392).sum := by decide
  have hdescent : baseEnd_7369392 < baseStart_7369392 := by decide
  rcases family_descends (prefixWord ++ tailWord_7369392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7369425 : List Nat := [1, 2, 2, 1, 2, 3, 1, 2, 3, 6]
def baseStart_7369425 : Nat := 118140960795 + 7369425 * 2 ^ 59
def prefixEnd_7369425 : Nat := 4983230072969 + 3 ^ 40 * 7369425 * 2
def baseEnd_7369425 : Nat := 1261352390753311608165379

theorem tailTrace_7369425 : CollatzResearch.WordTrace tailWord_7369425 prefixEnd_7369425 1261352390753311608165379 := by
  unfold tailWord_7369425
  simp only [CollatzResearch.WordTrace]
  refine ⟨268785011326839297433037729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179190007551226198288691819 268785011326839297433037729)
  ·
    refine ⟨201588758495129473074778297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 268785011326839297433037729 201588758495129473074778297)
    ·
      refine ⟨151191568871347104806083723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 201588758495129473074778297 151191568871347104806083723)
      ·
        refine ⟨226787353307020657209125585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 151191568871347104806083723 226787353307020657209125585)
        ·
          refine ⟨170090514980265492906844189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 226787353307020657209125585 170090514980265492906844189)
          ·
            refine ⟨63783943117599559840066571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 170090514980265492906844189 63783943117599559840066571)
            ·
              refine ⟨95675914676399339760099857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63783943117599559840066571 95675914676399339760099857)
              ·
                refine ⟨71756936007299504820074893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 95675914676399339760099857 71756936007299504820074893)
                ·
                  refine ⟨26908851002737314307528085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 71756936007299504820074893 26908851002737314307528085)
                  ·
                    refine ⟨1261352390753311608165379, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26908851002737314307528085 1261352390753311608165379)
                    ·
                      rfl

theorem cell23_7369425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 1, 2, 3, 6].length) (baseStart_7369425 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7369425 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7369425 prefixEnd_7369425 := by exact prefixLift 7369425
  have htrace : WordTrace (prefixWord ++ tailWord_7369425) baseStart_7369425 baseEnd_7369425 := by
    simpa [prefixWord, tailWord_7369425, baseEnd_7369425] using wordTrace_append hprefix tailTrace_7369425
  have hstable : (prefixWord ++ tailWord_7369425).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7369425).length < 2 ^ (prefixWord ++ tailWord_7369425).sum := by decide
  have hdescent : baseEnd_7369425 < baseStart_7369425 := by decide
  rcases family_descends (prefixWord ++ tailWord_7369425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7369432 : List Nat := [2, 1, 2, 2, 3, 2, 1, 2, 3, 1, 4]
def baseStart_7369432 : Nat := 118140960795 + 7369432 * 2 ^ 59
def prefixEnd_7369432 : Nat := 4983230072969 + 3 ^ 40 * 7369432 * 2
def baseEnd_7369432 : Nat := 3784060766624516297108605

theorem tailTrace_7369432 : CollatzResearch.WordTrace tailWord_7369432 prefixEnd_7369432 3784060766624516297108605 := by
  unfold tailWord_7369432
  simp only [CollatzResearch.WordTrace]
  refine ⟨134392633318906968814271275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 179190177758542625085695033 134392633318906968814271275)
  ·
    refine ⟨201588949978360453221406913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134392633318906968814271275 201588949978360453221406913)
    ·
      refine ⟨151191712483770339916055185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 201588949978360453221406913 151191712483770339916055185)
      ·
        refine ⟨113393784362827754937041389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 151191712483770339916055185 113393784362827754937041389)
        ·
          refine ⟨42522669136060408101390521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 113393784362827754937041389 42522669136060408101390521)
          ·
            refine ⟨31892001852045306076042891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42522669136060408101390521 31892001852045306076042891)
            ·
              refine ⟨47838002778067959114064337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31892001852045306076042891 47838002778067959114064337)
              ·
                refine ⟨35878502083550969335548253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47838002778067959114064337 35878502083550969335548253)
                ·
                  refine ⟨13454438281331613500830595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35878502083550969335548253 13454438281331613500830595)
                  ·
                    refine ⟨20181657421997420251245893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13454438281331613500830595 20181657421997420251245893)
                    ·
                      refine ⟨3784060766624516297108605, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20181657421997420251245893 3784060766624516297108605)
                      ·
                        rfl

theorem cell23_7369432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 2, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 2, 1, 2, 3, 1, 4].length) (baseStart_7369432 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7369432 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7369432 prefixEnd_7369432 := by exact prefixLift 7369432
  have htrace : WordTrace (prefixWord ++ tailWord_7369432) baseStart_7369432 baseEnd_7369432 := by
    simpa [prefixWord, tailWord_7369432, baseEnd_7369432] using wordTrace_append hprefix tailTrace_7369432
  have hstable : (prefixWord ++ tailWord_7369432).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7369432).length < 2 ^ (prefixWord ++ tailWord_7369432).sum := by decide
  have hdescent : baseEnd_7369432 < baseStart_7369432 := by decide
  rcases family_descends (prefixWord ++ tailWord_7369432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7369449 : List Nat := [1, 2, 1, 1, 1, 2, 5, 1, 5, 2, 2]
def baseStart_7369449 : Nat := 118140960795 + 7369449 * 2 ^ 59
def prefixEnd_7369449 : Nat := 4983230072969 + 3 ^ 40 * 7369449 * 2
def baseEnd_7369449 : Nat := 3784069495795642730596027

theorem tailTrace_7369449 : CollatzResearch.WordTrace tailWord_7369449 prefixEnd_7369449 3784069495795642730596027 := by
  unfold tailWord_7369449
  simp only [CollatzResearch.WordTrace]
  refine ⟨268785886678752349531911401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179190591119168233021274267 268785886678752349531911401)
  ·
    refine ⟨201589415009064262148933551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 268785886678752349531911401 201589415009064262148933551)
    ·
      refine ⟨302384122513596393223400327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 201589415009064262148933551 302384122513596393223400327)
      ·
        refine ⟨453576183770394589835100491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 302384122513596393223400327 453576183770394589835100491)
        ·
          refine ⟨680364275655591884752650737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 453576183770394589835100491 680364275655591884752650737)
          ·
            refine ⟨510273206741693913564488053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 680364275655591884752650737 510273206741693913564488053)
            ·
              refine ⟨47838113132033804396670755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 510273206741693913564488053 47838113132033804396670755)
              ·
                refine ⟨71757169698050706595006133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47838113132033804396670755 71757169698050706595006133)
                ·
                  refine ⟨6727234659192253743281825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 71757169698050706595006133 6727234659192253743281825)
                  ·
                    refine ⟨5045425994394190307461369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6727234659192253743281825 5045425994394190307461369)
                    ·
                      refine ⟨3784069495795642730596027, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5045425994394190307461369 3784069495795642730596027)
                      ·
                        rfl

theorem cell23_7369449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 5, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 5, 1, 5, 2, 2].length) (baseStart_7369449 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7369449 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7369449 prefixEnd_7369449 := by exact prefixLift 7369449
  have htrace : WordTrace (prefixWord ++ tailWord_7369449) baseStart_7369449 baseEnd_7369449 := by
    simpa [prefixWord, tailWord_7369449, baseEnd_7369449] using wordTrace_append hprefix tailTrace_7369449
  have hstable : (prefixWord ++ tailWord_7369449).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7369449).length < 2 ^ (prefixWord ++ tailWord_7369449).sum := by decide
  have hdescent : baseEnd_7369449 < baseStart_7369449 := by decide
  rcases family_descends (prefixWord ++ tailWord_7369449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7369469 : List Nat := [1, 4, 1, 1, 1, 1, 5, 3, 1, 2, 3]
def baseStart_7369469 : Nat := 118140960795 + 7369469 * 2 ^ 59
def prefixEnd_7369469 : Nat := 4983230072969 + 3 ^ 40 * 7369469 * 2
def baseEnd_7369469 : Nat := 3784079765408732652345935

theorem tailTrace_7369469 : CollatzResearch.WordTrace tailWord_7369469 prefixEnd_7369469 3784079765408732652345935 := by
  unfold tailWord_7369469
  simp only [CollatzResearch.WordTrace]
  refine ⟨268786616138679892947639461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179191077425786595298426307 268786616138679892947639461)
  ·
    refine ⟨50397490526002479927682399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 268786616138679892947639461 50397490526002479927682399)
    ·
      refine ⟨75596235789003719891523599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50397490526002479927682399 75596235789003719891523599)
      ·
        refine ⟨113394353683505579837285399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75596235789003719891523599 113394353683505579837285399)
        ·
          refine ⟨170091530525258369755928099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 113394353683505579837285399 170091530525258369755928099)
          ·
            refine ⟨255137295787887554633892149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 170091530525258369755928099 255137295787887554633892149)
            ·
              refine ⟨23919121480114458246927389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 255137295787887554633892149 23919121480114458246927389)
              ·
                refine ⟨8969670555042921842597771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23919121480114458246927389 8969670555042921842597771)
                ·
                  refine ⟨13454505832564382763896657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8969670555042921842597771 13454505832564382763896657)
                  ·
                    refine ⟨10090879374423287072922493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13454505832564382763896657 10090879374423287072922493)
                    ·
                      refine ⟨3784079765408732652345935, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10090879374423287072922493 3784079765408732652345935)
                      ·
                        rfl

theorem cell23_7369469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 5, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 5, 3, 1, 2, 3].length) (baseStart_7369469 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7369469 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7369469 prefixEnd_7369469 := by exact prefixLift 7369469
  have htrace : WordTrace (prefixWord ++ tailWord_7369469) baseStart_7369469 baseEnd_7369469 := by
    simpa [prefixWord, tailWord_7369469, baseEnd_7369469] using wordTrace_append hprefix tailTrace_7369469
  have hstable : (prefixWord ++ tailWord_7369469).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7369469).length < 2 ^ (prefixWord ++ tailWord_7369469).sum := by decide
  have hdescent : baseEnd_7369469 < baseStart_7369469 := by decide
  rcases family_descends (prefixWord ++ tailWord_7369469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7369475 : List Nat := [1, 1, 1, 3, 2, 2, 1, 2, 2, 2, 6]
def baseStart_7369475 : Nat := 118140960795 + 7369475 * 2 ^ 59
def prefixEnd_7369475 : Nat := 4983230072969 + 3 ^ 40 * 7369475 * 2
def baseEnd_7369475 : Nat := 3784082846292659628870907

theorem tailTrace_7369475 : CollatzResearch.WordTrace tailWord_7369475 prefixEnd_7369475 3784082846292659628870907 := by
  unfold tailWord_7369475
  simp only [CollatzResearch.WordTrace]
  refine ⟨268786834976658155972357879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179191223317772103981571919 268786834976658155972357879)
  ·
    refine ⟨403180252464987233958536819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 268786834976658155972357879 403180252464987233958536819)
    ·
      refine ⟨604770378697480850937805229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 403180252464987233958536819 604770378697480850937805229)
      ·
        refine ⟨226788892011555319101676961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 604770378697480850937805229 226788892011555319101676961)
        ·
          refine ⟨170091669008666489326257721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 226788892011555319101676961 170091669008666489326257721)
          ·
            refine ⟨127568751756499866994693291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 170091669008666489326257721 127568751756499866994693291)
            ·
              refine ⟨191353127634749800492039937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 127568751756499866994693291 191353127634749800492039937)
              ·
                refine ⟨143514845726062350369029953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 191353127634749800492039937 143514845726062350369029953)
                ·
                  refine ⟨107636134294546762776772465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 143514845726062350369029953 107636134294546762776772465)
                  ·
                    refine ⟨80727100720910072082579349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 107636134294546762776772465 80727100720910072082579349)
                    ·
                      refine ⟨3784082846292659628870907, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 80727100720910072082579349 3784082846292659628870907)
                      ·
                        rfl

theorem cell23_7369475_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 1, 2, 2, 2, 6].length) (baseStart_7369475 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7369475 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7369475 prefixEnd_7369475 := by exact prefixLift 7369475
  have htrace : WordTrace (prefixWord ++ tailWord_7369475) baseStart_7369475 baseEnd_7369475 := by
    simpa [prefixWord, tailWord_7369475, baseEnd_7369475] using wordTrace_append hprefix tailTrace_7369475
  have hstable : (prefixWord ++ tailWord_7369475).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7369475).length < 2 ^ (prefixWord ++ tailWord_7369475).sum := by decide
  have hdescent : baseEnd_7369475 < baseStart_7369475 := by decide
  rcases family_descends (prefixWord ++ tailWord_7369475) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7369512 : List Nat := [2, 1, 5, 1, 1, 1, 1, 1, 1, 4, 5]
def baseStart_7369512 : Nat := 118140960795 + 7369512 * 2 ^ 59
def prefixEnd_7369512 : Nat := 4983230072969 + 3 ^ 40 * 7369512 * 2
def baseEnd_7369512 : Nat := 3784101845076875984108237

theorem tailTrace_7369512 : CollatzResearch.WordTrace tailWord_7369512 prefixEnd_7369512 3784101845076875984108237 := by
  unfold tailWord_7369512
  simp only [CollatzResearch.WordTrace]
  refine ⟨134394092238762055645727395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 179192122985016074194303193 134394092238762055645727395)
  ·
    refine ⟨201591138358143083468591093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134394092238762055645727395 201591138358143083468591093)
    ·
      refine ⟨18899169221075914075180415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 201591138358143083468591093 18899169221075914075180415)
      ·
        refine ⟨28348753831613871112770623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18899169221075914075180415 28348753831613871112770623)
        ·
          refine ⟨42523130747420806669155935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28348753831613871112770623 42523130747420806669155935)
          ·
            refine ⟨63784696121131210003733903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42523130747420806669155935 63784696121131210003733903)
            ·
              refine ⟨95677044181696815005600855, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63784696121131210003733903 95677044181696815005600855)
              ·
                refine ⟨143515566272545222508401283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 95677044181696815005600855 143515566272545222508401283)
                ·
                  refine ⟨215273349408817833762601925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 143515566272545222508401283 215273349408817833762601925)
                  ·
                    refine ⟨40363753014153343830487861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 215273349408817833762601925 40363753014153343830487861)
                    ·
                      refine ⟨3784101845076875984108237, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 40363753014153343830487861 3784101845076875984108237)
                      ·
                        rfl

theorem cell23_7369512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 1, 1, 1, 4, 5].length) (baseStart_7369512 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7369512 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7369512 prefixEnd_7369512 := by exact prefixLift 7369512
  have htrace : WordTrace (prefixWord ++ tailWord_7369512) baseStart_7369512 baseEnd_7369512 := by
    simpa [prefixWord, tailWord_7369512, baseEnd_7369512] using wordTrace_append hprefix tailTrace_7369512
  have hstable : (prefixWord ++ tailWord_7369512).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7369512).length < 2 ^ (prefixWord ++ tailWord_7369512).sum := by decide
  have hdescent : baseEnd_7369512 < baseStart_7369512 := by decide
  rcases family_descends (prefixWord ++ tailWord_7369512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7369515 : List Nat := [1, 1, 1, 1, 2, 1, 2, 3, 3, 8]
def baseStart_7369515 : Nat := 118140960795 + 7369515 * 2 ^ 59
def prefixEnd_7369515 : Nat := 4983230072969 + 3 ^ 40 * 7369515 * 2
def baseEnd_7369515 : Nat := 1261367795172946490790241

theorem tailTrace_7369515 : CollatzResearch.WordTrace tailWord_7369515 prefixEnd_7369515 1261367795172946490790241 := by
  unfold tailWord_7369515
  simp only [CollatzResearch.WordTrace]
  refine ⟨268788293896513242803813999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179192195931008828535875999 268788293896513242803813999)
  ·
    refine ⟨403182440844769864205720999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 268788293896513242803813999 403182440844769864205720999)
    ·
      refine ⟨604773661267154796308581499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 403182440844769864205720999 604773661267154796308581499)
      ·
        refine ⟨907160491900732194462872249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 604773661267154796308581499 907160491900732194462872249)
        ·
          refine ⟨680370368925549145847154187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 907160491900732194462872249 680370368925549145847154187)
          ·
            refine ⟨1020555553388323718770731281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 680370368925549145847154187 1020555553388323718770731281)
            ·
              refine ⟨765416665041242789078048461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1020555553388323718770731281 765416665041242789078048461)
              ·
                refine ⟨287031249390466045904268173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 765416665041242789078048461 287031249390466045904268173)
                ·
                  refine ⟨107636718521424767214100565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 287031249390466045904268173 107636718521424767214100565)
                  ·
                    refine ⟨1261367795172946490790241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 107636718521424767214100565 1261367795172946490790241)
                    ·
                      rfl

theorem cell23_7369515_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 3, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 3, 3, 8].length) (baseStart_7369515 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7369515 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7369515 prefixEnd_7369515 := by exact prefixLift 7369515
  have htrace : WordTrace (prefixWord ++ tailWord_7369515) baseStart_7369515 baseEnd_7369515 := by
    simpa [prefixWord, tailWord_7369515, baseEnd_7369515] using wordTrace_append hprefix tailTrace_7369515
  have hstable : (prefixWord ++ tailWord_7369515).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7369515).length < 2 ^ (prefixWord ++ tailWord_7369515).sum := by decide
  have hdescent : baseEnd_7369515 < baseStart_7369515 := by decide
  rcases family_descends (prefixWord ++ tailWord_7369515) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7369552 : List Nat := [2, 1, 1, 1, 1, 4, 2, 3, 2, 2, 4]
def baseStart_7369552 : Nat := 118140960795 + 7369552 * 2 ^ 59
def prefixEnd_7369552 : Nat := 4983230072969 + 3 ^ 40 * 7369552 * 2
def baseEnd_7369552 : Nat := 3784122384303055827608053

theorem tailTrace_7369552 : CollatzResearch.WordTrace tailWord_7369552 prefixEnd_7369552 3784122384303055827608053 := by
  unfold tailWord_7369552
  simp only [CollatzResearch.WordTrace]
  refine ⟨134394821698689599061455455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 179193095598252798748607273 134394821698689599061455455)
  ·
    refine ⟨201592232548034398592183183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134394821698689599061455455 201592232548034398592183183)
    ·
      refine ⟨302388348822051597888274775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 201592232548034398592183183 302388348822051597888274775)
      ·
        refine ⟨453582523233077396832412163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 302388348822051597888274775 453582523233077396832412163)
        ·
          refine ⟨680373784849616095248618245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 453582523233077396832412163 680373784849616095248618245)
          ·
            refine ⟨127570084659303017859115921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 680373784849616095248618245 127570084659303017859115921)
            ·
              refine ⟨95677563494477263394336941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 127570084659303017859115921 95677563494477263394336941)
              ·
                refine ⟨35879086310428973772876353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 95677563494477263394336941 35879086310428973772876353)
                ·
                  refine ⟨26909314732821730329657265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35879086310428973772876353 26909314732821730329657265)
                  ·
                    refine ⟨20181986049616297747242949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26909314732821730329657265 20181986049616297747242949)
                    ·
                      refine ⟨3784122384303055827608053, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20181986049616297747242949 3784122384303055827608053)
                      ·
                        rfl

theorem cell23_7369552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 2, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 2, 3, 2, 2, 4].length) (baseStart_7369552 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7369552 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7369552 prefixEnd_7369552 := by exact prefixLift 7369552
  have htrace : WordTrace (prefixWord ++ tailWord_7369552) baseStart_7369552 baseEnd_7369552 := by
    simpa [prefixWord, tailWord_7369552, baseEnd_7369552] using wordTrace_append hprefix tailTrace_7369552
  have hstable : (prefixWord ++ tailWord_7369552).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7369552).length < 2 ^ (prefixWord ++ tailWord_7369552).sum := by decide
  have hdescent : baseEnd_7369552 < baseStart_7369552 := by decide
  rcases family_descends (prefixWord ++ tailWord_7369552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7369590 : List Nat := [5, 1, 1, 3, 1, 1, 1, 4, 2, 2, 2]
def baseStart_7369590 : Nat := 118140960795 + 7369590 * 2 ^ 59
def prefixEnd_7369590 : Nat := 4983230072969 + 3 ^ 40 * 7369590 * 2
def baseEnd_7369590 : Nat := 3784141896567926678932879

theorem tailTrace_7369590 : CollatzResearch.WordTrace tailWord_7369590 prefixEnd_7369590 3784141896567926678932879 := by
  unfold tailWord_7369590
  simp only [CollatzResearch.WordTrace]
  refine ⟨16799439335702595663299639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 179194019580827687075196149 16799439335702595663299639)
  ·
    refine ⟨25199159003553893494949459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16799439335702595663299639 25199159003553893494949459)
    ·
      refine ⟨37798738505330840242424189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25199159003553893494949459 37798738505330840242424189)
      ·
        refine ⟨14174526939499065090909071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37798738505330840242424189 14174526939499065090909071)
        ·
          refine ⟨21261790409248597636363607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14174526939499065090909071 21261790409248597636363607)
          ·
            refine ⟨31892685613872896454545411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21261790409248597636363607 31892685613872896454545411)
            ·
              refine ⟨47839028420809344681818117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31892685613872896454545411 47839028420809344681818117)
              ·
                refine ⟨8969817828901752127840897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 47839028420809344681818117 8969817828901752127840897)
                ·
                  refine ⟨6727363371676314095880673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8969817828901752127840897 6727363371676314095880673)
                  ·
                    refine ⟨5045522528757235571910505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6727363371676314095880673 5045522528757235571910505)
                    ·
                      refine ⟨3784141896567926678932879, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5045522528757235571910505 3784141896567926678932879)
                      ·
                        rfl

theorem cell23_7369590_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 1, 1, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 1, 1, 4, 2, 2, 2].length) (baseStart_7369590 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7369590 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7369590 prefixEnd_7369590 := by exact prefixLift 7369590
  have htrace : WordTrace (prefixWord ++ tailWord_7369590) baseStart_7369590 baseEnd_7369590 := by
    simpa [prefixWord, tailWord_7369590, baseEnd_7369590] using wordTrace_append hprefix tailTrace_7369590
  have hstable : (prefixWord ++ tailWord_7369590).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7369590).length < 2 ^ (prefixWord ++ tailWord_7369590).sum := by decide
  have hdescent : baseEnd_7369590 < baseStart_7369590 := by decide
  rcases family_descends (prefixWord ++ tailWord_7369590) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7369592 : List Nat := [2, 1, 2, 1, 1, 1, 1, 5, 4, 5]
def baseStart_7369592 : Nat := 118140960795 + 7369592 * 2 ^ 59
def prefixEnd_7369592 : Nat := 4983230072969 + 3 ^ 40 * 7369592 * 2
def baseEnd_7369592 : Nat := 1261380974509745223702623

theorem tailTrace_7369592 : CollatzResearch.WordTrace tailWord_7369592 prefixEnd_7369592 1261380974509745223702623 := by
  unfold tailWord_7369592
  simp only [CollatzResearch.WordTrace]
  refine ⟨134395551158617142477183515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 179194068211489523302911353 134395551158617142477183515)
  ·
    refine ⟨201593326737925713715775273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134395551158617142477183515 201593326737925713715775273)
    ·
      refine ⟨151194995053444285286831455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 201593326737925713715775273 151194995053444285286831455)
      ·
        refine ⟨226792492580166427930247183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 151194995053444285286831455 226792492580166427930247183)
        ·
          refine ⟨340188738870249641895370775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 226792492580166427930247183 340188738870249641895370775)
          ·
            refine ⟨510283108305374462843056163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 340188738870249641895370775 510283108305374462843056163)
            ·
              refine ⟨765424662458061694264584245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 510283108305374462843056163 765424662458061694264584245)
              ·
                refine ⟨71758562105443283837304773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 765424662458061694264584245 71758562105443283837304773)
                ·
                  refine ⟨13454730394770615719494645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 71758562105443283837304773 13454730394770615719494645)
                  ·
                    refine ⟨1261380974509745223702623, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13454730394770615719494645 1261380974509745223702623)
                    ·
                      rfl

theorem cell23_7369592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 5, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 5, 4, 5].length) (baseStart_7369592 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7369592 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7369592 prefixEnd_7369592 := by exact prefixLift 7369592
  have htrace : WordTrace (prefixWord ++ tailWord_7369592) baseStart_7369592 baseEnd_7369592 := by
    simpa [prefixWord, tailWord_7369592, baseEnd_7369592] using wordTrace_append hprefix tailTrace_7369592
  have hstable : (prefixWord ++ tailWord_7369592).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7369592).length < 2 ^ (prefixWord ++ tailWord_7369592).sum := by decide
  have hdescent : baseEnd_7369592 < baseStart_7369592 := by decide
  rcases family_descends (prefixWord ++ tailWord_7369592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7369599 : List Nat := [1, 1, 2, 2, 1, 1, 5, 1, 2, 5, 2]
def baseStart_7369599 : Nat := 118140960795 + 7369599 * 2 ^ 59
def prefixEnd_7369599 : Nat := 4983230072969 + 3 ^ 40 * 7369599 * 2
def baseEnd_7369599 : Nat := 3784146517893817143720337

theorem tailTrace_7369599 : CollatzResearch.WordTrace tailWord_7369599 prefixEnd_7369599 3784146517893817143720337 := by
  unfold tailWord_7369599
  simp only [CollatzResearch.WordTrace]
  refine ⟨268791357628208925149871851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179194238418805950099914567 268791357628208925149871851)
  ·
    refine ⟨403187036442313387724807777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 268791357628208925149871851 403187036442313387724807777)
    ·
      refine ⟨302390277331735040793605833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 403187036442313387724807777 302390277331735040793605833)
      ·
        refine ⟨226792707998801280595204375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 302390277331735040793605833 226792707998801280595204375)
        ·
          refine ⟨340189061998201920892806563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 226792707998801280595204375 340189061998201920892806563)
          ·
            refine ⟨510283592997302881339209845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 340189061998201920892806563 510283592997302881339209845)
            ·
              refine ⟨47839086843497145125550923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 510283592997302881339209845 47839086843497145125550923)
              ·
                refine ⟨71758630265245717688326385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47839086843497145125550923 71758630265245717688326385)
                ·
                  refine ⟨53818972698934288266244789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 71758630265245717688326385 53818972698934288266244789)
                  ·
                    refine ⟨5045528690525089524960449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 53818972698934288266244789 5045528690525089524960449)
                    ·
                      refine ⟨3784146517893817143720337, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5045528690525089524960449 3784146517893817143720337)
                      ·
                        rfl

theorem cell23_7369599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 5, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 5, 1, 2, 5, 2].length) (baseStart_7369599 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7369599 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7369599 prefixEnd_7369599 := by exact prefixLift 7369599
  have htrace : WordTrace (prefixWord ++ tailWord_7369599) baseStart_7369599 baseEnd_7369599 := by
    simpa [prefixWord, tailWord_7369599, baseEnd_7369599] using wordTrace_append hprefix tailTrace_7369599
  have hstable : (prefixWord ++ tailWord_7369599).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7369599).length < 2 ^ (prefixWord ++ tailWord_7369599).sum := by decide
  have hdescent : baseEnd_7369599 < baseStart_7369599 := by decide
  rcases family_descends (prefixWord ++ tailWord_7369599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7369629 : List Nat := [1, 4, 2, 1, 2, 1, 3, 1, 1, 3, 4]
def baseStart_7369629 : Nat := 118140960795 + 7369629 * 2 ^ 59
def prefixEnd_7369629 : Nat := 4983230072969 + 3 ^ 40 * 7369629 * 2
def baseEnd_7369629 : Nat := 3784161922313452026345199

theorem tailTrace_7369629 : CollatzResearch.WordTrace tailWord_7369629 prefixEnd_7369629 3784161922313452026345199 := by
  unfold tailWord_7369629
  simp only [CollatzResearch.WordTrace]
  refine ⟨268792451818100240273463941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179194967878733493515642627 268792451818100240273463941)
  ·
    refine ⟨50398584715893795051274489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 268792451818100240273463941 50398584715893795051274489)
    ·
      refine ⟨37798938536920346288455867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50398584715893795051274489 37798938536920346288455867)
      ·
        refine ⟨56698407805380519432683801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37798938536920346288455867 56698407805380519432683801)
        ·
          refine ⟨42523805854035389574512851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56698407805380519432683801 42523805854035389574512851)
          ·
            refine ⟨63785708781053084361769277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42523805854035389574512851 63785708781053084361769277)
            ·
              refine ⟨23919640792894906635663479, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 63785708781053084361769277 23919640792894906635663479)
              ·
                refine ⟨35879461189342359953495219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23919640792894906635663479 35879461189342359953495219)
                ·
                  refine ⟨53819191784013539930242829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35879461189342359953495219 53819191784013539930242829)
                  ·
                    refine ⟨20182196919005077473841061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 53819191784013539930242829 20182196919005077473841061)
                    ·
                      refine ⟨3784161922313452026345199, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20182196919005077473841061 3784161922313452026345199)
                      ·
                        rfl

theorem cell23_7369629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 3, 1, 1, 3, 4].length) (baseStart_7369629 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7369629 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7369629 prefixEnd_7369629 := by exact prefixLift 7369629
  have htrace : WordTrace (prefixWord ++ tailWord_7369629) baseStart_7369629 baseEnd_7369629 := by
    simpa [prefixWord, tailWord_7369629, baseEnd_7369629] using wordTrace_append hprefix tailTrace_7369629
  have hstable : (prefixWord ++ tailWord_7369629).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7369629).length < 2 ^ (prefixWord ++ tailWord_7369629).sum := by decide
  have hdescent : baseEnd_7369629 < baseStart_7369629 := by decide
  rcases family_descends (prefixWord ++ tailWord_7369629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7369656 : List Nat := [2, 1, 2, 1, 2, 5, 2, 1, 3, 4]
def baseStart_7369656 : Nat := 118140960795 + 7369656 * 2 ^ 59
def prefixEnd_7369656 : Nat := 4983230072969 + 3 ^ 40 * 7369656 * 2
def baseEnd_7369656 : Nat := 1261391928763707806902525

theorem tailTrace_7369656 : CollatzResearch.WordTrace tailWord_7369656 prefixEnd_7369656 1261391928763707806902525 := by
  unfold tailWord_7369656
  simp only [CollatzResearch.WordTrace]
  refine ⟨134396718294501211942348411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 179195624392668282589797881 134396718294501211942348411)
  ·
    refine ⟨201595077441751817913522617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134396718294501211942348411 201595077441751817913522617)
    ·
      refine ⟨151196308081313863435141963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 201595077441751817913522617 151196308081313863435141963)
      ·
        refine ⟨226794462121970795152712945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 151196308081313863435141963 226794462121970795152712945)
        ·
          refine ⟨170095846591478096364534709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 226794462121970795152712945 170095846591478096364534709)
          ·
            refine ⟨15946485617951071534175129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 170095846591478096364534709 15946485617951071534175129)
            ·
              refine ⟨11959864213463303650631347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15946485617951071534175129 11959864213463303650631347)
              ·
                refine ⟨17939796320194955475947021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11959864213463303650631347 17939796320194955475947021)
                ·
                  refine ⟨6727423620073108303480133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17939796320194955475947021 6727423620073108303480133)
                  ·
                    refine ⟨1261391928763707806902525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6727423620073108303480133 1261391928763707806902525)
                    ·
                      rfl

theorem cell23_7369656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 5, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 5, 2, 1, 3, 4].length) (baseStart_7369656 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7369656 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7369656 prefixEnd_7369656 := by exact prefixLift 7369656
  have htrace : WordTrace (prefixWord ++ tailWord_7369656) baseStart_7369656 baseEnd_7369656 := by
    simpa [prefixWord, tailWord_7369656, baseEnd_7369656] using wordTrace_append hprefix tailTrace_7369656
  have hstable : (prefixWord ++ tailWord_7369656).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7369656).length < 2 ^ (prefixWord ++ tailWord_7369656).sum := by decide
  have hdescent : baseEnd_7369656 < baseStart_7369656 := by decide
  rcases family_descends (prefixWord ++ tailWord_7369656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7369686 : List Nat := [5, 2, 1, 1, 2, 1, 1, 2, 8]
def baseStart_7369686 : Nat := 118140960795 + 7369686 * 2 ^ 59
def prefixEnd_7369686 : Nat := 4983230072969 + 3 ^ 40 * 7369686 * 2
def baseEnd_7369686 : Nat := 420465687856750922592493

theorem tailTrace_7369686 : CollatzResearch.WordTrace tailWord_7369686 prefixEnd_7369686 420465687856750922592493 := by
  unfold tailWord_7369686
  simp only [CollatzResearch.WordTrace]
  refine ⟨16799658173680858688018057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 179196353852595826005525941 16799658173680858688018057)
  ·
    refine ⟨12599743630260644016013543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16799658173680858688018057 12599743630260644016013543)
    ·
      refine ⟨18899615445390966024020315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12599743630260644016013543 18899615445390966024020315)
      ·
        refine ⟨28349423168086449036030473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18899615445390966024020315 28349423168086449036030473)
        ·
          refine ⟨21262067376064836777022855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28349423168086449036030473 21262067376064836777022855)
          ·
            refine ⟨31893101064097255165534283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21262067376064836777022855 31893101064097255165534283)
            ·
              refine ⟨47839651596145882748301425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31893101064097255165534283 47839651596145882748301425)
              ·
                refine ⟨35879738697109412061226069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47839651596145882748301425 35879738697109412061226069)
                ·
                  refine ⟨420465687856750922592493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 35879738697109412061226069 420465687856750922592493)
                  ·
                    rfl

theorem cell23_7369686_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 1, 1, 2, 8].length) (baseStart_7369686 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7369686 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7369686 prefixEnd_7369686 := by exact prefixLift 7369686
  have htrace : WordTrace (prefixWord ++ tailWord_7369686) baseStart_7369686 baseEnd_7369686 := by
    simpa [prefixWord, tailWord_7369686, baseEnd_7369686] using wordTrace_append hprefix tailTrace_7369686
  have hstable : (prefixWord ++ tailWord_7369686).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7369686).length < 2 ^ (prefixWord ++ tailWord_7369686).sum := by decide
  have hdescent : baseEnd_7369686 < baseStart_7369686 := by decide
  rcases family_descends (prefixWord ++ tailWord_7369686) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7369690 : List Nat := [3, 1, 1, 2, 4, 3, 1, 3, 1, 4]
def baseStart_7369690 : Nat := 118140960795 + 7369690 * 2 ^ 59
def prefixEnd_7369690 : Nat := 4983230072969 + 3 ^ 40 * 7369690 * 2
def baseEnd_7369690 : Nat := 1261397748211125429227473

theorem tailTrace_7369690 : CollatzResearch.WordTrace tailWord_7369690 prefixEnd_7369690 1261397748211125429227473 := by
  unfold tailWord_7369690
  simp only [CollatzResearch.WordTrace]
  refine ⟨67198669167719811922858631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 179196451113919498460956349 67198669167719811922858631)
  ·
    refine ⟨100798003751579717884287947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67198669167719811922858631 100798003751579717884287947)
    ·
      refine ⟨151197005627369576826431921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100798003751579717884287947 151197005627369576826431921)
      ·
        refine ⟨113397754220527182619823941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 151197005627369576826431921 113397754220527182619823941)
        ·
          refine ⟨21262078916348846741216989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 113397754220527182619823941 21262078916348846741216989)
          ·
            refine ⟨7973279593630817527956371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21262078916348846741216989 7973279593630817527956371)
            ·
              refine ⟨11959919390446226291934557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7973279593630817527956371 11959919390446226291934557)
              ·
                refine ⟨4484969771417334859475459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11959919390446226291934557 4484969771417334859475459)
                ·
                  refine ⟨6727454657126002289213189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4484969771417334859475459 6727454657126002289213189)
                  ·
                    refine ⟨1261397748211125429227473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6727454657126002289213189 1261397748211125429227473)
                    ·
                      rfl

theorem cell23_7369690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 3, 1, 3, 1, 4].length) (baseStart_7369690 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7369690 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7369690 prefixEnd_7369690 := by exact prefixLift 7369690
  have htrace : WordTrace (prefixWord ++ tailWord_7369690) baseStart_7369690 baseEnd_7369690 := by
    simpa [prefixWord, tailWord_7369690, baseEnd_7369690] using wordTrace_append hprefix tailTrace_7369690
  have hstable : (prefixWord ++ tailWord_7369690).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7369690).length < 2 ^ (prefixWord ++ tailWord_7369690).sum := by decide
  have hdescent : baseEnd_7369690 < baseStart_7369690 := by decide
  rcases family_descends (prefixWord ++ tailWord_7369690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7369713 : List Nat := [1, 2, 2, 2, 4, 1, 3, 1, 3, 1, 3]
def baseStart_7369713 : Nat := 118140960795 + 7369713 * 2 ^ 59
def prefixEnd_7369713 : Nat := 4983230072969 + 3 ^ 40 * 7369713 * 2
def baseEnd_7369713 : Nat := 3784205054688429697694813

theorem tailTrace_7369713 : CollatzResearch.WordTrace tailWord_7369713 prefixEnd_7369713 3784205054688429697694813 := by
  unfold tailWord_7369713
  simp only [CollatzResearch.WordTrace]
  refine ⟨268795515549795922619521793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179197010366530615079681195 268795515549795922619521793)
  ·
    refine ⟨201596636662346941964641345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 268795515549795922619521793 201596636662346941964641345)
    ·
      refine ⟨151197477496760206473481009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 201596636662346941964641345 151197477496760206473481009)
      ·
        refine ⟨113398108122570154855110757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 151197477496760206473481009 113398108122570154855110757)
        ·
          refine ⟨21262145272981904035333267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 113398108122570154855110757 21262145272981904035333267)
          ·
            refine ⟨31893217909472856052999901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21262145272981904035333267 31893217909472856052999901)
            ·
              refine ⟨11959956716052321019874963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31893217909472856052999901 11959956716052321019874963)
              ·
                refine ⟨17939935074078481529812445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11959956716052321019874963 17939935074078481529812445)
                ·
                  refine ⟨6727475652779430573679667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17939935074078481529812445 6727475652779430573679667)
                  ·
                    refine ⟨10091213479169145860519501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6727475652779430573679667 10091213479169145860519501)
                    ·
                      refine ⟨3784205054688429697694813, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10091213479169145860519501 3784205054688429697694813)
                      ·
                        rfl

theorem cell23_7369713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 1, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 1, 3, 1, 3, 1, 3].length) (baseStart_7369713 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7369713 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7369713 prefixEnd_7369713 := by exact prefixLift 7369713
  have htrace : WordTrace (prefixWord ++ tailWord_7369713) baseStart_7369713 baseEnd_7369713 := by
    simpa [prefixWord, tailWord_7369713, baseEnd_7369713] using wordTrace_append hprefix tailTrace_7369713
  have hstable : (prefixWord ++ tailWord_7369713).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7369713).length < 2 ^ (prefixWord ++ tailWord_7369713).sum := by decide
  have hdescent : baseEnd_7369713 < baseStart_7369713 := by decide
  rcases family_descends (prefixWord ++ tailWord_7369713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7369736 : List Nat := [2, 1, 3, 2, 1, 4, 1, 1, 3, 1, 4]
def baseStart_7369736 : Nat := 118140960795 + 7369736 * 2 ^ 59
def prefixEnd_7369736 : Nat := 4983230072969 + 3 ^ 40 * 7369736 * 2
def baseEnd_7369736 : Nat := 3784216864743483107707207

theorem tailTrace_7369736 : CollatzResearch.WordTrace tailWord_7369736 prefixEnd_7369736 3784216864743483107707207 := by
  unfold tailWord_7369736
  simp only [CollatzResearch.WordTrace]
  refine ⟨134398177214356298773804531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 179197569619141731698406041 134398177214356298773804531)
  ·
    refine ⟨201597265821534448160706797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134398177214356298773804531 201597265821534448160706797)
    ·
      refine ⟨75598974683075418060265049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 201597265821534448160706797 75598974683075418060265049)
      ·
        refine ⟨56699231012306563545198787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 75598974683075418060265049 56699231012306563545198787)
        ·
          refine ⟨85048846518459845317798181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56699231012306563545198787 85048846518459845317798181)
          ·
            refine ⟨15946658722211220997087159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 85048846518459845317798181 15946658722211220997087159)
            ·
              refine ⟨23919988083316831495630739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15946658722211220997087159 23919988083316831495630739)
              ·
                refine ⟨35879982124975247243446109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23919988083316831495630739 35879982124975247243446109)
                ·
                  refine ⟨13454993296865717716292291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35879982124975247243446109 13454993296865717716292291)
                  ·
                    refine ⟨20182489945298576574438437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13454993296865717716292291 20182489945298576574438437)
                    ·
                      refine ⟨3784216864743483107707207, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20182489945298576574438437 3784216864743483107707207)
                      ·
                        rfl

theorem cell23_7369736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 4, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 4, 1, 1, 3, 1, 4].length) (baseStart_7369736 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7369736 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7369736 prefixEnd_7369736 := by exact prefixLift 7369736
  have htrace : WordTrace (prefixWord ++ tailWord_7369736) baseStart_7369736 baseEnd_7369736 := by
    simpa [prefixWord, tailWord_7369736, baseEnd_7369736] using wordTrace_append hprefix tailTrace_7369736
  have hstable : (prefixWord ++ tailWord_7369736).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7369736).length < 2 ^ (prefixWord ++ tailWord_7369736).sum := by decide
  have hdescent : baseEnd_7369736 < baseStart_7369736 := by decide
  rcases family_descends (prefixWord ++ tailWord_7369736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7369763 : List Nat := [1, 1, 1, 4, 3, 3, 2, 2, 2, 4]
def baseStart_7369763 : Nat := 118140960795 + 7369763 * 2 ^ 59
def prefixEnd_7369763 : Nat := 4983230072969 + 3 ^ 40 * 7369763 * 2
def baseEnd_7369763 : Nat := 1261410242907051500689861

theorem tailTrace_7369763 : CollatzResearch.WordTrace tailWord_7369763 prefixEnd_7369763 1261410242907051500689861 := by
  unfold tailWord_7369763
  simp only [CollatzResearch.WordTrace]
  refine ⟨268797339199614781158841943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179198226133076520772561295 268797339199614781158841943)
  ·
    refine ⟨403196008799422171738262915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 268797339199614781158841943 403196008799422171738262915)
    ·
      refine ⟨604794013199133257607394373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 403196008799422171738262915 604794013199133257607394373)
      ·
        refine ⟨113398877474837485801386445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 604794013199133257607394373 113398877474837485801386445)
        ·
          refine ⟨42524579053064057175519917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 113398877474837485801386445 42524579053064057175519917)
          ·
            refine ⟨15946717144899021440819969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42524579053064057175519917 15946717144899021440819969)
            ·
              refine ⟨11960037858674266080614977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15946717144899021440819969 11960037858674266080614977)
              ·
                refine ⟨8970028394005699560461233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11960037858674266080614977 8970028394005699560461233)
                ·
                  refine ⟨6727521295504274670345925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8970028394005699560461233 6727521295504274670345925)
                  ·
                    refine ⟨1261410242907051500689861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6727521295504274670345925 1261410242907051500689861)
                    ·
                      rfl

theorem cell23_7369763_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 3, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 3, 2, 2, 2, 4].length) (baseStart_7369763 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7369763 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7369763 prefixEnd_7369763 := by exact prefixLift 7369763
  have htrace : WordTrace (prefixWord ++ tailWord_7369763) baseStart_7369763 baseEnd_7369763 := by
    simpa [prefixWord, tailWord_7369763, baseEnd_7369763] using wordTrace_append hprefix tailTrace_7369763
  have hstable : (prefixWord ++ tailWord_7369763).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7369763).length < 2 ^ (prefixWord ++ tailWord_7369763).sum := by decide
  have hdescent : baseEnd_7369763 < baseStart_7369763 := by decide
  rcases family_descends (prefixWord ++ tailWord_7369763) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7369764 : List Nat := [2, 3, 1, 4, 1, 3, 2, 2, 1, 1, 3]
def baseStart_7369764 : Nat := 118140960795 + 7369764 * 2 ^ 59
def prefixEnd_7369764 : Nat := 4983230072969 + 3 ^ 40 * 7369764 * 2
def baseEnd_7369764 : Nat := 3784231242201808998157079

theorem tailTrace_7369764 : CollatzResearch.WordTrace tailWord_7369764 prefixEnd_7369764 3784231242201808998157079 := by
  unfold tailWord_7369764
  simp only [CollatzResearch.WordTrace]
  refine ⟨134398687836305579164814173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 179198250448407438886418897 134398687836305579164814173)
  ·
    refine ⟨50399507938614592186805315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 134398687836305579164814173 50399507938614592186805315)
    ·
      refine ⟨75599261907921888280207973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50399507938614592186805315 75599261907921888280207973)
      ·
        refine ⟨14174861607735354052538995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 75599261907921888280207973 14174861607735354052538995)
        ·
          refine ⟨21262292411603031078808493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14174861607735354052538995 21262292411603031078808493)
          ·
            refine ⟨7973359654351136654553185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21262292411603031078808493 7973359654351136654553185)
            ·
              refine ⟨5980019740763352490914889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7973359654351136654553185 5980019740763352490914889)
              ·
                refine ⟨4485014805572514368186167, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5980019740763352490914889 4485014805572514368186167)
                ·
                  refine ⟨6727522208358771552279251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4485014805572514368186167 6727522208358771552279251)
                  ·
                    refine ⟨10091283312538157328418877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6727522208358771552279251 10091283312538157328418877)
                    ·
                      refine ⟨3784231242201808998157079, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10091283312538157328418877 3784231242201808998157079)
                      ·
                        rfl

theorem cell23_7369764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 3, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 3, 2, 2, 1, 1, 3].length) (baseStart_7369764 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7369764 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7369764 prefixEnd_7369764 := by exact prefixLift 7369764
  have htrace : WordTrace (prefixWord ++ tailWord_7369764) baseStart_7369764 baseEnd_7369764 := by
    simpa [prefixWord, tailWord_7369764, baseEnd_7369764] using wordTrace_append hprefix tailTrace_7369764
  have hstable : (prefixWord ++ tailWord_7369764).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7369764).length < 2 ^ (prefixWord ++ tailWord_7369764).sum := by decide
  have hdescent : baseEnd_7369764 < baseStart_7369764 := by decide
  rcases family_descends (prefixWord ++ tailWord_7369764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7369780 : List Nat := [2, 5, 1, 2, 1, 1, 2, 3, 2, 4]
def baseStart_7369780 : Nat := 118140960795 + 7369780 * 2 ^ 59
def prefixEnd_7369780 : Nat := 4983230072969 + 3 ^ 40 * 7369780 * 2
def baseEnd_7369780 : Nat := 1261413152630760311852335

theorem tailTrace_7369780 : CollatzResearch.WordTrace tailWord_7369780 prefixEnd_7369780 1261413152630760311852335 := by
  unfold tailWord_7369780
  simp only [CollatzResearch.WordTrace]
  refine ⟨134398979620276596531105397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 179198639493702128708140529 134398979620276596531105397)
  ·
    refine ⟨12599904339400930924791131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 134398979620276596531105397 12599904339400930924791131)
    ·
      refine ⟨18899856509101396387186697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12599904339400930924791131 18899856509101396387186697)
      ·
        refine ⟨14174892381826047290390023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18899856509101396387186697 14174892381826047290390023)
        ·
          refine ⟨21262338572739070935585035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14174892381826047290390023 21262338572739070935585035)
          ·
            refine ⟨31893507859108606403377553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21262338572739070935585035 31893507859108606403377553)
            ·
              refine ⟨23920130894331454802533165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31893507859108606403377553 23920130894331454802533165)
              ·
                refine ⟨8970049085374295550949937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23920130894331454802533165 8970049085374295550949937)
                ·
                  refine ⟨6727536814030721663212453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8970049085374295550949937 6727536814030721663212453)
                  ·
                    refine ⟨1261413152630760311852335, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6727536814030721663212453 1261413152630760311852335)
                    ·
                      rfl

theorem cell23_7369780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 1, 2, 3, 2, 4].length) (baseStart_7369780 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7369780 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7369780 prefixEnd_7369780 := by exact prefixLift 7369780
  have htrace : WordTrace (prefixWord ++ tailWord_7369780) baseStart_7369780 baseEnd_7369780 := by
    simpa [prefixWord, tailWord_7369780, baseEnd_7369780] using wordTrace_append hprefix tailTrace_7369780
  have hstable : (prefixWord ++ tailWord_7369780).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7369780).length < 2 ^ (prefixWord ++ tailWord_7369780).sum := by decide
  have hdescent : baseEnd_7369780 < baseStart_7369780 := by decide
  rcases family_descends (prefixWord ++ tailWord_7369780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7369786 : List Nat := [3, 1, 1, 1, 3, 1, 3, 3, 1, 3, 3]
def baseStart_7369786 : Nat := 118140960795 + 7369786 * 2 ^ 59
def prefixEnd_7369786 : Nat := 4983230072969 + 3 ^ 40 * 7369786 * 2
def baseEnd_7369786 : Nat := 3784242538776207912081977

theorem tailTrace_7369786 : CollatzResearch.WordTrace tailWord_7369786 prefixEnd_7369786 3784242538776207912081977 := by
  unfold tailWord_7369786
  simp only [CollatzResearch.WordTrace]
  refine ⟨67199544519632864021732303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 179198785385687637391286141 67199544519632864021732303)
  ·
    refine ⟨100799316779449296032598455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67199544519632864021732303 100799316779449296032598455)
    ·
      refine ⟨151198975169173944048897683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100799316779449296032598455 151198975169173944048897683)
      ·
        refine ⟨226798462753760916073346525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 151198975169173944048897683 226798462753760916073346525)
        ·
          refine ⟨85049423532660343527504947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 226798462753760916073346525 85049423532660343527504947)
          ·
            refine ⟨127574135298990515291257421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85049423532660343527504947 127574135298990515291257421)
            ·
              refine ⟨47840300737121443234221533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 127574135298990515291257421 47840300737121443234221533)
              ·
                refine ⟨17940112776420541212833075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 47840300737121443234221533 17940112776420541212833075)
                ·
                  refine ⟨26910169164630811819249613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17940112776420541212833075 26910169164630811819249613)
                  ·
                    refine ⟨10091313436736554432218605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 26910169164630811819249613 10091313436736554432218605)
                    ·
                      refine ⟨3784242538776207912081977, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10091313436736554432218605 3784242538776207912081977)
                      ·
                        rfl

theorem cell23_7369786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 3, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 3, 3, 1, 3, 3].length) (baseStart_7369786 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7369786 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7369786 prefixEnd_7369786 := by exact prefixLift 7369786
  have htrace : WordTrace (prefixWord ++ tailWord_7369786) baseStart_7369786 baseEnd_7369786 := by
    simpa [prefixWord, tailWord_7369786, baseEnd_7369786] using wordTrace_append hprefix tailTrace_7369786
  have hstable : (prefixWord ++ tailWord_7369786).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7369786).length < 2 ^ (prefixWord ++ tailWord_7369786).sum := by decide
  have hdescent : baseEnd_7369786 < baseStart_7369786 := by decide
  rcases family_descends (prefixWord ++ tailWord_7369786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7369793 : List Nat := [1, 2, 5, 1, 3, 1, 3, 7]
def baseStart_7369793 : Nat := 118140960795 + 7369793 * 2 ^ 59
def prefixEnd_7369793 : Nat := 4983230072969 + 3 ^ 40 * 7369793 * 2
def baseEnd_7369793 : Nat := 140157264190399606840535

theorem tailTrace_7369793 : CollatzResearch.WordTrace tailWord_7369793 prefixEnd_7369793 140157264190399606840535 := by
  unfold tailWord_7369793
  simp only [CollatzResearch.WordTrace]
  refine ⟨268798433389506096282434033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179198955593004064188289355 268798433389506096282434033)
  ·
    refine ⟨201598825042129572211825525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 268798433389506096282434033 201598825042129572211825525)
    ·
      refine ⟨18899889847699647394858643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 201598825042129572211825525 18899889847699647394858643)
      ·
        refine ⟨28349834771549471092287965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18899889847699647394858643 28349834771549471092287965)
        ·
          refine ⟨10631188039331051659607987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28349834771549471092287965 10631188039331051659607987)
          ·
            refine ⟨15946782058996577489411981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10631188039331051659607987 15946782058996577489411981)
            ·
              refine ⟨5980043272123716558529493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15946782058996577489411981 5980043272123716558529493)
              ·
                refine ⟨140157264190399606840535, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5980043272123716558529493 140157264190399606840535)
                ·
                  rfl

theorem cell23_7369793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 3, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 3, 1, 3, 7].length) (baseStart_7369793 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7369793 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7369793 prefixEnd_7369793 := by exact prefixLift 7369793
  have htrace : WordTrace (prefixWord ++ tailWord_7369793) baseStart_7369793 baseEnd_7369793 := by
    simpa [prefixWord, tailWord_7369793, baseEnd_7369793] using wordTrace_append hprefix tailTrace_7369793
  have hstable : (prefixWord ++ tailWord_7369793).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7369793).length < 2 ^ (prefixWord ++ tailWord_7369793).sum := by decide
  have hdescent : baseEnd_7369793 < baseStart_7369793 := by decide
  rcases family_descends (prefixWord ++ tailWord_7369793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7369814 : List Nat := [5, 2, 2, 1, 2, 2, 1, 2, 2, 4]
def baseStart_7369814 : Nat := 118140960795 + 7369814 * 2 ^ 59
def prefixEnd_7369814 : Nat := 4983230072969 + 3 ^ 40 * 7369814 * 2
def baseEnd_7369814 : Nat := 1261418972078177934177283

theorem tailTrace_7369814 : CollatzResearch.WordTrace tailWord_7369814 prefixEnd_7369814 1261418972078177934177283 := by
  unfold tailWord_7369814
  simp only [CollatzResearch.WordTrace]
  refine ⟨16799949957651876054309281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 179199466214953344579298997 16799949957651876054309281)
  ·
    refine ⟨12599962468238907040731961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16799949957651876054309281 12599962468238907040731961)
    ·
      refine ⟨9449971851179180280548971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12599962468238907040731961 9449971851179180280548971)
      ·
        refine ⟨14174957776768770420823457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9449971851179180280548971 14174957776768770420823457)
        ·
          refine ⟨10631218332576577815617593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14174957776768770420823457 10631218332576577815617593)
          ·
            refine ⟨7973413749432433361713195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10631218332576577815617593 7973413749432433361713195)
            ·
              refine ⟨11960120624148650042569793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7973413749432433361713195 11960120624148650042569793)
              ·
                refine ⟨8970090468111487531927345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11960120624148650042569793 8970090468111487531927345)
                ·
                  refine ⟨6727567851083615648945509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8970090468111487531927345 6727567851083615648945509)
                  ·
                    refine ⟨1261418972078177934177283, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6727567851083615648945509 1261418972078177934177283)
                    ·
                      rfl

theorem cell23_7369814_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 2, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 2, 2, 1, 2, 2, 4].length) (baseStart_7369814 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7369814 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7369814 prefixEnd_7369814 := by exact prefixLift 7369814
  have htrace : WordTrace (prefixWord ++ tailWord_7369814) baseStart_7369814 baseEnd_7369814 := by
    simpa [prefixWord, tailWord_7369814, baseEnd_7369814] using wordTrace_append hprefix tailTrace_7369814
  have hstable : (prefixWord ++ tailWord_7369814).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7369814).length < 2 ^ (prefixWord ++ tailWord_7369814).sum := by decide
  have hdescent : baseEnd_7369814 < baseStart_7369814 := by decide
  rcases family_descends (prefixWord ++ tailWord_7369814) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7369837 : List Nat := [1, 5, 1, 1, 2, 3, 3, 1, 2, 1, 3]
def baseStart_7369837 : Nat := 118140960795 + 7369837 * 2 ^ 59
def prefixEnd_7369837 : Nat := 4983230072969 + 3 ^ 40 * 7369837 * 2
def baseEnd_7369837 : Nat := 3784268726289587212544243

theorem tailTrace_7369837 : CollatzResearch.WordTrace tailWord_7369837 prefixEnd_7369837 3784268726289587212544243 := by
  unfold tailWord_7369837
  simp only [CollatzResearch.WordTrace]
  refine ⟨268800038201346691797035765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179200025467564461198023843 268800038201346691797035765)
  ·
    refine ⟨25200003581376252355972103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 268800038201346691797035765 25200003581376252355972103)
    ·
      refine ⟨37800005372064378533958155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25200003581376252355972103 37800005372064378533958155)
      ·
        refine ⟨56700008058096567800937233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37800005372064378533958155 56700008058096567800937233)
        ·
          refine ⟨42525006043572425850702925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56700008058096567800937233 42525006043572425850702925)
          ·
            refine ⟨15946877266339659694013597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42525006043572425850702925 15946877266339659694013597)
            ·
              refine ⟨5980078974877372385255099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15946877266339659694013597 5980078974877372385255099)
              ·
                refine ⟨8970118462316058577882649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5980078974877372385255099 8970118462316058577882649)
                ·
                  refine ⟨6727588846737043933411987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8970118462316058577882649 6727588846737043933411987)
                  ·
                    refine ⟨10091383270105565900117981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6727588846737043933411987 10091383270105565900117981)
                    ·
                      refine ⟨3784268726289587212544243, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10091383270105565900117981 3784268726289587212544243)
                      ·
                        rfl

theorem cell23_7369837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 3, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 3, 3, 1, 2, 1, 3].length) (baseStart_7369837 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7369837 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7369837 prefixEnd_7369837 := by exact prefixLift 7369837
  have htrace : WordTrace (prefixWord ++ tailWord_7369837) baseStart_7369837 baseEnd_7369837 := by
    simpa [prefixWord, tailWord_7369837, baseEnd_7369837] using wordTrace_append hprefix tailTrace_7369837
  have hstable : (prefixWord ++ tailWord_7369837).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7369837).length < 2 ^ (prefixWord ++ tailWord_7369837).sum := by decide
  have hdescent : baseEnd_7369837 < baseStart_7369837 := by decide
  rcases family_descends (prefixWord ++ tailWord_7369837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7369860 : List Nat := [2, 3, 2, 1, 2, 2, 1, 2, 4, 2, 2]
def baseStart_7369860 : Nat := 118140960795 + 7369860 * 2 ^ 59
def prefixEnd_7369860 : Nat := 4983230072969 + 3 ^ 40 * 7369860 * 2
def baseEnd_7369860 : Nat := 3784280536344640622556637

theorem tailTrace_7369860 : CollatzResearch.WordTrace tailWord_7369860 prefixEnd_7369860 3784280536344640622556637 := by
  unfold tailWord_7369860
  simp only [CollatzResearch.WordTrace]
  refine ⟨134400438540131683362561517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 179200584720175577816748689 134400438540131683362561517)
  ·
    refine ⟨50400164452549381260960569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 134400438540131683362561517 50400164452549381260960569)
    ·
      refine ⟨37800123339412035945720427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50400164452549381260960569 37800123339412035945720427)
      ·
        refine ⟨56700185009118053918580641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37800123339412035945720427 56700185009118053918580641)
        ·
          refine ⟨42525138756838540438935481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56700185009118053918580641 42525138756838540438935481)
          ·
            refine ⟨31893854067628905329201611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42525138756838540438935481 31893854067628905329201611)
            ·
              refine ⟨47840781101443357993802417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31893854067628905329201611 47840781101443357993802417)
              ·
                refine ⟨35880585826082518495351813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47840781101443357993802417 35880585826082518495351813)
                ·
                  refine ⟨6727609842390472217878465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 35880585826082518495351813 6727609842390472217878465)
                  ·
                    refine ⟨5045707381792854163408849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6727609842390472217878465 5045707381792854163408849)
                    ·
                      refine ⟨3784280536344640622556637, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5045707381792854163408849 3784280536344640622556637)
                      ·
                        rfl

theorem cell23_7369860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 2, 1, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 2, 1, 2, 4, 2, 2].length) (baseStart_7369860 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7369860 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7369860 prefixEnd_7369860 := by exact prefixLift 7369860
  have htrace : WordTrace (prefixWord ++ tailWord_7369860) baseStart_7369860 baseEnd_7369860 := by
    simpa [prefixWord, tailWord_7369860, baseEnd_7369860] using wordTrace_append hprefix tailTrace_7369860
  have hstable : (prefixWord ++ tailWord_7369860).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7369860).length < 2 ^ (prefixWord ++ tailWord_7369860).sum := by decide
  have hdescent : baseEnd_7369860 < baseStart_7369860 := by decide
  rcases family_descends (prefixWord ++ tailWord_7369860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7369913 : List Nat := [1, 2, 1, 4, 1, 4, 2, 1, 2, 5]
def baseStart_7369913 : Nat := 118140960795 + 7369913 * 2 ^ 59
def prefixEnd_7369913 : Nat := 4983230072969 + 3 ^ 40 * 7369913 * 2
def baseEnd_7369913 : Nat := 1261435916939776305064631

theorem tailTrace_7369913 : CollatzResearch.WordTrace tailWord_7369913 prefixEnd_7369913 1261435916939776305064631 := by
  unfold tailWord_7369913
  simp only [CollatzResearch.WordTrace]
  refine ⟨268802810149071356776802393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179201873432714237851201595 268802810149071356776802393)
  ·
    refine ⟨201602107611803517582601795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 268802810149071356776802393 201602107611803517582601795)
    ·
      refine ⟨302403161417705276373902693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 201602107611803517582601795 302403161417705276373902693)
      ·
        refine ⟨56700592765819739320106755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 302403161417705276373902693 56700592765819739320106755)
        ·
          refine ⟨85050889148729608980160133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56700592765819739320106755 85050889148729608980160133)
          ·
            refine ⟨15947041715386801683780025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 85050889148729608980160133 15947041715386801683780025)
            ·
              refine ⟨11960281286540101262835019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15947041715386801683780025 11960281286540101262835019)
              ·
                refine ⟨17940421929810151894252529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11960281286540101262835019 17940421929810151894252529)
                ·
                  refine ⟨13455316447357613920689397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17940421929810151894252529 13455316447357613920689397)
                  ·
                    refine ⟨1261435916939776305064631, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13455316447357613920689397 1261435916939776305064631)
                    ·
                      rfl

theorem cell23_7369913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 4, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 4, 2, 1, 2, 5].length) (baseStart_7369913 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7369913 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7369913 prefixEnd_7369913 := by exact prefixLift 7369913
  have htrace : WordTrace (prefixWord ++ tailWord_7369913) baseStart_7369913 baseEnd_7369913 := by
    simpa [prefixWord, tailWord_7369913, baseEnd_7369913] using wordTrace_append hprefix tailTrace_7369913
  have hstable : (prefixWord ++ tailWord_7369913).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7369913).length < 2 ^ (prefixWord ++ tailWord_7369913).sum := by decide
  have hdescent : baseEnd_7369913 < baseStart_7369913 := by decide
  rcases family_descends (prefixWord ++ tailWord_7369913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7369934 : List Nat := [4, 1, 1, 1, 6, 1, 2, 2, 5]
def baseStart_7369934 : Nat := 118140960795 + 7369934 * 2 ^ 59
def prefixEnd_7369934 : Nat := 4983230072969 + 3 ^ 40 * 7369934 * 2
def baseEnd_7369934 : Nat := 420479837101452592559033

theorem tailTrace_7369934 : CollatzResearch.WordTrace tailWord_7369934 prefixEnd_7369934 420479837101452592559033 := by
  unfold tailWord_7369934
  simp only [CollatzResearch.WordTrace]
  refine ⟨33600447010249409670414607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 179202384054663518242211237 33600447010249409670414607)
  ·
    refine ⟨50400670515374114505621911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33600447010249409670414607 50400670515374114505621911)
    ·
      refine ⟨75601005773061171758432867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50400670515374114505621911 75601005773061171758432867)
      ·
        refine ⟨113401508659591757637649301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75601005773061171758432867 113401508659591757637649301)
        ·
          refine ⟨5315695718418363639264811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 113401508659591757637649301 5315695718418363639264811)
          ·
            refine ⟨7973543577627545458897217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5315695718418363639264811 7973543577627545458897217)
            ·
              refine ⟨5980157683220659094172913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7973543577627545458897217 5980157683220659094172913)
              ·
                refine ⟨4485118262415494320629685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5980157683220659094172913 4485118262415494320629685)
                ·
                  refine ⟨420479837101452592559033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4485118262415494320629685 420479837101452592559033)
                  ·
                    rfl

theorem cell23_7369934_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 6, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 6, 1, 2, 2, 5].length) (baseStart_7369934 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7369934 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7369934 prefixEnd_7369934 := by exact prefixLift 7369934
  have htrace : WordTrace (prefixWord ++ tailWord_7369934) baseStart_7369934 baseEnd_7369934 := by
    simpa [prefixWord, tailWord_7369934, baseEnd_7369934] using wordTrace_append hprefix tailTrace_7369934
  have hstable : (prefixWord ++ tailWord_7369934).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7369934).length < 2 ^ (prefixWord ++ tailWord_7369934).sum := by decide
  have hdescent : baseEnd_7369934 < baseStart_7369934 := by decide
  rcases family_descends (prefixWord ++ tailWord_7369934) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7369946 : List Nat := [3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 4]
def baseStart_7369946 : Nat := 118140960795 + 7369946 * 2 ^ 59
def prefixEnd_7369946 : Nat := 4983230072969 + 3 ^ 40 * 7369946 * 2
def baseEnd_7369946 : Nat := 3784324695680927286081241

theorem tailTrace_7369946 : CollatzResearch.WordTrace tailWord_7369946 prefixEnd_7369946 3784324695680927286081241 := by
  unfold tailWord_7369946
  simp only [CollatzResearch.WordTrace]
  refine ⟨67201003439487950853188423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 179202675838634535608502461 67201003439487950853188423)
  ·
    refine ⟨100801505159231926279782635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67201003439487950853188423 100801505159231926279782635)
    ·
      refine ⟨151202257738847889419673953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100801505159231926279782635 151202257738847889419673953)
      ·
        refine ⟨113401693304135917064755465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 151202257738847889419673953 113401693304135917064755465)
        ·
          refine ⟨85051269978101937798566599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 113401693304135917064755465 85051269978101937798566599)
          ·
            refine ⟨127576904967152906697849899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85051269978101937798566599 127576904967152906697849899)
            ·
              refine ⟨191365357450729360046774849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 127576904967152906697849899 191365357450729360046774849)
              ·
                refine ⟨143524018088047020035081137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 191365357450729360046774849 143524018088047020035081137)
                ·
                  refine ⟨107643013566035265026310853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 143524018088047020035081137 107643013566035265026310853)
                  ·
                    refine ⟨20183065043631612192433285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 107643013566035265026310853 20183065043631612192433285)
                    ·
                      refine ⟨3784324695680927286081241, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20183065043631612192433285 3784324695680927286081241)
                      ·
                        rfl

theorem cell23_7369946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 4].length) (baseStart_7369946 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7369946 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7369946 prefixEnd_7369946 := by exact prefixLift 7369946
  have htrace : WordTrace (prefixWord ++ tailWord_7369946) baseStart_7369946 baseEnd_7369946 := by
    simpa [prefixWord, tailWord_7369946, baseEnd_7369946] using wordTrace_append hprefix tailTrace_7369946
  have hstable : (prefixWord ++ tailWord_7369946).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7369946).length < 2 ^ (prefixWord ++ tailWord_7369946).sum := by decide
  have hdescent : baseEnd_7369946 < baseStart_7369946 := by decide
  rcases family_descends (prefixWord ++ tailWord_7369946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7369967 : List Nat := [1, 1, 2, 1, 8, 1, 1, 1, 2, 1, 4]
def baseStart_7369967 : Nat := 118140960795 + 7369967 * 2 ^ 59
def prefixEnd_7369967 : Nat := 4983230072969 + 3 ^ 40 * 7369967 * 2
def baseEnd_7369967 : Nat := 3784335478774671703918645

theorem tailTrace_7369967 : CollatzResearch.WordTrace tailWord_7369967 prefixEnd_7369967 3784335478774671703918645 := by
  unfold tailWord_7369967
  simp only [CollatzResearch.WordTrace]
  refine ⟨268804779690875723999268155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179203186460583815999512103 268804779690875723999268155)
  ·
    refine ⟨403207169536313585998902233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 268804779690875723999268155 403207169536313585998902233)
    ·
      refine ⟨302405377152235189499176675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 403207169536313585998902233 302405377152235189499176675)
      ·
        refine ⟨453608065728352784248765013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 302405377152235189499176675 453608065728352784248765013)
        ·
          refine ⟨5315719520254134190415215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 453608065728352784248765013 5315719520254134190415215)
          ·
            refine ⟨7973579280381201285622823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5315719520254134190415215 7973579280381201285622823)
            ·
              refine ⟨11960368920571801928434235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7973579280381201285622823 11960368920571801928434235)
              ·
                refine ⟨17940553380857702892651353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11960368920571801928434235 17940553380857702892651353)
                ·
                  refine ⟨13455415035643277169488515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17940553380857702892651353 13455415035643277169488515)
                  ·
                    refine ⟨20183122553464915754232773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13455415035643277169488515 20183122553464915754232773)
                    ·
                      refine ⟨3784335478774671703918645, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20183122553464915754232773 3784335478774671703918645)
                      ·
                        rfl

theorem cell23_7369967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 8, 1, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 8, 1, 1, 1, 2, 1, 4].length) (baseStart_7369967 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7369967 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7369967 prefixEnd_7369967 := by exact prefixLift 7369967
  have htrace : WordTrace (prefixWord ++ tailWord_7369967) baseStart_7369967 baseEnd_7369967 := by
    simpa [prefixWord, tailWord_7369967, baseEnd_7369967] using wordTrace_append hprefix tailTrace_7369967
  have hstable : (prefixWord ++ tailWord_7369967).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7369967).length < 2 ^ (prefixWord ++ tailWord_7369967).sum := by decide
  have hdescent : baseEnd_7369967 < baseStart_7369967 := by decide
  rcases family_descends (prefixWord ++ tailWord_7369967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7369970 : List Nat := [3, 2, 1, 3, 3, 1, 1, 1, 1, 4, 3]
def baseStart_7369970 : Nat := 118140960795 + 7369970 * 2 ^ 59
def prefixEnd_7369970 : Nat := 4983230072969 + 3 ^ 40 * 7369970 * 2
def baseEnd_7369970 : Nat := 3784337019216635192181131

theorem tailTrace_7369970 : CollatzResearch.WordTrace tailWord_7369970 prefixEnd_7369970 3784337019216635192181131 := by
  unfold tailWord_7369970
  simp only [CollatzResearch.WordTrace]
  refine ⟨67201222277466213877906841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 179203259406576570341084909 67201222277466213877906841)
  ·
    refine ⟨50400916708099660408430131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67201222277466213877906841 50400916708099660408430131)
    ·
      refine ⟨75601375062149490612645197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50400916708099660408430131 75601375062149490612645197)
      ·
        refine ⟨28350515648306058979741949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 75601375062149490612645197 28350515648306058979741949)
        ·
          refine ⟨10631443368114772117403231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28350515648306058979741949 10631443368114772117403231)
          ·
            refine ⟨15947165052172158176104847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10631443368114772117403231 15947165052172158176104847)
            ·
              refine ⟨23920747578258237264157271, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15947165052172158176104847 23920747578258237264157271)
              ·
                refine ⟨35881121367387355896235907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23920747578258237264157271 35881121367387355896235907)
                ·
                  refine ⟨53821682051081033844353861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35881121367387355896235907 53821682051081033844353861)
                  ·
                    refine ⟨10091565384577693845816349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 53821682051081033844353861 10091565384577693845816349)
                    ·
                      refine ⟨3784337019216635192181131, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10091565384577693845816349 3784337019216635192181131)
                      ·
                        rfl

theorem cell23_7369970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 3, 1, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 3, 1, 1, 1, 1, 4, 3].length) (baseStart_7369970 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7369970 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7369970 prefixEnd_7369970 := by exact prefixLift 7369970
  have htrace : WordTrace (prefixWord ++ tailWord_7369970) baseStart_7369970 baseEnd_7369970 := by
    simpa [prefixWord, tailWord_7369970, baseEnd_7369970] using wordTrace_append hprefix tailTrace_7369970
  have hstable : (prefixWord ++ tailWord_7369970).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7369970).length < 2 ^ (prefixWord ++ tailWord_7369970).sum := by decide
  have hdescent : baseEnd_7369970 < baseStart_7369970 := by decide
  rcases family_descends (prefixWord ++ tailWord_7369970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7370010 : List Nat := [3, 1, 1, 3, 3, 1, 1, 2, 1, 5, 2]
def baseStart_7370010 : Nat := 118140960795 + 7370010 * 2 ^ 59
def prefixEnd_7370010 : Nat := 4983230072969 + 3 ^ 40 * 7370010 * 2
def baseEnd_7370010 : Nat := 3784357558442815035680947

theorem tailTrace_7370010 : CollatzResearch.WordTrace tailWord_7370010 prefixEnd_7370010 3784357558442815035680947 := by
  unfold tailWord_7370010
  simp only [CollatzResearch.WordTrace]
  refine ⟨67201587007429985585770871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 179204232019813294895388989 67201587007429985585770871)
  ·
    refine ⟨100802380511144978378656307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67201587007429985585770871 100802380511144978378656307)
    ·
      refine ⟨151203570766717467567984461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100802380511144978378656307 151203570766717467567984461)
      ·
        refine ⟨56701339037519050337994173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 151203570766717467567984461 56701339037519050337994173)
        ·
          refine ⟨21263002139069643876747815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 56701339037519050337994173 21263002139069643876747815)
          ·
            refine ⟨31894503208604465815121723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21263002139069643876747815 31894503208604465815121723)
            ·
              refine ⟨47841754812906698722682585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31894503208604465815121723 47841754812906698722682585)
              ·
                refine ⟨35881316109680024042011939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47841754812906698722682585 35881316109680024042011939)
                ·
                  refine ⟨53821974164520036063017909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35881316109680024042011939 53821974164520036063017909)
                  ·
                    refine ⟨5045810077923753380907929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 53821974164520036063017909 5045810077923753380907929)
                    ·
                      refine ⟨3784357558442815035680947, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5045810077923753380907929 3784357558442815035680947)
                      ·
                        rfl

theorem cell23_7370010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 1, 1, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 1, 1, 2, 1, 5, 2].length) (baseStart_7370010 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7370010 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7370010 prefixEnd_7370010 := by exact prefixLift 7370010
  have htrace : WordTrace (prefixWord ++ tailWord_7370010) baseStart_7370010 baseEnd_7370010 := by
    simpa [prefixWord, tailWord_7370010, baseEnd_7370010] using wordTrace_append hprefix tailTrace_7370010
  have hstable : (prefixWord ++ tailWord_7370010).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7370010).length < 2 ^ (prefixWord ++ tailWord_7370010).sum := by decide
  have hdescent : baseEnd_7370010 < baseStart_7370010 := by decide
  rcases family_descends (prefixWord ++ tailWord_7370010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7370020 : List Nat := [2, 3, 1, 3, 1, 1, 4, 2, 1, 5]
def baseStart_7370020 : Nat := 118140960795 + 7370020 * 2 ^ 59
def prefixEnd_7370020 : Nat := 4983230072969 + 3 ^ 40 * 7370020 * 2
def baseEnd_7370020 : Nat := 1261454231083119998851967

theorem tailTrace_7370020 : CollatzResearch.WordTrace tailWord_7370020 prefixEnd_7370020 1261454231083119998851967 := by
  unfold tailWord_7370020
  simp only [CollatzResearch.WordTrace]
  refine ⟨134403356379841857025473757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 179204475173122476033965009 134403356379841857025473757)
  ·
    refine ⟨50401258642440696384552659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 134403356379841857025473757 50401258642440696384552659)
    ·
      refine ⟨75601887963661044576828989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50401258642440696384552659 75601887963661044576828989)
      ·
        refine ⟨28350707986372891716310871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 75601887963661044576828989 28350707986372891716310871)
        ·
          refine ⟨42526061979559337574466307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28350707986372891716310871 42526061979559337574466307)
          ·
            refine ⟨63789092969339006361699461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42526061979559337574466307 63789092969339006361699461)
            ·
              refine ⟨11960454931751063692818649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 63789092969339006361699461 11960454931751063692818649)
              ·
                refine ⟨8970341198813297769613987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11960454931751063692818649 8970341198813297769613987)
                ·
                  refine ⟨13455511798219946654420981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8970341198813297769613987 13455511798219946654420981)
                  ·
                    refine ⟨1261454231083119998851967, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13455511798219946654420981 1261454231083119998851967)
                    ·
                      rfl

theorem cell23_7370020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 4, 2, 1, 5].length) (baseStart_7370020 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7370020 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7370020 prefixEnd_7370020 := by exact prefixLift 7370020
  have htrace : WordTrace (prefixWord ++ tailWord_7370020) baseStart_7370020 baseEnd_7370020 := by
    simpa [prefixWord, tailWord_7370020, baseEnd_7370020] using wordTrace_append hprefix tailTrace_7370020
  have hstable : (prefixWord ++ tailWord_7370020).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7370020).length < 2 ^ (prefixWord ++ tailWord_7370020).sum := by decide
  have hdescent : baseEnd_7370020 < baseStart_7370020 := by decide
  rcases family_descends (prefixWord ++ tailWord_7370020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7370034 : List Nat := [3, 2, 1, 1, 4, 1, 3, 3, 1, 1, 3]
def baseStart_7370034 : Nat := 118140960795 + 7370034 * 2 ^ 59
def prefixEnd_7370034 : Nat := 4983230072969 + 3 ^ 40 * 7370034 * 2
def baseEnd_7370034 : Nat := 3784369881978522941780837

theorem tailTrace_7370034 : CollatzResearch.WordTrace tailWord_7370034 prefixEnd_7370034 3784369881978522941780837 := by
  unfold tailWord_7370034
  simp only [CollatzResearch.WordTrace]
  refine ⟨67201805845408248610489289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 179204815587755329627971437 67201805845408248610489289)
  ·
    refine ⟨50401354384056186457866967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67201805845408248610489289 50401354384056186457866967)
    ·
      refine ⟨75602031576084279686800451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50401354384056186457866967 75602031576084279686800451)
      ·
        refine ⟨113403047364126419530200677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75602031576084279686800451 113403047364126419530200677)
        ·
          refine ⟨21263071380773703661912627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 113403047364126419530200677 21263071380773703661912627)
          ·
            refine ⟨31894607071160555492868941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21263071380773703661912627 31894607071160555492868941)
            ·
              refine ⟨11960477651685208309825853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31894607071160555492868941 11960477651685208309825853)
              ·
                refine ⟨4485179119381953116184695, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11960477651685208309825853 4485179119381953116184695)
                ·
                  refine ⟨6727768679072929674277043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4485179119381953116184695 6727768679072929674277043)
                  ·
                    refine ⟨10091653018609394511415565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6727768679072929674277043 10091653018609394511415565)
                    ·
                      refine ⟨3784369881978522941780837, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10091653018609394511415565 3784369881978522941780837)
                      ·
                        rfl

theorem cell23_7370034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 1, 3, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 1, 3, 3, 1, 1, 3].length) (baseStart_7370034 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7370034 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7370034 prefixEnd_7370034 := by exact prefixLift 7370034
  have htrace : WordTrace (prefixWord ++ tailWord_7370034) baseStart_7370034 baseEnd_7370034 := by
    simpa [prefixWord, tailWord_7370034, baseEnd_7370034] using wordTrace_append hprefix tailTrace_7370034
  have hstable : (prefixWord ++ tailWord_7370034).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7370034).length < 2 ^ (prefixWord ++ tailWord_7370034).sum := by decide
  have hdescent : baseEnd_7370034 < baseStart_7370034 := by decide
  rcases family_descends (prefixWord ++ tailWord_7370034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7370057 : List Nat := [1, 2, 1, 1, 2, 3, 5, 1, 3, 2, 2]
def baseStart_7370057 : Nat := 118140960795 + 7370057 * 2 ^ 59
def prefixEnd_7370057 : Nat := 4983230072969 + 3 ^ 40 * 7370057 * 2
def baseEnd_7370057 : Nat := 3784381692033576351793231

theorem tailTrace_7370057 : CollatzResearch.WordTrace tailWord_7370057 prefixEnd_7370057 3784381692033576351793231 := by
  unfold tailWord_7370057
  simp only [CollatzResearch.WordTrace]
  refine ⟨268808062260549669370044425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179205374840366446246696283 268808062260549669370044425)
  ·
    refine ⟨201606046695412252027533319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 268808062260549669370044425 201606046695412252027533319)
    ·
      refine ⟨302409070043118378041299979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 201606046695412252027533319 302409070043118378041299979)
      ·
        refine ⟨453613605064677567061949969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 302409070043118378041299979 453613605064677567061949969)
        ·
          refine ⟨340210203798508175296462477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 453613605064677567061949969 340210203798508175296462477)
          ·
            refine ⟨127578826424440565736173429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 340210203798508175296462477 127578826424440565736173429)
            ·
              refine ⟨11960514977291303037766259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 127578826424440565736173429 11960514977291303037766259)
              ·
                refine ⟨17940772465936954556649389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11960514977291303037766259 17940772465936954556649389)
                ·
                  refine ⟨6727789674726357958743521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17940772465936954556649389 6727789674726357958743521)
                  ·
                    refine ⟨5045842256044768469057641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6727789674726357958743521 5045842256044768469057641)
                    ·
                      refine ⟨3784381692033576351793231, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5045842256044768469057641 3784381692033576351793231)
                      ·
                        rfl

theorem cell23_7370057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 5, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 5, 1, 3, 2, 2].length) (baseStart_7370057 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7370057 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7370057 prefixEnd_7370057 := by exact prefixLift 7370057
  have htrace : WordTrace (prefixWord ++ tailWord_7370057) baseStart_7370057 baseEnd_7370057 := by
    simpa [prefixWord, tailWord_7370057, baseEnd_7370057] using wordTrace_append hprefix tailTrace_7370057
  have hstable : (prefixWord ++ tailWord_7370057).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7370057).length < 2 ^ (prefixWord ++ tailWord_7370057).sum := by decide
  have hdescent : baseEnd_7370057 < baseStart_7370057 := by decide
  rcases family_descends (prefixWord ++ tailWord_7370057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7370094 : List Nat := [4, 1, 2, 4, 1, 2, 1, 1, 1, 1, 5]
def baseStart_7370094 : Nat := 118140960795 + 7370094 * 2 ^ 59
def prefixEnd_7370094 : Nat := 4983230072969 + 3 ^ 40 * 7370094 * 2
def baseEnd_7370094 : Nat := 3784400690817792707030561

theorem tailTrace_7370094 : CollatzResearch.WordTrace tailWord_7370094 prefixEnd_7370094 3784400690817792707030561 := by
  unfold tailWord_7370094
  simp only [CollatzResearch.WordTrace]
  refine ⟨33601176470176953086142667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 179206274507610416459427557 33601176470176953086142667)
  ·
    refine ⟨50401764705265429629214001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33601176470176953086142667 50401764705265429629214001)
    ·
      refine ⟨37801323528949072221910501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50401764705265429629214001 37801323528949072221910501)
      ·
        refine ⟨7087748161677951041608219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 37801323528949072221910501 7087748161677951041608219)
        ·
          refine ⟨10631622242516926562412329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7087748161677951041608219 10631622242516926562412329)
          ·
            refine ⟨7973716681887694921809247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10631622242516926562412329 7973716681887694921809247)
            ·
              refine ⟨11960575022831542382713871, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7973716681887694921809247 11960575022831542382713871)
              ·
                refine ⟨17940862534247313574070807, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11960575022831542382713871 17940862534247313574070807)
                ·
                  refine ⟨26911293801370970361106211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17940862534247313574070807 26911293801370970361106211)
                  ·
                    refine ⟨40366940702056455541659317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 26911293801370970361106211 40366940702056455541659317)
                    ·
                      refine ⟨3784400690817792707030561, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 40366940702056455541659317 3784400690817792707030561)
                      ·
                        rfl

theorem cell23_7370094_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 1, 2, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 1, 2, 1, 1, 1, 1, 5].length) (baseStart_7370094 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7370094 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7370094 prefixEnd_7370094 := by exact prefixLift 7370094
  have htrace : WordTrace (prefixWord ++ tailWord_7370094) baseStart_7370094 baseEnd_7370094 := by
    simpa [prefixWord, tailWord_7370094, baseEnd_7370094] using wordTrace_append hprefix tailTrace_7370094
  have hstable : (prefixWord ++ tailWord_7370094).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7370094).length < 2 ^ (prefixWord ++ tailWord_7370094).sum := by decide
  have hdescent : baseEnd_7370094 < baseStart_7370094 := by decide
  rcases family_descends (prefixWord ++ tailWord_7370094) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7370107 : List Nat := [1, 1, 1, 1, 1, 6, 4, 2, 2, 1, 3]
def baseStart_7370107 : Nat := 118140960795 + 7370107 * 2 ^ 59
def prefixEnd_7370107 : Nat := 4983230072969 + 3 ^ 40 * 7370107 * 2
def baseEnd_7370107 : Nat := 3784407366066301156168001

theorem tailTrace_7370107 : CollatzResearch.WordTrace tailWord_7370107 prefixEnd_7370107 3784407366066301156168001 := by
  unfold tailWord_7370107
  simp only [CollatzResearch.WordTrace]
  refine ⟨268809885910368527909364575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179206590606912351939576383 268809885910368527909364575)
  ·
    refine ⟨403214828865552791864046863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 268809885910368527909364575 403214828865552791864046863)
    ·
      refine ⟨604822243298329187796070295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 403214828865552791864046863 604822243298329187796070295)
      ·
        refine ⟨907233364947493781694105443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 604822243298329187796070295 907233364947493781694105443)
        ·
          refine ⟨1360850047421240672541158165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 907233364947493781694105443 1360850047421240672541158165)
          ·
            refine ⟨63789845972870656525366789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 1360850047421240672541158165 63789845972870656525366789)
            ·
              refine ⟨11960596119913248098506273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 63789845972870656525366789 11960596119913248098506273)
              ·
                refine ⟨8970447089934936073879705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11960596119913248098506273 8970447089934936073879705)
                ·
                  refine ⟨6727835317451202055409779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8970447089934936073879705 6727835317451202055409779)
                  ·
                    refine ⟨10091752976176803083114669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6727835317451202055409779 10091752976176803083114669)
                    ·
                      refine ⟨3784407366066301156168001, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10091752976176803083114669 3784407366066301156168001)
                      ·
                        rfl

theorem cell23_7370107_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 4, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 4, 2, 2, 1, 3].length) (baseStart_7370107 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7370107 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7370107 prefixEnd_7370107 := by exact prefixLift 7370107
  have htrace : WordTrace (prefixWord ++ tailWord_7370107) baseStart_7370107 baseEnd_7370107 := by
    simpa [prefixWord, tailWord_7370107, baseEnd_7370107] using wordTrace_append hprefix tailTrace_7370107
  have hstable : (prefixWord ++ tailWord_7370107).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7370107).length < 2 ^ (prefixWord ++ tailWord_7370107).sum := by decide
  have hdescent : baseEnd_7370107 < baseStart_7370107 := by decide
  rcases family_descends (prefixWord ++ tailWord_7370107) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7370123 : List Nat := [1, 1, 1, 1, 4, 3, 3, 1, 2, 6]
def baseStart_7370123 : Nat := 118140960795 + 7370123 * 2 ^ 59
def prefixEnd_7370123 : Nat := 4983230072969 + 3 ^ 40 * 7370123 * 2
def baseEnd_7370123 : Nat := 1261471860585591031189309

theorem tailTrace_7370123 : CollatzResearch.WordTrace tailWord_7370123 prefixEnd_7370123 1261471860585591031189309 := by
  unfold tailWord_7370123
  simp only [CollatzResearch.WordTrace]
  refine ⟨268810469478310562641947023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179206979652207041761298015 268810469478310562641947023)
  ·
    refine ⟨403215704217465843962920535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 268810469478310562641947023 403215704217465843962920535)
    ·
      refine ⟨604823556326198765944380803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 403215704217465843962920535 604823556326198765944380803)
      ·
        refine ⟨907235334489298148916571205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 604823556326198765944380803 907235334489298148916571205)
        ·
          refine ⟨170106625216743402921857101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 907235334489298148916571205 170106625216743402921857101)
          ·
            refine ⟨63789984456278776095696413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 170106625216743402921857101 63789984456278776095696413)
            ·
              refine ⟨23921244171104541035886155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 63789984456278776095696413 23921244171104541035886155)
              ·
                refine ⟨35881866256656811553829233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23921244171104541035886155 35881866256656811553829233)
                ·
                  refine ⟨26911399692492608665371925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35881866256656811553829233 26911399692492608665371925)
                  ·
                    refine ⟨1261471860585591031189309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26911399692492608665371925 1261471860585591031189309)
                    ·
                      rfl

theorem cell23_7370123_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 3, 1, 2, 6].length) (baseStart_7370123 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7370123 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7370123 prefixEnd_7370123 := by exact prefixLift 7370123
  have htrace : WordTrace (prefixWord ++ tailWord_7370123) baseStart_7370123 baseEnd_7370123 := by
    simpa [prefixWord, tailWord_7370123, baseEnd_7370123] using wordTrace_append hprefix tailTrace_7370123
  have hstable : (prefixWord ++ tailWord_7370123).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7370123).length < 2 ^ (prefixWord ++ tailWord_7370123).sum := by decide
  have hdescent : baseEnd_7370123 < baseStart_7370123 := by decide
  rcases family_descends (prefixWord ++ tailWord_7370123) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7370133 : List Nat := [1, 3, 2, 1, 1, 2, 2, 1, 4, 1, 5]
def baseStart_7370133 : Nat := 118140960795 + 7370133 * 2 ^ 59
def prefixEnd_7370133 : Nat := 4983230072969 + 3 ^ 40 * 7370133 * 2
def baseEnd_7370133 : Nat := 3784420716563318054442881

theorem tailTrace_7370133 : CollatzResearch.WordTrace tailWord_7370133 prefixEnd_7370133 3784420716563318054442881 := by
  unfold tailWord_7370133
  simp only [CollatzResearch.WordTrace]
  refine ⟨268810834208274334349811053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179207222805516222899874035 268810834208274334349811053)
  ·
    refine ⟨100804062828102875381179145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 268810834208274334349811053 100804062828102875381179145)
    ·
      refine ⟨75603047121077156535884359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 100804062828102875381179145 75603047121077156535884359)
      ·
        refine ⟨113404570681615734803826539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75603047121077156535884359 113404570681615734803826539)
        ·
          refine ⟨170106856022423602205739809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 113404570681615734803826539 170106856022423602205739809)
          ·
            refine ⟨127580142016817701654304857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 170106856022423602205739809 127580142016817701654304857)
            ·
              refine ⟨95685106512613276240728643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 127580142016817701654304857 95685106512613276240728643)
              ·
                refine ⟨143527659768919914361092965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 95685106512613276240728643 143527659768919914361092965)
                ·
                  refine ⟨26911436206672483942704931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 143527659768919914361092965 26911436206672483942704931)
                  ·
                    refine ⟨40367154310008725914057397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 26911436206672483942704931 40367154310008725914057397)
                    ·
                      refine ⟨3784420716563318054442881, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 40367154310008725914057397 3784420716563318054442881)
                      ·
                        rfl

theorem cell23_7370133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 2, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 2, 1, 4, 1, 5].length) (baseStart_7370133 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7370133 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7370133 prefixEnd_7370133 := by exact prefixLift 7370133
  have htrace : WordTrace (prefixWord ++ tailWord_7370133) baseStart_7370133 baseEnd_7370133 := by
    simpa [prefixWord, tailWord_7370133, baseEnd_7370133] using wordTrace_append hprefix tailTrace_7370133
  have hstable : (prefixWord ++ tailWord_7370133).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7370133).length < 2 ^ (prefixWord ++ tailWord_7370133).sum := by decide
  have hdescent : baseEnd_7370133 < baseStart_7370133 := by decide
  rcases family_descends (prefixWord ++ tailWord_7370133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7370147 : List Nat := [1, 1, 1, 4, 1, 3, 2, 2, 4, 2, 2]
def baseStart_7370147 : Nat := 118140960795 + 7370147 * 2 ^ 59
def prefixEnd_7370147 : Nat := 4983230072969 + 3 ^ 40 * 7370147 * 2
def baseEnd_7370147 : Nat := 3784427905292480999667817

theorem tailTrace_7370147 : CollatzResearch.WordTrace tailWord_7370147 prefixEnd_7370147 3784427905292480999667817 := by
  unfold tailWord_7370147
  simp only [CollatzResearch.WordTrace]
  refine ⟨268811344830223614740820695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179207563220149076493880463 268811344830223614740820695)
  ·
    refine ⟨403217017245335422111231043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 268811344830223614740820695 403217017245335422111231043)
    ·
      refine ⟨604825525868003133166846565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 403217017245335422111231043 604825525868003133166846565)
      ·
        refine ⟨113404786100250587468783731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 604825525868003133166846565 113404786100250587468783731)
        ·
          refine ⟨170107179150375881203175597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 113404786100250587468783731 170107179150375881203175597)
          ·
            refine ⟨63790192181390955451190849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 170107179150375881203175597 63790192181390955451190849)
            ·
              refine ⟨47842644136043216588393137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 63790192181390955451190849 47842644136043216588393137)
              ·
                refine ⟨35881983102032412441294853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47842644136043216588393137 35881983102032412441294853)
                ·
                  refine ⟨6727871831631077332742785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 35881983102032412441294853 6727871831631077332742785)
                  ·
                    refine ⟨5045903873723307999557089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6727871831631077332742785 5045903873723307999557089)
                    ·
                      refine ⟨3784427905292480999667817, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5045903873723307999557089 3784427905292480999667817)
                      ·
                        rfl

theorem cell23_7370147_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 2, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 2, 2, 4, 2, 2].length) (baseStart_7370147 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7370147 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7370147 prefixEnd_7370147 := by exact prefixLift 7370147
  have htrace : WordTrace (prefixWord ++ tailWord_7370147) baseStart_7370147 baseEnd_7370147 := by
    simpa [prefixWord, tailWord_7370147, baseEnd_7370147] using wordTrace_append hprefix tailTrace_7370147
  have hstable : (prefixWord ++ tailWord_7370147).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7370147).length < 2 ^ (prefixWord ++ tailWord_7370147).sum := by decide
  have hdescent : baseEnd_7370147 < baseStart_7370147 := by decide
  rcases family_descends (prefixWord ++ tailWord_7370147) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7370183 : List Nat := [1, 1, 4, 1, 1, 3, 1, 1, 3, 7]
def baseStart_7370183 : Nat := 118140960795 + 7370183 * 2 ^ 59
def prefixEnd_7370183 : Nat := 4983230072969 + 3 ^ 40 * 7370183 * 2
def baseEnd_7370183 : Nat := 1261482130198680952939217

theorem tailTrace_7370183 : CollatzResearch.WordTrace tailWord_7370183 prefixEnd_7370183 1261482130198680952939217 := by
  unfold tailWord_7370183
  simp only [CollatzResearch.WordTrace]
  refine ⟨268812657858093192889131203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179208438572062128592754135 268812657858093192889131203)
  ·
    refine ⟨403218986787139789333696805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 268812657858093192889131203 403218986787139789333696805)
    ·
      refine ⟨75603560022588710500068151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 403218986787139789333696805 75603560022588710500068151)
      ·
        refine ⟨113405340033883065750102227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75603560022588710500068151 113405340033883065750102227)
        ·
          refine ⟨170108010050824598625153341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 113405340033883065750102227 170108010050824598625153341)
          ·
            refine ⟨63790503769059224484432503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 170108010050824598625153341 63790503769059224484432503)
            ·
              refine ⟨95685755653588836726648755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63790503769059224484432503 95685755653588836726648755)
              ·
                refine ⟨143528633480383255089973133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 95685755653588836726648755 143528633480383255089973133)
                ·
                  refine ⟨53823237555143720658739925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 143528633480383255089973133 53823237555143720658739925)
                  ·
                    refine ⟨1261482130198680952939217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 53823237555143720658739925 1261482130198680952939217)
                    ·
                      rfl

theorem cell23_7370183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 1, 1, 3, 7].length) (baseStart_7370183 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7370183 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7370183 prefixEnd_7370183 := by exact prefixLift 7370183
  have htrace : WordTrace (prefixWord ++ tailWord_7370183) baseStart_7370183 baseEnd_7370183 := by
    simpa [prefixWord, tailWord_7370183, baseEnd_7370183] using wordTrace_append hprefix tailTrace_7370183
  have hstable : (prefixWord ++ tailWord_7370183).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7370183).length < 2 ^ (prefixWord ++ tailWord_7370183).sum := by decide
  have hdescent : baseEnd_7370183 < baseStart_7370183 := by decide
  rcases family_descends (prefixWord ++ tailWord_7370183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7370193 : List Nat := [1, 2, 2, 1, 2, 1, 1, 1, 5, 2, 5]
def baseStart_7370193 : Nat := 118140960795 + 7370193 * 2 ^ 59
def prefixEnd_7370193 : Nat := 4983230072969 + 3 ^ 40 * 7370193 * 2
def baseEnd_7370193 : Nat := 3784451525402587819692605

theorem tailTrace_7370193 : CollatzResearch.WordTrace tailWord_7370193 prefixEnd_7370193 3784451525402587819692605 := by
  unfold tailWord_7370193
  simp only [CollatzResearch.WordTrace]
  refine ⟨268813022588056964596995233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179208681725371309731330155 268813022588056964596995233)
  ·
    refine ⟨201609766941042723447746425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 268813022588056964596995233 201609766941042723447746425)
    ·
      refine ⟨151207325205782042585809819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 201609766941042723447746425 151207325205782042585809819)
      ·
        refine ⟨226810987808673063878714729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 151207325205782042585809819 226810987808673063878714729)
        ·
          refine ⟨170108240856504797909036047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 226810987808673063878714729 170108240856504797909036047)
          ·
            refine ⟨255162361284757196863554071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 170108240856504797909036047 255162361284757196863554071)
            ·
              refine ⟨382743541927135795295331107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 255162361284757196863554071 382743541927135795295331107)
              ·
                refine ⟨574115312890703692942996661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 382743541927135795295331107 574115312890703692942996661)
                ·
                  refine ⟨53823310583503471213405937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 574115312890703692942996661 53823310583503471213405937)
                  ·
                    refine ⟨40367482937627603410054453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 53823310583503471213405937 40367482937627603410054453)
                    ·
                      refine ⟨3784451525402587819692605, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 40367482937627603410054453 3784451525402587819692605)
                      ·
                        rfl

theorem cell23_7370193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 1, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 1, 1, 5, 2, 5].length) (baseStart_7370193 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7370193 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7370193 prefixEnd_7370193 := by exact prefixLift 7370193
  have htrace : WordTrace (prefixWord ++ tailWord_7370193) baseStart_7370193 baseEnd_7370193 := by
    simpa [prefixWord, tailWord_7370193, baseEnd_7370193] using wordTrace_append hprefix tailTrace_7370193
  have hstable : (prefixWord ++ tailWord_7370193).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7370193).length < 2 ^ (prefixWord ++ tailWord_7370193).sum := by decide
  have hdescent : baseEnd_7370193 < baseStart_7370193 := by decide
  rcases family_descends (prefixWord ++ tailWord_7370193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7370221 : List Nat := [1, 5, 1, 3, 2, 1, 3, 2, 5]
def baseStart_7370221 : Nat := 118140960795 + 7370221 * 2 ^ 59
def prefixEnd_7370221 : Nat := 4983230072969 + 3 ^ 40 * 7370221 * 2
def baseEnd_7370221 : Nat := 420496211428990412238053

theorem tailTrace_7370221 : CollatzResearch.WordTrace tailWord_7370221 prefixEnd_7370221 420496211428990412238053 := by
  unfold tailWord_7370221
  simp only [CollatzResearch.WordTrace]
  refine ⟨268814043831955525379014517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179209362554637016919343011 268814043831955525379014517)
  ·
    refine ⟨25201316609245830504282611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 268814043831955525379014517 25201316609245830504282611)
    ·
      refine ⟨37801974913868745756423917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25201316609245830504282611 37801974913868745756423917)
      ·
        refine ⟨14175740592700779658658969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37801974913868745756423917 14175740592700779658658969)
        ·
          refine ⟨10631805444525584743994227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14175740592700779658658969 10631805444525584743994227)
          ·
            refine ⟨15947708166788377115991341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10631805444525584743994227 15947708166788377115991341)
            ·
              refine ⟨5980390562545641418496753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15947708166788377115991341 5980390562545641418496753)
              ·
                refine ⟨4485292921909231063872565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5980390562545641418496753 4485292921909231063872565)
                ·
                  refine ⟨420496211428990412238053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4485292921909231063872565 420496211428990412238053)
                  ·
                    rfl

theorem cell23_7370221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 2, 1, 3, 2, 5].length) (baseStart_7370221 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7370221 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7370221 prefixEnd_7370221 := by exact prefixLift 7370221
  have htrace : WordTrace (prefixWord ++ tailWord_7370221) baseStart_7370221 baseEnd_7370221 := by
    simpa [prefixWord, tailWord_7370221, baseEnd_7370221] using wordTrace_append hprefix tailTrace_7370221
  have hstable : (prefixWord ++ tailWord_7370221).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7370221).length < 2 ^ (prefixWord ++ tailWord_7370221).sum := by decide
  have hdescent : baseEnd_7370221 < baseStart_7370221 := by decide
  rcases family_descends (prefixWord ++ tailWord_7370221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7370243 : List Nat := [1, 1, 1, 3, 2, 1, 2, 2, 10]
def baseStart_7370243 : Nat := 118140960795 + 7370243 * 2 ^ 59
def prefixEnd_7370243 : Nat := 4983230072969 + 3 ^ 40 * 7370243 * 2
def baseEnd_7370243 : Nat := 420497466603923624896375

theorem tailTrace_7370243 : CollatzResearch.WordTrace tailWord_7370243 prefixEnd_7370243 420497466603923624896375 := by
  unfold tailWord_7370243
  simp only [CollatzResearch.WordTrace]
  refine ⟨268814846237875823136315383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179209897491917215424210255 268814846237875823136315383)
  ·
    refine ⟨403222269356813734704473075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 268814846237875823136315383 403222269356813734704473075)
    ·
      refine ⟨604833404035220602056709613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 403222269356813734704473075 604833404035220602056709613)
      ·
        refine ⟨226812526513207725771266105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 604833404035220602056709613 226812526513207725771266105)
        ·
          refine ⟨170109394884905794328449579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 226812526513207725771266105 170109394884905794328449579)
          ·
            refine ⟨255164092327358691492674369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 170109394884905794328449579 255164092327358691492674369)
            ·
              refine ⟨191373069245519018619505777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 255164092327358691492674369 191373069245519018619505777)
              ·
                refine ⟨143529801934139263964629333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 191373069245519018619505777 143529801934139263964629333)
                ·
                  refine ⟨420497466603923624896375, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 143529801934139263964629333 420497466603923624896375)
                  ·
                    rfl

theorem cell23_7370243_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 2, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 2, 2, 10].length) (baseStart_7370243 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7370243 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7370243 prefixEnd_7370243 := by exact prefixLift 7370243
  have htrace : WordTrace (prefixWord ++ tailWord_7370243) baseStart_7370243 baseEnd_7370243 := by
    simpa [prefixWord, tailWord_7370243, baseEnd_7370243] using wordTrace_append hprefix tailTrace_7370243
  have hstable : (prefixWord ++ tailWord_7370243).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7370243).length < 2 ^ (prefixWord ++ tailWord_7370243).sum := by decide
  have hdescent : baseEnd_7370243 < baseStart_7370243 := by decide
  rcases family_descends (prefixWord ++ tailWord_7370243) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7370254 : List Nat := [4, 1, 1, 2, 4, 1, 2, 1, 2, 1, 4]
def baseStart_7370254 : Nat := 118140960795 + 7370254 * 2 ^ 59
def prefixEnd_7370254 : Nat := 4983230072969 + 3 ^ 40 * 7370254 * 2
def baseEnd_7370254 : Nat := 3784482847722512081029825

theorem tailTrace_7370254 : CollatzResearch.WordTrace tailWord_7370254 prefixEnd_7370254 3784482847722512081029825 := by
  unfold tailWord_7370254
  simp only [CollatzResearch.WordTrace]
  refine ⟨33601905930104496501870727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 179210164960557314676643877 33601905930104496501870727)
  ·
    refine ⟨50402858895156744752806091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33601905930104496501870727 50402858895156744752806091)
    ·
      refine ⟨75604288342735117129209137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50402858895156744752806091 75604288342735117129209137)
      ·
        refine ⟨56703216257051337846906853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 75604288342735117129209137 56703216257051337846906853)
        ·
          refine ⟨10631853048197125846295035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 56703216257051337846906853 10631853048197125846295035)
          ·
            refine ⟨15947779572295688769442553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10631853048197125846295035 15947779572295688769442553)
            ·
              refine ⟨11960834679221766577081915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15947779572295688769442553 11960834679221766577081915)
              ·
                refine ⟨17941252018832649865622873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11960834679221766577081915 17941252018832649865622873)
                ·
                  refine ⟨13455939014124487399217155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17941252018832649865622873 13455939014124487399217155)
                  ·
                    refine ⟨20183908521186731098825733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13455939014124487399217155 20183908521186731098825733)
                    ·
                      refine ⟨3784482847722512081029825, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20183908521186731098825733 3784482847722512081029825)
                      ·
                        rfl

theorem cell23_7370254_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 4, 1, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 4, 1, 2, 1, 2, 1, 4].length) (baseStart_7370254 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7370254 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7370254 prefixEnd_7370254 := by exact prefixLift 7370254
  have htrace : WordTrace (prefixWord ++ tailWord_7370254) baseStart_7370254 baseEnd_7370254 := by
    simpa [prefixWord, tailWord_7370254, baseEnd_7370254] using wordTrace_append hprefix tailTrace_7370254
  have hstable : (prefixWord ++ tailWord_7370254).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7370254).length < 2 ^ (prefixWord ++ tailWord_7370254).sum := by decide
  have hdescent : baseEnd_7370254 < baseStart_7370254 := by decide
  rcases family_descends (prefixWord ++ tailWord_7370254) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7370257 : List Nat := [1, 2, 2, 1, 1, 2, 6, 1, 2, 2, 3]
def baseStart_7370257 : Nat := 118140960795 + 7370257 * 2 ^ 59
def prefixEnd_7370257 : Nat := 4983230072969 + 3 ^ 40 * 7370257 * 2
def baseEnd_7370257 : Nat := 3784484388164475569292311

theorem tailTrace_7370257 : CollatzResearch.WordTrace tailWord_7370257 prefixEnd_7370257 3784484388164475569292311 := by
  unfold tailWord_7370257
  simp only [CollatzResearch.WordTrace]
  refine ⟨268815356859825103527325025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179210237906550069018216683 268815356859825103527325025)
  ·
    refine ⟨201611517644868827645493769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 268815356859825103527325025 201611517644868827645493769)
    ·
      refine ⟨151208638233651620734120327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 201611517644868827645493769 151208638233651620734120327)
      ·
        refine ⟨226812957350477431101180491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 151208638233651620734120327 226812957350477431101180491)
        ·
          refine ⟨340219436025716146651770737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 226812957350477431101180491 340219436025716146651770737)
          ·
            refine ⟨255164577019287109988828053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 340219436025716146651770737 255164577019287109988828053)
            ·
              refine ⟨11960839547779083280726315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 255164577019287109988828053 11960839547779083280726315)
              ·
                refine ⟨17941259321668624921089473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11960839547779083280726315 17941259321668624921089473)
                ·
                  refine ⟨13455944491251468690817105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17941259321668624921089473 13455944491251468690817105)
                  ·
                    refine ⟨10091958368438601518112829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13455944491251468690817105 10091958368438601518112829)
                    ·
                      refine ⟨3784484388164475569292311, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10091958368438601518112829 3784484388164475569292311)
                      ·
                        rfl

theorem cell23_7370257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 2, 3].length) (baseStart_7370257 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7370257 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7370257 prefixEnd_7370257 := by exact prefixLift 7370257
  have htrace : WordTrace (prefixWord ++ tailWord_7370257) baseStart_7370257 baseEnd_7370257 := by
    simpa [prefixWord, tailWord_7370257, baseEnd_7370257] using wordTrace_append hprefix tailTrace_7370257
  have hstable : (prefixWord ++ tailWord_7370257).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7370257).length < 2 ^ (prefixWord ++ tailWord_7370257).sum := by decide
  have hdescent : baseEnd_7370257 < baseStart_7370257 := by decide
  rcases family_descends (prefixWord ++ tailWord_7370257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7370320 : List Nat := [2, 1, 1, 1, 1, 3, 3, 4, 1, 6]
def baseStart_7370320 : Nat := 118140960795 + 7370320 * 2 ^ 59
def prefixEnd_7370320 : Nat := 4983230072969 + 3 ^ 40 * 7370320 * 2
def baseEnd_7370320 : Nat := 1261505579148569607601507

theorem tailTrace_7370320 : CollatzResearch.WordTrace tailWord_7370320 prefixEnd_7370320 1261505579148569607601507 := by
  unfold tailWord_7370320
  simp only [CollatzResearch.WordTrace]
  refine ⟨134408827329298432643434207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 179211769772397910191245609 134408827329298432643434207)
  ·
    refine ⟨201613240993947648965151311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134408827329298432643434207 201613240993947648965151311)
    ·
      refine ⟨302419861490921473447726967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 201613240993947648965151311 302419861490921473447726967)
      ·
        refine ⟨453629792236382210171590451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 302419861490921473447726967 453629792236382210171590451)
        ·
          refine ⟨680444688354573315257385677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 453629792236382210171590451 680444688354573315257385677)
          ·
            refine ⟨255166758132964993221519629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 680444688354573315257385677 255166758132964993221519629)
            ·
              refine ⟨95687534299861872458069861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 255166758132964993221519629 95687534299861872458069861)
              ·
                refine ⟨17941412681224101085888099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 95687534299861872458069861 17941412681224101085888099)
                ·
                  refine ⟨26912119021836151628832149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17941412681224101085888099 26912119021836151628832149)
                  ·
                    refine ⟨1261505579148569607601507, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26912119021836151628832149 1261505579148569607601507)
                    ·
                      rfl

theorem cell23_7370320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 3, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 3, 4, 1, 6].length) (baseStart_7370320 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7370320 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7370320 prefixEnd_7370320 := by exact prefixLift 7370320
  have htrace : WordTrace (prefixWord ++ tailWord_7370320) baseStart_7370320 baseEnd_7370320 := by
    simpa [prefixWord, tailWord_7370320, baseEnd_7370320] using wordTrace_append hprefix tailTrace_7370320
  have hstable : (prefixWord ++ tailWord_7370320).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7370320).length < 2 ^ (prefixWord ++ tailWord_7370320).sum := by decide
  have hdescent : baseEnd_7370320 < baseStart_7370320 := by decide
  rcases family_descends (prefixWord ++ tailWord_7370320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7370321 : List Nat := [1, 2, 2, 1, 3, 2, 4, 3, 1, 1, 3]
def baseStart_7370321 : Nat := 118140960795 + 7370321 * 2 ^ 59
def prefixEnd_7370321 : Nat := 4983230072969 + 3 ^ 40 * 7370321 * 2
def baseEnd_7370321 : Nat := 3784517250926363318892017

theorem tailTrace_7370321 : CollatzResearch.WordTrace tailWord_7370321 prefixEnd_7370321 3784517250926363318892017 := by
  unfold tailWord_7370321
  simp only [CollatzResearch.WordTrace]
  refine ⟨268817691131593242457654817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179211794087728828305103211 268817691131593242457654817)
  ·
    refine ⟨201613268348694931843241113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 268817691131593242457654817 201613268348694931843241113)
    ·
      refine ⟨151209951261521198882430835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 201613268348694931843241113 151209951261521198882430835)
      ·
        refine ⟨226814926892281798323646253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 151209951261521198882430835 226814926892281798323646253)
        ·
          refine ⟨85055597584605674371367345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 226814926892281798323646253 85055597584605674371367345)
          ·
            refine ⟨63791698188454255778525509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 85055597584605674371367345 63791698188454255778525509)
            ·
              refine ⟨11960943410335172958473533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 63791698188454255778525509 11960943410335172958473533)
              ·
                refine ⟨4485353778875689859427575, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11960943410335172958473533 4485353778875689859427575)
                ·
                  refine ⟨6728030668313534789141363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4485353778875689859427575 6728030668313534789141363)
                  ·
                    refine ⟨10092046002470302183712045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6728030668313534789141363 10092046002470302183712045)
                    ·
                      refine ⟨3784517250926363318892017, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10092046002470302183712045 3784517250926363318892017)
                      ·
                        rfl

theorem cell23_7370321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 4, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 4, 3, 1, 1, 3].length) (baseStart_7370321 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7370321 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7370321 prefixEnd_7370321 := by exact prefixLift 7370321
  have htrace : WordTrace (prefixWord ++ tailWord_7370321) baseStart_7370321 baseEnd_7370321 := by
    simpa [prefixWord, tailWord_7370321, baseEnd_7370321] using wordTrace_append hprefix tailTrace_7370321
  have hstable : (prefixWord ++ tailWord_7370321).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7370321).length < 2 ^ (prefixWord ++ tailWord_7370321).sum := by decide
  have hdescent : baseEnd_7370321 < baseStart_7370321 := by decide
  rcases family_descends (prefixWord ++ tailWord_7370321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7370330 : List Nat := [3, 1, 1, 2, 1, 1, 1, 2, 5, 1, 5]
def baseStart_7370330 : Nat := 118140960795 + 7370330 * 2 ^ 59
def prefixEnd_7370330 : Nat := 4983230072969 + 3 ^ 40 * 7370330 * 2
def baseEnd_7370330 : Nat := 3784521872252253783679475

theorem tailTrace_7370330 : CollatzResearch.WordTrace tailWord_7370330 prefixEnd_7370330 3784521872252253783679475 := by
  unfold tailWord_7370330
  simp only [CollatzResearch.WordTrace]
  refine ⟨67204504847140159248683111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 179212012925707091329821629 67204504847140159248683111)
  ·
    refine ⟨100806757270710238873024667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67204504847140159248683111 100806757270710238873024667)
    ·
      refine ⟨151210135906065358309537001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100806757270710238873024667 151210135906065358309537001)
      ·
        refine ⟨113407601929549018732152751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 151210135906065358309537001 113407601929549018732152751)
        ·
          refine ⟨170111402894323528098229127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 113407601929549018732152751 170111402894323528098229127)
          ·
            refine ⟨255167104341485292147343691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 170111402894323528098229127 255167104341485292147343691)
            ·
              refine ⟨382750656512227938221015537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 255167104341485292147343691 382750656512227938221015537)
              ·
                refine ⟨287062992384170953665761653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 382750656512227938221015537 287062992384170953665761653)
                ·
                  refine ⟨26912155536016026906165155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 287062992384170953665761653 26912155536016026906165155)
                  ·
                    refine ⟨40368233304024040359247733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 26912155536016026906165155 40368233304024040359247733)
                    ·
                      refine ⟨3784521872252253783679475, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 40368233304024040359247733 3784521872252253783679475)
                      ·
                        rfl

theorem cell23_7370330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 1, 2, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 1, 2, 5, 1, 5].length) (baseStart_7370330 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7370330 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7370330 prefixEnd_7370330 := by exact prefixLift 7370330
  have htrace : WordTrace (prefixWord ++ tailWord_7370330) baseStart_7370330 baseEnd_7370330 := by
    simpa [prefixWord, tailWord_7370330, baseEnd_7370330] using wordTrace_append hprefix tailTrace_7370330
  have hstable : (prefixWord ++ tailWord_7370330).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7370330).length < 2 ^ (prefixWord ++ tailWord_7370330).sum := by decide
  have hdescent : baseEnd_7370330 < baseStart_7370330 := by decide
  rcases family_descends (prefixWord ++ tailWord_7370330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7370337 : List Nat := [1, 2, 3, 1, 1, 3, 3, 1, 4, 4]
def baseStart_7370337 : Nat := 118140960795 + 7370337 * 2 ^ 59
def prefixEnd_7370337 : Nat := 4983230072969 + 3 ^ 40 * 7370337 * 2
def baseEnd_7370337 : Nat := 1261508488872278418763981

theorem tailTrace_7370337 : CollatzResearch.WordTrace tailWord_7370337 prefixEnd_7370337 1261508488872278418763981 := by
  unfold tailWord_7370337
  simp only [CollatzResearch.WordTrace]
  refine ⟨268818274699535277190237265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179212183133023518126824843 268818274699535277190237265)
  ·
    refine ⟨201613706024651457892677949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 268818274699535277190237265 201613706024651457892677949)
    ·
      refine ⟨75605139759244296709754231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 201613706024651457892677949 75605139759244296709754231)
      ·
        refine ⟨113407709638866445064631347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75605139759244296709754231 113407709638866445064631347)
        ·
          refine ⟨170111564458299667596947021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 113407709638866445064631347 170111564458299667596947021)
          ·
            refine ⟨63791836671862375348855133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 170111564458299667596947021 63791836671862375348855133)
            ·
              refine ⟨23921938751948390755820675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 63791836671862375348855133 23921938751948390755820675)
              ·
                refine ⟨35882908127922586133731013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23921938751948390755820675 35882908127922586133731013)
                ·
                  refine ⟨6728045273985484900074565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 35882908127922586133731013 6728045273985484900074565)
                  ·
                    refine ⟨1261508488872278418763981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6728045273985484900074565 1261508488872278418763981)
                    ·
                      rfl

theorem cell23_7370337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 3, 1, 4, 4].length) (baseStart_7370337 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7370337 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7370337 prefixEnd_7370337 := by exact prefixLift 7370337
  have htrace : WordTrace (prefixWord ++ tailWord_7370337) baseStart_7370337 baseEnd_7370337 := by
    simpa [prefixWord, tailWord_7370337, baseEnd_7370337] using wordTrace_append hprefix tailTrace_7370337
  have hstable : (prefixWord ++ tailWord_7370337).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7370337).length < 2 ^ (prefixWord ++ tailWord_7370337).sum := by decide
  have hdescent : baseEnd_7370337 < baseStart_7370337 := by decide
  rcases family_descends (prefixWord ++ tailWord_7370337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7370354 : List Nat := [3, 2, 1, 2, 3, 3, 1, 1, 1, 6]
def baseStart_7370354 : Nat := 118140960795 + 7370354 * 2 ^ 59
def prefixEnd_7370354 : Nat := 4983230072969 + 3 ^ 40 * 7370354 * 2
def baseEnd_7370354 : Nat := 1261511398595987229926455

theorem tailTrace_7370354 : CollatzResearch.WordTrace tailWord_7370354 prefixEnd_7370354 1261511398595987229926455 := by
  unfold tailWord_7370354
  simp only [CollatzResearch.WordTrace]
  refine ⟨67204723685118422273401529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 179212596493649126062404077 67204723685118422273401529)
  ·
    refine ⟨50403542763838816705051147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67204723685118422273401529 50403542763838816705051147)
    ·
      refine ⟨75605314145758225057576721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50403542763838816705051147 75605314145758225057576721)
      ·
        refine ⟨56703985609318668793182541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 75605314145758225057576721 56703985609318668793182541)
        ·
          refine ⟨21263994603494500797443453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 56703985609318668793182541 21263994603494500797443453)
          ·
            refine ⟨7973997976310437799041295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21263994603494500797443453 7973997976310437799041295)
            ·
              refine ⟨11960996964465656698561943, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7973997976310437799041295 11960996964465656698561943)
              ·
                refine ⟨17941495446698485047842915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11960996964465656698561943 17941495446698485047842915)
                ·
                  refine ⟨26912243170047727571764373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17941495446698485047842915 26912243170047727571764373)
                  ·
                    refine ⟨1261511398595987229926455, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26912243170047727571764373 1261511398595987229926455)
                    ·
                      rfl

theorem cell23_7370354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 3, 1, 1, 1, 6].length) (baseStart_7370354 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7370354 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7370354 prefixEnd_7370354 := by exact prefixLift 7370354
  have htrace : WordTrace (prefixWord ++ tailWord_7370354) baseStart_7370354 baseEnd_7370354 := by
    simpa [prefixWord, tailWord_7370354, baseEnd_7370354] using wordTrace_append hprefix tailTrace_7370354
  have hstable : (prefixWord ++ tailWord_7370354).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7370354).length < 2 ^ (prefixWord ++ tailWord_7370354).sum := by decide
  have hdescent : baseEnd_7370354 < baseStart_7370354 := by decide
  rcases family_descends (prefixWord ++ tailWord_7370354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7370377 : List Nat := [1, 2, 1, 1, 4, 1, 2, 4, 1, 3, 3]
def baseStart_7370377 : Nat := 118140960795 + 7370377 * 2 ^ 59
def prefixEnd_7370377 : Nat := 4983230072969 + 3 ^ 40 * 7370377 * 2
def baseEnd_7370377 : Nat := 3784546005843015099791759

theorem tailTrace_7370377 : CollatzResearch.WordTrace tailWord_7370377 prefixEnd_7370377 3784546005843015099791759 := by
  unfold tailWord_7370377
  simp only [CollatzResearch.WordTrace]
  refine ⟨268819733619390364021693385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179213155746260242681128923 268819733619390364021693385)
  ·
    refine ⟨201614800214542773016270039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 268819733619390364021693385 201614800214542773016270039)
    ·
      refine ⟨302422200321814159524405059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 201614800214542773016270039 302422200321814159524405059)
      ·
        refine ⟨453633300482721239286607589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 302422200321814159524405059 453633300482721239286607589)
        ·
          refine ⟨85056243840510232366238923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 453633300482721239286607589 85056243840510232366238923)
          ·
            refine ⟨127584365760765348549358385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85056243840510232366238923 127584365760765348549358385)
            ·
              refine ⟨95688274320574011412018789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 127584365760765348549358385 95688274320574011412018789)
              ·
                refine ⟨17941551435107627139753523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 95688274320574011412018789 17941551435107627139753523)
                ·
                  refine ⟨26912327152661440709630285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17941551435107627139753523 26912327152661440709630285)
                  ·
                    refine ⟨10092122682248040266111357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 26912327152661440709630285 10092122682248040266111357)
                    ·
                      refine ⟨3784546005843015099791759, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10092122682248040266111357 3784546005843015099791759)
                      ·
                        rfl

theorem cell23_7370377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 2, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 2, 4, 1, 3, 3].length) (baseStart_7370377 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7370377 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7370377 prefixEnd_7370377 := by exact prefixLift 7370377
  have htrace : WordTrace (prefixWord ++ tailWord_7370377) baseStart_7370377 baseEnd_7370377 := by
    simpa [prefixWord, tailWord_7370377, baseEnd_7370377] using wordTrace_append hprefix tailTrace_7370377
  have hstable : (prefixWord ++ tailWord_7370377).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7370377).length < 2 ^ (prefixWord ++ tailWord_7370377).sum := by decide
  have hdescent : baseEnd_7370377 < baseStart_7370377 := by decide
  rcases family_descends (prefixWord ++ tailWord_7370377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7370445 : List Nat := [1, 6, 2, 1, 1, 2, 2, 2, 2, 1, 3]
def baseStart_7370445 : Nat := 118140960795 + 7370445 * 2 ^ 59
def prefixEnd_7370445 : Nat := 4983230072969 + 3 ^ 40 * 7370445 * 2
def baseEnd_7370445 : Nat := 3784580922527520833741447

theorem tailTrace_7370445 : CollatzResearch.WordTrace tailWord_7370445 prefixEnd_7370445 3784580922527520833741447 := by
  unfold tailWord_7370445
  simp only [CollatzResearch.WordTrace]
  refine ⟨268822213783144011635168789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179214809188762674423445859 268822213783144011635168789)
  ·
    refine ⟨12601041271084875545398537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 268822213783144011635168789 12601041271084875545398537)
    ·
      refine ⟨9450780953313656659048903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12601041271084875545398537 9450780953313656659048903)
      ·
        refine ⟨14176171429970484988573355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9450780953313656659048903 14176171429970484988573355)
        ·
          refine ⟨21264257144955727482860033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14176171429970484988573355 21264257144955727482860033)
          ·
            refine ⟨15948192858716795612145025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21264257144955727482860033 15948192858716795612145025)
            ·
              refine ⟨11961144644037596709108769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15948192858716795612145025 11961144644037596709108769)
              ·
                refine ⟨8970858483028197531831577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11961144644037596709108769 8970858483028197531831577)
                ·
                  refine ⟨6728143862271148148873683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8970858483028197531831577 6728143862271148148873683)
                  ·
                    refine ⟨10092215793406722223310525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6728143862271148148873683 10092215793406722223310525)
                    ·
                      refine ⟨3784580922527520833741447, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10092215793406722223310525 3784580922527520833741447)
                      ·
                        rfl

theorem cell23_7370445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 2, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 2, 2, 2, 2, 1, 3].length) (baseStart_7370445 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7370445 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7370445 prefixEnd_7370445 := by exact prefixLift 7370445
  have htrace : WordTrace (prefixWord ++ tailWord_7370445) baseStart_7370445 baseEnd_7370445 := by
    simpa [prefixWord, tailWord_7370445, baseEnd_7370445] using wordTrace_append hprefix tailTrace_7370445
  have hstable : (prefixWord ++ tailWord_7370445).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7370445).length < 2 ^ (prefixWord ++ tailWord_7370445).sum := by decide
  have hdescent : baseEnd_7370445 < baseStart_7370445 := by decide
  rcases family_descends (prefixWord ++ tailWord_7370445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7370461 : List Nat := [1, 4, 3, 3, 1, 1, 1, 1, 2, 6]
def baseStart_7370461 : Nat := 118140960795 + 7370461 * 2 ^ 59
def prefixEnd_7370461 : Nat := 4983230072969 + 3 ^ 40 * 7370461 * 2
def baseEnd_7370461 : Nat := 1261529712739330923713791

theorem tailTrace_7370461 : CollatzResearch.WordTrace tailWord_7370461 prefixEnd_7370461 1261529712739330923713791 := by
  unfold tailWord_7370461
  simp only [CollatzResearch.WordTrace]
  refine ⟨268822797351086046367751237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179215198234057364245167491 268822797351086046367751237)
  ·
    refine ⟨50404274503328633693953357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 268822797351086046367751237 50404274503328633693953357)
    ·
      refine ⟨18901602938748237635232509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 50404274503328633693953357 18901602938748237635232509)
      ·
        refine ⟨7088101102030589113212191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18901602938748237635232509 7088101102030589113212191)
        ·
          refine ⟨10632151653045883669818287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7088101102030589113212191 10632151653045883669818287)
          ·
            refine ⟨15948227479568825504727431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10632151653045883669818287 15948227479568825504727431)
            ·
              refine ⟨23922341219353238257091147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15948227479568825504727431 23922341219353238257091147)
              ·
                refine ⟨35883511829029857385636721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23922341219353238257091147 35883511829029857385636721)
                ·
                  refine ⟨26912633871772393039227541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35883511829029857385636721 26912633871772393039227541)
                  ·
                    refine ⟨1261529712739330923713791, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26912633871772393039227541 1261529712739330923713791)
                    ·
                      rfl

theorem cell23_7370461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 1, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 1, 1, 1, 1, 2, 6].length) (baseStart_7370461 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7370461 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7370461 prefixEnd_7370461 := by exact prefixLift 7370461
  have htrace : WordTrace (prefixWord ++ tailWord_7370461) baseStart_7370461 baseEnd_7370461 := by
    simpa [prefixWord, tailWord_7370461, baseEnd_7370461] using wordTrace_append hprefix tailTrace_7370461
  have hstable : (prefixWord ++ tailWord_7370461).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7370461).length < 2 ^ (prefixWord ++ tailWord_7370461).sum := by decide
  have hdescent : baseEnd_7370461 < baseStart_7370461 := by decide
  rcases family_descends (prefixWord ++ tailWord_7370461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7370497 : List Nat := [1, 2, 4, 1, 1, 1, 2, 1, 3, 2, 5]
def baseStart_7370497 : Nat := 118140960795 + 7370497 * 2 ^ 59
def prefixEnd_7370497 : Nat := 4983230072969 + 3 ^ 40 * 7370497 * 2
def baseEnd_7370497 : Nat := 3784607623521554630291207

theorem tailTrace_7370497 : CollatzResearch.WordTrace tailWord_7370497 prefixEnd_7370497 3784607623521554630291207 := by
  unfold tailWord_7370497
  simp only [CollatzResearch.WordTrace]
  refine ⟨268824110378955624516061745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179216073585970416344041163 268824110378955624516061745)
  ·
    refine ⟨201618082784216718387046309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 268824110378955624516061745 201618082784216718387046309)
    ·
      refine ⟨37803390522040634697571183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 201618082784216718387046309 37803390522040634697571183)
      ·
        refine ⟨56705085783060952046356775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37803390522040634697571183 56705085783060952046356775)
        ·
          refine ⟨85057628674591428069535163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56705085783060952046356775 85057628674591428069535163)
          ·
            refine ⟨127586443011887142104302745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85057628674591428069535163 127586443011887142104302745)
            ·
              refine ⟨95689832258915356578227059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 127586443011887142104302745 95689832258915356578227059)
              ·
                refine ⟨143534748388373034867340589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 95689832258915356578227059 143534748388373034867340589)
                ·
                  refine ⟨53825530645639888075252721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 143534748388373034867340589 53825530645639888075252721)
                  ·
                    refine ⟨40369147984229916056439541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 53825530645639888075252721 40369147984229916056439541)
                    ·
                      refine ⟨3784607623521554630291207, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 40369147984229916056439541 3784607623521554630291207)
                      ·
                        rfl

theorem cell23_7370497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 2, 1, 3, 2, 5].length) (baseStart_7370497 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7370497 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7370497 prefixEnd_7370497 := by exact prefixLift 7370497
  have htrace : WordTrace (prefixWord ++ tailWord_7370497) baseStart_7370497 baseEnd_7370497 := by
    simpa [prefixWord, tailWord_7370497, baseEnd_7370497] using wordTrace_append hprefix tailTrace_7370497
  have hstable : (prefixWord ++ tailWord_7370497).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7370497).length < 2 ^ (prefixWord ++ tailWord_7370497).sum := by decide
  have hdescent : baseEnd_7370497 < baseStart_7370497 := by decide
  rcases family_descends (prefixWord ++ tailWord_7370497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7370551 : List Nat := [1, 1, 3, 1, 2, 1, 2, 7, 1, 4]
def baseStart_7370551 : Nat := 118140960795 + 7370551 * 2 ^ 59
def prefixEnd_7370551 : Nat := 4983230072969 + 3 ^ 40 * 7370551 * 2
def baseEnd_7370551 : Nat := 1261545117158965806338653

theorem tailTrace_7370551 : CollatzResearch.WordTrace tailWord_7370551 prefixEnd_7370551 1261545117158965806338653 := by
  unfold tailWord_7370551
  simp only [CollatzResearch.WordTrace]
  refine ⟨268826079920759991738527507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179217386613839994492351671 268826079920759991738527507)
  ·
    refine ⟨403239119881139987607791261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 268826079920759991738527507 403239119881139987607791261)
    ·
      refine ⟨151214669955427495352921723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 403239119881139987607791261 151214669955427495352921723)
      ·
        refine ⟨226822004933141243029382585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 151214669955427495352921723 226822004933141243029382585)
        ·
          refine ⟨170116503699855932272036939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 226822004933141243029382585 170116503699855932272036939)
          ·
            refine ⟨255174755549783898408055409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 170116503699855932272036939 255174755549783898408055409)
            ·
              refine ⟨191381066662337923806041557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 255174755549783898408055409 191381066662337923806041557)
              ·
                refine ⟨4485493749898545089204099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 191381066662337923806041557 4485493749898545089204099)
                ·
                  refine ⟨6728240624847817633806149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4485493749898545089204099 6728240624847817633806149)
                  ·
                    refine ⟨1261545117158965806338653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6728240624847817633806149 1261545117158965806338653)
                    ·
                      rfl

theorem cell23_7370551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 2, 7, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 2, 7, 1, 4].length) (baseStart_7370551 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7370551 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7370551 prefixEnd_7370551 := by exact prefixLift 7370551
  have htrace : WordTrace (prefixWord ++ tailWord_7370551) baseStart_7370551 baseEnd_7370551 := by
    simpa [prefixWord, tailWord_7370551, baseEnd_7370551] using wordTrace_append hprefix tailTrace_7370551
  have hstable : (prefixWord ++ tailWord_7370551).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7370551).length < 2 ^ (prefixWord ++ tailWord_7370551).sum := by decide
  have hdescent : baseEnd_7370551 < baseStart_7370551 := by decide
  rcases family_descends (prefixWord ++ tailWord_7370551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7370567 : List Nat := [1, 1, 4, 1, 2, 1, 2, 1, 1, 1, 8]
def baseStart_7370567 : Nat := 118140960795 + 7370567 * 2 ^ 59
def prefixEnd_7370567 : Nat := 4983230072969 + 3 ^ 40 * 7370567 * 2
def baseEnd_7370567 : Nat := 3784643567167369356415885

theorem tailTrace_7370567 : CollatzResearch.WordTrace tailWord_7370567 prefixEnd_7370567 3784643567167369356415885 := by
  unfold tailWord_7370567
  simp only [CollatzResearch.WordTrace]
  refine ⟨268826663488702026471109955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179217775659134684314073303 268826663488702026471109955)
  ·
    refine ⟨403239995233053039706664933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 268826663488702026471109955 403239995233053039706664933)
    ·
      refine ⟨75607499106197444944999675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 403239995233053039706664933 75607499106197444944999675)
      ·
        refine ⟨113411248659296167417499513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75607499106197444944999675 113411248659296167417499513)
        ·
          refine ⟨85058436494472125563124635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 113411248659296167417499513 85058436494472125563124635)
          ·
            refine ⟨127587654741708188344686953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85058436494472125563124635 127587654741708188344686953)
            ·
              refine ⟨95690741056281141258515215, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 127587654741708188344686953 95690741056281141258515215)
              ·
                refine ⟨143536111584421711887772823, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 95690741056281141258515215 143536111584421711887772823)
                ·
                  refine ⟨215304167376632567831659235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 143536111584421711887772823 215304167376632567831659235)
                  ·
                    refine ⟨322956251064948851747488853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 215304167376632567831659235 322956251064948851747488853)
                    ·
                      refine ⟨3784643567167369356415885, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 322956251064948851747488853 3784643567167369356415885)
                      ·
                        rfl

theorem cell23_7370567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 2, 1, 1, 1, 8].length) (baseStart_7370567 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7370567 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7370567 prefixEnd_7370567 := by exact prefixLift 7370567
  have htrace : WordTrace (prefixWord ++ tailWord_7370567) baseStart_7370567 baseEnd_7370567 := by
    simpa [prefixWord, tailWord_7370567, baseEnd_7370567] using wordTrace_append hprefix tailTrace_7370567
  have hstable : (prefixWord ++ tailWord_7370567).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7370567).length < 2 ^ (prefixWord ++ tailWord_7370567).sum := by decide
  have hdescent : baseEnd_7370567 < baseStart_7370567 := by decide
  rcases family_descends (prefixWord ++ tailWord_7370567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7370581 : List Nat := [1, 3, 2, 2, 2, 2, 4, 1, 6]
def baseStart_7370581 : Nat := 118140960795 + 7370581 * 2 ^ 59
def prefixEnd_7370581 : Nat := 4983230072969 + 3 ^ 40 * 7370581 * 2
def baseEnd_7370581 : Nat := 420516750655170255737869

theorem tailTrace_7370581 : CollatzResearch.WordTrace tailWord_7370581 prefixEnd_7370581 420516750655170255737869 := by
  unfold tailWord_7370581
  simp only [CollatzResearch.WordTrace]
  refine ⟨268827174110651306862119597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179218116073767537908079731 268827174110651306862119597)
  ·
    refine ⟨100810190291494240073294849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 268827174110651306862119597 100810190291494240073294849)
    ·
      refine ⟨75607642718620680054971137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 100810190291494240073294849 75607642718620680054971137)
      ·
        refine ⟨56705732038965510041228353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 75607642718620680054971137 56705732038965510041228353)
        ·
          refine ⟨42529299029224132530921265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56705732038965510041228353 42529299029224132530921265)
          ·
            refine ⟨31896974271918099398190949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42529299029224132530921265 31896974271918099398190949)
            ·
              refine ⟨5980682675984643637160803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 31896974271918099398190949 5980682675984643637160803)
              ·
                refine ⟨8971024013976965455741205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5980682675984643637160803 8971024013976965455741205)
                ·
                  refine ⟨420516750655170255737869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8971024013976965455741205 420516750655170255737869)
                  ·
                    rfl

theorem cell23_7370581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 2, 4, 1, 6].length) (baseStart_7370581 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7370581 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7370581 prefixEnd_7370581 := by exact prefixLift 7370581
  have htrace : WordTrace (prefixWord ++ tailWord_7370581) baseStart_7370581 baseEnd_7370581 := by
    simpa [prefixWord, tailWord_7370581, baseEnd_7370581] using wordTrace_append hprefix tailTrace_7370581
  have hstable : (prefixWord ++ tailWord_7370581).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7370581).length < 2 ^ (prefixWord ++ tailWord_7370581).sum := by decide
  have hdescent : baseEnd_7370581 < baseStart_7370581 := by decide
  rcases family_descends (prefixWord ++ tailWord_7370581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7370608 : List Nat := [2, 1, 1, 1, 4, 1, 1, 7, 1, 1, 3]
def baseStart_7370608 : Nat := 118140960795 + 7370608 * 2 ^ 59
def prefixEnd_7370608 : Nat := 4983230072969 + 3 ^ 40 * 7370608 * 2
def baseEnd_7370608 : Nat := 3784664619874203696003197

theorem tailTrace_7370608 : CollatzResearch.WordTrace tailWord_7370608 prefixEnd_7370608 3784664619874203696003197 := by
  unfold tailWord_7370608
  simp only [CollatzResearch.WordTrace]
  refine ⟨134414079440776745236676239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 179218772587702326982234985 134414079440776745236676239)
  ·
    refine ⟨201621119161165117855014359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134414079440776745236676239 201621119161165117855014359)
    ·
      refine ⟨302431678741747676782521539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 201621119161165117855014359 302431678741747676782521539)
      ·
        refine ⟨453647518112621515173782309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 302431678741747676782521539 453647518112621515173782309)
        ·
          refine ⟨85058909646116534095084183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 453647518112621515173782309 85058909646116534095084183)
          ·
            refine ⟨127588364469174801142626275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85058909646116534095084183 127588364469174801142626275)
            ·
              refine ⟨191382546703762201713939413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 127588364469174801142626275 191382546703762201713939413)
              ·
                refine ⟨4485528438369426602670455, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 191382546703762201713939413 4485528438369426602670455)
                ·
                  refine ⟨6728292657554139904005683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4485528438369426602670455 6728292657554139904005683)
                  ·
                    refine ⟨10092438986331209856008525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6728292657554139904005683 10092438986331209856008525)
                    ·
                      refine ⟨3784664619874203696003197, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10092438986331209856008525 3784664619874203696003197)
                      ·
                        rfl

theorem cell23_7370608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 1, 7, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 1, 7, 1, 1, 3].length) (baseStart_7370608 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7370608 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7370608 prefixEnd_7370608 := by exact prefixLift 7370608
  have htrace : WordTrace (prefixWord ++ tailWord_7370608) baseStart_7370608 baseEnd_7370608 := by
    simpa [prefixWord, tailWord_7370608, baseEnd_7370608] using wordTrace_append hprefix tailTrace_7370608
  have hstable : (prefixWord ++ tailWord_7370608).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7370608).length < 2 ^ (prefixWord ++ tailWord_7370608).sum := by decide
  have hdescent : baseEnd_7370608 < baseStart_7370608 := by decide
  rcases family_descends (prefixWord ++ tailWord_7370608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7370641 : List Nat := [1, 2, 2, 1, 1, 1, 6, 3, 2, 4]
def baseStart_7370641 : Nat := 118140960795 + 7370641 * 2 ^ 59
def prefixEnd_7370641 : Nat := 4983230072969 + 3 ^ 40 * 7370641 * 2
def baseEnd_7370641 : Nat := 1261560521578600688963515

theorem tailTrace_7370641 : CollatzResearch.WordTrace tailWord_7370641 prefixEnd_7370641 1261560521578600688963515 := by
  unfold tailWord_7370641
  simp only [CollatzResearch.WordTrace]
  refine ⟨268829362490433937109303777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179219574993622624739535851 268829362490433937109303777)
  ·
    refine ⟨201622021867825452831977833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 268829362490433937109303777 201622021867825452831977833)
    ·
      refine ⟨151216516400869089623983375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 201622021867825452831977833 151216516400869089623983375)
      ·
        refine ⟨226824774601303634435975063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 151216516400869089623983375 226824774601303634435975063)
        ·
          refine ⟨340237161901955451653962595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 226824774601303634435975063 340237161901955451653962595)
          ·
            refine ⟨510355742852933177480943893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 340237161901955451653962595 510355742852933177480943893)
            ·
              refine ⟨23922925446231242694419245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 510355742852933177480943893 23922925446231242694419245)
              ·
                refine ⟨8971097042336716010407217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23922925446231242694419245 8971097042336716010407217)
                ·
                  refine ⟨6728322781752537007805413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8971097042336716010407217 6728322781752537007805413)
                  ·
                    refine ⟨1261560521578600688963515, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6728322781752537007805413 1261560521578600688963515)
                    ·
                      rfl

theorem cell23_7370641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 6, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 6, 3, 2, 4].length) (baseStart_7370641 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7370641 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7370641 prefixEnd_7370641 := by exact prefixLift 7370641
  have htrace : WordTrace (prefixWord ++ tailWord_7370641) baseStart_7370641 baseEnd_7370641 := by
    simpa [prefixWord, tailWord_7370641, baseEnd_7370641] using wordTrace_append hprefix tailTrace_7370641
  have hstable : (prefixWord ++ tailWord_7370641).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7370641).length < 2 ^ (prefixWord ++ tailWord_7370641).sum := by decide
  have hdescent : baseEnd_7370641 < baseStart_7370641 := by decide
  rcases family_descends (prefixWord ++ tailWord_7370641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7370698 : List Nat := [3, 1, 2, 1, 2, 1, 2, 5, 2, 1, 3]
def baseStart_7370698 : Nat := 118140960795 + 7370698 * 2 ^ 59
def prefixEnd_7370698 : Nat := 4983230072969 + 3 ^ 40 * 7370698 * 2
def baseEnd_7370698 : Nat := 3784710833133108343877783

theorem tailTrace_7370698 : CollatzResearch.WordTrace tailWord_7370698 prefixEnd_7370698 3784710833133108343877783 := by
  unfold tailWord_7370698
  simp only [CollatzResearch.WordTrace]
  refine ⟨67207860362806858961032187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 179220960967484957229419165 67207860362806858961032187)
  ·
    refine ⟨100811790544210288441548281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67207860362806858961032187 100811790544210288441548281)
    ·
      refine ⟨75608842908157716331161211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 100811790544210288441548281 75608842908157716331161211)
      ·
        refine ⟨113413264362236574496741817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75608842908157716331161211 113413264362236574496741817)
        ·
          refine ⟨85059948271677430872556363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 113413264362236574496741817 85059948271677430872556363)
          ·
            refine ⟨127589922407516146308834545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85059948271677430872556363 127589922407516146308834545)
            ·
              refine ⟨95692441805637109731625909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 127589922407516146308834545 95692441805637109731625909)
              ·
                refine ⟨8971166419278479037339929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 95692441805637109731625909 8971166419278479037339929)
                ·
                  refine ⟨6728374814458859278004947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8971166419278479037339929 6728374814458859278004947)
                  ·
                    refine ⟨10092562221688288917007421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6728374814458859278004947 10092562221688288917007421)
                    ·
                      refine ⟨3784710833133108343877783, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10092562221688288917007421 3784710833133108343877783)
                      ·
                        rfl

theorem cell23_7370698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 2, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 2, 5, 2, 1, 3].length) (baseStart_7370698 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7370698 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7370698 prefixEnd_7370698 := by exact prefixLift 7370698
  have htrace : WordTrace (prefixWord ++ tailWord_7370698) baseStart_7370698 baseEnd_7370698 := by
    simpa [prefixWord, tailWord_7370698, baseEnd_7370698] using wordTrace_append hprefix tailTrace_7370698
  have hstable : (prefixWord ++ tailWord_7370698).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7370698).length < 2 ^ (prefixWord ++ tailWord_7370698).sum := by decide
  have hdescent : baseEnd_7370698 < baseStart_7370698 := by decide
  rcases family_descends (prefixWord ++ tailWord_7370698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7370704 : List Nat := [2, 1, 1, 1, 1, 2, 4, 2, 2, 3, 4]
def baseStart_7370704 : Nat := 118140960795 + 7370704 * 2 ^ 59
def prefixEnd_7370704 : Nat := 4983230072969 + 3 ^ 40 * 7370704 * 2
def baseEnd_7370704 : Nat := 3784713914017035320402755

theorem tailTrace_7370704 : CollatzResearch.WordTrace tailWord_7370704 prefixEnd_7370704 3784713914017035320402755 := by
  unfold tailWord_7370704
  simp only [CollatzResearch.WordTrace]
  refine ⟨134415830144602849434423583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 179221106859470465912564777 134415830144602849434423583)
  ·
    refine ⟨201623745216904274151635375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134415830144602849434423583 201623745216904274151635375)
    ·
      refine ⟨302435617825356411227453063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 201623745216904274151635375 302435617825356411227453063)
      ·
        refine ⟨453653426738034616841179595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 302435617825356411227453063 453653426738034616841179595)
        ·
          refine ⟨680480140107051925261769393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 453653426738034616841179595 680480140107051925261769393)
          ·
            refine ⟨510360105080288943946327045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 680480140107051925261769393 510360105080288943946327045)
            ·
              refine ⟨95692519702554176989936321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 510360105080288943946327045 95692519702554176989936321)
              ·
                refine ⟨71769389776915632742452241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 95692519702554176989936321 71769389776915632742452241)
                ·
                  refine ⟨53827042332686724556839181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 71769389776915632742452241 53827042332686724556839181)
                  ·
                    refine ⟨20185140874757521708814693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 53827042332686724556839181 20185140874757521708814693)
                    ·
                      refine ⟨3784713914017035320402755, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20185140874757521708814693 3784713914017035320402755)
                      ·
                        rfl

theorem cell23_7370704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 4, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 4, 2, 2, 3, 4].length) (baseStart_7370704 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7370704 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7370704 prefixEnd_7370704 := by exact prefixLift 7370704
  have htrace : WordTrace (prefixWord ++ tailWord_7370704) baseStart_7370704 baseEnd_7370704 := by
    simpa [prefixWord, tailWord_7370704, baseEnd_7370704] using wordTrace_append hprefix tailTrace_7370704
  have hstable : (prefixWord ++ tailWord_7370704).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7370704).length < 2 ^ (prefixWord ++ tailWord_7370704).sum := by decide
  have hdescent : baseEnd_7370704 < baseStart_7370704 := by decide
  rcases family_descends (prefixWord ++ tailWord_7370704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7370801 : List Nat := [1, 2, 2, 3, 1, 3, 2, 1, 1, 2, 5]
def baseStart_7370801 : Nat := 118140960795 + 7370801 * 2 ^ 59
def prefixEnd_7370801 : Nat := 4983230072969 + 3 ^ 40 * 7370801 * 2
def baseEnd_7370801 : Nat := 3784763721640521440889809

theorem tailTrace_7370801 : CollatzResearch.WordTrace tailWord_7370801 prefixEnd_7370801 3784763721640521440889809 := by
  unfold tailWord_7370801
  simp only [CollatzResearch.WordTrace]
  refine ⟨268835198169854284435128257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179223465446569522956752171 268835198169854284435128257)
  ·
    refine ⟨201626398627390713326346193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 268835198169854284435128257 201626398627390713326346193)
    ·
      refine ⟨151219798970543034994759645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 201626398627390713326346193 151219798970543034994759645)
      ·
        refine ⟨56707424613953638123034867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 151219798970543034994759645 56707424613953638123034867)
        ·
          refine ⟨85061136920930457184552301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56707424613953638123034867 85061136920930457184552301)
          ·
            refine ⟨31897926345348921444207113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 85061136920930457184552301 31897926345348921444207113)
            ·
              refine ⟨23923444759011691083155335, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31897926345348921444207113 23923444759011691083155335)
              ·
                refine ⟨35885167138517536624733003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23923444759011691083155335 35885167138517536624733003)
                ·
                  refine ⟨53827750707776304937099505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35885167138517536624733003 53827750707776304937099505)
                  ·
                    refine ⟨40370813030832228702824629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 53827750707776304937099505 40370813030832228702824629)
                    ·
                      refine ⟨3784763721640521440889809, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 40370813030832228702824629 3784763721640521440889809)
                      ·
                        rfl

theorem cell23_7370801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 3, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 3, 2, 1, 1, 2, 5].length) (baseStart_7370801 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7370801 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7370801 prefixEnd_7370801 := by exact prefixLift 7370801
  have htrace : WordTrace (prefixWord ++ tailWord_7370801) baseStart_7370801 baseEnd_7370801 := by
    simpa [prefixWord, tailWord_7370801, baseEnd_7370801] using wordTrace_append hprefix tailTrace_7370801
  have hstable : (prefixWord ++ tailWord_7370801).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7370801).length < 2 ^ (prefixWord ++ tailWord_7370801).sum := by decide
  have hdescent : baseEnd_7370801 < baseStart_7370801 := by decide
  rcases family_descends (prefixWord ++ tailWord_7370801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7370828 : List Nat := [2, 2, 1, 3, 1, 1, 5, 1, 2, 1, 4]
def baseStart_7370828 : Nat := 118140960795 + 7370828 * 2 ^ 59
def prefixEnd_7370828 : Nat := 4983230072969 + 3 ^ 40 * 7370828 * 2
def baseEnd_7370828 : Nat := 3784777585618192835252185

theorem tailTrace_7370828 : CollatzResearch.WordTrace tailWord_7370828 prefixEnd_7370828 3784777585618192835252185 := by
  unfold tailWord_7370828
  simp only [CollatzResearch.WordTrace]
  refine ⟨134418091470378234023180569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 179224121960504312030907425 134418091470378234023180569)
  ·
    refine ⟨100813568602783675517385427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 134418091470378234023180569 100813568602783675517385427)
    ·
      refine ⟨151220352904175513276078141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100813568602783675517385427 151220352904175513276078141)
      ·
        refine ⟨56707632339065817478529303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 151220352904175513276078141 56707632339065817478529303)
        ·
          refine ⟨85061448508598726217793955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56707632339065817478529303 85061448508598726217793955)
          ·
            refine ⟨127592172762898089326690933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85061448508598726217793955 127592172762898089326690933)
            ·
              refine ⟨11961766196521695874377275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 127592172762898089326690933 11961766196521695874377275)
              ·
                refine ⟨17942649294782543811565913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11961766196521695874377275 17942649294782543811565913)
                ·
                  refine ⟨13456986971086907858674435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17942649294782543811565913 13456986971086907858674435)
                  ·
                    refine ⟨20185480456630361788011653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13456986971086907858674435 20185480456630361788011653)
                    ·
                      refine ⟨3784777585618192835252185, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20185480456630361788011653 3784777585618192835252185)
                      ·
                        rfl

theorem cell23_7370828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 5, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 5, 1, 2, 1, 4].length) (baseStart_7370828 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7370828 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7370828 prefixEnd_7370828 := by exact prefixLift 7370828
  have htrace : WordTrace (prefixWord ++ tailWord_7370828) baseStart_7370828 baseEnd_7370828 := by
    simpa [prefixWord, tailWord_7370828, baseEnd_7370828] using wordTrace_append hprefix tailTrace_7370828
  have hstable : (prefixWord ++ tailWord_7370828).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7370828).length < 2 ^ (prefixWord ++ tailWord_7370828).sum := by decide
  have hdescent : baseEnd_7370828 < baseStart_7370828 := by decide
  rcases family_descends (prefixWord ++ tailWord_7370828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7370831 : List Nat := [1, 1, 2, 1, 1, 2, 2, 5, 1, 4, 3]
def baseStart_7370831 : Nat := 118140960795 + 7370831 * 2 ^ 59
def prefixEnd_7370831 : Nat := 4983230072969 + 3 ^ 40 * 7370831 * 2
def baseEnd_7370831 : Nat := 3784779126060156323514671

theorem tailTrace_7370831 : CollatzResearch.WordTrace tailWord_7370831 prefixEnd_7370831 3784779126060156323514671 := by
  unfold tailWord_7370831
  simp only [CollatzResearch.WordTrace]
  refine ⟨268836292359745599558720347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179224194906497066372480231 268836292359745599558720347)
  ·
    refine ⟨403254438539618399338080521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 268836292359745599558720347 403254438539618399338080521)
    ·
      refine ⟨302440828904713799503560391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 403254438539618399338080521 302440828904713799503560391)
      ·
        refine ⟨453661243357070699255340587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 302440828904713799503560391 453661243357070699255340587)
        ·
          refine ⟨680491865035606048883010881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 453661243357070699255340587 680491865035606048883010881)
          ·
            refine ⟨510368898776704536662258161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 680491865035606048883010881 510368898776704536662258161)
            ·
              refine ⟨382776674082528402496693621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 510368898776704536662258161 382776674082528402496693621)
              ·
                refine ⟨35885313195237037734065027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 382776674082528402496693621 35885313195237037734065027)
                ·
                  refine ⟨53827969792855556601097541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35885313195237037734065027 53827969792855556601097541)
                  ·
                    refine ⟨10092744336160416862705789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 53827969792855556601097541 10092744336160416862705789)
                    ·
                      refine ⟨3784779126060156323514671, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10092744336160416862705789 3784779126060156323514671)
                      ·
                        rfl

theorem cell23_7370831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 2, 5, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 2, 5, 1, 4, 3].length) (baseStart_7370831 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7370831 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7370831 prefixEnd_7370831 := by exact prefixLift 7370831
  have htrace : WordTrace (prefixWord ++ tailWord_7370831) baseStart_7370831 baseEnd_7370831 := by
    simpa [prefixWord, tailWord_7370831, baseEnd_7370831] using wordTrace_append hprefix tailTrace_7370831
  have hstable : (prefixWord ++ tailWord_7370831).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7370831).length < 2 ^ (prefixWord ++ tailWord_7370831).sum := by decide
  have hdescent : baseEnd_7370831 < baseStart_7370831 := by decide
  rcases family_descends (prefixWord ++ tailWord_7370831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7370855 : List Nat := [1, 1, 5, 1, 1, 2, 1, 6, 1, 4]
def baseStart_7370855 : Nat := 118140960795 + 7370855 * 2 ^ 59
def prefixEnd_7370855 : Nat := 4983230072969 + 3 ^ 40 * 7370855 * 2
def baseEnd_7370855 : Nat := 1261597149865288076538187

theorem tailTrace_7370855 : CollatzResearch.WordTrace tailWord_7370855 prefixEnd_7370855 1261597149865288076538187 := by
  unfold tailWord_7370855
  simp only [CollatzResearch.WordTrace]
  refine ⟨268837167711658651657594019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179224778474439101105062679 268837167711658651657594019)
  ·
    refine ⟨403255751567487977486391029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 268837167711658651657594019 403255751567487977486391029)
    ·
      refine ⟨37805226709451997889349159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 403255751567487977486391029 37805226709451997889349159)
      ·
        refine ⟨56707840064177996834023739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37805226709451997889349159 56707840064177996834023739)
        ·
          refine ⟨85061760096266995251035609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56707840064177996834023739 85061760096266995251035609)
          ·
            refine ⟨63796320072200246438276707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 85061760096266995251035609 63796320072200246438276707)
            ·
              refine ⟨95694480108300369657415061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63796320072200246438276707 95694480108300369657415061)
              ·
                refine ⟨4485678755076579827691331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 95694480108300369657415061 4485678755076579827691331)
                ·
                  refine ⟨6728518132614869741536997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4485678755076579827691331 6728518132614869741536997)
                  ·
                    refine ⟨1261597149865288076538187, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6728518132614869741536997 1261597149865288076538187)
                    ·
                      rfl

theorem cell23_7370855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 1, 6, 1, 4].length) (baseStart_7370855 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7370855 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7370855 prefixEnd_7370855 := by exact prefixLift 7370855
  have htrace : WordTrace (prefixWord ++ tailWord_7370855) baseStart_7370855 baseEnd_7370855 := by
    simpa [prefixWord, tailWord_7370855, baseEnd_7370855] using wordTrace_append hprefix tailTrace_7370855
  have hstable : (prefixWord ++ tailWord_7370855).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7370855).length < 2 ^ (prefixWord ++ tailWord_7370855).sum := by decide
  have hdescent : baseEnd_7370855 < baseStart_7370855 := by decide
  rcases family_descends (prefixWord ++ tailWord_7370855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7370912 : List Nat := [2, 1, 1, 4, 2, 4, 1, 1, 3, 1, 3]
def baseStart_7370912 : Nat := 118140960795 + 7370912 * 2 ^ 59
def prefixEnd_7370912 : Nat := 4983230072969 + 3 ^ 40 * 7370912 * 2
def baseEnd_7370912 : Nat := 3784820717993170506601799

theorem tailTrace_7370912 : CollatzResearch.WordTrace tailWord_7370912 prefixEnd_7370912 3784820717993170506601799 := by
  unfold tailWord_7370912
  simp only [CollatzResearch.WordTrace]
  refine ⟨134419623336226075196209495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 179226164448301433594945993 134419623336226075196209495)
  ·
    refine ⟨201629435004339112794314243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134419623336226075196209495 201629435004339112794314243)
    ·
      refine ⟨302444152506508669191471365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 201629435004339112794314243 302444152506508669191471365)
      ·
        refine ⟨56708278594970375473400881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 302444152506508669191471365 56708278594970375473400881)
        ·
          refine ⟨42531208946227781605050661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56708278594970375473400881 42531208946227781605050661)
          ·
            refine ⟨7974601677417709050946999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 42531208946227781605050661 7974601677417709050946999)
            ·
              refine ⟨11961902516126563576420499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7974601677417709050946999 11961902516126563576420499)
              ·
                refine ⟨17942853774189845364630749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11961902516126563576420499 17942853774189845364630749)
                ·
                  refine ⟨6728570165321192011736531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17942853774189845364630749 6728570165321192011736531)
                  ·
                    refine ⟨10092855247981788017604797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6728570165321192011736531 10092855247981788017604797)
                    ·
                      refine ⟨3784820717993170506601799, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10092855247981788017604797 3784820717993170506601799)
                      ·
                        rfl

theorem cell23_7370912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 4, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 4, 1, 1, 3, 1, 3].length) (baseStart_7370912 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7370912 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7370912 prefixEnd_7370912 := by exact prefixLift 7370912
  have htrace : WordTrace (prefixWord ++ tailWord_7370912) baseStart_7370912 baseEnd_7370912 := by
    simpa [prefixWord, tailWord_7370912, baseEnd_7370912] using wordTrace_append hprefix tailTrace_7370912
  have hstable : (prefixWord ++ tailWord_7370912).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7370912).length < 2 ^ (prefixWord ++ tailWord_7370912).sum := by decide
  have hdescent : baseEnd_7370912 < baseStart_7370912 := by decide
  rcases family_descends (prefixWord ++ tailWord_7370912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7370919 : List Nat := [1, 1, 6, 2, 3, 1, 2, 1, 6]
def baseStart_7370919 : Nat := 118140960795 + 7370919 * 2 ^ 59
def prefixEnd_7370919 : Nat := 4983230072969 + 3 ^ 40 * 7370919 * 2
def baseEnd_7370919 : Nat := 420536034706416886579363

theorem tailTrace_7370919 : CollatzResearch.WordTrace tailWord_7370919 prefixEnd_7370919 420536034706416886579363 := by
  unfold tailWord_7370919
  simp only [CollatzResearch.WordTrace]
  refine ⟨268839501983426790587923811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179226334655617860391949207 268839501983426790587923811)
  ·
    refine ⟨403259252975140185881885717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 268839501983426790587923811 403259252975140185881885717)
    ·
      refine ⟨18902777483209696213213393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 403259252975140185881885717 18902777483209696213213393)
      ·
        refine ⟨14177083112407272159910045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18902777483209696213213393 14177083112407272159910045)
        ·
          refine ⟨5316406167152727059966267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14177083112407272159910045 5316406167152727059966267)
          ·
            refine ⟨7974609250729090589949401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5316406167152727059966267 7974609250729090589949401)
            ·
              refine ⟨5980956938046817942462051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7974609250729090589949401 5980956938046817942462051)
              ·
                refine ⟨8971435407070226913693077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5980956938046817942462051 8971435407070226913693077)
                ·
                  refine ⟨420536034706416886579363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8971435407070226913693077 420536034706416886579363)
                  ·
                    rfl

theorem cell23_7370919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 3, 1, 2, 1, 6].length) (baseStart_7370919 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7370919 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7370919 prefixEnd_7370919 := by exact prefixLift 7370919
  have htrace : WordTrace (prefixWord ++ tailWord_7370919) baseStart_7370919 baseEnd_7370919 := by
    simpa [prefixWord, tailWord_7370919, baseEnd_7370919] using wordTrace_append hprefix tailTrace_7370919
  have hstable : (prefixWord ++ tailWord_7370919).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7370919).length < 2 ^ (prefixWord ++ tailWord_7370919).sum := by decide
  have hdescent : baseEnd_7370919 < baseStart_7370919 := by decide
  rcases family_descends (prefixWord ++ tailWord_7370919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7370935 : List Nat := [1, 1, 3, 1, 4, 2, 3, 2, 1, 1, 4]
def baseStart_7370935 : Nat := 118140960795 + 7370935 * 2 ^ 59
def prefixEnd_7370935 : Nat := 4983230072969 + 3 ^ 40 * 7370935 * 2
def baseEnd_7370935 : Nat := 3784832528048223916614193

theorem tailTrace_7370935 : CollatzResearch.WordTrace tailWord_7370935 prefixEnd_7370935 3784832528048223916614193 := by
  unfold tailWord_7370935
  simp only [CollatzResearch.WordTrace]
  refine ⟨268840085551368825320506259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179226723700912550213670839 268840085551368825320506259)
  ·
    refine ⟨403260128327053237980759389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 268840085551368825320506259 403260128327053237980759389)
    ·
      refine ⟨151222548122644964242784771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 403260128327053237980759389 151222548122644964242784771)
      ·
        refine ⟨226833822183967446364177157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 151222548122644964242784771 226833822183967446364177157)
        ·
          refine ⟨42531341659493896193283217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 226833822183967446364177157 42531341659493896193283217)
          ·
            refine ⟨31898506244620422144962413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42531341659493896193283217 31898506244620422144962413)
            ·
              refine ⟨11961939841732658304360905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31898506244620422144962413 11961939841732658304360905)
              ·
                refine ⟨8971454881299493728270679, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11961939841732658304360905 8971454881299493728270679)
                ·
                  refine ⟨13457182321949240592406019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8971454881299493728270679 13457182321949240592406019)
                  ·
                    refine ⟨20185773482923860888609029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13457182321949240592406019 20185773482923860888609029)
                    ·
                      refine ⟨3784832528048223916614193, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20185773482923860888609029 3784832528048223916614193)
                      ·
                        rfl

theorem cell23_7370935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 2, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 2, 3, 2, 1, 1, 4].length) (baseStart_7370935 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7370935 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7370935 prefixEnd_7370935 := by exact prefixLift 7370935
  have htrace : WordTrace (prefixWord ++ tailWord_7370935) baseStart_7370935 baseEnd_7370935 := by
    simpa [prefixWord, tailWord_7370935, baseEnd_7370935] using wordTrace_append hprefix tailTrace_7370935
  have hstable : (prefixWord ++ tailWord_7370935).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7370935).length < 2 ^ (prefixWord ++ tailWord_7370935).sum := by decide
  have hdescent : baseEnd_7370935 < baseStart_7370935 := by decide
  rcases family_descends (prefixWord ++ tailWord_7370935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7370962 : List Nat := [3, 2, 2, 2, 1, 3, 2, 2, 2, 4]
def baseStart_7370962 : Nat := 118140960795 + 7370962 * 2 ^ 59
def prefixEnd_7370962 : Nat := 4983230072969 + 3 ^ 40 * 7370962 * 2
def baseEnd_7370962 : Nat := 1261615464008631770325523

theorem tailTrace_7370962 : CollatzResearch.WordTrace tailWord_7370962 prefixEnd_7370962 1261615464008631770325523 := by
  unfold tailWord_7370962
  simp only [CollatzResearch.WordTrace]
  refine ⟨67210267580567752232934785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 179227380214847339287826093 67210267580567752232934785)
  ·
    refine ⟨50407700685425814174701089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67210267580567752232934785 50407700685425814174701089)
    ·
      refine ⟨37805775514069360631025817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50407700685425814174701089 37805775514069360631025817)
      ·
        refine ⟨28354331635552020473269363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37805775514069360631025817 28354331635552020473269363)
        ·
          refine ⟨42531497453328030709904045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28354331635552020473269363 42531497453328030709904045)
          ·
            refine ⟨15949311544998011516214017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42531497453328030709904045 15949311544998011516214017)
            ·
              refine ⟨11961983658748508637160513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15949311544998011516214017 11961983658748508637160513)
              ·
                refine ⟨8971487744061381477870385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11961983658748508637160513 8971487744061381477870385)
                ·
                  refine ⟨6728615808046036108402789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8971487744061381477870385 6728615808046036108402789)
                  ·
                    refine ⟨1261615464008631770325523, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6728615808046036108402789 1261615464008631770325523)
                    ·
                      rfl

theorem cell23_7370962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 3, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 3, 2, 2, 2, 4].length) (baseStart_7370962 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7370962 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7370962 prefixEnd_7370962 := by exact prefixLift 7370962
  have htrace : WordTrace (prefixWord ++ tailWord_7370962) baseStart_7370962 baseEnd_7370962 := by
    simpa [prefixWord, tailWord_7370962, baseEnd_7370962] using wordTrace_append hprefix tailTrace_7370962
  have hstable : (prefixWord ++ tailWord_7370962).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7370962).length < 2 ^ (prefixWord ++ tailWord_7370962).sum := by decide
  have hdescent : baseEnd_7370962 < baseStart_7370962 := by decide
  rcases family_descends (prefixWord ++ tailWord_7370962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7370971 : List Nat := [1, 1, 1, 1, 1, 1, 1, 7, 2, 7]
def baseStart_7370971 : Nat := 118140960795 + 7370971 * 2 ^ 59
def prefixEnd_7370971 : Nat := 4983230072969 + 3 ^ 40 * 7370971 * 2
def baseEnd_7370971 : Nat := 1261617004450595258588009

theorem tailTrace_7370971 : CollatzResearch.WordTrace tailWord_7370971 prefixEnd_7370971 1261617004450595258588009 := by
  unfold tailWord_7370971
  simp only [CollatzResearch.WordTrace]
  refine ⟨268841398579238403468816767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179227599052825602312544511 268841398579238403468816767)
  ·
    refine ⟨403262097868857605203225151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 268841398579238403468816767 403262097868857605203225151)
    ·
      refine ⟨604893146803286407804837727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 403262097868857605203225151 604893146803286407804837727)
      ·
        refine ⟨907339720204929611707256591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 604893146803286407804837727 907339720204929611707256591)
        ·
          refine ⟨1361009580307394417560884887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 907339720204929611707256591 1361009580307394417560884887)
          ·
            refine ⟨2041514370461091626341327331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1361009580307394417560884887 2041514370461091626341327331)
            ·
              refine ⟨3062271555691637439511990997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2041514370461091626341327331 3062271555691637439511990997)
              ·
                refine ⟨71771989586522752488562289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3062271555691637439511990997 71771989586522752488562289)
                ·
                  refine ⟨53828992189892064366421717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 71771989586522752488562289 53828992189892064366421717)
                  ·
                    refine ⟨1261617004450595258588009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 53828992189892064366421717 1261617004450595258588009)
                    ·
                      rfl

theorem cell23_7370971_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 7, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 7, 2, 7].length) (baseStart_7370971 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7370971 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7370971 prefixEnd_7370971 := by exact prefixLift 7370971
  have htrace : WordTrace (prefixWord ++ tailWord_7370971) baseStart_7370971 baseEnd_7370971 := by
    simpa [prefixWord, tailWord_7370971, baseEnd_7370971] using wordTrace_append hprefix tailTrace_7370971
  have hstable : (prefixWord ++ tailWord_7370971).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7370971).length < 2 ^ (prefixWord ++ tailWord_7370971).sum := by decide
  have hdescent : baseEnd_7370971 < baseStart_7370971 := by decide
  rcases family_descends (prefixWord ++ tailWord_7370971) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7370995 : List Nat := [1, 1, 1, 2, 2, 4, 1, 3, 3, 3, 2]
def baseStart_7370995 : Nat := 118140960795 + 7370995 * 2 ^ 59
def prefixEnd_7370995 : Nat := 4983230072969 + 3 ^ 40 * 7370995 * 2
def baseEnd_7370995 : Nat := 3784863336887493681863917

theorem tailTrace_7370995 : CollatzResearch.WordTrace tailWord_7370995 prefixEnd_7370995 3784863336887493681863917 := by
  unfold tailWord_7370995
  simp only [CollatzResearch.WordTrace]
  refine ⟨268842273931151455567690439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179228182620767637045126959 268842273931151455567690439)
  ·
    refine ⟨403263410896727183351535659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 268842273931151455567690439 403263410896727183351535659)
    ·
      refine ⟨604895116345090775027303489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 403263410896727183351535659 604895116345090775027303489)
      ·
        refine ⟨453671337258818081270477617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 604895116345090775027303489 453671337258818081270477617)
        ·
          refine ⟨340253502944113560952858213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 453671337258818081270477617 340253502944113560952858213)
          ·
            refine ⟨63797531802021292678660915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 340253502944113560952858213 63797531802021292678660915)
            ·
              refine ⟨95696297703031939017991373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63797531802021292678660915 95696297703031939017991373)
              ·
                refine ⟨35886111638636977131746765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 95696297703031939017991373 35886111638636977131746765)
                ·
                  refine ⟨13457291864488866424405037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35886111638636977131746765 13457291864488866424405037)
                  ·
                    refine ⟨5046484449183324909151889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13457291864488866424405037 5046484449183324909151889)
                    ·
                      refine ⟨3784863336887493681863917, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5046484449183324909151889 3784863336887493681863917)
                      ·
                        rfl

theorem cell23_7370995_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 1, 3, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 1, 3, 3, 3, 2].length) (baseStart_7370995 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7370995 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7370995 prefixEnd_7370995 := by exact prefixLift 7370995
  have htrace : WordTrace (prefixWord ++ tailWord_7370995) baseStart_7370995 baseEnd_7370995 := by
    simpa [prefixWord, tailWord_7370995, baseEnd_7370995] using wordTrace_append hprefix tailTrace_7370995
  have hstable : (prefixWord ++ tailWord_7370995).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7370995).length < 2 ^ (prefixWord ++ tailWord_7370995).sum := by decide
  have hdescent : baseEnd_7370995 < baseStart_7370995 := by decide
  rcases family_descends (prefixWord ++ tailWord_7370995) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7371018 : List Nat := [3, 1, 2, 2, 1, 1, 3, 2, 2, 6]
def baseStart_7371018 : Nat := 118140960795 + 7371018 * 2 ^ 59
def prefixEnd_7371018 : Nat := 4983230072969 + 3 ^ 40 * 7371018 * 2
def baseEnd_7371018 : Nat := 1261625048980849030625437

theorem tailTrace_7371018 : CollatzResearch.WordTrace tailWord_7371018 prefixEnd_7371018 1261625048980849030625437 := by
  unfold tailWord_7371018
  simp only [CollatzResearch.WordTrace]
  refine ⟨67210778202517032623944427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 179228741873378753663851805 67210778202517032623944427)
  ·
    refine ⟨100816167303775548935916641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67210778202517032623944427 100816167303775548935916641)
    ·
      refine ⟨75612125477831661701937481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 100816167303775548935916641 75612125477831661701937481)
      ·
        refine ⟨56709094108373746276453111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 75612125477831661701937481 56709094108373746276453111)
        ·
          refine ⟨85063641162560619414679667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56709094108373746276453111 85063641162560619414679667)
          ·
            refine ⟨127595461743840929122019501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85063641162560619414679667 127595461743840929122019501)
            ·
              refine ⟨47848298153940348420757313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 127595461743840929122019501 47848298153940348420757313)
              ·
                refine ⟨35886223615455261315567985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47848298153940348420757313 35886223615455261315567985)
                ·
                  refine ⟨26914667711591445986675989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35886223615455261315567985 26914667711591445986675989)
                  ·
                    refine ⟨1261625048980849030625437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26914667711591445986675989 1261625048980849030625437)
                    ·
                      rfl

theorem cell23_7371018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 3, 2, 2, 6].length) (baseStart_7371018 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7371018 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7371018 prefixEnd_7371018 := by exact prefixLift 7371018
  have htrace : WordTrace (prefixWord ++ tailWord_7371018) baseStart_7371018 baseEnd_7371018 := by
    simpa [prefixWord, tailWord_7371018, baseEnd_7371018] using wordTrace_append hprefix tailTrace_7371018
  have hstable : (prefixWord ++ tailWord_7371018).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7371018).length < 2 ^ (prefixWord ++ tailWord_7371018).sum := by decide
  have hdescent : baseEnd_7371018 < baseStart_7371018 := by decide
  rcases family_descends (prefixWord ++ tailWord_7371018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7371088 : List Nat := [2, 1, 1, 1, 1, 6, 1, 1, 1, 1, 7]
def baseStart_7371088 : Nat := 118140960795 + 7371088 * 2 ^ 59
def prefixEnd_7371088 : Nat := 4983230072969 + 3 ^ 40 * 7371088 * 2
def baseEnd_7371088 : Nat := 3784911090588361818000989

theorem tailTrace_7371088 : CollatzResearch.WordTrace tailWord_7371088 prefixEnd_7371088 3784911090588361818000989 := by
  unfold tailWord_7371088
  simp only [CollatzResearch.WordTrace]
  refine ⟨134422832959907266225412959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 179230443946543021633883945 134422832959907266225412959)
  ·
    refine ⟨201634249439860899338119439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134422832959907266225412959 201634249439860899338119439)
    ·
      refine ⟨302451374159791349007179159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 201634249439860899338119439 302451374159791349007179159)
      ·
        refine ⟨453677061239687023510768739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 302451374159791349007179159 453677061239687023510768739)
        ·
          refine ⟨680515591859530535266153109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 453677061239687023510768739 680515591859530535266153109)
          ·
            refine ⟨31899168368415493840600927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 680515591859530535266153109 31899168368415493840600927)
            ·
              refine ⟨47848752552623240760901391, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31899168368415493840600927 47848752552623240760901391)
              ·
                refine ⟨71773128828934861141352087, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47848752552623240760901391 71773128828934861141352087)
                ·
                  refine ⟨107659693243402291712028131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 71773128828934861141352087 107659693243402291712028131)
                  ·
                    refine ⟨161489539865103437568042197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 107659693243402291712028131 161489539865103437568042197)
                    ·
                      refine ⟨3784911090588361818000989, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 161489539865103437568042197 3784911090588361818000989)
                      ·
                        rfl

theorem cell23_7371088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 6, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 6, 1, 1, 1, 1, 7].length) (baseStart_7371088 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7371088 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7371088 prefixEnd_7371088 := by exact prefixLift 7371088
  have htrace : WordTrace (prefixWord ++ tailWord_7371088) baseStart_7371088 baseEnd_7371088 := by
    simpa [prefixWord, tailWord_7371088, baseEnd_7371088] using wordTrace_append hprefix tailTrace_7371088
  have hstable : (prefixWord ++ tailWord_7371088).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7371088).length < 2 ^ (prefixWord ++ tailWord_7371088).sum := by decide
  have hdescent : baseEnd_7371088 < baseStart_7371088 := by decide
  rcases family_descends (prefixWord ++ tailWord_7371088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7371093 : List Nat := [1, 3, 2, 2, 4, 2, 2, 1, 2, 2, 2]
def baseStart_7371093 : Nat := 118140960795 + 7371093 * 2 ^ 59
def prefixEnd_7371093 : Nat := 4983230072969 + 3 ^ 40 * 7371093 * 2
def baseEnd_7371093 : Nat := 3784913657991634298438467

theorem tailTrace_7371093 : CollatzResearch.WordTrace tailWord_7371093 prefixEnd_7371093 3784913657991634298438467 := by
  unfold tailWord_7371093
  simp only [CollatzResearch.WordTrace]
  refine ⟨268845848284796418304757933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179230565523197612203171955 268845848284796418304757933)
  ·
    refine ⟨100817193106798656864284225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 268845848284796418304757933 100817193106798656864284225)
    ·
      refine ⟨75612894830098992648213169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 100817193106798656864284225 75612894830098992648213169)
      ·
        refine ⟨56709671122574244486159877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 75612894830098992648213169 56709671122574244486159877)
        ·
          refine ⟨10633063335482670841154977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 56709671122574244486159877 10633063335482670841154977)
          ·
            refine ⟨7974797501612003130866233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10633063335482670841154977 7974797501612003130866233)
            ·
              refine ⟨5981098126209002348149675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7974797501612003130866233 5981098126209002348149675)
              ·
                refine ⟨8971647189313503522224513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5981098126209002348149675 8971647189313503522224513)
                ·
                  refine ⟨6728735391985127641668385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8971647189313503522224513 6728735391985127641668385)
                  ·
                    refine ⟨5046551543988845731251289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6728735391985127641668385 5046551543988845731251289)
                    ·
                      refine ⟨3784913657991634298438467, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5046551543988845731251289 3784913657991634298438467)
                      ·
                        rfl

theorem cell23_7371093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 4, 2, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 4, 2, 2, 1, 2, 2, 2].length) (baseStart_7371093 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7371093 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7371093 prefixEnd_7371093 := by exact prefixLift 7371093
  have htrace : WordTrace (prefixWord ++ tailWord_7371093) baseStart_7371093 baseEnd_7371093 := by
    simpa [prefixWord, tailWord_7371093, baseEnd_7371093] using wordTrace_append hprefix tailTrace_7371093
  have hstable : (prefixWord ++ tailWord_7371093).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7371093).length < 2 ^ (prefixWord ++ tailWord_7371093).sum := by decide
  have hdescent : baseEnd_7371093 < baseStart_7371093 := by decide
  rcases family_descends (prefixWord ++ tailWord_7371093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7371112 : List Nat := [2, 1, 4, 2, 2, 2, 2, 1, 2, 5]
def baseStart_7371112 : Nat := 118140960795 + 7371112 * 2 ^ 59
def prefixEnd_7371112 : Nat := 4983230072969 + 3 ^ 40 * 7371112 * 2
def baseEnd_7371112 : Nat := 1261641138041356574700293

theorem tailTrace_7371112 : CollatzResearch.WordTrace tailWord_7371112 prefixEnd_7371112 1261641138041356574700293 := by
  unfold tailWord_7371112
  simp only [CollatzResearch.WordTrace]
  refine ⟨134423270635863792274849795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 179231027514485056366466393 134423270635863792274849795)
  ·
    refine ⟨201634905953795688412274693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134423270635863792274849795 201634905953795688412274693)
    ·
      refine ⟨37806544866336691577301505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 201634905953795688412274693 37806544866336691577301505)
      ·
        refine ⟨28354908649752518682976129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37806544866336691577301505 28354908649752518682976129)
        ·
          refine ⟨21266181487314389012232097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28354908649752518682976129 21266181487314389012232097)
          ·
            refine ⟨15949636115485791759174073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21266181487314389012232097 15949636115485791759174073)
            ·
              refine ⟨11962227086614343819380555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15949636115485791759174073 11962227086614343819380555)
              ·
                refine ⟨17943340629921515729070833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11962227086614343819380555 17943340629921515729070833)
                ·
                  refine ⟨13457505472441136796803125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17943340629921515729070833 13457505472441136796803125)
                  ·
                    refine ⟨1261641138041356574700293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13457505472441136796803125 1261641138041356574700293)
                    ·
                      rfl

theorem cell23_7371112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 2, 2, 1, 2, 5].length) (baseStart_7371112 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7371112 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7371112 prefixEnd_7371112 := by exact prefixLift 7371112
  have htrace : WordTrace (prefixWord ++ tailWord_7371112) baseStart_7371112 baseEnd_7371112 := by
    simpa [prefixWord, tailWord_7371112, baseEnd_7371112] using wordTrace_append hprefix tailTrace_7371112
  have hstable : (prefixWord ++ tailWord_7371112).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7371112).length < 2 ^ (prefixWord ++ tailWord_7371112).sum := by decide
  have hdescent : baseEnd_7371112 < baseStart_7371112 := by decide
  rcases family_descends (prefixWord ++ tailWord_7371112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7371115 : List Nat := [1, 1, 1, 1, 2, 2, 2, 4, 1, 6, 2]
def baseStart_7371115 : Nat := 118140960795 + 7371115 * 2 ^ 59
def prefixEnd_7371115 : Nat := 4983230072969 + 3 ^ 40 * 7371115 * 2
def baseEnd_7371115 : Nat := 3784924954566033212363365

theorem tailTrace_7371115 : CollatzResearch.WordTrace tailWord_7371115 prefixEnd_7371115 3784924954566033212363365 := by
  unfold tailWord_7371115
  simp only [CollatzResearch.WordTrace]
  refine ⟨268846650690716716062058799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179231100460477810708039199 268846650690716716062058799)
  ·
    refine ⟨403269976036075074093088199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 268846650690716716062058799 403269976036075074093088199)
    ·
      refine ⟨604904964054112611139632299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 403269976036075074093088199 604904964054112611139632299)
      ·
        refine ⟨907357446081168916709448449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 604904964054112611139632299 907357446081168916709448449)
        ·
          refine ⟨680518084560876687532086337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 907357446081168916709448449 680518084560876687532086337)
          ·
            refine ⟨510388563420657515649064753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 680518084560876687532086337 510388563420657515649064753)
            ·
              refine ⟨382791422565493136736798565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 510388563420657515649064753 382791422565493136736798565)
              ·
                refine ⟨71773391731029963138149731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 382791422565493136736798565 71773391731029963138149731)
                ·
                  refine ⟨107660087596544944707224597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 71773391731029963138149731 107660087596544944707224597)
                  ·
                    refine ⟨5046566606088044283151153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 107660087596544944707224597 5046566606088044283151153)
                    ·
                      refine ⟨3784924954566033212363365, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5046566606088044283151153 3784924954566033212363365)
                      ·
                        rfl

theorem cell23_7371115_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 2, 4, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 2, 4, 1, 6, 2].length) (baseStart_7371115 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7371115 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7371115 prefixEnd_7371115 := by exact prefixLift 7371115
  have htrace : WordTrace (prefixWord ++ tailWord_7371115) baseStart_7371115 baseEnd_7371115 := by
    simpa [prefixWord, tailWord_7371115, baseEnd_7371115] using wordTrace_append hprefix tailTrace_7371115
  have hstable : (prefixWord ++ tailWord_7371115).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7371115).length < 2 ^ (prefixWord ++ tailWord_7371115).sum := by decide
  have hdescent : baseEnd_7371115 < baseStart_7371115 := by decide
  rcases family_descends (prefixWord ++ tailWord_7371115) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7371166 : List Nat := [4, 3, 1, 2, 1, 3, 1, 1, 2, 1, 4]
def baseStart_7371166 : Nat := 118140960795 + 7371166 * 2 ^ 59
def prefixEnd_7371166 : Nat := 4983230072969 + 3 ^ 40 * 7371166 * 2
def baseEnd_7371166 : Nat := 3784951142079412512825631

theorem tailTrace_7371166 : CollatzResearch.WordTrace tailWord_7371166 prefixEnd_7371166 3784951142079412512825631 := by
  unfold tailWord_7371166
  simp only [CollatzResearch.WordTrace]
  refine ⟨33606063851691493971520669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 179232340542354634514776901 33606063851691493971520669)
  ·
    refine ⟨12602273944384310239320251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33606063851691493971520669 12602273944384310239320251)
    ·
      refine ⟨18903410916576465358980377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12602273944384310239320251 18903410916576465358980377)
      ·
        refine ⟨14177558187432349019235283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18903410916576465358980377 14177558187432349019235283)
        ·
          refine ⟨21266337281148523528852925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14177558187432349019235283 21266337281148523528852925)
          ·
            refine ⟨7974876480430696323319847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21266337281148523528852925 7974876480430696323319847)
            ·
              refine ⟨11962314720646044484979771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7974876480430696323319847 11962314720646044484979771)
              ·
                refine ⟨17943472080969066727469657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11962314720646044484979771 17943472080969066727469657)
                ·
                  refine ⟨13457604060726800045602243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17943472080969066727469657 13457604060726800045602243)
                  ·
                    refine ⟨20186406091090200068403365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13457604060726800045602243 20186406091090200068403365)
                    ·
                      refine ⟨3784951142079412512825631, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20186406091090200068403365 3784951142079412512825631)
                      ·
                        rfl

theorem cell23_7371166_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 3, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 3, 1, 1, 2, 1, 4].length) (baseStart_7371166 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7371166 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7371166 prefixEnd_7371166 := by exact prefixLift 7371166
  have htrace : WordTrace (prefixWord ++ tailWord_7371166) baseStart_7371166 baseEnd_7371166 := by
    simpa [prefixWord, tailWord_7371166, baseEnd_7371166] using wordTrace_append hprefix tailTrace_7371166
  have hstable : (prefixWord ++ tailWord_7371166).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7371166).length < 2 ^ (prefixWord ++ tailWord_7371166).sum := by decide
  have hdescent : baseEnd_7371166 < baseStart_7371166 := by decide
  rcases family_descends (prefixWord ++ tailWord_7371166) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7371169 : List Nat := [1, 2, 3, 5, 1, 1, 1, 1, 1, 4, 3]
def baseStart_7371169 : Nat := 118140960795 + 7371169 * 2 ^ 59
def prefixEnd_7371169 : Nat := 4983230072969 + 3 ^ 40 * 7371169 * 2
def baseEnd_7371169 : Nat := 3784952682521376001088117

theorem tailTrace_7371169 : CollatzResearch.WordTrace tailWord_7371169 prefixEnd_7371169 3784952682521376001088117 := by
  unfold tailWord_7371169
  simp only [CollatzResearch.WordTrace]
  refine ⟨268848620232521083284524561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179232413488347388856349707 268848620232521083284524561)
  ·
    refine ⟨201636465174390812463393421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 268848620232521083284524561 201636465174390812463393421)
    ·
      refine ⟨75613674440396554673772533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 201636465174390812463393421 75613674440396554673772533)
      ·
        refine ⟨7088781978787177000666175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 75613674440396554673772533 7088781978787177000666175)
        ·
          refine ⟨10633172968180765500999263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7088781978787177000666175 10633172968180765500999263)
          ·
            refine ⟨15949759452271148251498895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10633172968180765500999263 15949759452271148251498895)
            ·
              refine ⟨23924639178406722377248343, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15949759452271148251498895 23924639178406722377248343)
              ·
                refine ⟨35886958767610083565872515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23924639178406722377248343 35886958767610083565872515)
                ·
                  refine ⟨53830438151415125348808773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35886958767610083565872515 53830438151415125348808773)
                  ·
                    refine ⟨10093207153390336002901645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 53830438151415125348808773 10093207153390336002901645)
                    ·
                      refine ⟨3784952682521376001088117, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10093207153390336002901645 3784952682521376001088117)
                      ·
                        rfl

theorem cell23_7371169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 1, 1, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 1, 1, 1, 1, 1, 4, 3].length) (baseStart_7371169 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7371169 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7371169 prefixEnd_7371169 := by exact prefixLift 7371169
  have htrace : WordTrace (prefixWord ++ tailWord_7371169) baseStart_7371169 baseEnd_7371169 := by
    simpa [prefixWord, tailWord_7371169, baseEnd_7371169] using wordTrace_append hprefix tailTrace_7371169
  have hstable : (prefixWord ++ tailWord_7371169).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7371169).length < 2 ^ (prefixWord ++ tailWord_7371169).sum := by decide
  have hdescent : baseEnd_7371169 < baseStart_7371169 := by decide
  rcases family_descends (prefixWord ++ tailWord_7371169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7371176 : List Nat := [2, 1, 6, 1, 1, 1, 1, 5, 1, 4]
def baseStart_7371176 : Nat := 118140960795 + 7371176 * 2 ^ 59
def prefixEnd_7371176 : Nat := 4983230072969 + 3 ^ 40 * 7371176 * 2
def baseEnd_7371176 : Nat := 1261652092295319157900195

theorem tailTrace_7371176 : CollatzResearch.WordTrace tailWord_7371176 prefixEnd_7371176 1261652092295319157900195 := by
  unfold tailWord_7371176
  simp only [CollatzResearch.WordTrace]
  refine ⟨134424437771747861740014691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 179232583695663815653352921 134424437771747861740014691)
  ·
    refine ⟨201636656657621792610022037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134424437771747861740014691 201636656657621792610022037)
    ·
      refine ⟨9451718280826021528594783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 201636656657621792610022037 9451718280826021528594783)
      ·
        refine ⟨14177577421239032292892175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9451718280826021528594783 14177577421239032292892175)
        ·
          refine ⟨21266366131858548439338263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14177577421239032292892175 21266366131858548439338263)
          ·
            refine ⟨31899549197787822659007395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21266366131858548439338263 31899549197787822659007395)
            ·
              refine ⟨47849323796681733988511093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31899549197787822659007395 47849323796681733988511093)
              ·
                refine ⟨4485874105938912561422915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 47849323796681733988511093 4485874105938912561422915)
                ·
                  refine ⟨6728811158908368842134373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4485874105938912561422915 6728811158908368842134373)
                  ·
                    refine ⟨1261652092295319157900195, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6728811158908368842134373 1261652092295319157900195)
                    ·
                      rfl

theorem cell23_7371176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 1, 1, 5, 1, 4].length) (baseStart_7371176 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7371176 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7371176 prefixEnd_7371176 := by exact prefixLift 7371176
  have htrace : WordTrace (prefixWord ++ tailWord_7371176) baseStart_7371176 baseEnd_7371176 := by
    simpa [prefixWord, tailWord_7371176, baseEnd_7371176] using wordTrace_append hprefix tailTrace_7371176
  have hstable : (prefixWord ++ tailWord_7371176).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7371176).length < 2 ^ (prefixWord ++ tailWord_7371176).sum := by decide
  have hdescent : baseEnd_7371176 < baseStart_7371176 := by decide
  rcases family_descends (prefixWord ++ tailWord_7371176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7371189 : List Nat := [1, 3, 3, 2, 3, 2, 1, 2, 6]
def baseStart_7371189 : Nat := 118140960795 + 7371189 * 2 ^ 59
def prefixEnd_7371189 : Nat := 4983230072969 + 3 ^ 40 * 7371189 * 2
def baseEnd_7371189 : Nat := 420551439126051769204225

theorem tailTrace_7371189 : CollatzResearch.WordTrace tailWord_7371189 prefixEnd_7371189 420551439126051769204225 := by
  unfold tailWord_7371189
  simp only [CollatzResearch.WordTrace]
  refine ⟨268849349692448626700252621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179232899794965751133501747 268849349692448626700252621)
  ·
    refine ⟨100818506134668235012594733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 268849349692448626700252621 100818506134668235012594733)
    ·
      refine ⟨37806939800500588129723025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 100818506134668235012594733 37806939800500588129723025)
      ·
        refine ⟨28355204850375441097292269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37806939800500588129723025 28355204850375441097292269)
        ·
          refine ⟨10633201818890790411484601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28355204850375441097292269 10633201818890790411484601)
          ·
            refine ⟨7974901364168092808613451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10633201818890790411484601 7974901364168092808613451)
            ·
              refine ⟨11962352046252139212920177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7974901364168092808613451 11962352046252139212920177)
              ·
                refine ⟨8971764034689104409690133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11962352046252139212920177 8971764034689104409690133)
                ·
                  refine ⟨420551439126051769204225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8971764034689104409690133 420551439126051769204225)
                  ·
                    rfl

theorem cell23_7371189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 3, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 3, 2, 1, 2, 6].length) (baseStart_7371189 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7371189 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7371189 prefixEnd_7371189 := by exact prefixLift 7371189
  have htrace : WordTrace (prefixWord ++ tailWord_7371189) baseStart_7371189 baseEnd_7371189 := by
    simpa [prefixWord, tailWord_7371189, baseEnd_7371189] using wordTrace_append hprefix tailTrace_7371189
  have hstable : (prefixWord ++ tailWord_7371189).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7371189).length < 2 ^ (prefixWord ++ tailWord_7371189).sum := by decide
  have hdescent : baseEnd_7371189 < baseStart_7371189 := by decide
  rcases family_descends (prefixWord ++ tailWord_7371189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7371192 : List Nat := [2, 1, 2, 1, 2, 2, 1, 3, 4, 3, 2]
def baseStart_7371192 : Nat := 118140960795 + 7371192 * 2 ^ 59
def prefixEnd_7371192 : Nat := 4983230072969 + 3 ^ 40 * 7371192 * 2
def baseEnd_7371192 : Nat := 3784964492576429411100511

theorem tailTrace_7371192 : CollatzResearch.WordTrace tailWord_7371192 prefixEnd_7371192 3784964492576429411100511 := by
  unfold tailWord_7371192
  simp only [CollatzResearch.WordTrace]
  refine ⟨134424729555718879106305915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 179232972740958505475074553 134424729555718879106305915)
  ·
    refine ⟨201637094333578318659458873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134424729555718879106305915 201637094333578318659458873)
    ·
      refine ⟨151227820750183738994594155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 201637094333578318659458873 151227820750183738994594155)
      ·
        refine ⟨226841731125275608491891233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 151227820750183738994594155 226841731125275608491891233)
        ·
          refine ⟨170131298343956706368918425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 226841731125275608491891233 170131298343956706368918425)
          ·
            refine ⟨127598473757967529776688819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 170131298343956706368918425 127598473757967529776688819)
            ·
              refine ⟨191397710636951294665033229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 127598473757967529776688819 191397710636951294665033229)
              ·
                refine ⟨71774141488856735499387461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 191397710636951294665033229 71774141488856735499387461)
                ·
                  refine ⟨13457651529160637906135149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 71774141488856735499387461 13457651529160637906135149)
                  ·
                    refine ⟨5046619323435239214800681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13457651529160637906135149 5046619323435239214800681)
                    ·
                      refine ⟨3784964492576429411100511, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5046619323435239214800681 3784964492576429411100511)
                      ·
                        rfl

theorem cell23_7371192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 1, 3, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 1, 3, 4, 3, 2].length) (baseStart_7371192 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7371192 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7371192 prefixEnd_7371192 := by exact prefixLift 7371192
  have htrace : WordTrace (prefixWord ++ tailWord_7371192) baseStart_7371192 baseEnd_7371192 := by
    simpa [prefixWord, tailWord_7371192, baseEnd_7371192] using wordTrace_append hprefix tailTrace_7371192
  have hstable : (prefixWord ++ tailWord_7371192).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7371192).length < 2 ^ (prefixWord ++ tailWord_7371192).sum := by decide
  have hdescent : baseEnd_7371192 < baseStart_7371192 := by decide
  rcases family_descends (prefixWord ++ tailWord_7371192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7371225 : List Nat := [1, 2, 1, 2, 4, 1, 1, 2, 3, 1, 5]
def baseStart_7371225 : Nat := 118140960795 + 7371225 * 2 ^ 59
def prefixEnd_7371225 : Nat := 4983230072969 + 3 ^ 40 * 7371225 * 2
def baseEnd_7371225 : Nat := 3784981437438027781987859

theorem tailTrace_7371225 : CollatzResearch.WordTrace tailWord_7371225 prefixEnd_7371225 3784981437438027781987859 := by
  unfold tailWord_7371225
  simp only [CollatzResearch.WordTrace]
  refine ⟨268850662720318204848563129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179233775146878803232375419 268850662720318204848563129)
  ·
    refine ⟨201637997040238653636422347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 268850662720318204848563129 201637997040238653636422347)
    ·
      refine ⟨302456995560357980454633521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 201637997040238653636422347 302456995560357980454633521)
      ·
        refine ⟨226842746670268485340975141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 302456995560357980454633521 226842746670268485340975141)
        ·
          refine ⟨42533015000675341001432839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 226842746670268485340975141 42533015000675341001432839)
          ·
            refine ⟨63799522501013011502149259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42533015000675341001432839 63799522501013011502149259)
            ·
              refine ⟨95699283751519517253223889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63799522501013011502149259 95699283751519517253223889)
              ·
                refine ⟨71774462813639637939917917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 95699283751519517253223889 71774462813639637939917917)
                ·
                  refine ⟨26915423555114864227469219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 71774462813639637939917917 26915423555114864227469219)
                  ·
                    refine ⟨40373135332672296341203829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 26915423555114864227469219 40373135332672296341203829)
                    ·
                      refine ⟨3784981437438027781987859, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 40373135332672296341203829 3784981437438027781987859)
                      ·
                        rfl

theorem cell23_7371225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 1, 2, 3, 1, 5].length) (baseStart_7371225 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7371225 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7371225 prefixEnd_7371225 := by exact prefixLift 7371225
  have htrace : WordTrace (prefixWord ++ tailWord_7371225) baseStart_7371225 baseEnd_7371225 := by
    simpa [prefixWord, tailWord_7371225, baseEnd_7371225] using wordTrace_append hprefix tailTrace_7371225
  have hstable : (prefixWord ++ tailWord_7371225).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7371225).length < 2 ^ (prefixWord ++ tailWord_7371225).sum := by decide
  have hdescent : baseEnd_7371225 < baseStart_7371225 := by decide
  rcases family_descends (prefixWord ++ tailWord_7371225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7371242 : List Nat := [3, 1, 3, 1, 3, 1, 1, 3, 1, 1, 5]
def baseStart_7371242 : Nat := 118140960795 + 7371242 * 2 ^ 59
def prefixEnd_7371242 : Nat := 4983230072969 + 3 ^ 40 * 7371242 * 2
def baseEnd_7371242 : Nat := 3784990166609154215475281

theorem tailTrace_7371242 : CollatzResearch.WordTrace tailWord_7371242 prefixEnd_7371242 3784990166609154215475281 := by
  unfold tailWord_7371242
  simp only [CollatzResearch.WordTrace]
  refine ⟨67212820690314154187982995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 179234188507504411167954653 67212820690314154187982995)
  ·
    refine ⟨100819231035471231281974493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67212820690314154187982995 100819231035471231281974493)
    ·
      refine ⟨37807211638301711730740435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 100819231035471231281974493 37807211638301711730740435)
      ·
        refine ⟨56710817457452567596110653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37807211638301711730740435 56710817457452567596110653)
        ·
          refine ⟨21266556546544712848541495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 56710817457452567596110653 21266556546544712848541495)
          ·
            refine ⟨31899834819817069272812243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21266556546544712848541495 31899834819817069272812243)
            ·
              refine ⟨47849752229725603909218365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31899834819817069272812243 47849752229725603909218365)
              ·
                refine ⟨17943657086147101465956887, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 47849752229725603909218365 17943657086147101465956887)
                ·
                  refine ⟨26915485629220652198935331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17943657086147101465956887 26915485629220652198935331)
                  ·
                    refine ⟨40373228443830978298402997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 26915485629220652198935331 40373228443830978298402997)
                    ·
                      refine ⟨3784990166609154215475281, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 40373228443830978298402997 3784990166609154215475281)
                      ·
                        rfl

theorem cell23_7371242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 1, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 1, 1, 3, 1, 1, 5].length) (baseStart_7371242 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7371242 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7371242 prefixEnd_7371242 := by exact prefixLift 7371242
  have htrace : WordTrace (prefixWord ++ tailWord_7371242) baseStart_7371242 baseEnd_7371242 := by
    simpa [prefixWord, tailWord_7371242, baseEnd_7371242] using wordTrace_append hprefix tailTrace_7371242
  have hstable : (prefixWord ++ tailWord_7371242).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7371242).length < 2 ^ (prefixWord ++ tailWord_7371242).sum := by decide
  have hdescent : baseEnd_7371242 < baseStart_7371242 := by decide
  rcases family_descends (prefixWord ++ tailWord_7371242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7371250 : List Nat := [3, 2, 1, 4, 2, 1, 3, 2, 1, 1, 3]
def baseStart_7371250 : Nat := 118140960795 + 7371250 * 2 ^ 59
def prefixEnd_7371250 : Nat := 4983230072969 + 3 ^ 40 * 7371250 * 2
def baseEnd_7371250 : Nat := 3784994274454390184175245

theorem tailTrace_7371250 : CollatzResearch.WordTrace tailWord_7371250 prefixEnd_7371250 3784994274454390184175245 := by
  unfold tailWord_7371250
  simp only [CollatzResearch.WordTrace]
  refine ⟨67212893636306908529555801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 179234383030151756078815469 67212893636306908529555801)
  ·
    refine ⟨50409670227230181397166851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67212893636306908529555801 50409670227230181397166851)
    ·
      refine ⟨75614505340845272095750277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50409670227230181397166851 75614505340845272095750277)
      ·
        refine ⟨14177719751408488517953177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 75614505340845272095750277 14177719751408488517953177)
        ·
          refine ⟨10633289813556366388464883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14177719751408488517953177 10633289813556366388464883)
          ·
            refine ⟨15949934720334549582697325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10633289813556366388464883 15949934720334549582697325)
            ·
              refine ⟨5981225520125456093511497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15949934720334549582697325 5981225520125456093511497)
              ·
                refine ⟨4485919140094092070133623, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5981225520125456093511497 4485919140094092070133623)
                ·
                  refine ⟨6728878710141138105200435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4485919140094092070133623 6728878710141138105200435)
                  ·
                    refine ⟨10093318065211707157800653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6728878710141138105200435 10093318065211707157800653)
                    ·
                      refine ⟨3784994274454390184175245, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10093318065211707157800653 3784994274454390184175245)
                      ·
                        rfl

theorem cell23_7371250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 2, 1, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 2, 1, 3, 2, 1, 1, 3].length) (baseStart_7371250 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7371250 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7371250 prefixEnd_7371250 := by exact prefixLift 7371250
  have htrace : WordTrace (prefixWord ++ tailWord_7371250) baseStart_7371250 baseEnd_7371250 := by
    simpa [prefixWord, tailWord_7371250, baseEnd_7371250] using wordTrace_append hprefix tailTrace_7371250
  have hstable : (prefixWord ++ tailWord_7371250).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7371250).length < 2 ^ (prefixWord ++ tailWord_7371250).sum := by decide
  have hdescent : baseEnd_7371250 < baseStart_7371250 := by decide
  rcases family_descends (prefixWord ++ tailWord_7371250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7371270 : List Nat := [6, 2, 1, 1, 1, 3, 1, 2, 1, 5]
def baseStart_7371270 : Nat := 118140960795 + 7371270 * 2 ^ 59
def prefixEnd_7371270 : Nat := 4983230072969 + 3 ^ 40 * 7371270 * 2
def baseEnd_7371270 : Nat := 1261668181355826701975051

theorem tailTrace_7371270 : CollatzResearch.WordTrace tailWord_7371270 prefixEnd_7371270 1261668181355826701975051 := by
  unfold tailWord_7371270
  simp only [CollatzResearch.WordTrace]
  refine ⟨8401634500161099297935977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 179234869336770118355967509 8401634500161099297935977)
  ·
    refine ⟨6301225875120824473451983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8401634500161099297935977 6301225875120824473451983)
    ·
      refine ⟨9451838812681236710177975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6301225875120824473451983 9451838812681236710177975)
      ·
        refine ⟨14177758219021855065266963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9451838812681236710177975 14177758219021855065266963)
        ·
          refine ⟨21266637328532782597900445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14177758219021855065266963 21266637328532782597900445)
          ·
            refine ⟨7974988998199793474212667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21266637328532782597900445 7974988998199793474212667)
            ·
              refine ⟨11962483497299690211319001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7974988998199793474212667 11962483497299690211319001)
              ·
                refine ⟨8971862622974767658489251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11962483497299690211319001 8971862622974767658489251)
                ·
                  refine ⟨13457793934462151487733877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8971862622974767658489251 13457793934462151487733877)
                  ·
                    refine ⟨1261668181355826701975051, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13457793934462151487733877 1261668181355826701975051)
                    ·
                      rfl

theorem cell23_7371270_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 3, 1, 2, 1, 5].length) (baseStart_7371270 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7371270 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7371270 prefixEnd_7371270 := by exact prefixLift 7371270
  have htrace : WordTrace (prefixWord ++ tailWord_7371270) baseStart_7371270 baseEnd_7371270 := by
    simpa [prefixWord, tailWord_7371270, baseEnd_7371270] using wordTrace_append hprefix tailTrace_7371270
  have hstable : (prefixWord ++ tailWord_7371270).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7371270).length < 2 ^ (prefixWord ++ tailWord_7371270).sum := by decide
  have hdescent : baseEnd_7371270 < baseStart_7371270 := by decide
  rcases family_descends (prefixWord ++ tailWord_7371270) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7371272 : List Nat := [2, 1, 3, 2, 1, 1, 1, 5, 1, 3, 3]
def baseStart_7371272 : Nat := 118140960795 + 7371272 * 2 ^ 59
def prefixEnd_7371272 : Nat := 4983230072969 + 3 ^ 40 * 7371272 * 2
def baseEnd_7371272 : Nat := 3785005571028789098100143

theorem tailTrace_7371272 : CollatzResearch.WordTrace tailWord_7371272 prefixEnd_7371272 3785005571028789098100143 := by
  unfold tailWord_7371272
  simp only [CollatzResearch.WordTrace]
  refine ⟨134426188475573965937762035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 179234917967431954583682713 134426188475573965937762035)
  ·
    refine ⟨201639282713360948906643053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134426188475573965937762035 201639282713360948906643053)
    ·
      refine ⟨75614731017510355839991145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 201639282713360948906643053 75614731017510355839991145)
      ·
        refine ⟨56711048263132766879993359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 75614731017510355839991145 56711048263132766879993359)
        ·
          refine ⟨85066572394699150319990039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56711048263132766879993359 85066572394699150319990039)
          ·
            refine ⟨127599858592048725479985059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85066572394699150319990039 127599858592048725479985059)
            ·
              refine ⟨191399787888073088219977589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 127599858592048725479985059 191399787888073088219977589)
              ·
                refine ⟨17943730114506852020622899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 191399787888073088219977589 17943730114506852020622899)
                ·
                  refine ⟨26915595171760278030934349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17943730114506852020622899 26915595171760278030934349)
                  ·
                    refine ⟨10093348189410104261600381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 26915595171760278030934349 10093348189410104261600381)
                    ·
                      refine ⟨3785005571028789098100143, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10093348189410104261600381 3785005571028789098100143)
                      ·
                        rfl

theorem cell23_7371272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 1, 5, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 1, 5, 1, 3, 3].length) (baseStart_7371272 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7371272 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7371272 prefixEnd_7371272 := by exact prefixLift 7371272
  have htrace : WordTrace (prefixWord ++ tailWord_7371272) baseStart_7371272 baseEnd_7371272 := by
    simpa [prefixWord, tailWord_7371272, baseEnd_7371272] using wordTrace_append hprefix tailTrace_7371272
  have hstable : (prefixWord ++ tailWord_7371272).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7371272).length < 2 ^ (prefixWord ++ tailWord_7371272).sum := by decide
  have hdescent : baseEnd_7371272 < baseStart_7371272 := by decide
  rcases family_descends (prefixWord ++ tailWord_7371272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7371276 : List Nat := [2, 2, 1, 2, 4, 3, 1, 2, 1, 2, 3]
def baseStart_7371276 : Nat := 118140960795 + 7371276 * 2 ^ 59
def prefixEnd_7371276 : Nat := 4983230072969 + 3 ^ 40 * 7371276 * 2
def baseEnd_7371276 : Nat := 3785007624951407082450125

theorem tailTrace_7371276 : CollatzResearch.WordTrace tailWord_7371276 prefixEnd_7371276 3785007624951407082450125 := by
  unfold tailWord_7371276
  simp only [CollatzResearch.WordTrace]
  refine ⟨134426261421566720279334841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 179235015228755627039113121 134426261421566720279334841)
  ·
    refine ⟨100819696066175040209501131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 134426261421566720279334841 100819696066175040209501131)
    ·
      refine ⟨151229544099262560314251697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100819696066175040209501131 151229544099262560314251697)
      ·
        refine ⟨113422158074446920235688773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 151229544099262560314251697 113422158074446920235688773)
        ·
          refine ⟨21266654638958797544191645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 113422158074446920235688773 21266654638958797544191645)
          ·
            refine ⟨7974995489609549079071867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21266654638958797544191645 7974995489609549079071867)
            ·
              refine ⟨11962493234414323618607801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7974995489609549079071867 11962493234414323618607801)
              ·
                refine ⟨8971869925810742713955851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11962493234414323618607801 8971869925810742713955851)
                ·
                  refine ⟨13457804888716114070933777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8971869925810742713955851 13457804888716114070933777)
                  ·
                    refine ⟨10093353666537085553200333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13457804888716114070933777 10093353666537085553200333)
                    ·
                      refine ⟨3785007624951407082450125, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10093353666537085553200333 3785007624951407082450125)
                      ·
                        rfl

theorem cell23_7371276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 3, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 3, 1, 2, 1, 2, 3].length) (baseStart_7371276 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7371276 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7371276 prefixEnd_7371276 := by exact prefixLift 7371276
  have htrace : WordTrace (prefixWord ++ tailWord_7371276) baseStart_7371276 baseEnd_7371276 := by
    simpa [prefixWord, tailWord_7371276, baseEnd_7371276] using wordTrace_append hprefix tailTrace_7371276
  have hstable : (prefixWord ++ tailWord_7371276).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7371276).length < 2 ^ (prefixWord ++ tailWord_7371276).sum := by decide
  have hdescent : baseEnd_7371276 < baseStart_7371276 := by decide
  rcases family_descends (prefixWord ++ tailWord_7371276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7371306 : List Nat := [3, 1, 4, 1, 1, 2, 1, 4, 2, 1, 3]
def baseStart_7371306 : Nat := 118140960795 + 7371306 * 2 ^ 59
def prefixEnd_7371306 : Nat := 4983230072969 + 3 ^ 40 * 7371306 * 2
def baseEnd_7371306 : Nat := 3785023029371041965074987

theorem tailTrace_7371306 : CollatzResearch.WordTrace tailWord_7371306 prefixEnd_7371306 3785023029371041965074987 := by
  unfold tailWord_7371306
  simp only [CollatzResearch.WordTrace]
  refine ⟨67213404258256188920565443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 179235744688683170454841181 67213404258256188920565443)
  ·
    refine ⟨100820106387384283380848165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67213404258256188920565443 100820106387384283380848165)
    ·
      refine ⟨18903769947634553133909031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 100820106387384283380848165 18903769947634553133909031)
      ·
        refine ⟨28355654921451829700863547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18903769947634553133909031 28355654921451829700863547)
        ·
          refine ⟨42533482382177744551295321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28355654921451829700863547 42533482382177744551295321)
          ·
            refine ⟨31900111786633308413471491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42533482382177744551295321 31900111786633308413471491)
            ·
              refine ⟨47850167679949962620207237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31900111786633308413471491 47850167679949962620207237)
              ·
                refine ⟨8971906439990617991288857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 47850167679949962620207237 8971906439990617991288857)
                ·
                  refine ⟨6728929829992963493466643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8971906439990617991288857 6728929829992963493466643)
                  ·
                    refine ⟨10093394744989445240199965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6728929829992963493466643 10093394744989445240199965)
                    ·
                      refine ⟨3785023029371041965074987, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10093394744989445240199965 3785023029371041965074987)
                      ·
                        rfl

theorem cell23_7371306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 2, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 2, 1, 4, 2, 1, 3].length) (baseStart_7371306 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7371306 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7371306 prefixEnd_7371306 := by exact prefixLift 7371306
  have htrace : WordTrace (prefixWord ++ tailWord_7371306) baseStart_7371306 baseEnd_7371306 := by
    simpa [prefixWord, tailWord_7371306, baseEnd_7371306] using wordTrace_append hprefix tailTrace_7371306
  have hstable : (prefixWord ++ tailWord_7371306).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7371306).length < 2 ^ (prefixWord ++ tailWord_7371306).sum := by decide
  have hdescent : baseEnd_7371306 < baseStart_7371306 := by decide
  rcases family_descends (prefixWord ++ tailWord_7371306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7371322 : List Nat := [3, 1, 1, 1, 3, 4, 1, 1, 2, 6]
def baseStart_7371322 : Nat := 118140960795 + 7371322 * 2 ^ 59
def prefixEnd_7371322 : Nat := 4983230072969 + 3 ^ 40 * 7371322 * 2
def baseEnd_7371322 : Nat := 1261677081687171300824971

theorem tailTrace_7371322 : CollatzResearch.WordTrace tailWord_7371322 prefixEnd_7371322 1261677081687171300824971 := by
  unfold tailWord_7371322
  simp only [CollatzResearch.WordTrace]
  refine ⟨67213550150241697603711055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 179236133733977860276562813 67213550150241697603711055)
  ·
    refine ⟨100820325225362546405566583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67213550150241697603711055 100820325225362546405566583)
    ·
      refine ⟨151230487838043819608349875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100820325225362546405566583 151230487838043819608349875)
      ·
        refine ⟨226845731757065729412524813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 151230487838043819608349875 226845731757065729412524813)
        ·
          refine ⟨85067149408899648529696805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 226845731757065729412524813 85067149408899648529696805)
          ·
            refine ⟨15950090514168684099318151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 85067149408899648529696805 15950090514168684099318151)
            ·
              refine ⟨23925135771253026148977227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15950090514168684099318151 23925135771253026148977227)
              ·
                refine ⟨35887703656879539223465841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23925135771253026148977227 35887703656879539223465841)
                ·
                  refine ⟨26915777742659654417599381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35887703656879539223465841 26915777742659654417599381)
                  ·
                    refine ⟨1261677081687171300824971, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26915777742659654417599381 1261677081687171300824971)
                    ·
                      rfl

theorem cell23_7371322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 4, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 4, 1, 1, 2, 6].length) (baseStart_7371322 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7371322 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7371322 prefixEnd_7371322 := by exact prefixLift 7371322
  have htrace : WordTrace (prefixWord ++ tailWord_7371322) baseStart_7371322 baseEnd_7371322 := by
    simpa [prefixWord, tailWord_7371322, baseEnd_7371322] using wordTrace_append hprefix tailTrace_7371322
  have hstable : (prefixWord ++ tailWord_7371322).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7371322).length < 2 ^ (prefixWord ++ tailWord_7371322).sum := by decide
  have hdescent : baseEnd_7371322 < baseStart_7371322 := by decide
  rcases family_descends (prefixWord ++ tailWord_7371322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7371346 : List Nat := [3, 2, 2, 1, 2, 1, 2, 2, 4, 2, 2]
def baseStart_7371346 : Nat := 118140960795 + 7371346 * 2 ^ 59
def prefixEnd_7371346 : Nat := 4983230072969 + 3 ^ 40 * 7371346 * 2
def baseEnd_7371346 : Nat := 3785043568597221808574803

theorem tailTrace_7371346 : CollatzResearch.WordTrace tailWord_7371346 prefixEnd_7371346 3785043568597221808574803 := by
  unfold tailWord_7371346
  simp only [CollatzResearch.WordTrace]
  refine ⟨67213768988219960628429473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 179236717301919895009145261 67213768988219960628429473)
  ·
    refine ⟨50410326741164970471322105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67213768988219960628429473 50410326741164970471322105)
    ·
      refine ⟨37807745055873727853491579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50410326741164970471322105 37807745055873727853491579)
      ·
        refine ⟨56711617583810591780237369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37807745055873727853491579 56711617583810591780237369)
        ·
          refine ⟨42533713187857943835178027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56711617583810591780237369 42533713187857943835178027)
          ·
            refine ⟨63800569781786915752767041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42533713187857943835178027 63800569781786915752767041)
            ·
              refine ⟨47850427336340186814575281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 63800569781786915752767041 47850427336340186814575281)
              ·
                refine ⟨35887820502255140110931461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47850427336340186814575281 35887820502255140110931461)
                ·
                  refine ⟨6728966344172838770799649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 35887820502255140110931461 6728966344172838770799649)
                  ·
                    refine ⟨5046724758129629078099737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6728966344172838770799649 5046724758129629078099737)
                    ·
                      refine ⟨3785043568597221808574803, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5046724758129629078099737 3785043568597221808574803)
                      ·
                        rfl

theorem cell23_7371346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 2, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 2, 2, 4, 2, 2].length) (baseStart_7371346 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7371346 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7371346 prefixEnd_7371346 := by exact prefixLift 7371346
  have htrace : WordTrace (prefixWord ++ tailWord_7371346) baseStart_7371346 baseEnd_7371346 := by
    simpa [prefixWord, tailWord_7371346, baseEnd_7371346] using wordTrace_append hprefix tailTrace_7371346
  have hstable : (prefixWord ++ tailWord_7371346).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7371346).length < 2 ^ (prefixWord ++ tailWord_7371346).sum := by decide
  have hdescent : baseEnd_7371346 < baseStart_7371346 := by decide
  rcases family_descends (prefixWord ++ tailWord_7371346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7371456 : List Nat := [2, 1, 1, 2, 4, 3, 2, 1, 2, 2, 3]
def baseStart_7371456 : Nat := 118140960795 + 7371456 * 2 ^ 59
def prefixEnd_7371456 : Nat := 4983230072969 + 3 ^ 40 * 7371456 * 2
def baseEnd_7371456 : Nat := 3785100051469216378199297

theorem tailTrace_7371456 : CollatzResearch.WordTrace tailWord_7371456 prefixEnd_7371456 3785100051469216378199297 := by
  unfold tailWord_7371456
  simp only [CollatzResearch.WordTrace]
  refine ⟨134429543991240665650111111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 179239391988320887533481481 134429543991240665650111111)
  ·
    refine ⟨201644315986860998475166667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134429543991240665650111111 201644315986860998475166667)
    ·
      refine ⟨302466473980291497712750001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 201644315986860998475166667 302466473980291497712750001)
      ·
        refine ⟨226849855485218623284562501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 302466473980291497712750001 226849855485218623284562501)
        ·
          refine ⟨42534347903478491865855469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 226849855485218623284562501 42534347903478491865855469)
          ·
            refine ⟨15950380463804434449695801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42534347903478491865855469 15950380463804434449695801)
            ·
              refine ⟨11962785347853325837271851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15950380463804434449695801 11962785347853325837271851)
              ·
                refine ⟨17944178021779988755907777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11962785347853325837271851 17944178021779988755907777)
                ·
                  refine ⟨13458133516334991566930833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17944178021779988755907777 13458133516334991566930833)
                  ·
                    refine ⟨10093600137251243675198125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13458133516334991566930833 10093600137251243675198125)
                    ·
                      refine ⟨3785100051469216378199297, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10093600137251243675198125 3785100051469216378199297)
                      ·
                        rfl

theorem cell23_7371456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 3, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 3, 2, 1, 2, 2, 3].length) (baseStart_7371456 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7371456 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7371456 prefixEnd_7371456 := by exact prefixLift 7371456
  have htrace : WordTrace (prefixWord ++ tailWord_7371456) baseStart_7371456 baseEnd_7371456 := by
    simpa [prefixWord, tailWord_7371456, baseEnd_7371456] using wordTrace_append hprefix tailTrace_7371456
  have hstable : (prefixWord ++ tailWord_7371456).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7371456).length < 2 ^ (prefixWord ++ tailWord_7371456).sum := by decide
  have hdescent : baseEnd_7371456 < baseStart_7371456 := by decide
  rcases family_descends (prefixWord ++ tailWord_7371456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7371480 : List Nat := [2, 1, 2, 2, 3, 4, 2, 2, 1, 4]
def baseStart_7371480 : Nat := 118140960795 + 7371480 * 2 ^ 59
def prefixEnd_7371480 : Nat := 4983230072969 + 3 ^ 40 * 7371480 * 2
def baseEnd_7371480 : Nat := 1261704125001641428099729

theorem tailTrace_7371480 : CollatzResearch.WordTrace tailWord_7371480 prefixEnd_7371480 1261704125001641428099729 := by
  unfold tailWord_7371480
  simp only [CollatzResearch.WordTrace]
  refine ⟨134429981667197191699547947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 179239975556262922266063929 134429981667197191699547947)
  ·
    refine ⟨201644972500795787549321921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134429981667197191699547947 201644972500795787549321921)
    ·
      refine ⟨151233729375596840661991441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 201644972500795787549321921 151233729375596840661991441)
      ·
        refine ⟨113425297031697630496493581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 151233729375596840661991441 113425297031697630496493581)
        ·
          refine ⟨42534486386886611436185093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 113425297031697630496493581 42534486386886611436185093)
          ·
            refine ⟨7975216197541239644284705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 42534486386886611436185093 7975216197541239644284705)
            ·
              refine ⟨5981412148155929733213529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7975216197541239644284705 5981412148155929733213529)
              ·
                refine ⟨4486059111116947299910147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5981412148155929733213529 4486059111116947299910147)
                ·
                  refine ⟨6729088666675420949865221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4486059111116947299910147 6729088666675420949865221)
                  ·
                    refine ⟨1261704125001641428099729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6729088666675420949865221 1261704125001641428099729)
                    ·
                      rfl

theorem cell23_7371480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 4, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 4, 2, 2, 1, 4].length) (baseStart_7371480 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7371480 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7371480 prefixEnd_7371480 := by exact prefixLift 7371480
  have htrace : WordTrace (prefixWord ++ tailWord_7371480) baseStart_7371480 baseEnd_7371480 := by
    simpa [prefixWord, tailWord_7371480, baseEnd_7371480] using wordTrace_append hprefix tailTrace_7371480
  have hstable : (prefixWord ++ tailWord_7371480).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7371480).length < 2 ^ (prefixWord ++ tailWord_7371480).sum := by decide
  have hdescent : baseEnd_7371480 < baseStart_7371480 := by decide
  rcases family_descends (prefixWord ++ tailWord_7371480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7371489 : List Nat := [1, 2, 3, 1, 4, 1, 1, 2, 3, 5]
def baseStart_7371489 : Nat := 118140960795 + 7371489 * 2 ^ 59
def prefixEnd_7371489 : Nat := 4983230072969 + 3 ^ 40 * 7371489 * 2
def baseEnd_7371489 : Nat := 1261705665443604916362215

theorem tailTrace_7371489 : CollatzResearch.WordTrace tailWord_7371489 prefixEnd_7371489 1261705665443604916362215 := by
  unfold tailWord_7371489
  simp only [CollatzResearch.WordTrace]
  refine ⟨268860291591361777936173521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179240194394241185290782347 268860291591361777936173521)
  ·
    refine ⟨201645218693521333452130141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 268860291591361777936173521 201645218693521333452130141)
    ·
      refine ⟨75616957010070500044548803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 201645218693521333452130141 75616957010070500044548803)
      ·
        refine ⟨113425435515105750066823205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75616957010070500044548803 113425435515105750066823205)
        ·
          refine ⟨21267269159082328137529351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 113425435515105750066823205 21267269159082328137529351)
          ·
            refine ⟨31900903738623492206294027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21267269159082328137529351 31900903738623492206294027)
            ·
              refine ⟨47851355607935238309441041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31900903738623492206294027 47851355607935238309441041)
              ·
                refine ⟨35888516705951428732080781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47851355607935238309441041 35888516705951428732080781)
                ·
                  refine ⟨13458193764731785774530293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35888516705951428732080781 13458193764731785774530293)
                  ·
                    refine ⟨1261705665443604916362215, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13458193764731785774530293 1261705665443604916362215)
                    ·
                      rfl

theorem cell23_7371489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 1, 1, 2, 3, 5].length) (baseStart_7371489 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7371489 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7371489 prefixEnd_7371489 := by exact prefixLift 7371489
  have htrace : WordTrace (prefixWord ++ tailWord_7371489) baseStart_7371489 baseEnd_7371489 := by
    simpa [prefixWord, tailWord_7371489, baseEnd_7371489] using wordTrace_append hprefix tailTrace_7371489
  have hstable : (prefixWord ++ tailWord_7371489).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7371489).length < 2 ^ (prefixWord ++ tailWord_7371489).sum := by decide
  have hdescent : baseEnd_7371489 < baseStart_7371489 := by decide
  rcases family_descends (prefixWord ++ tailWord_7371489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7371519 : List Nat := [1, 1, 2, 2, 1, 3, 1, 4, 4, 4]
def baseStart_7371519 : Nat := 118140960795 + 7371519 * 2 ^ 59
def prefixEnd_7371519 : Nat := 4983230072969 + 3 ^ 40 * 7371519 * 2
def baseEnd_7371519 : Nat := 1261710800250149877237169

theorem tailTrace_7371519 : CollatzResearch.WordTrace tailWord_7371519 prefixEnd_7371519 1261710800250149877237169 := by
  unfold tailWord_7371519
  simp only [CollatzResearch.WordTrace]
  refine ⟨268861385781253093059765611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179240923854168728706510407 268861385781253093059765611)
  ·
    refine ⟨403292078671879639589648417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 268861385781253093059765611 403292078671879639589648417)
    ·
      refine ⟨302469059003909729692236313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 403292078671879639589648417 302469059003909729692236313)
      ·
        refine ⟨226851794252932297269177235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 302469059003909729692236313 226851794252932297269177235)
        ·
          refine ⟨340277691379398445903765853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 226851794252932297269177235 340277691379398445903765853)
          ·
            refine ⟨127604134267274417213912195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 340277691379398445903765853 127604134267274417213912195)
            ·
              refine ⟨191406201400911625820868293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 127604134267274417213912195 191406201400911625820868293)
              ·
                refine ⟨35888662762670929841412805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 191406201400911625820868293 35888662762670929841412805)
                ·
                  refine ⟨6729124268000799345264901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 35888662762670929841412805 6729124268000799345264901)
                  ·
                    refine ⟨1261710800250149877237169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6729124268000799345264901 1261710800250149877237169)
                    ·
                      rfl

theorem cell23_7371519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 1, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 1, 4, 4, 4].length) (baseStart_7371519 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7371519 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7371519 prefixEnd_7371519 := by exact prefixLift 7371519
  have htrace : WordTrace (prefixWord ++ tailWord_7371519) baseStart_7371519 baseEnd_7371519 := by
    simpa [prefixWord, tailWord_7371519, baseEnd_7371519] using wordTrace_append hprefix tailTrace_7371519
  have hstable : (prefixWord ++ tailWord_7371519).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7371519).length < 2 ^ (prefixWord ++ tailWord_7371519).sum := by decide
  have hdescent : baseEnd_7371519 < baseStart_7371519 := by decide
  rcases family_descends (prefixWord ++ tailWord_7371519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7371553 : List Nat := [1, 2, 3, 2, 1, 2, 5, 1, 2, 4]
def baseStart_7371553 : Nat := 118140960795 + 7371553 * 2 ^ 59
def prefixEnd_7371553 : Nat := 4983230072969 + 3 ^ 40 * 7371553 * 2
def baseEnd_7371553 : Nat := 1261716619697567499562117

theorem tailTrace_7371553 : CollatzResearch.WordTrace tailWord_7371553 prefixEnd_7371553 1261716619697567499562117 := by
  unfold tailWord_7371553
  simp only [CollatzResearch.WordTrace]
  refine ⟨268862625863129916866503313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179241750575419944577668875 268862625863129916866503313)
  ·
    refine ⟨201646969397347437649877485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 268862625863129916866503313 201646969397347437649877485)
    ·
      refine ⟨75617613524005289118704057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 201646969397347437649877485 75617613524005289118704057)
      ·
        refine ⟨56713210143003966839028043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 75617613524005289118704057 56713210143003966839028043)
        ·
          refine ⟨85069815214505950258542065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56713210143003966839028043 85069815214505950258542065)
          ·
            refine ⟨63802361410879462693906549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 85069815214505950258542065 63802361410879462693906549)
            ·
              refine ⟨5981471382269949627553739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 63802361410879462693906549 5981471382269949627553739)
              ·
                refine ⟨8972207073404924441330609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5981471382269949627553739 8972207073404924441330609)
                ·
                  refine ⟨6729155305053693330997957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8972207073404924441330609 6729155305053693330997957)
                  ·
                    refine ⟨1261716619697567499562117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6729155305053693330997957 1261716619697567499562117)
                    ·
                      rfl

theorem cell23_7371553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 5, 1, 2, 4].length) (baseStart_7371553 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7371553 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7371553 prefixEnd_7371553 := by exact prefixLift 7371553
  have htrace : WordTrace (prefixWord ++ tailWord_7371553) baseStart_7371553 baseEnd_7371553 := by
    simpa [prefixWord, tailWord_7371553, baseEnd_7371553] using wordTrace_append hprefix tailTrace_7371553
  have hstable : (prefixWord ++ tailWord_7371553).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7371553).length < 2 ^ (prefixWord ++ tailWord_7371553).sum := by decide
  have hdescent : baseEnd_7371553 < baseStart_7371553 := by decide
  rcases family_descends (prefixWord ++ tailWord_7371553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7371556 : List Nat := [2, 3, 1, 3, 3, 1, 1, 1, 1, 1, 6]
def baseStart_7371556 : Nat := 118140960795 + 7371556 * 2 ^ 59
def prefixEnd_7371556 : Nat := 4983230072969 + 3 ^ 40 * 7371556 * 2
def baseEnd_7371556 : Nat := 3785151399534665986948837

theorem tailTrace_7371556 : CollatzResearch.WordTrace tailWord_7371556 prefixEnd_7371556 3785151399534665986948837 := by
  unfold tailWord_7371556
  simp only [CollatzResearch.WordTrace]
  refine ⟨134431367641059524189431261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 179241823521412698919241681 134431367641059524189431261)
  ·
    refine ⟨50411762865397321571036723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 134431367641059524189431261 50411762865397321571036723)
    ·
      refine ⟨75617644298095982356555085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50411762865397321571036723 75617644298095982356555085)
      ·
        refine ⟨28356616611785993383708157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 75617644298095982356555085 28356616611785993383708157)
        ·
          refine ⟨10633731229419747518890559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28356616611785993383708157 10633731229419747518890559)
          ·
            refine ⟨15950596844129621278335839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10633731229419747518890559 15950596844129621278335839)
            ·
              refine ⟨23925895266194431917503759, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15950596844129621278335839 23925895266194431917503759)
              ·
                refine ⟨35888842899291647876255639, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23925895266194431917503759 35888842899291647876255639)
                ·
                  refine ⟨53833264348937471814383459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35888842899291647876255639 53833264348937471814383459)
                  ·
                    refine ⟨80749896523406207721575189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 53833264348937471814383459 80749896523406207721575189)
                    ·
                      refine ⟨3785151399534665986948837, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 80749896523406207721575189 3785151399534665986948837)
                      ·
                        rfl

theorem cell23_7371556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 3, 1, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 3, 1, 1, 1, 1, 1, 6].length) (baseStart_7371556 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7371556 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7371556 prefixEnd_7371556 := by exact prefixLift 7371556
  have htrace : WordTrace (prefixWord ++ tailWord_7371556) baseStart_7371556 baseEnd_7371556 := by
    simpa [prefixWord, tailWord_7371556, baseEnd_7371556] using wordTrace_append hprefix tailTrace_7371556
  have hstable : (prefixWord ++ tailWord_7371556).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7371556).length < 2 ^ (prefixWord ++ tailWord_7371556).sum := by decide
  have hdescent : baseEnd_7371556 < baseStart_7371556 := by decide
  rcases family_descends (prefixWord ++ tailWord_7371556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7371566 : List Nat := [4, 1, 3, 2, 1, 2, 1, 9]
def baseStart_7371566 : Nat := 118140960795 + 7371566 * 2 ^ 59
def prefixEnd_7371566 : Nat := 4983230072969 + 3 ^ 40 * 7371566 * 2
def baseEnd_7371566 : Nat := 140190982753378183252733

theorem tailTrace_7371566 : CollatzResearch.WordTrace tailWord_7371566 prefixEnd_7371566 140190982753378183252733 := by
  unfold tailWord_7371566
  simp only [CollatzResearch.WordTrace]
  refine ⟨33607887501510352510840819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 179242066674721880057817701 33607887501510352510840819)
  ·
    refine ⟨50411831252265528766261229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33607887501510352510840819 50411831252265528766261229)
    ·
      refine ⟨18904436719599573287347961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 50411831252265528766261229 18904436719599573287347961)
      ·
        refine ⟨14178327539699679965510971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18904436719599573287347961 14178327539699679965510971)
        ·
          refine ⟨21267491309549519948266457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14178327539699679965510971 21267491309549519948266457)
          ·
            refine ⟨15950618482162139961199843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21267491309549519948266457 15950618482162139961199843)
            ·
              refine ⟨23925927723243209941799765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15950618482162139961199843 23925927723243209941799765)
              ·
                refine ⟨140190982753378183252733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 23925927723243209941799765 140190982753378183252733)
                ·
                  rfl

theorem cell23_7371566_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 2, 1, 9].length) (baseStart_7371566 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7371566 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7371566 prefixEnd_7371566 := by exact prefixLift 7371566
  have htrace : WordTrace (prefixWord ++ tailWord_7371566) baseStart_7371566 baseEnd_7371566 := by
    simpa [prefixWord, tailWord_7371566, baseEnd_7371566] using wordTrace_append hprefix tailTrace_7371566
  have hstable : (prefixWord ++ tailWord_7371566).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7371566).length < 2 ^ (prefixWord ++ tailWord_7371566).sum := by decide
  have hdescent : baseEnd_7371566 < baseStart_7371566 := by decide
  rcases family_descends (prefixWord ++ tailWord_7371566) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7371576 : List Nat := [2, 1, 2, 1, 3, 2, 1, 1, 6, 1, 3]
def baseStart_7371576 : Nat := 118140960795 + 7371576 * 2 ^ 59
def prefixEnd_7371576 : Nat := 4983230072969 + 3 ^ 40 * 7371576 * 2
def baseEnd_7371576 : Nat := 3785161669147755908698745

theorem tailTrace_7371576 : CollatzResearch.WordTrace tailWord_7371576 prefixEnd_7371576 3785161669147755908698745 := by
  unfold tailWord_7371576
  simp only [CollatzResearch.WordTrace]
  refine ⟨134431732371023295897295291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 179242309828031061196393721 134431732371023295897295291)
  ·
    refine ⟨201647598556534943845942937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134431732371023295897295291 201647598556534943845942937)
    ·
      refine ⟨151235698917401207884457203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 201647598556534943845942937 151235698917401207884457203)
      ·
        refine ⟨226853548376101811826685805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 151235698917401207884457203 226853548376101811826685805)
        ·
          refine ⟨85070080641038179435007177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 226853548376101811826685805 85070080641038179435007177)
          ·
            refine ⟨63802560480778634576255383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 85070080641038179435007177 63802560480778634576255383)
            ·
              refine ⟨95703840721167951864383075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63802560480778634576255383 95703840721167951864383075)
              ·
                refine ⟨143555761081751927796574613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 95703840721167951864383075 143555761081751927796574613)
                ·
                  refine ⟨6729176300707121615464435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 143555761081751927796574613 6729176300707121615464435)
                  ·
                    refine ⟨10093764451060682423196653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6729176300707121615464435 10093764451060682423196653)
                    ·
                      refine ⟨3785161669147755908698745, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10093764451060682423196653 3785161669147755908698745)
                      ·
                        rfl

theorem cell23_7371576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 1, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 1, 1, 6, 1, 3].length) (baseStart_7371576 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7371576 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7371576 prefixEnd_7371576 := by exact prefixLift 7371576
  have htrace : WordTrace (prefixWord ++ tailWord_7371576) baseStart_7371576 baseEnd_7371576 := by
    simpa [prefixWord, tailWord_7371576, baseEnd_7371576] using wordTrace_append hprefix tailTrace_7371576
  have hstable : (prefixWord ++ tailWord_7371576).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7371576).length < 2 ^ (prefixWord ++ tailWord_7371576).sum := by decide
  have hdescent : baseEnd_7371576 < baseStart_7371576 := by decide
  rcases family_descends (prefixWord ++ tailWord_7371576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7371610 : List Nat := [3, 1, 1, 2, 1, 4, 4, 1, 2, 1, 3]
def baseStart_7371610 : Nat := 118140960795 + 7371610 * 2 ^ 59
def prefixEnd_7371610 : Nat := 4983230072969 + 3 ^ 40 * 7371610 * 2
def baseEnd_7371610 : Nat := 3785179127490008775673589

theorem tailTrace_7371610 : CollatzResearch.WordTrace tailWord_7371610 prefixEnd_7371610 3785179127490008775673589 := by
  unfold tailWord_7371610
  simp only [CollatzResearch.WordTrace]
  refine ⟨67216176205980853900332071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 179243136549282277067552189 67216176205980853900332071)
  ·
    refine ⟨100824264308971280850498107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67216176205980853900332071 100824264308971280850498107)
    ·
      refine ⟨151236396463456921275747161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100824264308971280850498107 151236396463456921275747161)
      ·
        refine ⟨113427297347592690956810371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 151236396463456921275747161 113427297347592690956810371)
        ·
          refine ⟨170140946021389036435215557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 113427297347592690956810371 170140946021389036435215557)
          ·
            refine ⟨31901427379010444331602917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 170140946021389036435215557 31901427379010444331602917)
            ·
              refine ⟨5981517633564458312175547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 31901427379010444331602917 5981517633564458312175547)
              ·
                refine ⟨8972276450346687468263321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5981517633564458312175547 8972276450346687468263321)
                ·
                  refine ⟨6729207337760015601197491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8972276450346687468263321 6729207337760015601197491)
                  ·
                    refine ⟨10093811006640023401796237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6729207337760015601197491 10093811006640023401796237)
                    ·
                      refine ⟨3785179127490008775673589, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10093811006640023401796237 3785179127490008775673589)
                      ·
                        rfl

theorem cell23_7371610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 4, 4, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 4, 4, 1, 2, 1, 3].length) (baseStart_7371610 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7371610 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7371610 prefixEnd_7371610 := by exact prefixLift 7371610
  have htrace : WordTrace (prefixWord ++ tailWord_7371610) baseStart_7371610 baseEnd_7371610 := by
    simpa [prefixWord, tailWord_7371610, baseEnd_7371610] using wordTrace_append hprefix tailTrace_7371610
  have hstable : (prefixWord ++ tailWord_7371610).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7371610).length < 2 ^ (prefixWord ++ tailWord_7371610).sum := by decide
  have hdescent : baseEnd_7371610 < baseStart_7371610 := by decide
  rcases family_descends (prefixWord ++ tailWord_7371610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7371620 : List Nat := [2, 3, 1, 1, 4, 1, 3, 2, 1, 3, 2]
def baseStart_7371620 : Nat := 118140960795 + 7371620 * 2 ^ 59
def prefixEnd_7371620 : Nat := 4983230072969 + 3 ^ 40 * 7371620 * 2
def baseEnd_7371620 : Nat := 3785184262296553736548543

theorem tailTrace_7371620 : CollatzResearch.WordTrace tailWord_7371620 prefixEnd_7371620 3785184262296553736548543 := by
  unfold tailWord_7371620
  simp only [CollatzResearch.WordTrace]
  refine ⟨134432534776943593654596157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 179243379702591458206128209 134432534776943593654596157)
  ·
    refine ⟨50412200541353847620473559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 134432534776943593654596157 50412200541353847620473559)
    ·
      refine ⟨75618300812030771430710339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50412200541353847620473559 75618300812030771430710339)
      ·
        refine ⟨113427451218046157146065509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75618300812030771430710339 113427451218046157146065509)
        ·
          refine ⟨21267647103383654464887283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 113427451218046157146065509 21267647103383654464887283)
          ·
            refine ⟨31901470655075481697330925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21267647103383654464887283 31901470655075481697330925)
            ·
              refine ⟨11963051495653305636499097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31901470655075481697330925 11963051495653305636499097)
              ·
                refine ⟨8972288621739979227374323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11963051495653305636499097 8972288621739979227374323)
                ·
                  refine ⟨13458432932609968841061485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8972288621739979227374323 13458432932609968841061485)
                  ·
                    refine ⟨5046912349728738315398057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13458432932609968841061485 5046912349728738315398057)
                    ·
                      refine ⟨3785184262296553736548543, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5046912349728738315398057 3785184262296553736548543)
                      ·
                        rfl

theorem cell23_7371620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 1, 3, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 1, 3, 2, 1, 3, 2].length) (baseStart_7371620 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7371620 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7371620 prefixEnd_7371620 := by exact prefixLift 7371620
  have htrace : WordTrace (prefixWord ++ tailWord_7371620) baseStart_7371620 baseEnd_7371620 := by
    simpa [prefixWord, tailWord_7371620, baseEnd_7371620] using wordTrace_append hprefix tailTrace_7371620
  have hstable : (prefixWord ++ tailWord_7371620).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7371620).length < 2 ^ (prefixWord ++ tailWord_7371620).sum := by decide
  have hdescent : baseEnd_7371620 < baseStart_7371620 := by decide
  rcases family_descends (prefixWord ++ tailWord_7371620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7371633 : List Nat := [1, 2, 2, 2, 1, 5, 1, 2, 1, 4, 2]
def baseStart_7371633 : Nat := 118140960795 + 7371633 * 2 ^ 59
def prefixEnd_7371633 : Nat := 4983230072969 + 3 ^ 40 * 7371633 * 2
def baseEnd_7371633 : Nat := 3785190937545062185685983

theorem tailTrace_7371633 : CollatzResearch.WordTrace tailWord_7371633 prefixEnd_7371633 3785190937545062185685983 := by
  unfold tailWord_7371633
  simp only [CollatzResearch.WordTrace]
  refine ⟨268865543702840090529415553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179243695801893393686277035 268865543702840090529415553)
  ·
    refine ⟨201649157777130067897061665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 268865543702840090529415553 201649157777130067897061665)
    ·
      refine ⟨151236868332847550922796249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 201649157777130067897061665 151236868332847550922796249)
      ·
        refine ⟨113427651249635663192097187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 151236868332847550922796249 113427651249635663192097187)
        ·
          refine ⟨170141476874453494788145781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 113427651249635663192097187 170141476874453494788145781)
          ·
            refine ⟨15950763456980015136388667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 170141476874453494788145781 15950763456980015136388667)
            ·
              refine ⟨23926145185470022704583001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15950763456980015136388667 23926145185470022704583001)
              ·
                refine ⟨17944608889102517028437251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23926145185470022704583001 17944608889102517028437251)
                ·
                  refine ⟨26916913333653775542655877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17944608889102517028437251 26916913333653775542655877)
                  ·
                    refine ⟨5046921250060082914247977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 26916913333653775542655877 5046921250060082914247977)
                    ·
                      refine ⟨3785190937545062185685983, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5046921250060082914247977 3785190937545062185685983)
                      ·
                        rfl

theorem cell23_7371633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 5, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 5, 1, 2, 1, 4, 2].length) (baseStart_7371633 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7371633 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7371633 prefixEnd_7371633 := by exact prefixLift 7371633
  have htrace : WordTrace (prefixWord ++ tailWord_7371633) baseStart_7371633 baseEnd_7371633 := by
    simpa [prefixWord, tailWord_7371633, baseEnd_7371633] using wordTrace_append hprefix tailTrace_7371633
  have hstable : (prefixWord ++ tailWord_7371633).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7371633).length < 2 ^ (prefixWord ++ tailWord_7371633).sum := by decide
  have hdescent : baseEnd_7371633 < baseStart_7371633 := by decide
  rcases family_descends (prefixWord ++ tailWord_7371633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7371637 : List Nat := [1, 3, 4, 1, 1, 3, 3, 1, 1, 3, 2]
def baseStart_7371637 : Nat := 118140960795 + 7371637 * 2 ^ 59
def prefixEnd_7371637 : Nat := 4983230072969 + 3 ^ 40 * 7371637 * 2
def baseEnd_7371637 : Nat := 3785192991467680170035965

theorem tailTrace_7371637 : CollatzResearch.WordTrace tailWord_7371637 prefixEnd_7371637 3785192991467680170035965 := by
  unfold tailWord_7371637
  simp only [CollatzResearch.WordTrace]
  refine ⟨268865689594825599212561165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179243793063217066141707443 268865689594825599212561165)
  ·
    refine ⟨100824633598059599704710437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 268865689594825599212561165 100824633598059599704710437)
    ·
      refine ⟨18904618799636174944633207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 100824633598059599704710437 18904618799636174944633207)
      ·
        refine ⟨28356928199454262416949811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18904618799636174944633207 28356928199454262416949811)
        ·
          refine ⟨42535392299181393625424717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28356928199454262416949811 42535392299181393625424717)
          ·
            refine ⟨15950772112193022609534269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42535392299181393625424717 15950772112193022609534269)
            ·
              refine ⟨5981539542072383478575351, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15950772112193022609534269 5981539542072383478575351)
              ·
                refine ⟨8972309313108575217863027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5981539542072383478575351 8972309313108575217863027)
                ·
                  refine ⟨13458463969662862826794541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8972309313108575217863027 13458463969662862826794541)
                  ·
                    refine ⟨5046923988623573560047953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13458463969662862826794541 5046923988623573560047953)
                    ·
                      refine ⟨3785192991467680170035965, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5046923988623573560047953 3785192991467680170035965)
                      ·
                        rfl

theorem cell23_7371637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 3, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 3, 3, 1, 1, 3, 2].length) (baseStart_7371637 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7371637 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7371637 prefixEnd_7371637 := by exact prefixLift 7371637
  have htrace : WordTrace (prefixWord ++ tailWord_7371637) baseStart_7371637 baseEnd_7371637 := by
    simpa [prefixWord, tailWord_7371637, baseEnd_7371637] using wordTrace_append hprefix tailTrace_7371637
  have hstable : (prefixWord ++ tailWord_7371637).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7371637).length < 2 ^ (prefixWord ++ tailWord_7371637).sum := by decide
  have hdescent : baseEnd_7371637 < baseStart_7371637 := by decide
  rcases family_descends (prefixWord ++ tailWord_7371637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7371700 : List Nat := [2, 5, 2, 1, 1, 1, 1, 2, 2, 3, 3]
def baseStart_7371700 : Nat := 118140960795 + 7371700 * 2 ^ 59
def prefixEnd_7371700 : Nat := 4983230072969 + 3 ^ 40 * 7371700 * 2
def baseEnd_7371700 : Nat := 3785225340748913423548175

theorem tailTrace_7371700 : CollatzResearch.WordTrace tailWord_7371700 prefixEnd_7371700 3785225340748913423548175 := by
  unfold tailWord_7371700
  simp only [CollatzResearch.WordTrace]
  refine ⟨134433993696798680486052277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 179245324929064907314736369 134433993696798680486052277)
  ·
    refine ⟨12603186909074876295567401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 134433993696798680486052277 12603186909074876295567401)
    ·
      refine ⟨9452390181806157221675551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12603186909074876295567401 9452390181806157221675551)
      ·
        refine ⟨14178585272709235832513327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9452390181806157221675551 14178585272709235832513327)
        ·
          refine ⟨21267877909063853748769991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14178585272709235832513327 21267877909063853748769991)
          ·
            refine ⟨31901816863595780623154987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21267877909063853748769991 31901816863595780623154987)
            ·
              refine ⟨47852725295393670934732481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31901816863595780623154987 47852725295393670934732481)
              ·
                refine ⟨35889543971545253201049361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47852725295393670934732481 35889543971545253201049361)
                ·
                  refine ⟨26917157978658939900787021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35889543971545253201049361 26917157978658939900787021)
                  ·
                    refine ⟨10093934241997102462795133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 26917157978658939900787021 10093934241997102462795133)
                    ·
                      refine ⟨3785225340748913423548175, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10093934241997102462795133 3785225340748913423548175)
                      ·
                        rfl

theorem cell23_7371700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 1, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 1, 1, 2, 2, 3, 3].length) (baseStart_7371700 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7371700 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7371700 prefixEnd_7371700 := by exact prefixLift 7371700
  have htrace : WordTrace (prefixWord ++ tailWord_7371700) baseStart_7371700 baseEnd_7371700 := by
    simpa [prefixWord, tailWord_7371700, baseEnd_7371700] using wordTrace_append hprefix tailTrace_7371700
  have hstable : (prefixWord ++ tailWord_7371700).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7371700).length < 2 ^ (prefixWord ++ tailWord_7371700).sum := by decide
  have hdescent : baseEnd_7371700 < baseStart_7371700 := by decide
  rcases family_descends (prefixWord ++ tailWord_7371700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7371706 : List Nat := [3, 1, 1, 1, 2, 1, 4, 1, 4, 1, 4]
def baseStart_7371706 : Nat := 118140960795 + 7371706 * 2 ^ 59
def prefixEnd_7371706 : Nat := 4983230072969 + 3 ^ 40 * 7371706 * 2
def baseEnd_7371706 : Nat := 3785228421632840400073147

theorem tailTrace_7371706 : CollatzResearch.WordTrace tailWord_7371706 prefixEnd_7371706 3785228421632840400073147 := by
  unfold tailWord_7371706
  simp only [CollatzResearch.WordTrace]
  refine ⟨67217051557893905999205743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 179245470821050415997881981 67217051557893905999205743)
  ·
    refine ⟨100825577336840858998808615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67217051557893905999205743 100825577336840858998808615)
    ·
      refine ⟨151238366005261288498212923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100825577336840858998808615 151238366005261288498212923)
      ·
        refine ⟨226857549007891932747319385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 151238366005261288498212923 226857549007891932747319385)
        ·
          refine ⟨170143161755918949560489539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 226857549007891932747319385 170143161755918949560489539)
          ·
            refine ⟨255214742633878424340734309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 170143161755918949560489539 255214742633878424340734309)
            ·
              refine ⟨47852764243852204563887683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 255214742633878424340734309 47852764243852204563887683)
              ·
                refine ⟨71779146365778306845831525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47852764243852204563887683 71779146365778306845831525)
                ·
                  refine ⟨13458589943583432533593411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 71779146365778306845831525 13458589943583432533593411)
                  ·
                    refine ⟨20187884915375148800390117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13458589943583432533593411 20187884915375148800390117)
                    ·
                      refine ⟨3785228421632840400073147, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20187884915375148800390117 3785228421632840400073147)
                      ·
                        rfl

theorem cell23_7371706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 4, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 4, 1, 4, 1, 4].length) (baseStart_7371706 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7371706 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7371706 prefixEnd_7371706 := by exact prefixLift 7371706
  have htrace : WordTrace (prefixWord ++ tailWord_7371706) baseStart_7371706 baseEnd_7371706 := by
    simpa [prefixWord, tailWord_7371706, baseEnd_7371706] using wordTrace_append hprefix tailTrace_7371706
  have hstable : (prefixWord ++ tailWord_7371706).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7371706).length < 2 ^ (prefixWord ++ tailWord_7371706).sum := by decide
  have hdescent : baseEnd_7371706 < baseStart_7371706 := by decide
  rcases family_descends (prefixWord ++ tailWord_7371706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7371718 : List Nat := [6, 1, 3, 1, 1, 2, 1, 1, 1, 4, 2]
def baseStart_7371718 : Nat := 118140960795 + 7371718 * 2 ^ 59
def prefixEnd_7371718 : Nat := 4983230072969 + 3 ^ 40 * 7371718 * 2
def baseEnd_7371718 : Nat := 3785234583400694353123093

theorem tailTrace_7371718 : CollatzResearch.WordTrace tailWord_7371718 prefixEnd_7371718 3785234583400694353123093 := by
  unfold tailWord_7371718
  simp only [CollatzResearch.WordTrace]
  refine ⟨8402145122110379688945619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 179245762605021433364173205 8402145122110379688945619)
  ·
    refine ⟨12603217683165569533418429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8402145122110379688945619 12603217683165569533418429)
    ·
      refine ⟨4726206631187088575031911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12603217683165569533418429 4726206631187088575031911)
      ·
        refine ⟨7089309946780632862547867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4726206631187088575031911 7089309946780632862547867)
        ·
          refine ⟨10633964920170949293821801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7089309946780632862547867 10633964920170949293821801)
          ·
            refine ⟨7975473690128211970366351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10633964920170949293821801 7975473690128211970366351)
            ·
              refine ⟨11963210535192317955549527, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7975473690128211970366351 11963210535192317955549527)
              ·
                refine ⟨17944815802788476933324291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11963210535192317955549527 17944815802788476933324291)
                ·
                  refine ⟨26917223704182715399986437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17944815802788476933324291 26917223704182715399986437)
                  ·
                    refine ⟨5046979444534259137497457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 26917223704182715399986437 5046979444534259137497457)
                    ·
                      refine ⟨3785234583400694353123093, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5046979444534259137497457 3785234583400694353123093)
                      ·
                        rfl

theorem cell23_7371718_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 1, 2, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 1, 2, 1, 1, 1, 4, 2].length) (baseStart_7371718 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7371718 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7371718 prefixEnd_7371718 := by exact prefixLift 7371718
  have htrace : WordTrace (prefixWord ++ tailWord_7371718) baseStart_7371718 baseEnd_7371718 := by
    simpa [prefixWord, tailWord_7371718, baseEnd_7371718] using wordTrace_append hprefix tailTrace_7371718
  have hstable : (prefixWord ++ tailWord_7371718).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7371718).length < 2 ^ (prefixWord ++ tailWord_7371718).sum := by decide
  have hdescent : baseEnd_7371718 < baseStart_7371718 := by decide
  rcases family_descends (prefixWord ++ tailWord_7371718) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7371723 : List Nat := [1, 1, 1, 1, 3, 5, 2, 1, 2, 4, 2]
def baseStart_7371723 : Nat := 118140960795 + 7371723 * 2 ^ 59
def prefixEnd_7371723 : Nat := 4983230072969 + 3 ^ 40 * 7371723 * 2
def baseEnd_7371723 : Nat := 3785237150803966833560569

theorem tailTrace_7371723 : CollatzResearch.WordTrace tailWord_7371723 prefixEnd_7371723 3785237150803966833560569 := by
  unfold tailWord_7371723
  simp only [CollatzResearch.WordTrace]
  refine ⟨268868826272514035900191823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179245884181676023933461215 268868826272514035900191823)
  ·
    refine ⟨403303239408771053850287735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 268868826272514035900191823 403303239408771053850287735)
    ·
      refine ⟨604954859113156580775431603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 403303239408771053850287735 604954859113156580775431603)
      ·
        refine ⟨907432288669734871163147405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 604954859113156580775431603 907432288669734871163147405)
        ·
          refine ⟨340287108251150576686180277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 907432288669734871163147405 340287108251150576686180277)
          ·
            refine ⟨31901916398545366564329401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 340287108251150576686180277 31901916398545366564329401)
            ·
              refine ⟨23926437298909024923247051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31901916398545366564329401 23926437298909024923247051)
              ·
                refine ⟨35889655948363537384870577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23926437298909024923247051 35889655948363537384870577)
                ·
                  refine ⟨26917241961272653038652933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35889655948363537384870577 26917241961272653038652933)
                  ·
                    refine ⟨5046982867738622444747425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 26917241961272653038652933 5046982867738622444747425)
                    ·
                      refine ⟨3785237150803966833560569, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5046982867738622444747425 3785237150803966833560569)
                      ·
                        rfl

theorem cell23_7371723_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 5, 2, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 5, 2, 1, 2, 4, 2].length) (baseStart_7371723 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7371723 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7371723 prefixEnd_7371723 := by exact prefixLift 7371723
  have htrace : WordTrace (prefixWord ++ tailWord_7371723) baseStart_7371723 baseEnd_7371723 := by
    simpa [prefixWord, tailWord_7371723, baseEnd_7371723] using wordTrace_append hprefix tailTrace_7371723
  have hstable : (prefixWord ++ tailWord_7371723).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7371723).length < 2 ^ (prefixWord ++ tailWord_7371723).sum := by decide
  have hdescent : baseEnd_7371723 < baseStart_7371723 := by decide
  rcases family_descends (prefixWord ++ tailWord_7371723) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7371739 : List Nat := [1, 1, 1, 1, 1, 1, 1, 2, 1, 6, 7]
def baseStart_7371739 : Nat := 118140960795 + 7371739 * 2 ^ 59
def prefixEnd_7371739 : Nat := 4983230072969 + 3 ^ 40 * 7371739 * 2
def baseEnd_7371739 : Nat := 3785245366494438770960495

theorem tailTrace_7371739 : CollatzResearch.WordTrace tailWord_7371739 prefixEnd_7371739 3785245366494438770960495 := by
  unfold tailWord_7371739
  simp only [CollatzResearch.WordTrace]
  refine ⟨268869409840456070632774271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179246273226970713755182847 268869409840456070632774271)
  ·
    refine ⟨403304114760684105949161407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 268869409840456070632774271 403304114760684105949161407)
    ·
      refine ⟨604956172141026158923742111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 403304114760684105949161407 604956172141026158923742111)
      ·
        refine ⟨907434258211539238385613167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 604956172141026158923742111 907434258211539238385613167)
        ·
          refine ⟨1361151387317308857578419751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 907434258211539238385613167 1361151387317308857578419751)
          ·
            refine ⟨2041727080975963286367629627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1361151387317308857578419751 2041727080975963286367629627)
            ·
              refine ⟨3062590621463944929551444441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2041727080975963286367629627 3062590621463944929551444441)
              ·
                refine ⟨2296942966097958697163583331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3062590621463944929551444441 2296942966097958697163583331)
                ·
                  refine ⟨3445414449146938045745374997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2296942966097958697163583331 3445414449146938045745374997)
                  ·
                    refine ⟨161503802303762720894314453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3445414449146938045745374997 161503802303762720894314453)
                    ·
                      refine ⟨3785245366494438770960495, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 161503802303762720894314453 3785245366494438770960495)
                      ·
                        rfl

theorem cell23_7371739_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 6, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 6, 7].length) (baseStart_7371739 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7371739 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7371739 prefixEnd_7371739 := by exact prefixLift 7371739
  have htrace : WordTrace (prefixWord ++ tailWord_7371739) baseStart_7371739 baseEnd_7371739 := by
    simpa [prefixWord, tailWord_7371739, baseEnd_7371739] using wordTrace_append hprefix tailTrace_7371739
  have hstable : (prefixWord ++ tailWord_7371739).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7371739).length < 2 ^ (prefixWord ++ tailWord_7371739).sum := by decide
  have hdescent : baseEnd_7371739 < baseStart_7371739 := by decide
  rcases family_descends (prefixWord ++ tailWord_7371739) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7371764 : List Nat := [2, 6, 2, 1, 1, 1, 1, 1, 1, 2, 5]
def baseStart_7371764 : Nat := 118140960795 + 7371764 * 2 ^ 59
def prefixEnd_7371764 : Nat := 4983230072969 + 3 ^ 40 * 7371764 * 2
def baseEnd_7371764 : Nat := 3785258203510801173147881

theorem tailTrace_7371764 : CollatzResearch.WordTrace tailWord_7371764 prefixEnd_7371764 3785258203510801173147881 := by
  unfold tailWord_7371764
  simp only [CollatzResearch.WordTrace]
  refine ⟨134435160832682749951217173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 179246881110243666601622897 134435160832682749951217173)
  ·
    refine ⟨6301648164032003903963305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 134435160832682749951217173 6301648164032003903963305)
    ·
      refine ⟨4726236123024002927972479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6301648164032003903963305 4726236123024002927972479)
      ·
        refine ⟨7089354184536004391958719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4726236123024002927972479 7089354184536004391958719)
        ·
          refine ⟨10634031276804006587938079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7089354184536004391958719 10634031276804006587938079)
          ·
            refine ⟨15951046915206009881907119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10634031276804006587938079 15951046915206009881907119)
            ·
              refine ⟨23926570372809014822860679, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15951046915206009881907119 23926570372809014822860679)
              ·
                refine ⟨35889855559213522234291019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23926570372809014822860679 35889855559213522234291019)
                ·
                  refine ⟨53834783338820283351436529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35889855559213522234291019 53834783338820283351436529)
                  ·
                    refine ⟨40376087504115212513577397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 53834783338820283351436529 40376087504115212513577397)
                    ·
                      refine ⟨3785258203510801173147881, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 40376087504115212513577397 3785258203510801173147881)
                      ·
                        rfl

theorem cell23_7371764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 1, 1, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 1, 1, 1, 1, 1, 2, 5].length) (baseStart_7371764 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7371764 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7371764 prefixEnd_7371764 := by exact prefixLift 7371764
  have htrace : WordTrace (prefixWord ++ tailWord_7371764) baseStart_7371764 baseEnd_7371764 := by
    simpa [prefixWord, tailWord_7371764, baseEnd_7371764] using wordTrace_append hprefix tailTrace_7371764
  have hstable : (prefixWord ++ tailWord_7371764).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7371764).length < 2 ^ (prefixWord ++ tailWord_7371764).sum := by decide
  have hdescent : baseEnd_7371764 < baseStart_7371764 := by decide
  rcases family_descends (prefixWord ++ tailWord_7371764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7371800 : List Nat := [2, 1, 2, 3, 2, 2, 1, 3, 2, 3, 2]
def baseStart_7371800 : Nat := 118140960795 + 7371800 * 2 ^ 59
def prefixEnd_7371800 : Nat := 4983230072969 + 3 ^ 40 * 7371800 * 2
def baseEnd_7371800 : Nat := 3785276688814363032297715

theorem tailTrace_7371800 : CollatzResearch.WordTrace tailWord_7371800 prefixEnd_7371800 3785276688814363032297715 := by
  unfold tailWord_7371800
  simp only [CollatzResearch.WordTrace]
  refine ⟨134435817346617539025372427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 179247756462156718700496569 134435817346617539025372427)
  ·
    refine ⟨201653726019926308538058641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134435817346617539025372427 201653726019926308538058641)
    ·
      refine ⟨151240294514944731403543981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 201653726019926308538058641 151240294514944731403543981)
      ·
        refine ⟨56715110443104274276328993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 151240294514944731403543981 56715110443104274276328993)
        ·
          refine ⟨42536332832328205707246745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56715110443104274276328993 42536332832328205707246745)
          ·
            refine ⟨31902249624246154280435059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42536332832328205707246745 31902249624246154280435059)
            ·
              refine ⟨47853374436369231420652589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31902249624246154280435059 47853374436369231420652589)
              ·
                refine ⟨17945015413638461782744721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 47853374436369231420652589 17945015413638461782744721)
                ·
                  refine ⟨13458761560228846337058541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17945015413638461782744721 13458761560228846337058541)
                  ·
                    refine ⟨5047035585085817376396953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13458761560228846337058541 5047035585085817376396953)
                    ·
                      refine ⟨3785276688814363032297715, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5047035585085817376396953 3785276688814363032297715)
                      ·
                        rfl

theorem cell23_7371800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 2, 1, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 2, 1, 3, 2, 3, 2].length) (baseStart_7371800 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7371800 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7371800 prefixEnd_7371800 := by exact prefixLift 7371800
  have htrace : WordTrace (prefixWord ++ tailWord_7371800) baseStart_7371800 baseEnd_7371800 := by
    simpa [prefixWord, tailWord_7371800, baseEnd_7371800] using wordTrace_append hprefix tailTrace_7371800
  have hstable : (prefixWord ++ tailWord_7371800).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7371800).length < 2 ^ (prefixWord ++ tailWord_7371800).sum := by decide
  have hdescent : baseEnd_7371800 < baseStart_7371800 := by decide
  rcases family_descends (prefixWord ++ tailWord_7371800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7371830 : List Nat := [5, 1, 2, 1, 1, 2, 1, 2, 3, 1, 4]
def baseStart_7371830 : Nat := 118140960795 + 7371830 * 2 ^ 59
def prefixEnd_7371830 : Nat := 4983230072969 + 3 ^ 40 * 7371830 * 2
def baseEnd_7371830 : Nat := 3785292093233997914922577

theorem tailTrace_7371830 : CollatzResearch.WordTrace tailWord_7371830 prefixEnd_7371830 3785292093233997914922577 := by
  unfold tailWord_7371830
  simp only [CollatzResearch.WordTrace]
  refine ⟨16804545555195399573396059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 179248485922084262116224629 16804545555195399573396059)
  ·
    refine ⟨25206818332793099360094089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16804545555195399573396059 25206818332793099360094089)
    ·
      refine ⟨18905113749594824520070567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25206818332793099360094089 18905113749594824520070567)
      ·
        refine ⟨28357670624392236780105851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18905113749594824520070567 28357670624392236780105851)
        ·
          refine ⟨42536505936588355170158777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28357670624392236780105851 42536505936588355170158777)
          ·
            refine ⟨31902379452441266377619083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42536505936588355170158777 31902379452441266377619083)
            ·
              refine ⟨47853569178661899566428625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31902379452441266377619083 47853569178661899566428625)
              ·
                refine ⟨35890176883996424674821469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47853569178661899566428625 35890176883996424674821469)
                ·
                  refine ⟨13458816331498659253058051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35890176883996424674821469 13458816331498659253058051)
                  ·
                    refine ⟨20188224497247988879587077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13458816331498659253058051 20188224497247988879587077)
                    ·
                      refine ⟨3785292093233997914922577, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20188224497247988879587077 3785292093233997914922577)
                      ·
                        rfl

theorem cell23_7371830_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 2, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 2, 1, 2, 3, 1, 4].length) (baseStart_7371830 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7371830 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7371830 prefixEnd_7371830 := by exact prefixLift 7371830
  have htrace : WordTrace (prefixWord ++ tailWord_7371830) baseStart_7371830 baseEnd_7371830 := by
    simpa [prefixWord, tailWord_7371830, baseEnd_7371830] using wordTrace_append hprefix tailTrace_7371830
  have hstable : (prefixWord ++ tailWord_7371830).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7371830).length < 2 ^ (prefixWord ++ tailWord_7371830).sum := by decide
  have hdescent : baseEnd_7371830 < baseStart_7371830 := by decide
  rcases family_descends (prefixWord ++ tailWord_7371830) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7371843 : List Nat := [1, 1, 1, 3, 1, 2, 6, 1, 1, 2, 4]
def baseStart_7371843 : Nat := 118140960795 + 7371843 * 2 ^ 59
def prefixEnd_7371843 : Nat := 4983230072969 + 3 ^ 40 * 7371843 * 2
def baseEnd_7371843 : Nat := 3785298768482506364060017

theorem tailTrace_7371843 : CollatzResearch.WordTrace tailWord_7371843 prefixEnd_7371843 3785298768482506364060017 := by
  unfold tailWord_7371843
  simp only [CollatzResearch.WordTrace]
  refine ⟨268873203032079296394560183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179248802021386197596373455 268873203032079296394560183)
  ·
    refine ⟨403309804548118944591840275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 268873203032079296394560183 403309804548118944591840275)
    ·
      refine ⟨604964706822178416887760413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 403309804548118944591840275 604964706822178416887760413)
      ·
        refine ⟨226861765058316906332910155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 604964706822178416887760413 226861765058316906332910155)
        ·
          refine ⟨340292647587475359499365233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 226861765058316906332910155 340292647587475359499365233)
          ·
            refine ⟨255219485690606519624523925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 340292647587475359499365233 255219485690606519624523925)
            ·
              refine ⟨11963413391747180607399559, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 255219485690606519624523925 11963413391747180607399559)
              ·
                refine ⟨17945120087620770911099339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11963413391747180607399559 17945120087620770911099339)
                ·
                  refine ⟨26917680131431156366649009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17945120087620770911099339 26917680131431156366649009)
                  ·
                    refine ⟨20188260098573367274986757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26917680131431156366649009 20188260098573367274986757)
                    ·
                      refine ⟨3785298768482506364060017, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20188260098573367274986757 3785298768482506364060017)
                      ·
                        rfl

theorem cell23_7371843_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 6, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 6, 1, 1, 2, 4].length) (baseStart_7371843 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7371843 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7371843 prefixEnd_7371843 := by exact prefixLift 7371843
  have htrace : WordTrace (prefixWord ++ tailWord_7371843) baseStart_7371843 baseEnd_7371843 := by
    simpa [prefixWord, tailWord_7371843, baseEnd_7371843] using wordTrace_append hprefix tailTrace_7371843
  have hstable : (prefixWord ++ tailWord_7371843).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7371843).length < 2 ^ (prefixWord ++ tailWord_7371843).sum := by decide
  have hdescent : baseEnd_7371843 < baseStart_7371843 := by decide
  rcases family_descends (prefixWord ++ tailWord_7371843) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7371847 : List Nat := [1, 1, 4, 1, 3, 3, 1, 2, 3, 2, 2]
def baseStart_7371847 : Nat := 118140960795 + 7371847 * 2 ^ 59
def prefixEnd_7371847 : Nat := 4983230072969 + 3 ^ 40 * 7371847 * 2
def baseEnd_7371847 : Nat := 3785300822405124348409999

theorem tailTrace_7371847 : CollatzResearch.WordTrace tailWord_7371847 prefixEnd_7371847 3785300822405124348409999 := by
  unfold tailWord_7371847
  simp only [CollatzResearch.WordTrace]
  refine ⟨268873348924064805077705795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179248899282709870051803863 268873348924064805077705795)
  ·
    refine ⟨403310023386097207616558693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 268873348924064805077705795 403310023386097207616558693)
    ·
      refine ⟨75620629384893226428104755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 403310023386097207616558693 75620629384893226428104755)
      ·
        refine ⟨113430944077339839642157133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75620629384893226428104755 113430944077339839642157133)
        ·
          refine ⟨42536604029002439865808925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 113430944077339839642157133 42536604029002439865808925)
          ·
            refine ⟨15951226510875914949678347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42536604029002439865808925 15951226510875914949678347)
            ·
              refine ⟨23926839766313872424517521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15951226510875914949678347 23926839766313872424517521)
              ·
                refine ⟨17945129824735404318388141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23926839766313872424517521 17945129824735404318388141)
                ·
                  refine ⟨6729423684275776619395553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17945129824735404318388141 6729423684275776619395553)
                  ·
                    refine ⟨5047067763206832464546665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6729423684275776619395553 5047067763206832464546665)
                    ·
                      refine ⟨3785300822405124348409999, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5047067763206832464546665 3785300822405124348409999)
                      ·
                        rfl

theorem cell23_7371847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 3, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 3, 1, 2, 3, 2, 2].length) (baseStart_7371847 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7371847 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7371847 prefixEnd_7371847 := by exact prefixLift 7371847
  have htrace : WordTrace (prefixWord ++ tailWord_7371847) baseStart_7371847 baseEnd_7371847 := by
    simpa [prefixWord, tailWord_7371847, baseEnd_7371847] using wordTrace_append hprefix tailTrace_7371847
  have hstable : (prefixWord ++ tailWord_7371847).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7371847).length < 2 ^ (prefixWord ++ tailWord_7371847).sum := by decide
  have hdescent : baseEnd_7371847 < baseStart_7371847 := by decide
  rcases family_descends (prefixWord ++ tailWord_7371847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7371864 : List Nat := [2, 1, 2, 2, 1, 3, 4, 3, 1, 2, 2]
def baseStart_7371864 : Nat := 118140960795 + 7371864 * 2 ^ 59
def prefixEnd_7371864 : Nat := 4983230072969 + 3 ^ 40 * 7371864 * 2
def baseEnd_7371864 : Nat := 3785309551576250781897421

theorem tailTrace_7371864 : CollatzResearch.WordTrace tailWord_7371864 prefixEnd_7371864 3785309551576250781897421 := by
  unfold tailWord_7371864
  simp only [CollatzResearch.WordTrace]
  refine ⟨134436984482501608490537323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 179249312643335477987383097 134436984482501608490537323)
  ·
    refine ⟨201655476723752412735805985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134436984482501608490537323 201655476723752412735805985)
    ·
      refine ⟨151241607542814309551854489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 201655476723752412735805985 151241607542814309551854489)
      ·
        refine ⟨113431205657110732163890867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 151241607542814309551854489 113431205657110732163890867)
        ·
          refine ⟨170146808485666098245836301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 113431205657110732163890867 170146808485666098245836301)
          ·
            refine ⟨63805053182124786842188613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 170146808485666098245836301 63805053182124786842188613)
            ·
              refine ⟨11963447471648397532910365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 63805053182124786842188613 11963447471648397532910365)
              ·
                refine ⟨4486292801868149074841387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11963447471648397532910365 4486292801868149074841387)
                ·
                  refine ⟨6729439202802223612262081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4486292801868149074841387 6729439202802223612262081)
                  ·
                    refine ⟨5047079402101667709196561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6729439202802223612262081 5047079402101667709196561)
                    ·
                      refine ⟨3785309551576250781897421, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5047079402101667709196561 3785309551576250781897421)
                      ·
                        rfl

theorem cell23_7371864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 4, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 4, 3, 1, 2, 2].length) (baseStart_7371864 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7371864 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7371864 prefixEnd_7371864 := by exact prefixLift 7371864
  have htrace : WordTrace (prefixWord ++ tailWord_7371864) baseStart_7371864 baseEnd_7371864 := by
    simpa [prefixWord, tailWord_7371864, baseEnd_7371864] using wordTrace_append hprefix tailTrace_7371864
  have hstable : (prefixWord ++ tailWord_7371864).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7371864).length < 2 ^ (prefixWord ++ tailWord_7371864).sum := by decide
  have hdescent : baseEnd_7371864 < baseStart_7371864 := by decide
  rcases family_descends (prefixWord ++ tailWord_7371864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7371866 : List Nat := [3, 1, 1, 2, 1, 1, 2, 2, 1, 9]
def baseStart_7371866 : Nat := 118140960795 + 7371866 * 2 ^ 59
def prefixEnd_7371866 : Nat := 4983230072969 + 3 ^ 40 * 7371866 * 2
def baseEnd_7371866 : Nat := 1261770192845853258024137

theorem tailTrace_7371866 : CollatzResearch.WordTrace tailWord_7371866 prefixEnd_7371866 1261770192845853258024137 := by
  unfold tailWord_7371866
  simp only [CollatzResearch.WordTrace]
  refine ⟨67218510477748992830661863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 179249361273997314215098301 67218510477748992830661863)
  ·
    refine ⟨100827765716623489245992795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67218510477748992830661863 100827765716623489245992795)
    ·
      refine ⟨151241648574935233868989193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100827765716623489245992795 151241648574935233868989193)
      ·
        refine ⟨113431236431201425401741895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 151241648574935233868989193 113431236431201425401741895)
        ·
          refine ⟨170146854646802138102612843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 113431236431201425401741895 170146854646802138102612843)
          ·
            refine ⟨255220281970203207153919265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 170146854646802138102612843 255220281970203207153919265)
            ·
              refine ⟨191415211477652405365439449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 255220281970203207153919265 191415211477652405365439449)
              ·
                refine ⟨143561408608239304024079587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 191415211477652405365439449 143561408608239304024079587)
                ·
                  refine ⟨215342112912358956036119381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 143561408608239304024079587 215342112912358956036119381)
                  ·
                    refine ⟨1261770192845853258024137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 215342112912358956036119381 1261770192845853258024137)
                    ·
                      rfl

theorem cell23_7371866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 2, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 2, 2, 1, 9].length) (baseStart_7371866 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7371866 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7371866 prefixEnd_7371866 := by exact prefixLift 7371866
  have htrace : WordTrace (prefixWord ++ tailWord_7371866) baseStart_7371866 baseEnd_7371866 := by
    simpa [prefixWord, tailWord_7371866, baseEnd_7371866] using wordTrace_append hprefix tailTrace_7371866
  have hstable : (prefixWord ++ tailWord_7371866).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7371866).length < 2 ^ (prefixWord ++ tailWord_7371866).sum := by decide
  have hdescent : baseEnd_7371866 < baseStart_7371866 := by decide
  rcases family_descends (prefixWord ++ tailWord_7371866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7371874 : List Nat := [3, 3, 2, 2, 1, 3, 1, 2, 2, 4]
def baseStart_7371874 : Nat := 118140960795 + 7371874 * 2 ^ 59
def prefixEnd_7371874 : Nat := 4983230072969 + 3 ^ 40 * 7371874 * 2
def baseEnd_7371874 : Nat := 1261771562127598580924125

theorem tailTrace_7371874 : CollatzResearch.WordTrace tailWord_7371874 prefixEnd_7371874 1261771562127598580924125 := by
  unfold tailWord_7371874
  simp only [CollatzResearch.WordTrace]
  refine ⟨67218583423741747172234669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 179249555796644659125959117 67218583423741747172234669)
  ·
    refine ⟨25206968783903155189588001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 67218583423741747172234669 25206968783903155189588001)
    ·
      refine ⟨18905226587927366392191001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25206968783903155189588001 18905226587927366392191001)
      ·
        refine ⟨14178919940945524794143251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18905226587927366392191001 14178919940945524794143251)
        ·
          refine ⟨21268379911418287191214877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14178919940945524794143251 21268379911418287191214877)
          ·
            refine ⟨7975642466781857696705579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21268379911418287191214877 7975642466781857696705579)
            ·
              refine ⟨11963463700172786545058369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7975642466781857696705579 11963463700172786545058369)
              ·
                refine ⟨8972597775129589908793777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11963463700172786545058369 8972597775129589908793777)
                ·
                  refine ⟨6729448331347192431595333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8972597775129589908793777 6729448331347192431595333)
                  ·
                    refine ⟨1261771562127598580924125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6729448331347192431595333 1261771562127598580924125)
                    ·
                      rfl

theorem cell23_7371874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 3, 1, 2, 2, 4].length) (baseStart_7371874 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7371874 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7371874 prefixEnd_7371874 := by exact prefixLift 7371874
  have htrace : WordTrace (prefixWord ++ tailWord_7371874) baseStart_7371874 baseEnd_7371874 := by
    simpa [prefixWord, tailWord_7371874, baseEnd_7371874] using wordTrace_append hprefix tailTrace_7371874
  have hstable : (prefixWord ++ tailWord_7371874).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7371874).length < 2 ^ (prefixWord ++ tailWord_7371874).sum := by decide
  have hdescent : baseEnd_7371874 < baseStart_7371874 := by decide
  rcases family_descends (prefixWord ++ tailWord_7371874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7371897 : List Nat := [1, 2, 1, 3, 5, 2, 1, 1, 1, 3, 3]
def baseStart_7371897 : Nat := 118140960795 + 7371897 * 2 ^ 59
def prefixEnd_7371897 : Nat := 4983230072969 + 3 ^ 40 * 7371897 * 2
def baseEnd_7371897 : Nat := 3785326496437849152784769

theorem tailTrace_7371897 : CollatzResearch.WordTrace tailWord_7371897 prefixEnd_7371897 3785326496437849152784769 := by
  unfold tailWord_7371897
  simp only [CollatzResearch.WordTrace]
  refine ⟨268875172573883663617025945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179250115049255775744683963 268875172573883663617025945)
  ·
    refine ⟨201656379430412747712769459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 268875172573883663617025945 201656379430412747712769459)
    ·
      refine ⟨302484569145619121569154189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 201656379430412747712769459 302484569145619121569154189)
      ·
        refine ⟨113431713429607170588432821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 302484569145619121569154189 113431713429607170588432821)
        ·
          refine ⟨10634223134025672242665577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 113431713429607170588432821 10634223134025672242665577)
          ·
            refine ⟨7975667350519254181999183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10634223134025672242665577 7975667350519254181999183)
            ·
              refine ⟨11963501025778881272998775, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7975667350519254181999183 11963501025778881272998775)
              ·
                refine ⟨17945251538668321909498163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11963501025778881272998775 17945251538668321909498163)
                ·
                  refine ⟨26917877308002482864247245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17945251538668321909498163 26917877308002482864247245)
                  ·
                    refine ⟨10094203990500931074092717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 26917877308002482864247245 10094203990500931074092717)
                    ·
                      refine ⟨3785326496437849152784769, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10094203990500931074092717 3785326496437849152784769)
                      ·
                        rfl

theorem cell23_7371897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 5, 2, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 5, 2, 1, 1, 1, 3, 3].length) (baseStart_7371897 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7371897 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7371897 prefixEnd_7371897 := by exact prefixLift 7371897
  have htrace : WordTrace (prefixWord ++ tailWord_7371897) baseStart_7371897 baseEnd_7371897 := by
    simpa [prefixWord, tailWord_7371897, baseEnd_7371897] using wordTrace_append hprefix tailTrace_7371897
  have hstable : (prefixWord ++ tailWord_7371897).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7371897).length < 2 ^ (prefixWord ++ tailWord_7371897).sum := by decide
  have hdescent : baseEnd_7371897 < baseStart_7371897 := by decide
  rcases family_descends (prefixWord ++ tailWord_7371897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7371907 : List Nat := [1, 1, 1, 3, 3, 2, 4, 2, 1, 3, 2]
def baseStart_7371907 : Nat := 118140960795 + 7371907 * 2 ^ 59
def prefixEnd_7371907 : Nat := 4983230072969 + 3 ^ 40 * 7371907 * 2
def baseEnd_7371907 : Nat := 3785331631244394113659723

theorem tailTrace_7371907 : CollatzResearch.WordTrace tailWord_7371907 prefixEnd_7371907 3785331631244394113659723 := by
  unfold tailWord_7371907
  simp only [CollatzResearch.WordTrace]
  refine ⟨268875537303847435324889975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179250358202564956883259983 268875537303847435324889975)
  ·
    refine ⟨403313305955771152987334963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 268875537303847435324889975 403313305955771152987334963)
    ·
      refine ⟨604969958933656729481002445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 403313305955771152987334963 604969958933656729481002445)
      ·
        refine ⟨226863734600121273555375917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 604969958933656729481002445 226863734600121273555375917)
        ·
          refine ⟨85073900475045477583265969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 226863734600121273555375917 85073900475045477583265969)
          ·
            refine ⟨63805425356284108187449477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 85073900475045477583265969 63805425356284108187449477)
            ·
              refine ⟨11963517254303270285146777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 63805425356284108187449477 11963517254303270285146777)
              ·
                refine ⟨8972637940727452713860083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11963517254303270285146777 8972637940727452713860083)
                ·
                  refine ⟨13458956911091179070790125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8972637940727452713860083 13458956911091179070790125)
                  ·
                    refine ⟨5047108841659192151546297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13458956911091179070790125 5047108841659192151546297)
                    ·
                      refine ⟨3785331631244394113659723, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5047108841659192151546297 3785331631244394113659723)
                      ·
                        rfl

theorem cell23_7371907_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 4, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 4, 2, 1, 3, 2].length) (baseStart_7371907 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7371907 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7371907 prefixEnd_7371907 := by exact prefixLift 7371907
  have htrace : WordTrace (prefixWord ++ tailWord_7371907) baseStart_7371907 baseEnd_7371907 := by
    simpa [prefixWord, tailWord_7371907, baseEnd_7371907] using wordTrace_append hprefix tailTrace_7371907
  have hstable : (prefixWord ++ tailWord_7371907).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7371907).length < 2 ^ (prefixWord ++ tailWord_7371907).sum := by decide
  have hdescent : baseEnd_7371907 < baseStart_7371907 := by decide
  rcases family_descends (prefixWord ++ tailWord_7371907) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7371937 : List Nat := [1, 2, 3, 3, 1, 1, 1, 3, 4, 2, 2]
def baseStart_7371937 : Nat := 118140960795 + 7371937 * 2 ^ 59
def prefixEnd_7371937 : Nat := 4983230072969 + 3 ^ 40 * 7371937 * 2
def baseEnd_7371937 : Nat := 3785347035664028996284585

theorem tailTrace_7371937 : CollatzResearch.WordTrace tailWord_7371937 prefixEnd_7371937 3785347035664028996284585 := by
  unfold tailWord_7371937
  simp only [CollatzResearch.WordTrace]
  refine ⟨268876631493738750448482065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179251087662492500298988043 268876631493738750448482065)
  ·
    refine ⟨201657473620304062836361549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 268876631493738750448482065 201657473620304062836361549)
    ·
      refine ⟨75621552607614023563635581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 201657473620304062836361549 75621552607614023563635581)
      ·
        refine ⟨28358082227855258836363343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 75621552607614023563635581 28358082227855258836363343)
        ·
          refine ⟨42537123341782888254545015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28358082227855258836363343 42537123341782888254545015)
          ·
            refine ⟨63805685012674332381817523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42537123341782888254545015 63805685012674332381817523)
            ·
              refine ⟨95708527519011498572726285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63805685012674332381817523 95708527519011498572726285)
              ·
                refine ⟨35890697819629311964772357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 95708527519011498572726285 35890697819629311964772357)
                ·
                  refine ⟨6729505841180495993394817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 35890697819629311964772357 6729505841180495993394817)
                  ·
                    refine ⟨5047129380885371995046113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6729505841180495993394817 5047129380885371995046113)
                    ·
                      refine ⟨3785347035664028996284585, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5047129380885371995046113 3785347035664028996284585)
                      ·
                        rfl

theorem cell23_7371937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 1, 3, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 1, 3, 4, 2, 2].length) (baseStart_7371937 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7371937 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7371937 prefixEnd_7371937 := by exact prefixLift 7371937
  have htrace : WordTrace (prefixWord ++ tailWord_7371937) baseStart_7371937 baseEnd_7371937 := by
    simpa [prefixWord, tailWord_7371937, baseEnd_7371937] using wordTrace_append hprefix tailTrace_7371937
  have hstable : (prefixWord ++ tailWord_7371937).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7371937).length < 2 ^ (prefixWord ++ tailWord_7371937).sum := by decide
  have hdescent : baseEnd_7371937 < baseStart_7371937 := by decide
  rcases family_descends (prefixWord ++ tailWord_7371937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7371954 : List Nat := [3, 2, 1, 1, 1, 5, 1, 3, 2, 2, 2]
def baseStart_7371954 : Nat := 118140960795 + 7371954 * 2 ^ 59
def prefixEnd_7371954 : Nat := 4983230072969 + 3 ^ 40 * 7371954 * 2
def baseEnd_7371954 : Nat := 3785355764835155429772007

theorem tailTrace_7371954 : CollatzResearch.WordTrace tailWord_7371954 prefixEnd_7371954 3785355764835155429772007 := by
  unfold tailWord_7371954
  simp only [CollatzResearch.WordTrace]
  refine ⟨67219312883669290587962729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 179251501023118108234567277 67219312883669290587962729)
  ·
    refine ⟨50414484662751967940972047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67219312883669290587962729 50414484662751967940972047)
    ·
      refine ⟨75621726994127951911458071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50414484662751967940972047 75621726994127951911458071)
      ·
        refine ⟨113432590491191927867187107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75621726994127951911458071 113432590491191927867187107)
        ·
          refine ⟨170148885736787891800780661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 113432590491191927867187107 170148885736787891800780661)
          ·
            refine ⟨15951458037823864856323187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 170148885736787891800780661 15951458037823864856323187)
            ·
              refine ⟨23927187056735797284484781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15951458037823864856323187 23927187056735797284484781)
              ·
                refine ⟨8972695146275923981681793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23927187056735797284484781 8972695146275923981681793)
                ·
                  refine ⟨6729521359706942986261345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8972695146275923981681793 6729521359706942986261345)
                  ·
                    refine ⟨5047141019780207239696009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6729521359706942986261345 5047141019780207239696009)
                    ·
                      refine ⟨3785355764835155429772007, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5047141019780207239696009 3785355764835155429772007)
                      ·
                        rfl

theorem cell23_7371954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 5, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 5, 1, 3, 2, 2, 2].length) (baseStart_7371954 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7371954 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7371954 prefixEnd_7371954 := by exact prefixLift 7371954
  have htrace : WordTrace (prefixWord ++ tailWord_7371954) baseStart_7371954 baseEnd_7371954 := by
    simpa [prefixWord, tailWord_7371954, baseEnd_7371954] using wordTrace_append hprefix tailTrace_7371954
  have hstable : (prefixWord ++ tailWord_7371954).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7371954).length < 2 ^ (prefixWord ++ tailWord_7371954).sum := by decide
  have hdescent : baseEnd_7371954 < baseStart_7371954 := by decide
  rcases family_descends (prefixWord ++ tailWord_7371954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7371988 : List Nat := [2, 4, 1, 4, 1, 1, 2, 2, 2, 2, 2]
def baseStart_7371988 : Nat := 118140960795 + 7371988 * 2 ^ 59
def prefixEnd_7371988 : Nat := 4983230072969 + 3 ^ 40 * 7371988 * 2
def baseEnd_7371988 : Nat := 3785373223177408296746851

theorem tailTrace_7371988 : CollatzResearch.WordTrace tailWord_7371988 prefixEnd_7371988 3785373223177408296746851 := by
  unfold tailWord_7371988
  simp only [CollatzResearch.WordTrace]
  refine ⟨134439245808276993079294309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 179252327744369324105725745 134439245808276993079294309)
  ·
    refine ⟨25207358589051936202367683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 134439245808276993079294309 25207358589051936202367683)
    ·
      refine ⟨37811037883577904303551525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25207358589051936202367683 37811037883577904303551525)
      ·
        refine ⟨7089569603170857056915911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 37811037883577904303551525 7089569603170857056915911)
        ·
          refine ⟨10634354404756285585373867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7089569603170857056915911 10634354404756285585373867)
          ·
            refine ⟨15951531607134428378060801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10634354404756285585373867 15951531607134428378060801)
            ·
              refine ⟨11963648705350821283545601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15951531607134428378060801 11963648705350821283545601)
              ·
                refine ⟨8972736529013115962659201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11963648705350821283545601 8972736529013115962659201)
                ·
                  refine ⟨6729552396759836971994401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8972736529013115962659201 6729552396759836971994401)
                  ·
                    refine ⟨5047164297569877728995801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6729552396759836971994401 5047164297569877728995801)
                    ·
                      refine ⟨3785373223177408296746851, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5047164297569877728995801 3785373223177408296746851)
                      ·
                        rfl

theorem cell23_7371988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 1, 1, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 1, 1, 2, 2, 2, 2, 2].length) (baseStart_7371988 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7371988 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7371988 prefixEnd_7371988 := by exact prefixLift 7371988
  have htrace : WordTrace (prefixWord ++ tailWord_7371988) baseStart_7371988 baseEnd_7371988 := by
    simpa [prefixWord, tailWord_7371988, baseEnd_7371988] using wordTrace_append hprefix tailTrace_7371988
  have hstable : (prefixWord ++ tailWord_7371988).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7371988).length < 2 ^ (prefixWord ++ tailWord_7371988).sum := by decide
  have hdescent : baseEnd_7371988 < baseStart_7371988 := by decide
  rcases family_descends (prefixWord ++ tailWord_7371988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7371993 : List Nat := [1, 2, 1, 2, 3, 1, 1, 2, 3, 3, 4]
def baseStart_7371993 : Nat := 118140960795 + 7371993 * 2 ^ 59
def prefixEnd_7371993 : Nat := 4983230072969 + 3 ^ 40 * 7371993 * 2
def baseEnd_7371993 : Nat := 3785375790580680777184327

theorem tailTrace_7371993 : CollatzResearch.WordTrace tailWord_7371993 prefixEnd_7371993 3785375790580680777184327 := by
  unfold tailWord_7371993
  simp only [CollatzResearch.WordTrace]
  refine ⟨268878673981535872012520633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179252449321023914675013755 268878673981535872012520633)
  ·
    refine ⟨201659005486151904009390475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 268878673981535872012520633 201659005486151904009390475)
    ·
      refine ⟨302488508229227856014085713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 201659005486151904009390475 302488508229227856014085713)
      ·
        refine ⟨226866381171920892010564285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 302488508229227856014085713 226866381171920892010564285)
        ·
          refine ⟨85074892939470334503961607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 226866381171920892010564285 85074892939470334503961607)
          ·
            refine ⟨127612339409205501755942411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85074892939470334503961607 127612339409205501755942411)
            ·
              refine ⟨191418509113808252633913617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 127612339409205501755942411 191418509113808252633913617)
              ·
                refine ⟨143563881835356189475435213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 191418509113808252633913617 143563881835356189475435213)
                ·
                  refine ⟨53836455688258571053288205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 143563881835356189475435213 53836455688258571053288205)
                  ·
                    refine ⟨20188670883096964144983077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 53836455688258571053288205 20188670883096964144983077)
                    ·
                      refine ⟨3785375790580680777184327, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20188670883096964144983077 3785375790580680777184327)
                      ·
                        rfl

theorem cell23_7371993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 1, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 1, 2, 3, 3, 4].length) (baseStart_7371993 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7371993 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7371993 prefixEnd_7371993 := by exact prefixLift 7371993
  have htrace : WordTrace (prefixWord ++ tailWord_7371993) baseStart_7371993 baseEnd_7371993 := by
    simpa [prefixWord, tailWord_7371993, baseEnd_7371993] using wordTrace_append hprefix tailTrace_7371993
  have hstable : (prefixWord ++ tailWord_7371993).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7371993).length < 2 ^ (prefixWord ++ tailWord_7371993).sum := by decide
  have hdescent : baseEnd_7371993 < baseStart_7371993 := by decide
  rcases family_descends (prefixWord ++ tailWord_7371993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7372023 : List Nat := [1, 1, 3, 1, 1, 1, 2, 3, 2, 4, 4]
def baseStart_7372023 : Nat := 118140960795 + 7372023 * 2 ^ 59
def prefixEnd_7372023 : Nat := 4983230072969 + 3 ^ 40 * 7372023 * 2
def baseEnd_7372023 : Nat := 3785391195000315659809189

theorem tailTrace_7372023 : CollatzResearch.WordTrace tailWord_7372023 prefixEnd_7372023 3785391195000315659809189 := by
  unfold tailWord_7372023
  simp only [CollatzResearch.WordTrace]
  refine ⟨268879768171427187136112723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179253178780951458090741815 268879768171427187136112723)
  ·
    refine ⟨403319652257140780704169085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 268879768171427187136112723 403319652257140780704169085)
    ·
      refine ⟨151244869596427792764063407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 403319652257140780704169085 151244869596427792764063407)
      ·
        refine ⟨226867304394641689146095111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 151244869596427792764063407 226867304394641689146095111)
        ·
          refine ⟨340300956591962533719142667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 226867304394641689146095111 340300956591962533719142667)
          ·
            refine ⟨510451434887943800578714001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 340300956591962533719142667 510451434887943800578714001)
            ·
              refine ⟨382838576165957850434035501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 510451434887943800578714001 382838576165957850434035501)
              ·
                refine ⟨143564466062234193912763313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 382838576165957850434035501 143564466062234193912763313)
                ·
                  refine ⟨107673349546675645434572485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 143564466062234193912763313 107673349546675645434572485)
                  ·
                    refine ⟨20188753040001683518982341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 107673349546675645434572485 20188753040001683518982341)
                    ·
                      refine ⟨3785391195000315659809189, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20188753040001683518982341 3785391195000315659809189)
                      ·
                        rfl

theorem cell23_7372023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 2, 3, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 2, 3, 2, 4, 4].length) (baseStart_7372023 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7372023 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7372023 prefixEnd_7372023 := by exact prefixLift 7372023
  have htrace : WordTrace (prefixWord ++ tailWord_7372023) baseStart_7372023 baseEnd_7372023 := by
    simpa [prefixWord, tailWord_7372023, baseEnd_7372023] using wordTrace_append hprefix tailTrace_7372023
  have hstable : (prefixWord ++ tailWord_7372023).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7372023).length < 2 ^ (prefixWord ++ tailWord_7372023).sum := by decide
  have hdescent : baseEnd_7372023 < baseStart_7372023 := by decide
  rcases family_descends (prefixWord ++ tailWord_7372023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7372067 : List Nat := [1, 1, 1, 4, 2, 4, 3, 1, 6]
def baseStart_7372067 : Nat := 118140960795 + 7372067 * 2 ^ 59
def prefixEnd_7372067 : Nat := 4983230072969 + 3 ^ 40 * 7372067 * 2
def baseEnd_7372067 : Nat := 420601532016568165295443

theorem tailTrace_7372067 : CollatzResearch.WordTrace tailWord_7372067 prefixEnd_7372067 420601532016568165295443 := by
  unfold tailWord_7372067
  simp only [CollatzResearch.WordTrace]
  refine ⟨268881372983267782650714455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179254248655511855100476303 268881372983267782650714455)
  ·
    refine ⟨403322059474901673976071683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 268881372983267782650714455 403322059474901673976071683)
    ·
      refine ⟨604983089212352510964107525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 403322059474901673976071683 604983089212352510964107525)
      ·
        refine ⟨113434329227316095805770161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 604983089212352510964107525 113434329227316095805770161)
        ·
          refine ⟨85075746920487071854327621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 113434329227316095805770161 85075746920487071854327621)
          ·
            refine ⟨15951702547591325972686429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 85075746920487071854327621 15951702547591325972686429)
            ·
              refine ⟨5981888455346747239757411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15951702547591325972686429 5981888455346747239757411)
              ·
                refine ⟨8972832683020120859636117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5981888455346747239757411 8972832683020120859636117)
                ·
                  refine ⟨420601532016568165295443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8972832683020120859636117 420601532016568165295443)
                  ·
                    rfl

theorem cell23_7372067_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 4, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 4, 3, 1, 6].length) (baseStart_7372067 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7372067 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7372067 prefixEnd_7372067 := by exact prefixLift 7372067
  have htrace : WordTrace (prefixWord ++ tailWord_7372067) baseStart_7372067 baseEnd_7372067 := by
    simpa [prefixWord, tailWord_7372067, baseEnd_7372067] using wordTrace_append hprefix tailTrace_7372067
  have hstable : (prefixWord ++ tailWord_7372067).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7372067).length < 2 ^ (prefixWord ++ tailWord_7372067).sum := by decide
  have hdescent : baseEnd_7372067 < baseStart_7372067 := by decide
  rcases family_descends (prefixWord ++ tailWord_7372067) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7372073 : List Nat := [1, 2, 1, 1, 1, 1, 1, 2, 4, 4, 5]
def baseStart_7372073 : Nat := 118140960795 + 7372073 * 2 ^ 59
def prefixEnd_7372073 : Nat := 4983230072969 + 3 ^ 40 * 7372073 * 2
def baseEnd_7372073 : Nat := 3785416869033040464183959

theorem tailTrace_7372073 : CollatzResearch.WordTrace tailWord_7372073 prefixEnd_7372073 3785416869033040464183959 := by
  unfold tailWord_7372073
  simp only [CollatzResearch.WordTrace]
  refine ⟨268881591821246045675432873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179254394547497363783621915 268881591821246045675432873)
  ·
    refine ⟨201661193865934534256574655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 268881591821246045675432873 201661193865934534256574655)
    ·
      refine ⟨302491790798901801384861983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 201661193865934534256574655 302491790798901801384861983)
      ·
        refine ⟨453737686198352702077292975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 302491790798901801384861983 453737686198352702077292975)
        ·
          refine ⟨680606529297529053115939463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 453737686198352702077292975 680606529297529053115939463)
          ·
            refine ⟨1020909793946293579673909195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 680606529297529053115939463 1020909793946293579673909195)
            ·
              refine ⟨1531364690919440369510863793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1020909793946293579673909195 1531364690919440369510863793)
              ·
                refine ⟨1148523518189580277133147845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1531364690919440369510863793 1148523518189580277133147845)
                ·
                  refine ⟨215348159660546301962465221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1148523518189580277133147845 215348159660546301962465221)
                  ·
                    refine ⟨40377779936352431617962229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 215348159660546301962465221 40377779936352431617962229)
                    ·
                      refine ⟨3785416869033040464183959, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 40377779936352431617962229 3785416869033040464183959)
                      ·
                        rfl

theorem cell23_7372073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 2, 4, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 2, 4, 4, 5].length) (baseStart_7372073 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7372073 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7372073 prefixEnd_7372073 := by exact prefixLift 7372073
  have htrace : WordTrace (prefixWord ++ tailWord_7372073) baseStart_7372073 baseEnd_7372073 := by
    simpa [prefixWord, tailWord_7372073, baseEnd_7372073] using wordTrace_append hprefix tailTrace_7372073
  have hstable : (prefixWord ++ tailWord_7372073).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7372073).length < 2 ^ (prefixWord ++ tailWord_7372073).sum := by decide
  have hdescent : baseEnd_7372073 < baseStart_7372073 := by decide
  rcases family_descends (prefixWord ++ tailWord_7372073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7372118 : List Nat := [5, 2, 3, 1, 1, 1, 1, 3, 6]
def baseStart_7372118 : Nat := 118140960795 + 7372118 * 2 ^ 59
def prefixEnd_7372118 : Nat := 4983230072969 + 3 ^ 40 * 7372118 * 2
def baseEnd_7372118 : Nat := 420604441740276976457917

theorem tailTrace_7372118 : CollatzResearch.WordTrace tailWord_7372118 prefixEnd_7372118 420604441740276976457917 := by
  unfold tailWord_7372118
  simp only [CollatzResearch.WordTrace]
  refine ⟨16805202069130188647551313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 179255488737388678907214005 16805202069130188647551313)
  ·
    refine ⟨12603901551847641485663485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16805202069130188647551313 12603901551847641485663485)
    ·
      refine ⟨4726463081942865557123807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12603901551847641485663485 4726463081942865557123807)
      ·
        refine ⟨7089694622914298335685711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4726463081942865557123807 7089694622914298335685711)
        ·
          refine ⟨10634541934371447503528567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7089694622914298335685711 10634541934371447503528567)
          ·
            refine ⟨15951812901557171255292851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10634541934371447503528567 15951812901557171255292851)
            ·
              refine ⟨23927719352335756882939277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15951812901557171255292851 23927719352335756882939277)
              ·
                refine ⟨8972894757125908831102229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23927719352335756882939277 8972894757125908831102229)
                ·
                  refine ⟨420604441740276976457917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8972894757125908831102229 420604441740276976457917)
                  ·
                    rfl

theorem cell23_7372118_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 1, 1, 1, 3, 6].length) (baseStart_7372118 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7372118 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7372118 prefixEnd_7372118 := by exact prefixLift 7372118
  have htrace : WordTrace (prefixWord ++ tailWord_7372118) baseStart_7372118 baseEnd_7372118 := by
    simpa [prefixWord, tailWord_7372118, baseEnd_7372118] using wordTrace_append hprefix tailTrace_7372118
  have hstable : (prefixWord ++ tailWord_7372118).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7372118).length < 2 ^ (prefixWord ++ tailWord_7372118).sum := by decide
  have hdescent : baseEnd_7372118 < baseStart_7372118 := by decide
  rcases family_descends (prefixWord ++ tailWord_7372118) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7372120 : List Nat := [2, 1, 2, 2, 1, 1, 3, 4, 1, 1, 5]
def baseStart_7372120 : Nat := 118140960795 + 7372120 * 2 ^ 59
def prefixEnd_7372120 : Nat := 4983230072969 + 3 ^ 40 * 7372120 * 2
def baseEnd_7372120 : Nat := 3785441002623801780296243

theorem tailTrace_7372120 : CollatzResearch.WordTrace tailWord_7372120 prefixEnd_7372120 3785441002623801780296243 := by
  unfold tailWord_7372120
  simp only [CollatzResearch.WordTrace]
  refine ⟨134441653026037886351196907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 179255537368050515134929209 134441653026037886351196907)
  ·
    refine ⟨201662479539056829526795361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134441653026037886351196907 201662479539056829526795361)
    ·
      refine ⟨151246859654292622145096521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 201662479539056829526795361 151246859654292622145096521)
      ·
        refine ⟨113435144740719466608822391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 151246859654292622145096521 113435144740719466608822391)
        ·
          refine ⟨170152717111079199913233587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 113435144740719466608822391 170152717111079199913233587)
          ·
            refine ⟨255229075666618799869850381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 170152717111079199913233587 255229075666618799869850381)
            ·
              refine ⟨95710903374982049951193893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 255229075666618799869850381 95710903374982049951193893)
              ·
                refine ⟨17945794382809134365848855, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 95710903374982049951193893 17945794382809134365848855)
                ·
                  refine ⟨26918691574213701548773283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17945794382809134365848855 26918691574213701548773283)
                  ·
                    refine ⟨40378037361320552323159925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 26918691574213701548773283 40378037361320552323159925)
                    ·
                      refine ⟨3785441002623801780296243, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 40378037361320552323159925 3785441002623801780296243)
                      ·
                        rfl

theorem cell23_7372120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 3, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 3, 4, 1, 1, 5].length) (baseStart_7372120 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7372120 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7372120 prefixEnd_7372120 := by exact prefixLift 7372120
  have htrace : WordTrace (prefixWord ++ tailWord_7372120) baseStart_7372120 baseEnd_7372120 := by
    simpa [prefixWord, tailWord_7372120, baseEnd_7372120] using wordTrace_append hprefix tailTrace_7372120
  have hstable : (prefixWord ++ tailWord_7372120).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7372120).length < 2 ^ (prefixWord ++ tailWord_7372120).sum := by decide
  have hdescent : baseEnd_7372120 < baseStart_7372120 := by decide
  rcases family_descends (prefixWord ++ tailWord_7372120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7372137 : List Nat := [1, 2, 1, 1, 1, 3, 2, 6, 1, 2, 3]
def baseStart_7372137 : Nat := 118140960795 + 7372137 * 2 ^ 59
def prefixEnd_7372137 : Nat := 4983230072969 + 3 ^ 40 * 7372137 * 2
def baseEnd_7372137 : Nat := 3785449731794928213783665

theorem tailTrace_7372137 : CollatzResearch.WordTrace tailWord_7372137 prefixEnd_7372137 3785449731794928213783665 := by
  unfold tailWord_7372137
  simp only [CollatzResearch.WordTrace]
  refine ⟨268883926093014184605762665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179255950728676123070508443 268883926093014184605762665)
  ·
    refine ⟨201662944569760638454321999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 268883926093014184605762665 201662944569760638454321999)
    ·
      refine ⟨302494416854640957681482999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 201662944569760638454321999 302494416854640957681482999)
      ·
        refine ⟨453741625281961436522224499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 302494416854640957681482999 453741625281961436522224499)
        ·
          refine ⟨680612437922942154783336749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 453741625281961436522224499 680612437922942154783336749)
          ·
            refine ⟨255229664221103308043751281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 680612437922942154783336749 255229664221103308043751281)
            ·
              refine ⟨191422248165827481032813461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 255229664221103308043751281 191422248165827481032813461)
              ·
                refine ⟨8972917882773163173413131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 191422248165827481032813461 8972917882773163173413131)
                ·
                  refine ⟨13459376824159744760119697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8972917882773163173413131 13459376824159744760119697)
                  ·
                    refine ⟨10094532618119808570089773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13459376824159744760119697 10094532618119808570089773)
                    ·
                      refine ⟨3785449731794928213783665, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10094532618119808570089773 3785449731794928213783665)
                      ·
                        rfl

theorem cell23_7372137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 2, 6, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 2, 6, 1, 2, 3].length) (baseStart_7372137 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7372137 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7372137 prefixEnd_7372137 := by exact prefixLift 7372137
  have htrace : WordTrace (prefixWord ++ tailWord_7372137) baseStart_7372137 baseEnd_7372137 := by
    simpa [prefixWord, tailWord_7372137, baseEnd_7372137] using wordTrace_append hprefix tailTrace_7372137
  have hstable : (prefixWord ++ tailWord_7372137).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7372137).length < 2 ^ (prefixWord ++ tailWord_7372137).sum := by decide
  have hdescent : baseEnd_7372137 < baseStart_7372137 := by decide
  rcases family_descends (prefixWord ++ tailWord_7372137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7372140 : List Nat := [2, 2, 1, 1, 5, 1, 2, 9]
def baseStart_7372140 : Nat := 118140960795 + 7372140 * 2 ^ 59
def prefixEnd_7372140 : Nat := 4983230072969 + 3 ^ 40 * 7372140 * 2
def baseEnd_7372140 : Nat := 140201898971736729705413

theorem tailTrace_7372140 : CollatzResearch.WordTrace tailWord_7372140 prefixEnd_7372140 140201898971736729705413 := by
  unfold tailWord_7372140
  simp only [CollatzResearch.WordTrace]
  refine ⟨134442017756001658059060937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 179256023674668877412081249 134442017756001658059060937)
  ·
    refine ⟨100831513317001243544295703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 134442017756001658059060937 100831513317001243544295703)
    ·
      refine ⟨151247269975501865316443555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100831513317001243544295703 151247269975501865316443555)
      ·
        refine ⟨226870904963252797974665333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 151247269975501865316443555 226870904963252797974665333)
        ·
          refine ⟨21269147340304949810124875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 226870904963252797974665333 21269147340304949810124875)
          ·
            refine ⟨31903721010457424715187313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21269147340304949810124875 31903721010457424715187313)
            ·
              refine ⟨23927790757843068536390485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31903721010457424715187313 23927790757843068536390485)
              ·
                refine ⟨140201898971736729705413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 23927790757843068536390485 140201898971736729705413)
                ·
                  rfl

theorem cell23_7372140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 1, 2, 9].length) (baseStart_7372140 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7372140 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7372140 prefixEnd_7372140 := by exact prefixLift 7372140
  have htrace : WordTrace (prefixWord ++ tailWord_7372140) baseStart_7372140 baseEnd_7372140 := by
    simpa [prefixWord, tailWord_7372140, baseEnd_7372140] using wordTrace_append hprefix tailTrace_7372140
  have hstable : (prefixWord ++ tailWord_7372140).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7372140).length < 2 ^ (prefixWord ++ tailWord_7372140).sum := by decide
  have hdescent : baseEnd_7372140 < baseStart_7372140 := by decide
  rcases family_descends (prefixWord ++ tailWord_7372140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7372151 : List Nat := [1, 1, 3, 1, 1, 2, 4, 5, 1, 2, 2]
def baseStart_7372151 : Nat := 118140960795 + 7372151 * 2 ^ 59
def prefixEnd_7372151 : Nat := 4983230072969 + 3 ^ 40 * 7372151 * 2
def baseEnd_7372151 : Nat := 3785456920524091159008601

theorem tailTrace_7372151 : CollatzResearch.WordTrace tailWord_7372151 prefixEnd_7372151 3785456920524091159008601 := by
  unfold tailWord_7372151
  simp only [CollatzResearch.WordTrace]
  refine ⟨268884436714963464996772307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179256291143308976664514871 268884436714963464996772307)
  ·
    refine ⟨403326655072445197495158461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 268884436714963464996772307 403326655072445197495158461)
    ·
      refine ⟨151247495652166949060684423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 403326655072445197495158461 151247495652166949060684423)
      ·
        refine ⟨226871243478250423591026635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 151247495652166949060684423 226871243478250423591026635)
        ·
          refine ⟨340306865217375635386539953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 226871243478250423591026635 340306865217375635386539953)
          ·
            refine ⟨255230148913031726539904965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 340306865217375635386539953 255230148913031726539904965)
            ·
              refine ⟨47855652921193448726232181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 255230148913031726539904965 47855652921193448726232181)
              ·
                refine ⟨4486467461361885818084267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 47855652921193448726232181 4486467461361885818084267)
                ·
                  refine ⟨6729701192042828727126401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4486467461361885818084267 6729701192042828727126401)
                  ·
                    refine ⟨5047275894032121545344801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6729701192042828727126401 5047275894032121545344801)
                    ·
                      refine ⟨3785456920524091159008601, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5047275894032121545344801 3785456920524091159008601)
                      ·
                        rfl

theorem cell23_7372151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 4, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 4, 5, 1, 2, 2].length) (baseStart_7372151 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7372151 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7372151 prefixEnd_7372151 := by exact prefixLift 7372151
  have htrace : WordTrace (prefixWord ++ tailWord_7372151) baseStart_7372151 baseEnd_7372151 := by
    simpa [prefixWord, tailWord_7372151, baseEnd_7372151] using wordTrace_append hprefix tailTrace_7372151
  have hstable : (prefixWord ++ tailWord_7372151).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7372151).length < 2 ^ (prefixWord ++ tailWord_7372151).sum := by decide
  have hdescent : baseEnd_7372151 < baseStart_7372151 := by decide
  rcases family_descends (prefixWord ++ tailWord_7372151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7372161 : List Nat := [1, 2, 4, 3, 2, 1, 2, 2, 2, 4]
def baseStart_7372161 : Nat := 118140960795 + 7372161 * 2 ^ 59
def prefixEnd_7372161 : Nat := 4983230072969 + 3 ^ 40 * 7372161 * 2
def baseEnd_7372161 : Nat := 1261820685110212039961185

theorem tailTrace_7372161 : CollatzResearch.WordTrace tailWord_7372161 prefixEnd_7372161 1261820685110212039961185 := by
  unfold tailWord_7372161
  simp only [CollatzResearch.WordTrace]
  refine ⟨268884801444927236704636337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179256534296618157803090891 268884801444927236704636337)
  ·
    refine ⟨201663601083695427528477253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 268884801444927236704636337 201663601083695427528477253)
    ·
      refine ⟨37811925203192892661589485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 201663601083695427528477253 37811925203192892661589485)
      ·
        refine ⟨14179471951197334748096057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37811925203192892661589485 14179471951197334748096057)
        ·
          refine ⟨10634603963398001061072043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14179471951197334748096057 10634603963398001061072043)
          ·
            refine ⟨15951905945097001591608065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10634603963398001061072043 15951905945097001591608065)
            ·
              refine ⟨11963929458822751193706049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15951905945097001591608065 11963929458822751193706049)
              ·
                refine ⟨8972947094117063395279537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11963929458822751193706049 8972947094117063395279537)
                ·
                  refine ⟨6729710320587797546459653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8972947094117063395279537 6729710320587797546459653)
                  ·
                    refine ⟨1261820685110212039961185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6729710320587797546459653 1261820685110212039961185)
                    ·
                      rfl

theorem cell23_7372161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 2, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 2, 1, 2, 2, 2, 4].length) (baseStart_7372161 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7372161 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7372161 prefixEnd_7372161 := by exact prefixLift 7372161
  have htrace : WordTrace (prefixWord ++ tailWord_7372161) baseStart_7372161 baseEnd_7372161 := by
    simpa [prefixWord, tailWord_7372161, baseEnd_7372161] using wordTrace_append hprefix tailTrace_7372161
  have hstable : (prefixWord ++ tailWord_7372161).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7372161).length < 2 ^ (prefixWord ++ tailWord_7372161).sum := by decide
  have hdescent : baseEnd_7372161 < baseStart_7372161 := by decide
  rcases family_descends (prefixWord ++ tailWord_7372161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7372162 : List Nat := [3, 4, 2, 1, 1, 3, 2, 2, 1, 1, 3]
def baseStart_7372162 : Nat := 118140960795 + 7372162 * 2 ^ 59
def prefixEnd_7372162 : Nat := 4983230072969 + 3 ^ 40 * 7372162 * 2
def baseEnd_7372162 : Nat := 3785462568811290615971051

theorem tailTrace_7372162 : CollatzResearch.WordTrace tailWord_7372162 prefixEnd_7372162 3785462568811290615971051 := by
  unfold tailWord_7372162
  simp only [CollatzResearch.WordTrace]
  refine ⟨67221209479480903468855685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 179256558611949075916948493 67221209479480903468855685)
  ·
    refine ⟨12603976777402669400410441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 67221209479480903468855685 12603976777402669400410441)
    ·
      refine ⟨9452982583052002050307831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12603976777402669400410441 9452982583052002050307831)
      ·
        refine ⟨14179473874578003075461747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9452982583052002050307831 14179473874578003075461747)
        ·
          refine ⟨21269210811867004613192621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14179473874578003075461747 21269210811867004613192621)
          ·
            refine ⟨7975954054450126729947233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21269210811867004613192621 7975954054450126729947233)
            ·
              refine ⟨5981965540837595047460425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7975954054450126729947233 5981965540837595047460425)
              ·
                refine ⟨4486474155628196285595319, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5981965540837595047460425 4486474155628196285595319)
                ·
                  refine ⟨6729711233442294428392979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4486474155628196285595319 6729711233442294428392979)
                  ·
                    refine ⟨10094566850163441642589469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6729711233442294428392979 10094566850163441642589469)
                    ·
                      refine ⟨3785462568811290615971051, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10094566850163441642589469 3785462568811290615971051)
                      ·
                        rfl

theorem cell23_7372162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 3, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 3, 2, 2, 1, 1, 3].length) (baseStart_7372162 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7372162 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7372162 prefixEnd_7372162 := by exact prefixLift 7372162
  have htrace : WordTrace (prefixWord ++ tailWord_7372162) baseStart_7372162 baseEnd_7372162 := by
    simpa [prefixWord, tailWord_7372162, baseEnd_7372162] using wordTrace_append hprefix tailTrace_7372162
  have hstable : (prefixWord ++ tailWord_7372162).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7372162).length < 2 ^ (prefixWord ++ tailWord_7372162).sum := by decide
  have hdescent : baseEnd_7372162 < baseStart_7372162 := by decide
  rcases family_descends (prefixWord ++ tailWord_7372162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7372168 : List Nat := [2, 1, 3, 3, 1, 3, 1, 4, 1, 2, 2]
def baseStart_7372168 : Nat := 118140960795 + 7372168 * 2 ^ 59
def prefixEnd_7372168 : Nat := 4983230072969 + 3 ^ 40 * 7372168 * 2
def baseEnd_7372168 : Nat := 3785465649695217592496023

theorem tailTrace_7372168 : CollatzResearch.WordTrace tailWord_7372168 prefixEnd_7372168 3785465649695217592496023 := by
  unfold tailWord_7372168
  simp only [CollatzResearch.WordTrace]
  refine ⟨134442528377950938450070579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 179256704503934584600094105 134442528377950938450070579)
  ·
    refine ⟨201663792566926407675105869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134442528377950938450070579 201663792566926407675105869)
    ·
      refine ⟨75623922212597402878164701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 201663792566926407675105869 75623922212597402878164701)
      ·
        refine ⟨28358970829724026079311763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 75623922212597402878164701 28358970829724026079311763)
        ·
          refine ⟨42538456244586039118967645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28358970829724026079311763 42538456244586039118967645)
          ·
            refine ⟨15951921091719764669612867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42538456244586039118967645 15951921091719764669612867)
            ·
              refine ⟨23927881637579647004419301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15951921091719764669612867 23927881637579647004419301)
              ·
                refine ⟨4486477807046183813328619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23927881637579647004419301 4486477807046183813328619)
                ·
                  refine ⟨6729716710569275719992929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4486477807046183813328619 6729716710569275719992929)
                  ·
                    refine ⟨5047287532926956789994697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6729716710569275719992929 5047287532926956789994697)
                    ·
                      refine ⟨3785465649695217592496023, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5047287532926956789994697 3785465649695217592496023)
                      ·
                        rfl

theorem cell23_7372168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 3, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 3, 1, 4, 1, 2, 2].length) (baseStart_7372168 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7372168 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7372168 prefixEnd_7372168 := by exact prefixLift 7372168
  have htrace : WordTrace (prefixWord ++ tailWord_7372168) baseStart_7372168 baseEnd_7372168 := by
    simpa [prefixWord, tailWord_7372168, baseEnd_7372168] using wordTrace_append hprefix tailTrace_7372168
  have hstable : (prefixWord ++ tailWord_7372168).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7372168).length < 2 ^ (prefixWord ++ tailWord_7372168).sum := by decide
  have hdescent : baseEnd_7372168 < baseStart_7372168 := by decide
  rcases family_descends (prefixWord ++ tailWord_7372168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7372174 : List Nat := [4, 1, 1, 4, 2, 2, 1, 8]
def baseStart_7372174 : Nat := 118140960795 + 7372174 * 2 ^ 59
def prefixEnd_7372174 : Nat := 4983230072969 + 3 ^ 40 * 7372174 * 2
def baseEnd_7372174 : Nat := 140202545577005354408185

theorem tailTrace_7372174 : CollatzResearch.WordTrace tailWord_7372174 prefixEnd_7372174 140202545577005354408185 := by
  unfold tailWord_7372174
  simp only [CollatzResearch.WordTrace]
  refine ⟨33610659449235017490607447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 179256850395920093283239717 33610659449235017490607447)
  ·
    refine ⟨50415989173852526235911171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33610659449235017490607447 50415989173852526235911171)
    ·
      refine ⟨75623983760778789353866757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50415989173852526235911171 75623983760778789353866757)
      ·
        refine ⟨14179496955146023003850017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 75623983760778789353866757 14179496955146023003850017)
        ·
          refine ⟨10634622716359517252887513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14179496955146023003850017 10634622716359517252887513)
          ·
            refine ⟨7975967037269637939665635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10634622716359517252887513 7975967037269637939665635)
            ·
              refine ⟨11963950555904456909498453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7975967037269637939665635 11963950555904456909498453)
              ·
                refine ⟨140202545577005354408185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 11963950555904456909498453 140202545577005354408185)
                ·
                  rfl

theorem cell23_7372174_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 2, 2, 1, 8].length) (baseStart_7372174 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7372174 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7372174 prefixEnd_7372174 := by exact prefixLift 7372174
  have htrace : WordTrace (prefixWord ++ tailWord_7372174) baseStart_7372174 baseEnd_7372174 := by
    simpa [prefixWord, tailWord_7372174, baseEnd_7372174] using wordTrace_append hprefix tailTrace_7372174
  have hstable : (prefixWord ++ tailWord_7372174).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7372174).length < 2 ^ (prefixWord ++ tailWord_7372174).sum := by decide
  have hdescent : baseEnd_7372174 < baseStart_7372174 := by decide
  rcases family_descends (prefixWord ++ tailWord_7372174) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7372292 : List Nat := [2, 3, 2, 3, 2, 2, 2, 1, 2, 2, 2]
def baseStart_7372292 : Nat := 118140960795 + 7372292 * 2 ^ 59
def prefixEnd_7372292 : Nat := 4983230072969 + 3 ^ 40 * 7372292 * 2
def baseEnd_7372292 : Nat := 3785529321296375107345453

theorem tailTrace_7372292 : CollatzResearch.WordTrace tailWord_7372292 prefixEnd_7372292 3785529321296375107345453 := by
  unfold tailWord_7372292
  simp only [CollatzResearch.WordTrace]
  refine ⟨134444789703726323038827565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 179259719604968430718436753 134444789703726323038827565)
  ·
    refine ⟨50416796138897371139560337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 134444789703726323038827565 50416796138897371139560337)
    ·
      refine ⟨37812597104173028354670253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50416796138897371139560337 37812597104173028354670253)
      ·
        refine ⟨14179723914064885633001345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37812597104173028354670253 14179723914064885633001345)
        ·
          refine ⟨10634792935548664224751009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14179723914064885633001345 10634792935548664224751009)
          ·
            refine ⟨7976094701661498168563257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10634792935548664224751009 7976094701661498168563257)
            ·
              refine ⟨5982071026246123626422443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7976094701661498168563257 5982071026246123626422443)
              ·
                refine ⟨8973106539369185439633665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5982071026246123626422443 8973106539369185439633665)
                ·
                  refine ⟨6729829904526889079725249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8973106539369185439633665 6729829904526889079725249)
                  ·
                    refine ⟨5047372428395166809793937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6729829904526889079725249 5047372428395166809793937)
                    ·
                      refine ⟨3785529321296375107345453, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5047372428395166809793937 3785529321296375107345453)
                      ·
                        rfl

theorem cell23_7372292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 2, 2, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 2, 2, 2, 1, 2, 2, 2].length) (baseStart_7372292 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7372292 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7372292 prefixEnd_7372292 := by exact prefixLift 7372292
  have htrace : WordTrace (prefixWord ++ tailWord_7372292) baseStart_7372292 baseEnd_7372292 := by
    simpa [prefixWord, tailWord_7372292, baseEnd_7372292] using wordTrace_append hprefix tailTrace_7372292
  have hstable : (prefixWord ++ tailWord_7372292).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7372292).length < 2 ^ (prefixWord ++ tailWord_7372292).sum := by decide
  have hdescent : baseEnd_7372292 < baseStart_7372292 := by decide
  rcases family_descends (prefixWord ++ tailWord_7372292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7372297 : List Nat := [1, 2, 1, 1, 3, 1, 3, 2, 4, 1, 4]
def baseStart_7372297 : Nat := 118140960795 + 7372297 * 2 ^ 59
def prefixEnd_7372297 : Nat := 4983230072969 + 3 ^ 40 * 7372297 * 2
def baseEnd_7372297 : Nat := 3785531888699647587782929

theorem tailTrace_7372297 : CollatzResearch.WordTrace tailWord_7372297 prefixEnd_7372297 3785531888699647587782929 := by
  unfold tailWord_7372297
  simp only [CollatzResearch.WordTrace]
  refine ⟨268889761772434531931587145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179259841181623021287724763 268889761772434531931587145)
  ·
    refine ⟨201667321329325898948690359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 268889761772434531931587145 201667321329325898948690359)
    ·
      refine ⟨302500981993988848423035539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 201667321329325898948690359 302500981993988848423035539)
      ·
        refine ⟨453751472990983272634553309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 302500981993988848423035539 453751472990983272634553309)
        ·
          refine ⟨170156802371618727237957491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 453751472990983272634553309 170156802371618727237957491)
          ·
            refine ⟨255235203557428090856936237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 170156802371618727237957491 255235203557428090856936237)
            ·
              refine ⟨95713201334035534071351089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 255235203557428090856936237 95713201334035534071351089)
              ·
                refine ⟨71784901000526650553513317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 95713201334035534071351089 71784901000526650553513317)
                ·
                  refine ⟨13459668937598746978783747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 71784901000526650553513317 13459668937598746978783747)
                  ·
                    refine ⟨20189503406398120468175621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13459668937598746978783747 20189503406398120468175621)
                    ·
                      refine ⟨3785531888699647587782929, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20189503406398120468175621 3785531888699647587782929)
                      ·
                        rfl

theorem cell23_7372297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 3, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 3, 2, 4, 1, 4].length) (baseStart_7372297 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7372297 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7372297 prefixEnd_7372297 := by exact prefixLift 7372297
  have htrace : WordTrace (prefixWord ++ tailWord_7372297) baseStart_7372297 baseEnd_7372297 := by
    simpa [prefixWord, tailWord_7372297, baseEnd_7372297] using wordTrace_append hprefix tailTrace_7372297
  have hstable : (prefixWord ++ tailWord_7372297).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7372297).length < 2 ^ (prefixWord ++ tailWord_7372297).sum := by decide
  have hdescent : baseEnd_7372297 < baseStart_7372297 := by decide
  rcases family_descends (prefixWord ++ tailWord_7372297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7372314 : List Nat := [3, 1, 1, 3, 1, 1, 1, 2, 4, 4, 2]
def baseStart_7372314 : Nat := 118140960795 + 7372314 * 2 ^ 59
def prefixEnd_7372314 : Nat := 4983230072969 + 3 ^ 40 * 7372314 * 2
def baseEnd_7372314 : Nat := 3785540617870774021270351

theorem tailTrace_7372314 : CollatzResearch.WordTrace tailWord_7372314 prefixEnd_7372314 3785540617870774021270351 := by
  unfold tailWord_7372314
  simp only [CollatzResearch.WordTrace]
  refine ⟨67222595453343235958738999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 179260254542248629223303997 67222595453343235958738999)
  ·
    refine ⟨100833893180014853938108499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67222595453343235958738999 100833893180014853938108499)
    ·
      refine ⟨151250839770022280907162749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100833893180014853938108499 151250839770022280907162749)
      ·
        refine ⟨56719064913758355340186031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 151250839770022280907162749 56719064913758355340186031)
        ·
          refine ⟨85078597370637533010279047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56719064913758355340186031 85078597370637533010279047)
          ·
            refine ⟨127617896055956299515418571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85078597370637533010279047 127617896055956299515418571)
            ·
              refine ⟨191426844083934449273127857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 127617896055956299515418571 191426844083934449273127857)
              ·
                refine ⟨143570133062950836954845893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 191426844083934449273127857 143570133062950836954845893)
                ·
                  refine ⟨26919399949303281929033605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 143570133062950836954845893 26919399949303281929033605)
                  ·
                    refine ⟨5047387490494365361693801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 26919399949303281929033605 5047387490494365361693801)
                    ·
                      refine ⟨3785540617870774021270351, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5047387490494365361693801 3785540617870774021270351)
                      ·
                        rfl

theorem cell23_7372314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 1, 2, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 1, 2, 4, 4, 2].length) (baseStart_7372314 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7372314 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7372314 prefixEnd_7372314 := by exact prefixLift 7372314
  have htrace : WordTrace (prefixWord ++ tailWord_7372314) baseStart_7372314 baseEnd_7372314 := by
    simpa [prefixWord, tailWord_7372314, baseEnd_7372314] using wordTrace_append hprefix tailTrace_7372314
  have hstable : (prefixWord ++ tailWord_7372314).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7372314).length < 2 ^ (prefixWord ++ tailWord_7372314).sum := by decide
  have hdescent : baseEnd_7372314 < baseStart_7372314 := by decide
  rcases family_descends (prefixWord ++ tailWord_7372314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7372365 : List Nat := [1, 6, 1, 1, 4, 1, 1, 1, 2, 1, 4]
def baseStart_7372365 : Nat := 118140960795 + 7372365 * 2 ^ 59
def prefixEnd_7372365 : Nat := 4983230072969 + 3 ^ 40 * 7372365 * 2
def baseEnd_7372365 : Nat := 3785566805384153321732617

theorem tailTrace_7372365 : CollatzResearch.WordTrace tailWord_7372365 prefixEnd_7372365 3785566805384153321732617 := by
  unfold tailWord_7372365
  simp only [CollatzResearch.WordTrace]
  refine ⟨268892241936188179545062549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179261494624125453030041699 268892241936188179545062549)
  ·
    refine ⟨12604323840758820916174807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 268892241936188179545062549 12604323840758820916174807)
    ·
      refine ⟨18906485761138231374262211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12604323840758820916174807 18906485761138231374262211)
      ·
        refine ⟨28359728641707347061393317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18906485761138231374262211 28359728641707347061393317)
        ·
          refine ⟨5317449120320127574011247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 28359728641707347061393317 5317449120320127574011247)
          ·
            refine ⟨7976173680480191361016871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5317449120320127574011247 7976173680480191361016871)
            ·
              refine ⟨11964260520720287041525307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7976173680480191361016871 11964260520720287041525307)
              ·
                refine ⟨17946390781080430562287961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11964260520720287041525307 17946390781080430562287961)
                ·
                  refine ⟨13459793085810322921715971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17946390781080430562287961 13459793085810322921715971)
                  ·
                    refine ⟨20189689628715484382573957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13459793085810322921715971 20189689628715484382573957)
                    ·
                      refine ⟨3785566805384153321732617, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20189689628715484382573957 3785566805384153321732617)
                      ·
                        rfl

theorem cell23_7372365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 4, 1, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 4, 1, 1, 1, 2, 1, 4].length) (baseStart_7372365 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7372365 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7372365 prefixEnd_7372365 := by exact prefixLift 7372365
  have htrace : WordTrace (prefixWord ++ tailWord_7372365) baseStart_7372365 baseEnd_7372365 := by
    simpa [prefixWord, tailWord_7372365, baseEnd_7372365] using wordTrace_append hprefix tailTrace_7372365
  have hstable : (prefixWord ++ tailWord_7372365).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7372365).length < 2 ^ (prefixWord ++ tailWord_7372365).sum := by decide
  have hdescent : baseEnd_7372365 < baseStart_7372365 := by decide
  rcases family_descends (prefixWord ++ tailWord_7372365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7372391 : List Nat := [1, 1, 5, 1, 1, 1, 2, 4, 2, 3, 2]
def baseStart_7372391 : Nat := 118140960795 + 7372391 * 2 ^ 59
def prefixEnd_7372391 : Nat := 4983230072969 + 3 ^ 40 * 7372391 * 2
def baseEnd_7372391 : Nat := 3785580155881170220007497

theorem tailTrace_7372391 : CollatzResearch.WordTrace tailWord_7372391 prefixEnd_7372391 3785580155881170220007497 := by
  unfold tailWord_7372391
  simp only [CollatzResearch.WordTrace]
  refine ⟨268893190234093985985509027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179262126822729323990339351 268893190234093985985509027)
  ·
    refine ⟨403339785351140978978263541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 268893190234093985985509027 403339785351140978978263541)
    ·
      refine ⟨37813104876669466779212207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 403339785351140978978263541 37813104876669466779212207)
      ·
        refine ⟨56719657315004200168818311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37813104876669466779212207 56719657315004200168818311)
        ·
          refine ⟨85079485972506300253227467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56719657315004200168818311 85079485972506300253227467)
          ·
            refine ⟨127619228958759450379841201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85079485972506300253227467 127619228958759450379841201)
            ·
              refine ⟨95714421719069587784880901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 127619228958759450379841201 95714421719069587784880901)
              ·
                refine ⟨17946454072325547709665169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 95714421719069587784880901 17946454072325547709665169)
                ·
                  refine ⟨13459840554244160782248877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17946454072325547709665169 13459840554244160782248877)
                  ·
                    refine ⟨5047440207841560293343329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13459840554244160782248877 5047440207841560293343329)
                    ·
                      refine ⟨3785580155881170220007497, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5047440207841560293343329 3785580155881170220007497)
                      ·
                        rfl

theorem cell23_7372391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 2, 4, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 2, 4, 2, 3, 2].length) (baseStart_7372391 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7372391 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7372391 prefixEnd_7372391 := by exact prefixLift 7372391
  have htrace : WordTrace (prefixWord ++ tailWord_7372391) baseStart_7372391 baseEnd_7372391 := by
    simpa [prefixWord, tailWord_7372391, baseEnd_7372391] using wordTrace_append hprefix tailTrace_7372391
  have hstable : (prefixWord ++ tailWord_7372391).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7372391).length < 2 ^ (prefixWord ++ tailWord_7372391).sum := by decide
  have hdescent : baseEnd_7372391 < baseStart_7372391 := by decide
  rcases family_descends (prefixWord ++ tailWord_7372391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7372421 : List Nat := [1, 3, 1, 1, 4, 1, 4, 2, 1, 1, 4]
def baseStart_7372421 : Nat := 118140960795 + 7372421 * 2 ^ 59
def prefixEnd_7372421 : Nat := 4983230072969 + 3 ^ 40 * 7372421 * 2
def baseEnd_7372421 : Nat := 3785595560300805102632359

theorem tailTrace_7372421 : CollatzResearch.WordTrace tailWord_7372421 prefixEnd_7372421 3785595560300805102632359 := by
  unfold tailWord_7372421
  simp only [CollatzResearch.WordTrace]
  refine ⟨268894284423985301109101117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179262856282656867406067411 268894284423985301109101117)
  ·
    refine ⟨100835356658994487915912919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 268894284423985301109101117 100835356658994487915912919)
    ·
      refine ⟨151253034988491731873869379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100835356658994487915912919 151253034988491731873869379)
      ·
        refine ⟨226879552482737597810804069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 151253034988491731873869379 226879552482737597810804069)
        ·
          refine ⟨42539916090513299589525763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 226879552482737597810804069 42539916090513299589525763)
          ·
            refine ⟨63809874135769949384288645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42539916090513299589525763 63809874135769949384288645)
            ·
              refine ⟨11964351400456865509554121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 63809874135769949384288645 11964351400456865509554121)
              ·
                refine ⟨8973263550342649132165591, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11964351400456865509554121 8973263550342649132165591)
                ·
                  refine ⟨13459895325513973698248387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8973263550342649132165591 13459895325513973698248387)
                  ·
                    refine ⟨20189842988270960547372581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13459895325513973698248387 20189842988270960547372581)
                    ·
                      refine ⟨3785595560300805102632359, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20189842988270960547372581 3785595560300805102632359)
                      ·
                        rfl

theorem cell23_7372421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 4, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 4, 2, 1, 1, 4].length) (baseStart_7372421 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7372421 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7372421 prefixEnd_7372421 := by exact prefixLift 7372421
  have htrace : WordTrace (prefixWord ++ tailWord_7372421) baseStart_7372421 baseEnd_7372421 := by
    simpa [prefixWord, tailWord_7372421, baseEnd_7372421] using wordTrace_append hprefix tailTrace_7372421
  have hstable : (prefixWord ++ tailWord_7372421).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7372421).length < 2 ^ (prefixWord ++ tailWord_7372421).sum := by decide
  have hdescent : baseEnd_7372421 < baseStart_7372421 := by decide
  rcases family_descends (prefixWord ++ tailWord_7372421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7372427 : List Nat := [1, 1, 1, 1, 4, 1, 5, 9]
def baseStart_7372427 : Nat := 118140960795 + 7372427 * 2 ^ 59
def prefixEnd_7372427 : Nat := 4983230072969 + 3 ^ 40 * 7372427 * 2
def baseEnd_7372427 : Nat := 140207357080916002931753

theorem tailTrace_7372427 : CollatzResearch.WordTrace tailWord_7372427 prefixEnd_7372427 140207357080916002931753 := by
  unfold tailWord_7372427
  simp only [CollatzResearch.WordTrace]
  refine ⟨268894503261963564133819535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179263002174642376089213023 268894503261963564133819535)
  ·
    refine ⟨403341754892945346200729303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 268894503261963564133819535 403341754892945346200729303)
    ·
      refine ⟨605012632339418019301093955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 403341754892945346200729303 605012632339418019301093955)
      ·
        refine ⟨907518948509127028951640933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 605012632339418019301093955 907518948509127028951640933)
        ·
          refine ⟨170159802845461317928432675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 907518948509127028951640933 170159802845461317928432675)
          ·
            refine ⟨255239704268191976892649013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 170159802845461317928432675 255239704268191976892649013)
            ·
              refine ⟨23928722275142997833685845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 255239704268191976892649013 23928722275142997833685845)
              ·
                refine ⟨140207357080916002931753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 23928722275142997833685845 140207357080916002931753)
                ·
                  rfl

theorem cell23_7372427_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 5, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 5, 9].length) (baseStart_7372427 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7372427 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7372427 prefixEnd_7372427 := by exact prefixLift 7372427
  have htrace : WordTrace (prefixWord ++ tailWord_7372427) baseStart_7372427 baseEnd_7372427 := by
    simpa [prefixWord, tailWord_7372427, baseEnd_7372427] using wordTrace_append hprefix tailTrace_7372427
  have hstable : (prefixWord ++ tailWord_7372427).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7372427).length < 2 ^ (prefixWord ++ tailWord_7372427).sum := by decide
  have hdescent : baseEnd_7372427 < baseStart_7372427 := by decide
  rcases family_descends (prefixWord ++ tailWord_7372427) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7372504 : List Nat := [2, 1, 2, 2, 3, 1, 2, 2, 2, 6]
def baseStart_7372504 : Nat := 118140960795 + 7372504 * 2 ^ 59
def prefixEnd_7372504 : Nat := 4983230072969 + 3 ^ 40 * 7372504 * 2
def baseEnd_7372504 : Nat := 1261879393065042759298159

theorem tailTrace_7372504 : CollatzResearch.WordTrace tailWord_7372504 prefixEnd_7372504 1261879393065042759298159 := by
  unfold tailWord_7372504
  simp only [CollatzResearch.WordTrace]
  refine ⟨134448655841342303142186283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 179264874455123070856248377 134448655841342303142186283)
  ·
    refine ⟨201672983762013454713279425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134448655841342303142186283 201672983762013454713279425)
    ·
      refine ⟨151254737821510091034959569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 201672983762013454713279425 151254737821510091034959569)
      ·
        refine ⟨113441053366132568276219677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 151254737821510091034959569 113441053366132568276219677)
        ·
          refine ⟨42540395012299713103582379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 113441053366132568276219677 42540395012299713103582379)
          ·
            refine ⟨63810592518449569655373569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42540395012299713103582379 63810592518449569655373569)
            ·
              refine ⟨47857944388837177241530177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 63810592518449569655373569 47857944388837177241530177)
              ·
                refine ⟨35893458291627882931147633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47857944388837177241530177 35893458291627882931147633)
                ·
                  refine ⟨26920093718720912198360725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35893458291627882931147633 26920093718720912198360725)
                  ·
                    refine ⟨1261879393065042759298159, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26920093718720912198360725 1261879393065042759298159)
                    ·
                      rfl

theorem cell23_7372504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 2, 2, 2, 6].length) (baseStart_7372504 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7372504 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7372504 prefixEnd_7372504 := by exact prefixLift 7372504
  have htrace : WordTrace (prefixWord ++ tailWord_7372504) baseStart_7372504 baseEnd_7372504 := by
    simpa [prefixWord, tailWord_7372504, baseEnd_7372504] using wordTrace_append hprefix tailTrace_7372504
  have hstable : (prefixWord ++ tailWord_7372504).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7372504).length < 2 ^ (prefixWord ++ tailWord_7372504).sum := by decide
  have hdescent : baseEnd_7372504 < baseStart_7372504 := by decide
  rcases family_descends (prefixWord ++ tailWord_7372504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7372511 : List Nat := [1, 1, 2, 3, 2, 2, 1, 2, 3, 4, 2]
def baseStart_7372511 : Nat := 118140960795 + 7372511 * 2 ^ 59
def prefixEnd_7372511 : Nat := 4983230072969 + 3 ^ 40 * 7372511 * 2
def baseEnd_7372511 : Nat := 3785641773559709750506945

theorem tailTrace_7372511 : CollatzResearch.WordTrace tailWord_7372511 prefixEnd_7372511 3785641773559709750506945 := by
  unfold tailWord_7372511
  simp only [CollatzResearch.WordTrace]
  refine ⟨268897566993659246479877387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179265044662439497653251591 268897566993659246479877387)
  ·
    refine ⟨403346350490488869719816081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 268897566993659246479877387 403346350490488869719816081)
    ·
      refine ⟨302509762867866652289862061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 403346350490488869719816081 302509762867866652289862061)
      ·
        refine ⟨113441161075449994608698273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 302509762867866652289862061 113441161075449994608698273)
        ·
          refine ⟨85080870806587495956523705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 113441161075449994608698273 85080870806587495956523705)
          ·
            refine ⟨63810653104940621967392779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 85080870806587495956523705 63810653104940621967392779)
            ·
              refine ⟨95715979657410932951089169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63810653104940621967392779 95715979657410932951089169)
              ·
                refine ⟨71786984743058199713316877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 95715979657410932951089169 71786984743058199713316877)
                ·
                  refine ⟨26920119278646824892493829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 71786984743058199713316877 26920119278646824892493829)
                  ·
                    refine ⟨5047522364746279667342593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 26920119278646824892493829 5047522364746279667342593)
                    ·
                      refine ⟨3785641773559709750506945, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5047522364746279667342593 3785641773559709750506945)
                      ·
                        rfl

theorem cell23_7372511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 1, 2, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 1, 2, 3, 4, 2].length) (baseStart_7372511 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7372511 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7372511 prefixEnd_7372511 := by exact prefixLift 7372511
  have htrace : WordTrace (prefixWord ++ tailWord_7372511) baseStart_7372511 baseEnd_7372511 := by
    simpa [prefixWord, tailWord_7372511, baseEnd_7372511] using wordTrace_append hprefix tailTrace_7372511
  have hstable : (prefixWord ++ tailWord_7372511).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7372511).length < 2 ^ (prefixWord ++ tailWord_7372511).sum := by decide
  have hdescent : baseEnd_7372511 < baseStart_7372511 := by decide
  rcases family_descends (prefixWord ++ tailWord_7372511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7372524 : List Nat := [2, 2, 1, 1, 2, 2, 3, 1, 1, 4, 4]
def baseStart_7372524 : Nat := 118140960795 + 7372524 * 2 ^ 59
def prefixEnd_7372524 : Nat := 4983230072969 + 3 ^ 40 * 7372524 * 2
def baseEnd_7372524 : Nat := 3785648448808218199644385

theorem tailTrace_7372524 : CollatzResearch.WordTrace tailWord_7372524 prefixEnd_7372524 3785648448808218199644385 := by
  unfold tailWord_7372524
  simp only [CollatzResearch.WordTrace]
  refine ⟨134449020571306074850050313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 179265360761741433133400417 134449020571306074850050313)
  ·
    refine ⟨100836765428479556137537735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 134449020571306074850050313 100836765428479556137537735)
    ·
      refine ⟨151255148142719334206306603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100836765428479556137537735 151255148142719334206306603)
      ·
        refine ⟨226882722214079001309459905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 151255148142719334206306603 226882722214079001309459905)
        ·
          refine ⟨170162041660559250982094929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 226882722214079001309459905 170162041660559250982094929)
          ·
            refine ⟨127621531245419438236571197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 170162041660559250982094929 127621531245419438236571197)
            ·
              refine ⟨47858074217032289338714199, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 127621531245419438236571197 47858074217032289338714199)
              ·
                refine ⟨71787111325548434008071299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47858074217032289338714199 71787111325548434008071299)
                ·
                  refine ⟨107680666988322651012106949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 71787111325548434008071299 107680666988322651012106949)
                  ·
                    refine ⟨20190125060310497064770053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 107680666988322651012106949 20190125060310497064770053)
                    ·
                      refine ⟨3785648448808218199644385, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20190125060310497064770053 3785648448808218199644385)
                      ·
                        rfl

theorem cell23_7372524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 4, 4].length) (baseStart_7372524 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7372524 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7372524 prefixEnd_7372524 := by exact prefixLift 7372524
  have htrace : WordTrace (prefixWord ++ tailWord_7372524) baseStart_7372524 baseEnd_7372524 := by
    simpa [prefixWord, tailWord_7372524, baseEnd_7372524] using wordTrace_append hprefix tailTrace_7372524
  have hstable : (prefixWord ++ tailWord_7372524).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7372524).length < 2 ^ (prefixWord ++ tailWord_7372524).sum := by decide
  have hdescent : baseEnd_7372524 < baseStart_7372524 := by decide
  rcases family_descends (prefixWord ++ tailWord_7372524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7372532 : List Nat := [2, 6, 1, 1, 1, 1, 2, 1, 3, 3, 2]
def baseStart_7372532 : Nat := 118140960795 + 7372532 * 2 ^ 59
def prefixEnd_7372532 : Nat := 4983230072969 + 3 ^ 40 * 7372532 * 2
def baseEnd_7372532 : Nat := 3785652556653454168344349

theorem tailTrace_7372532 : CollatzResearch.WordTrace tailWord_7372532 prefixEnd_7372532 3785652556653454168344349 := by
  unfold tailWord_7372532
  simp only [CollatzResearch.WordTrace]
  refine ⟨134449166463291583533195925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 179265555284388778044261233 134449166463291583533195925)
  ·
    refine ⟨6302304677966792978118559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 134449166463291583533195925 6302304677966792978118559)
    ·
      refine ⟨9453457016950189467177839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6302304677966792978118559 9453457016950189467177839)
      ·
        refine ⟨14180185525425284200766759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9453457016950189467177839 14180185525425284200766759)
        ·
          refine ⟨21270278288137926301150139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14180185525425284200766759 21270278288137926301150139)
          ·
            refine ⟨31905417432206889451725209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21270278288137926301150139 31905417432206889451725209)
            ·
              refine ⟨23929063074155167088793907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31905417432206889451725209 23929063074155167088793907)
              ·
                refine ⟨35893594611232750633190861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23929063074155167088793907 35893594611232750633190861)
                ·
                  refine ⟨13460097979212281487446573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35893594611232750633190861 13460097979212281487446573)
                  ·
                    refine ⟨5047536742204605557792465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13460097979212281487446573 5047536742204605557792465)
                    ·
                      refine ⟨3785652556653454168344349, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5047536742204605557792465 3785652556653454168344349)
                      ·
                        rfl

theorem cell23_7372532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 1, 2, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 1, 2, 1, 3, 3, 2].length) (baseStart_7372532 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7372532 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7372532 prefixEnd_7372532 := by exact prefixLift 7372532
  have htrace : WordTrace (prefixWord ++ tailWord_7372532) baseStart_7372532 baseEnd_7372532 := by
    simpa [prefixWord, tailWord_7372532, baseEnd_7372532] using wordTrace_append hprefix tailTrace_7372532
  have hstable : (prefixWord ++ tailWord_7372532).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7372532).length < 2 ^ (prefixWord ++ tailWord_7372532).sum := by decide
  have hdescent : baseEnd_7372532 < baseStart_7372532 := by decide
  rcases family_descends (prefixWord ++ tailWord_7372532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7372562 : List Nat := [3, 2, 4, 1, 1, 2, 1, 1, 4, 2, 2]
def baseStart_7372562 : Nat := 118140960795 + 7372562 * 2 ^ 59
def prefixEnd_7372562 : Nat := 4983230072969 + 3 ^ 40 * 7372562 * 2
def baseEnd_7372562 : Nat := 3785667961073089050969211

theorem tailTrace_7372562 : CollatzResearch.WordTrace tailWord_7372562 prefixEnd_7372562 3785667961073089050969211 := by
  unfold tailWord_7372562
  simp only [CollatzResearch.WordTrace]
  refine ⟨67224856779118620547495985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 179266284744316321459989293 67224856779118620547495985)
  ·
    refine ⟨50418642584338965410621989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67224856779118620547495985 50418642584338965410621989)
    ·
      refine ⟨9453495484563556014491623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 50418642584338965410621989 9453495484563556014491623)
      ·
        refine ⟨14180243226845334021737435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9453495484563556014491623 14180243226845334021737435)
        ·
          refine ⟨21270364840268001032606153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14180243226845334021737435 21270364840268001032606153)
          ·
            refine ⟨15952773630201000774454615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21270364840268001032606153 15952773630201000774454615)
            ·
              refine ⟨23929160445301501161681923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15952773630201000774454615 23929160445301501161681923)
              ·
                refine ⟨35893740667952251742522885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23929160445301501161681923 35893740667952251742522885)
                ·
                  refine ⟨6730076375241047201723041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 35893740667952251742522885 6730076375241047201723041)
                  ·
                    refine ⟨5047557281430785401292281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6730076375241047201723041 5047557281430785401292281)
                    ·
                      refine ⟨3785667961073089050969211, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5047557281430785401292281 3785667961073089050969211)
                      ·
                        rfl

theorem cell23_7372562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 2, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 2, 1, 1, 4, 2, 2].length) (baseStart_7372562 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7372562 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7372562 prefixEnd_7372562 := by exact prefixLift 7372562
  have htrace : WordTrace (prefixWord ++ tailWord_7372562) baseStart_7372562 baseEnd_7372562 := by
    simpa [prefixWord, tailWord_7372562, baseEnd_7372562] using wordTrace_append hprefix tailTrace_7372562
  have hstable : (prefixWord ++ tailWord_7372562).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7372562).length < 2 ^ (prefixWord ++ tailWord_7372562).sum := by decide
  have hdescent : baseEnd_7372562 < baseStart_7372562 := by decide
  rcases family_descends (prefixWord ++ tailWord_7372562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7372598 : List Nat := [5, 1, 2, 2, 1, 1, 2, 1, 1, 7]
def baseStart_7372598 : Nat := 118140960795 + 7372598 * 2 ^ 59
def prefixEnd_7372598 : Nat := 4983230072969 + 3 ^ 40 * 7372598 * 2
def baseEnd_7372598 : Nat := 1261895482125550303373015

theorem tailTrace_7372598 : CollatzResearch.WordTrace tailWord_7372598 prefixEnd_7372598 1261895482125550303373015 := by
  unfold tailWord_7372598
  simp only [CollatzResearch.WordTrace]
  refine ⟨16806296259021503771143403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 179267160096229373558862965 16806296259021503771143403)
  ·
    refine ⟨25209444388532255656715105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16806296259021503771143403 25209444388532255656715105)
    ·
      refine ⟨18907083291399191742536329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25209444388532255656715105 18907083291399191742536329)
      ·
        refine ⟨14180312468549393806902247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18907083291399191742536329 14180312468549393806902247)
        ·
          refine ⟨21270468702824090710353371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14180312468549393806902247 21270468702824090710353371)
          ·
            refine ⟨31905703054236136065530057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21270468702824090710353371 31905703054236136065530057)
            ·
              refine ⟨23929277290677102049147543, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31905703054236136065530057 23929277290677102049147543)
              ·
                refine ⟨35893915936015653073721315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23929277290677102049147543 35893915936015653073721315)
                ·
                  refine ⟨53840873904023479610581973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35893915936015653073721315 53840873904023479610581973)
                  ·
                    refine ⟨1261895482125550303373015, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 53840873904023479610581973 1261895482125550303373015)
                    ·
                      rfl

theorem cell23_7372598_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 1, 2, 1, 1, 7].length) (baseStart_7372598 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7372598 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7372598 prefixEnd_7372598 := by exact prefixLift 7372598
  have htrace : WordTrace (prefixWord ++ tailWord_7372598) baseStart_7372598 baseEnd_7372598 := by
    simpa [prefixWord, tailWord_7372598, baseEnd_7372598] using wordTrace_append hprefix tailTrace_7372598
  have hstable : (prefixWord ++ tailWord_7372598).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7372598).length < 2 ^ (prefixWord ++ tailWord_7372598).sum := by decide
  have hdescent : baseEnd_7372598 < baseStart_7372598 := by decide
  rcases family_descends (prefixWord ++ tailWord_7372598) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7372641 : List Nat := [1, 2, 3, 1, 1, 1, 5, 3, 6]
def baseStart_7372641 : Nat := 118140960795 + 7372641 * 2 ^ 59
def prefixEnd_7372641 : Nat := 4983230072969 + 3 ^ 40 * 7372641 * 2
def baseEnd_7372641 : Nat := 420634280671643804653483

theorem tailTrace_7372641 : CollatzResearch.WordTrace tailWord_7372641 prefixEnd_7372641 420634280671643804653483 := by
  unfold tailWord_7372641
  simp only [CollatzResearch.WordTrace]
  refine ⟨268902308483188278682109777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179268205655458852454739851 268902308483188278682109777)
  ·
    refine ⟨201676731362391209011582333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 268902308483188278682109777 201676731362391209011582333)
    ·
      refine ⟨75628774260896703379343375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 201676731362391209011582333 75628774260896703379343375)
      ·
        refine ⟨113443161391345055069015063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75628774260896703379343375 113443161391345055069015063)
        ·
          refine ⟨170164742087017582603522595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 113443161391345055069015063 170164742087017582603522595)
          ·
            refine ⟨255247113130526373905283893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 170164742087017582603522595 255247113130526373905283893)
            ·
              refine ⟨23929416855986847553620365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 255247113130526373905283893 23929416855986847553620365)
              ·
                refine ⟨8973531320995067832607637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23929416855986847553620365 8973531320995067832607637)
                ·
                  refine ⟨420634280671643804653483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8973531320995067832607637 420634280671643804653483)
                  ·
                    rfl

theorem cell23_7372641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 5, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 5, 3, 6].length) (baseStart_7372641 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7372641 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7372641 prefixEnd_7372641 := by exact prefixLift 7372641
  have htrace : WordTrace (prefixWord ++ tailWord_7372641) baseStart_7372641 baseEnd_7372641 := by
    simpa [prefixWord, tailWord_7372641, baseEnd_7372641] using wordTrace_append hprefix tailTrace_7372641
  have hstable : (prefixWord ++ tailWord_7372641).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7372641).length < 2 ^ (prefixWord ++ tailWord_7372641).sum := by decide
  have hdescent : baseEnd_7372641 < baseStart_7372641 := by decide
  rcases family_descends (prefixWord ++ tailWord_7372641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7372679 : List Nat := [1, 1, 4, 2, 4, 2, 2, 2, 1, 4]
def baseStart_7372679 : Nat := 118140960795 + 7372679 * 2 ^ 59
def prefixEnd_7372679 : Nat := 4983230072969 + 3 ^ 40 * 7372679 * 2
def baseEnd_7372679 : Nat := 1261909346103221697735391

theorem tailTrace_7372679 : CollatzResearch.WordTrace tailWord_7372679 prefixEnd_7372679 1261909346103221697735391 := by
  unfold tailWord_7372679
  simp only [CollatzResearch.WordTrace]
  refine ⟨268903694457050611171993091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179269129638033740781328727 268903694457050611171993091)
  ·
    refine ⟨403355541685575916757989637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 268903694457050611171993091 403355541685575916757989637)
    ·
      refine ⟨75629164066045484392123057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 403355541685575916757989637 75629164066045484392123057)
      ·
        refine ⟨56721873049534113294092293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 75629164066045484392123057 56721873049534113294092293)
        ·
          refine ⟨10635351196787646242642305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 56721873049534113294092293 10635351196787646242642305)
          ·
            refine ⟨7976513397590734681981729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10635351196787646242642305 7976513397590734681981729)
            ·
              refine ⟨5982385048193051011486297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7976513397590734681981729 5982385048193051011486297)
              ·
                refine ⟨4486788786144788258614723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5982385048193051011486297 4486788786144788258614723)
                ·
                  refine ⟨6730183179217182387922085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4486788786144788258614723 6730183179217182387922085)
                  ·
                    refine ⟨1261909346103221697735391, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6730183179217182387922085 1261909346103221697735391)
                    ·
                      rfl

theorem cell23_7372679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 4, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 4, 2, 2, 2, 1, 4].length) (baseStart_7372679 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7372679 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7372679 prefixEnd_7372679 := by exact prefixLift 7372679
  have htrace : WordTrace (prefixWord ++ tailWord_7372679) baseStart_7372679 baseEnd_7372679 := by
    simpa [prefixWord, tailWord_7372679, baseEnd_7372679] using wordTrace_append hprefix tailTrace_7372679
  have hstable : (prefixWord ++ tailWord_7372679).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7372679).length < 2 ^ (prefixWord ++ tailWord_7372679).sum := by decide
  have hdescent : baseEnd_7372679 < baseStart_7372679 := by decide
  rcases family_descends (prefixWord ++ tailWord_7372679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7372708 : List Nat := [2, 3, 1, 2, 1, 3, 2, 1, 3, 1, 4]
def baseStart_7372708 : Nat := 118140960795 + 7372708 * 2 ^ 59
def prefixEnd_7372708 : Nat := 4983230072969 + 3 ^ 40 * 7372708 * 2
def baseEnd_7372708 : Nat := 3785742929248645479743539

theorem tailTrace_7372708 : CollatzResearch.WordTrace tailWord_7372708 prefixEnd_7372708 3785742929248645479743539 := by
  unfold tailWord_7372708
  simp only [CollatzResearch.WordTrace]
  refine ⟨134452376086972774562399389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 179269834782630366083199185 134452376086972774562399389)
  ·
    refine ⟨50419641032614790460899771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 134452376086972774562399389 50419641032614790460899771)
    ·
      refine ⟨75629461548922185691349657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50419641032614790460899771 75629461548922185691349657)
      ·
        refine ⟨56722096161691639268512243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 75629461548922185691349657 56722096161691639268512243)
        ·
          refine ⟨85083144242537458902768365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56722096161691639268512243 85083144242537458902768365)
          ·
            refine ⟨31906179090951547088538137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 85083144242537458902768365 31906179090951547088538137)
            ·
              refine ⟨23929634318213660316403603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31906179090951547088538137 23929634318213660316403603)
              ·
                refine ⟨35894451477320490474605405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23929634318213660316403603 35894451477320490474605405)
                ·
                  refine ⟨13460419303995183927977027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35894451477320490474605405 13460419303995183927977027)
                  ·
                    refine ⟨20190628955992775891965541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13460419303995183927977027 20190628955992775891965541)
                    ·
                      refine ⟨3785742929248645479743539, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20190628955992775891965541 3785742929248645479743539)
                      ·
                        rfl

theorem cell23_7372708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 3, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 3, 2, 1, 3, 1, 4].length) (baseStart_7372708 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7372708 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7372708 prefixEnd_7372708 := by exact prefixLift 7372708
  have htrace : WordTrace (prefixWord ++ tailWord_7372708) baseStart_7372708 baseEnd_7372708 := by
    simpa [prefixWord, tailWord_7372708, baseEnd_7372708] using wordTrace_append hprefix tailTrace_7372708
  have hstable : (prefixWord ++ tailWord_7372708).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7372708).length < 2 ^ (prefixWord ++ tailWord_7372708).sum := by decide
  have hdescent : baseEnd_7372708 < baseStart_7372708 := by decide
  rcases family_descends (prefixWord ++ tailWord_7372708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7372725 : List Nat := [1, 3, 3, 2, 1, 3, 1, 3, 1, 1, 4]
def baseStart_7372725 : Nat := 118140960795 + 7372725 * 2 ^ 59
def prefixEnd_7372725 : Nat := 4983230072969 + 3 ^ 40 * 7372725 * 2
def baseEnd_7372725 : Nat := 3785751658419771913230961

theorem tailTrace_7372725 : CollatzResearch.WordTrace tailWord_7372725 prefixEnd_7372725 3785751658419771913230961 := by
  unfold tailWord_7372725
  simp only [CollatzResearch.WordTrace]
  refine ⟨268905372214883961028167629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179270248143255974018778419 268905372214883961028167629)
  ·
    refine ⟨100839514580581485385562861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 268905372214883961028167629 100839514580581485385562861)
    ·
      refine ⟨37814817967718057019586073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 100839514580581485385562861 37814817967718057019586073)
      ·
        refine ⟨28361113475788542764689555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37814817967718057019586073 28361113475788542764689555)
        ·
          refine ⟨42541670213682814147034333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28361113475788542764689555 42541670213682814147034333)
          ·
            refine ⟨15953126330131055305137875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42541670213682814147034333 15953126330131055305137875)
            ·
              refine ⟨23929689495196582957706813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15953126330131055305137875 23929689495196582957706813)
              ·
                refine ⟨8973633560698718609140055, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23929689495196582957706813 8973633560698718609140055)
                ·
                  refine ⟨13460450341048077913710083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8973633560698718609140055 13460450341048077913710083)
                  ·
                    refine ⟨20190675511572116870565125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13460450341048077913710083 20190675511572116870565125)
                    ·
                      refine ⟨3785751658419771913230961, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20190675511572116870565125 3785751658419771913230961)
                      ·
                        rfl

theorem cell23_7372725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 3, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 3, 1, 3, 1, 1, 4].length) (baseStart_7372725 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7372725 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7372725 prefixEnd_7372725 := by exact prefixLift 7372725
  have htrace : WordTrace (prefixWord ++ tailWord_7372725) baseStart_7372725 baseEnd_7372725 := by
    simpa [prefixWord, tailWord_7372725, baseEnd_7372725] using wordTrace_append hprefix tailTrace_7372725
  have hstable : (prefixWord ++ tailWord_7372725).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7372725).length < 2 ^ (prefixWord ++ tailWord_7372725).sum := by decide
  have hdescent : baseEnd_7372725 < baseStart_7372725 := by decide
  rcases family_descends (prefixWord ++ tailWord_7372725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7372762 : List Nat := [3, 1, 1, 2, 5, 1, 2, 2, 1, 2, 3]
def baseStart_7372762 : Nat := 118140960795 + 7372762 * 2 ^ 59
def prefixEnd_7372762 : Nat := 4983230072969 + 3 ^ 40 * 7372762 * 2
def baseEnd_7372762 : Nat := 3785770657203988268468291

theorem tailTrace_7372762 : CollatzResearch.WordTrace tailWord_7372762 prefixEnd_7372762 3785770657203988268468291 := by
  unfold tailWord_7372762
  simp only [CollatzResearch.WordTrace]
  refine ⟨67226680428937479086816135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 179271147810499944231509693 67226680428937479086816135)
  ·
    refine ⟨100840020643406218630224203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67226680428937479086816135 100840020643406218630224203)
    ·
      refine ⟨151260030965109327945336305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100840020643406218630224203 151260030965109327945336305)
      ·
        refine ⟨113445023223831995959002229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 151260030965109327945336305 113445023223831995959002229)
        ·
          refine ⟨10635470927234249621156459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 113445023223831995959002229 10635470927234249621156459)
          ·
            refine ⟨15953206390851374431734689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10635470927234249621156459 15953206390851374431734689)
            ·
              refine ⟨11964904793138530823801017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15953206390851374431734689 11964904793138530823801017)
              ·
                refine ⟨8973678594853898117850763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11964904793138530823801017 8973678594853898117850763)
                ·
                  refine ⟨13460517892280847176776145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8973678594853898117850763 13460517892280847176776145)
                  ·
                    refine ⟨10095388419210635382582109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13460517892280847176776145 10095388419210635382582109)
                    ·
                      refine ⟨3785770657203988268468291, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10095388419210635382582109 3785770657203988268468291)
                      ·
                        rfl

theorem cell23_7372762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 5, 1, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 5, 1, 2, 2, 1, 2, 3].length) (baseStart_7372762 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7372762 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7372762 prefixEnd_7372762 := by exact prefixLift 7372762
  have htrace : WordTrace (prefixWord ++ tailWord_7372762) baseStart_7372762 baseEnd_7372762 := by
    simpa [prefixWord, tailWord_7372762, baseEnd_7372762] using wordTrace_append hprefix tailTrace_7372762
  have hstable : (prefixWord ++ tailWord_7372762).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7372762).length < 2 ^ (prefixWord ++ tailWord_7372762).sum := by decide
  have hdescent : baseEnd_7372762 < baseStart_7372762 := by decide
  rcases family_descends (prefixWord ++ tailWord_7372762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7372768 : List Nat := [2, 1, 1, 3, 1, 1, 1, 2, 2, 7, 2]
def baseStart_7372768 : Nat := 118140960795 + 7372768 * 2 ^ 59
def prefixEnd_7372768 : Nat := 4983230072969 + 3 ^ 40 * 7372768 * 2
def baseEnd_7372768 : Nat := 3785773738087915244993263

theorem tailTrace_7372768 : CollatzResearch.WordTrace tailWord_7372768 prefixEnd_7372768 3785773738087915244993263 := by
  unfold tailWord_7372768
  simp only [CollatzResearch.WordTrace]
  refine ⟨134453470276864089685991479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 179271293702485452914655305 134453470276864089685991479)
  ·
    refine ⟨201680205415296134528987219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134453470276864089685991479 201680205415296134528987219)
    ·
      refine ⟨302520308122944201793480829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 201680205415296134528987219 302520308122944201793480829)
      ·
        refine ⟨113445115546104075672555311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 302520308122944201793480829 113445115546104075672555311)
        ·
          refine ⟨170167673319156113508832967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 113445115546104075672555311 170167673319156113508832967)
          ·
            refine ⟨255251509978734170263249451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 170167673319156113508832967 255251509978734170263249451)
            ·
              refine ⟨382877264968101255394874177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 255251509978734170263249451 382877264968101255394874177)
              ·
                refine ⟨287157948726075941546155633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 382877264968101255394874177 287157948726075941546155633)
                ·
                  refine ⟨215368461544556956159616725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 287157948726075941546155633 215368461544556956159616725)
                  ·
                    refine ⟨5047698317450553659991017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 215368461544556956159616725 5047698317450553659991017)
                    ·
                      refine ⟨3785773738087915244993263, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5047698317450553659991017 3785773738087915244993263)
                      ·
                        rfl

theorem cell23_7372768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 1, 2, 2, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 1, 2, 2, 7, 2].length) (baseStart_7372768 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7372768 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7372768 prefixEnd_7372768 := by exact prefixLift 7372768
  have htrace : WordTrace (prefixWord ++ tailWord_7372768) baseStart_7372768 baseEnd_7372768 := by
    simpa [prefixWord, tailWord_7372768, baseEnd_7372768] using wordTrace_append hprefix tailTrace_7372768
  have hstable : (prefixWord ++ tailWord_7372768).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7372768).length < 2 ^ (prefixWord ++ tailWord_7372768).sum := by decide
  have hdescent : baseEnd_7372768 < baseStart_7372768 := by decide
  rcases family_descends (prefixWord ++ tailWord_7372768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7372813 : List Nat := [1, 7, 1, 2, 1, 2, 1, 2, 1, 2, 3]
def baseStart_7372813 : Nat := 118140960795 + 7372813 * 2 ^ 59
def prefixEnd_7372813 : Nat := 4983230072969 + 3 ^ 40 * 7372813 * 2
def baseEnd_7372813 : Nat := 3785796844717367568930557

theorem tailTrace_7372813 : CollatzResearch.WordTrace tailWord_7372813 prefixEnd_7372813 3785796844717367568930557 := by
  unfold tailWord_7372813
  simp only [CollatzResearch.WordTrace]
  refine ⟨268908581838565152057371093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179272387892376768038247395 268908581838565152057371093)
  ·
    refine ⟨6302544886841370751344635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 268908581838565152057371093 6302544886841370751344635)
    ·
      refine ⟨9453817330262056127016953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6302544886841370751344635 9453817330262056127016953)
      ·
        refine ⟨7090362997696542095262715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9453817330262056127016953 7090362997696542095262715)
        ·
          refine ⟨10635544496544813142894073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7090362997696542095262715 10635544496544813142894073)
          ·
            refine ⟨7976658372408609857170555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10635544496544813142894073 7976658372408609857170555)
            ·
              refine ⟨11964987558612914785755833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7976658372408609857170555 11964987558612914785755833)
              ·
                refine ⟨8973740668959686089316875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11964987558612914785755833 8973740668959686089316875)
                ·
                  refine ⟨13460611003439529133975313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8973740668959686089316875 13460611003439529133975313)
                  ·
                    refine ⟨10095458252579646850481485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13460611003439529133975313 10095458252579646850481485)
                    ·
                      refine ⟨3785796844717367568930557, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10095458252579646850481485 3785796844717367568930557)
                      ·
                        rfl

theorem cell23_7372813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 1, 2, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 1, 2, 1, 2, 1, 2, 3].length) (baseStart_7372813 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7372813 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7372813 prefixEnd_7372813 := by exact prefixLift 7372813
  have htrace : WordTrace (prefixWord ++ tailWord_7372813) baseStart_7372813 baseEnd_7372813 := by
    simpa [prefixWord, tailWord_7372813, baseEnd_7372813] using wordTrace_append hprefix tailTrace_7372813
  have hstable : (prefixWord ++ tailWord_7372813).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7372813).length < 2 ^ (prefixWord ++ tailWord_7372813).sum := by decide
  have hdescent : baseEnd_7372813 < baseStart_7372813 := by decide
  rcases family_descends (prefixWord ++ tailWord_7372813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7372836 : List Nat := [2, 3, 1, 4, 2, 1, 3, 1, 1, 3, 2]
def baseStart_7372836 : Nat := 118140960795 + 7372836 * 2 ^ 59
def prefixEnd_7372836 : Nat := 4983230072969 + 3 ^ 40 * 7372836 * 2
def baseEnd_7372836 : Nat := 3785808654772420978942951

theorem tailTrace_7372836 : CollatzResearch.WordTrace tailWord_7372836 prefixEnd_7372836 3785808654772420978942951 := by
  unfold tailWord_7372836
  simp only [CollatzResearch.WordTrace]
  refine ⟨134454710358740913492729181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 179272947144987884656972241 134454710358740913492729181)
  ·
    refine ⟨50420516384527842559773443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 134454710358740913492729181 50420516384527842559773443)
    ·
      refine ⟨75630774576791763839660165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50420516384527842559773443 75630774576791763839660165)
      ·
        refine ⟨14180770233148455719936281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 75630774576791763839660165 14180770233148455719936281)
        ·
          refine ⟨10635577674861341789952211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14180770233148455719936281 10635577674861341789952211)
          ·
            refine ⟨15953366512292012684928317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10635577674861341789952211 15953366512292012684928317)
            ·
              refine ⟨5982512442109504756848119, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15953366512292012684928317 5982512442109504756848119)
              ·
                refine ⟨8973768663164257135272179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5982512442109504756848119 8973768663164257135272179)
                ·
                  refine ⟨13460652994746385702908269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8973768663164257135272179 13460652994746385702908269)
                  ·
                    refine ⟨5047744873029894638590601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13460652994746385702908269 5047744873029894638590601)
                    ·
                      refine ⟨3785808654772420978942951, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5047744873029894638590601 3785808654772420978942951)
                      ·
                        rfl

theorem cell23_7372836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 2, 1, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 2, 1, 3, 1, 1, 3, 2].length) (baseStart_7372836 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7372836 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7372836 prefixEnd_7372836 := by exact prefixLift 7372836
  have htrace : WordTrace (prefixWord ++ tailWord_7372836) baseStart_7372836 baseEnd_7372836 := by
    simpa [prefixWord, tailWord_7372836, baseEnd_7372836] using wordTrace_append hprefix tailTrace_7372836
  have hstable : (prefixWord ++ tailWord_7372836).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7372836).length < 2 ^ (prefixWord ++ tailWord_7372836).sum := by decide
  have hdescent : baseEnd_7372836 < baseStart_7372836 := by decide
  rcases family_descends (prefixWord ++ tailWord_7372836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7372841 : List Nat := [1, 2, 1, 1, 1, 1, 1, 1, 3, 3, 8]
def baseStart_7372841 : Nat := 118140960795 + 7372841 * 2 ^ 59
def prefixEnd_7372841 : Nat := 4983230072969 + 3 ^ 40 * 7372841 * 2
def baseEnd_7372841 : Nat := 3785811222175693459380427

theorem tailTrace_7372841 : CollatzResearch.WordTrace tailWord_7372841 prefixEnd_7372841 3785811222175693459380427 := by
  unfold tailWord_7372841
  simp only [CollatzResearch.WordTrace]
  refine ⟨268909603082463712839390377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179273068721642475226260251 268909603082463712839390377)
  ·
    refine ⟨201682202311847784629542783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 268909603082463712839390377 201682202311847784629542783)
    ·
      refine ⟨302523303467771676944314175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 201682202311847784629542783 302523303467771676944314175)
      ·
        refine ⟨453784955201657515416471263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 302523303467771676944314175 453784955201657515416471263)
        ·
          refine ⟨680677432802486273124706895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 453784955201657515416471263 680677432802486273124706895)
          ·
            refine ⟨1021016149203729409687060343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 680677432802486273124706895 1021016149203729409687060343)
            ·
              refine ⟨1531524223805594114530590515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1021016149203729409687060343 1531524223805594114530590515)
              ·
                refine ⟨2297286335708391171795885773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1531524223805594114530590515 2297286335708391171795885773)
                ·
                  refine ⟨861482375890646689423457165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2297286335708391171795885773 861482375890646689423457165)
                  ·
                    refine ⟨323055890958992508533796437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 861482375890646689423457165 323055890958992508533796437)
                    ·
                      refine ⟨3785811222175693459380427, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 323055890958992508533796437 3785811222175693459380427)
                      ·
                        rfl

theorem cell23_7372841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 3, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 3, 3, 8].length) (baseStart_7372841 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7372841 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7372841 prefixEnd_7372841 := by exact prefixLift 7372841
  have htrace : WordTrace (prefixWord ++ tailWord_7372841) baseStart_7372841 baseEnd_7372841 := by
    simpa [prefixWord, tailWord_7372841, baseEnd_7372841] using wordTrace_append hprefix tailTrace_7372841
  have hstable : (prefixWord ++ tailWord_7372841).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7372841).length < 2 ^ (prefixWord ++ tailWord_7372841).sum := by decide
  have hdescent : baseEnd_7372841 < baseStart_7372841 := by decide
  rcases family_descends (prefixWord ++ tailWord_7372841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7372849 : List Nat := [1, 2, 2, 3, 1, 4, 2, 2, 2, 2, 2]
def baseStart_7372849 : Nat := 118140960795 + 7372849 * 2 ^ 59
def prefixEnd_7372849 : Nat := 4983230072969 + 3 ^ 40 * 7372849 * 2
def baseEnd_7372849 : Nat := 3785815330020929428080391

theorem tailTrace_7372849 : CollatzResearch.WordTrace tailWord_7372849 prefixEnd_7372849 3785815330020929428080391 := by
  unfold tailWord_7372849
  simp only [CollatzResearch.WordTrace]
  refine ⟨268909894866434730205681601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179273263244289820137121067 268909894866434730205681601)
  ·
    refine ⟨201682421149826047654261201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 268909894866434730205681601 201682421149826047654261201)
    ·
      refine ⟨151261815862369535740695901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 201682421149826047654261201 151261815862369535740695901)
      ·
        refine ⟨56723180948388575902760963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 151261815862369535740695901 56723180948388575902760963)
        ·
          refine ⟨85084771422582863854141445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56723180948388575902760963 85084771422582863854141445)
          ·
            refine ⟨15953394641734286972651521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 85084771422582863854141445 15953394641734286972651521)
            ·
              refine ⟨11965045981300715229488641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15953394641734286972651521 11965045981300715229488641)
              ·
                refine ⟨8973784485975536422116481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11965045981300715229488641 8973784485975536422116481)
                ·
                  refine ⟨6730338364481652316587361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8973784485975536422116481 6730338364481652316587361)
                  ·
                    refine ⟨5047753773361239237440521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6730338364481652316587361 5047753773361239237440521)
                    ·
                      refine ⟨3785815330020929428080391, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5047753773361239237440521 3785815330020929428080391)
                      ·
                        rfl

theorem cell23_7372849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 4, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 4, 2, 2, 2, 2, 2].length) (baseStart_7372849 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7372849 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7372849 prefixEnd_7372849 := by exact prefixLift 7372849
  have htrace : WordTrace (prefixWord ++ tailWord_7372849) baseStart_7372849 baseEnd_7372849 := by
    simpa [prefixWord, tailWord_7372849, baseEnd_7372849] using wordTrace_append hprefix tailTrace_7372849
  have hstable : (prefixWord ++ tailWord_7372849).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7372849).length < 2 ^ (prefixWord ++ tailWord_7372849).sum := by decide
  have hdescent : baseEnd_7372849 < baseStart_7372849 := by decide
  rcases family_descends (prefixWord ++ tailWord_7372849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7372862 : List Nat := [4, 2, 1, 3, 2, 1, 1, 1, 2, 2, 4]
def baseStart_7372862 : Nat := 118140960795 + 7372862 * 2 ^ 59
def prefixEnd_7372862 : Nat := 4983230072969 + 3 ^ 40 * 7372862 * 2
def baseEnd_7372862 : Nat := 3785822005269437877217831

theorem tailTrace_7372862 : CollatzResearch.WordTrace tailWord_7372862 prefixEnd_7372862 3785822005269437877217831 := by
  unfold tailWord_7372862
  simp only [CollatzResearch.WordTrace]
  refine ⟨33613796126923454178238105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 179273579343591755617269893 33613796126923454178238105)
  ·
    refine ⟨25210347095192590633678579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33613796126923454178238105 25210347095192590633678579)
    ·
      refine ⟨37815520642788885950517869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25210347095192590633678579 37815520642788885950517869)
      ·
        refine ⟨14180820241045832231444201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37815520642788885950517869 14180820241045832231444201)
        ·
          refine ⟨10635615180784374173583151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14180820241045832231444201 10635615180784374173583151)
          ·
            refine ⟨15953422771176561260374727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10635615180784374173583151 15953422771176561260374727)
            ·
              refine ⟨23930134156764841890562091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15953422771176561260374727 23930134156764841890562091)
              ·
                refine ⟨35895201235147262835843137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23930134156764841890562091 35895201235147262835843137)
                ·
                  refine ⟨26921400926360447126882353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35895201235147262835843137 26921400926360447126882353)
                  ·
                    refine ⟨20191050694770335345161765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26921400926360447126882353 20191050694770335345161765)
                    ·
                      refine ⟨3785822005269437877217831, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20191050694770335345161765 3785822005269437877217831)
                      ·
                        rfl

theorem cell23_7372862_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 2, 1, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 2, 1, 1, 1, 2, 2, 4].length) (baseStart_7372862 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7372862 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7372862 prefixEnd_7372862 := by exact prefixLift 7372862
  have htrace : WordTrace (prefixWord ++ tailWord_7372862) baseStart_7372862 baseEnd_7372862 := by
    simpa [prefixWord, tailWord_7372862, baseEnd_7372862] using wordTrace_append hprefix tailTrace_7372862
  have hstable : (prefixWord ++ tailWord_7372862).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7372862).length < 2 ^ (prefixWord ++ tailWord_7372862).sum := by decide
  have hdescent : baseEnd_7372862 < baseStart_7372862 := by decide
  rcases family_descends (prefixWord ++ tailWord_7372862) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7372865 : List Nat := [1, 2, 5, 1, 2, 1, 1, 1, 1, 5, 3]
def baseStart_7372865 : Nat := 118140960795 + 7372865 * 2 ^ 59
def prefixEnd_7372865 : Nat := 4983230072969 + 3 ^ 40 * 7372865 * 2
def baseEnd_7372865 : Nat := 3785823545711401365480317

theorem tailTrace_7372865 : CollatzResearch.WordTrace tailWord_7372865 prefixEnd_7372865 3785823545711401365480317 := by
  unfold tailWord_7372865
  simp only [CollatzResearch.WordTrace]
  refine ⟨268910478434376764938264049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179273652289584509958842699 268910478434376764938264049)
  ·
    refine ⟨201682858825782573703698037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 268910478434376764938264049 201682858825782573703698037)
    ·
      refine ⟨18907768014917116284721691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 201682858825782573703698037 18907768014917116284721691)
      ·
        refine ⟨28361652022375674427082537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18907768014917116284721691 28361652022375674427082537)
        ·
          refine ⟨21271239016781755820311903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28361652022375674427082537 21271239016781755820311903)
          ·
            refine ⟨31906858525172633730467855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21271239016781755820311903 31906858525172633730467855)
            ·
              refine ⟨47860287787758950595701783, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31906858525172633730467855 47860287787758950595701783)
              ·
                refine ⟨71790431681638425893552675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47860287787758950595701783 71790431681638425893552675)
                ·
                  refine ⟨107685647522457638840329013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 71790431681638425893552675 107685647522457638840329013)
                  ·
                    refine ⟨10095529455230403641280845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 107685647522457638840329013 10095529455230403641280845)
                    ·
                      refine ⟨3785823545711401365480317, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10095529455230403641280845 3785823545711401365480317)
                      ·
                        rfl

theorem cell23_7372865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 1, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 1, 1, 1, 1, 5, 3].length) (baseStart_7372865 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7372865 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7372865 prefixEnd_7372865 := by exact prefixLift 7372865
  have htrace : WordTrace (prefixWord ++ tailWord_7372865) baseStart_7372865 baseEnd_7372865 := by
    simpa [prefixWord, tailWord_7372865, baseEnd_7372865] using wordTrace_append hprefix tailTrace_7372865
  have hstable : (prefixWord ++ tailWord_7372865).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7372865).length < 2 ^ (prefixWord ++ tailWord_7372865).sum := by decide
  have hdescent : baseEnd_7372865 < baseStart_7372865 := by decide
  rcases family_descends (prefixWord ++ tailWord_7372865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7372885 : List Nat := [1, 3, 2, 2, 1, 3, 3, 1, 2, 5]
def baseStart_7372885 : Nat := 118140960795 + 7372885 * 2 ^ 59
def prefixEnd_7372885 : Nat := 4983230072969 + 3 ^ 40 * 7372885 * 2
def baseEnd_7372885 : Nat := 1261944605108163762410075

theorem tailTrace_7372885 : CollatzResearch.WordTrace tailWord_7372885 prefixEnd_7372885 1261944605108163762410075 := by
  unfold tailWord_7372885
  simp only [CollatzResearch.WordTrace]
  refine ⟨268911207894304308353992109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179274138596202872235994739 268911207894304308353992109)
  ·
    refine ⟨100841702960364115632747041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 268911207894304308353992109 100841702960364115632747041)
    ·
      refine ⟨75631277220273086724560281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 100841702960364115632747041 75631277220273086724560281)
      ·
        refine ⟨56723457915204815043420211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 75631277220273086724560281 56723457915204815043420211)
        ·
          refine ⟨85085186872807222565130317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56723457915204815043420211 85085186872807222565130317)
          ·
            refine ⟨31906945077302708461923869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 85085186872807222565130317 31906945077302708461923869)
            ·
              refine ⟨11965104403988515673221451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31906945077302708461923869 11965104403988515673221451)
              ·
                refine ⟨17947656605982773509832177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11965104403988515673221451 17947656605982773509832177)
                ·
                  refine ⟨13460742454487080132374133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17947656605982773509832177 13460742454487080132374133)
                  ·
                    refine ⟨1261944605108163762410075, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13460742454487080132374133 1261944605108163762410075)
                    ·
                      rfl

theorem cell23_7372885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 3, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 3, 3, 1, 2, 5].length) (baseStart_7372885 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7372885 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7372885 prefixEnd_7372885 := by exact prefixLift 7372885
  have htrace : WordTrace (prefixWord ++ tailWord_7372885) baseStart_7372885 baseEnd_7372885 := by
    simpa [prefixWord, tailWord_7372885, baseEnd_7372885] using wordTrace_append hprefix tailTrace_7372885
  have hstable : (prefixWord ++ tailWord_7372885).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7372885).length < 2 ^ (prefixWord ++ tailWord_7372885).sum := by decide
  have hdescent : baseEnd_7372885 < baseStart_7372885 := by decide
  rcases family_descends (prefixWord ++ tailWord_7372885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7372905 : List Nat := [1, 2, 1, 1, 1, 5, 1, 1, 4, 4, 2]
def baseStart_7372905 : Nat := 118140960795 + 7372905 * 2 ^ 59
def prefixEnd_7372905 : Nat := 4983230072969 + 3 ^ 40 * 7372905 * 2
def baseEnd_7372905 : Nat := 3785844084937581208980133

theorem tailTrace_7372905 : CollatzResearch.WordTrace tailWord_7372905 prefixEnd_7372905 3785844084937581208980133 := by
  unfold tailWord_7372905
  simp only [CollatzResearch.WordTrace]
  refine ⟨268911937354231851769720169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179274624902821234513146779 268911937354231851769720169)
  ·
    refine ⟨201683953015673888827290127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 268911937354231851769720169 201683953015673888827290127)
    ·
      refine ⟨302525929523510833240935191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 201683953015673888827290127 302525929523510833240935191)
      ·
        refine ⟨453788894285266249861402787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 302525929523510833240935191 453788894285266249861402787)
        ·
          refine ⟨680683341427899374792104181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 453788894285266249861402787 680683341427899374792104181)
          ·
            refine ⟨63814063258865566386759767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 680683341427899374792104181 63814063258865566386759767)
            ·
              refine ⟨95721094888298349580139651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63814063258865566386759767 95721094888298349580139651)
              ·
                refine ⟨143581642332447524370209477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 95721094888298349580139651 143581642332447524370209477)
                ·
                  refine ⟨26921557937333910819414277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 143581642332447524370209477 26921557937333910819414277)
                  ·
                    refine ⟨5047792113250108278640177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 26921557937333910819414277 5047792113250108278640177)
                    ·
                      refine ⟨3785844084937581208980133, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5047792113250108278640177 3785844084937581208980133)
                      ·
                        rfl

theorem cell23_7372905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 1, 1, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 1, 1, 4, 4, 2].length) (baseStart_7372905 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7372905 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7372905 prefixEnd_7372905 := by exact prefixLift 7372905
  have htrace : WordTrace (prefixWord ++ tailWord_7372905) baseStart_7372905 baseEnd_7372905 := by
    simpa [prefixWord, tailWord_7372905, baseEnd_7372905] using wordTrace_append hprefix tailTrace_7372905
  have hstable : (prefixWord ++ tailWord_7372905).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7372905).length < 2 ^ (prefixWord ++ tailWord_7372905).sum := by decide
  have hdescent : baseEnd_7372905 < baseStart_7372905 := by decide
  rcases family_descends (prefixWord ++ tailWord_7372905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7372925 : List Nat := [1, 4, 1, 1, 3, 2, 1, 2, 1, 4, 3]
def baseStart_7372925 : Nat := 118140960795 + 7372925 * 2 ^ 59
def prefixEnd_7372925 : Nat := 4983230072969 + 3 ^ 40 * 7372925 * 2
def baseEnd_7372925 : Nat := 3785854354550671130730041

theorem tailTrace_7372925 : CollatzResearch.WordTrace tailWord_7372925 prefixEnd_7372925 3785854354550671130730041 := by
  unfold tailWord_7372925
  simp only [CollatzResearch.WordTrace]
  refine ⟨268912666814159395185448229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179275111209439596790298819 268912666814159395185448229)
  ·
    refine ⟨50421125027654886597271543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 268912666814159395185448229 50421125027654886597271543)
    ·
      refine ⟨75631687541482329895907315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50421125027654886597271543 75631687541482329895907315)
      ·
        refine ⟨113447531312223494843860973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75631687541482329895907315 113447531312223494843860973)
        ·
          refine ⟨42542824242083810566447865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 113447531312223494843860973 42542824242083810566447865)
          ·
            refine ⟨31907118181562857924835899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42542824242083810566447865 31907118181562857924835899)
            ·
              refine ⟨47860677272344286887253849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31907118181562857924835899 47860677272344286887253849)
              ·
                refine ⟨35895507954258215165440387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47860677272344286887253849 35895507954258215165440387)
                ·
                  refine ⟨53843261931387322748160581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35895507954258215165440387 53843261931387322748160581)
                  ·
                    refine ⟨10095611612135123015280109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 53843261931387322748160581 10095611612135123015280109)
                    ·
                      refine ⟨3785854354550671130730041, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10095611612135123015280109 3785854354550671130730041)
                      ·
                        rfl

theorem cell23_7372925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 2, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 2, 1, 2, 1, 4, 3].length) (baseStart_7372925 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7372925 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7372925 prefixEnd_7372925 := by exact prefixLift 7372925
  have htrace : WordTrace (prefixWord ++ tailWord_7372925) baseStart_7372925 baseEnd_7372925 := by
    simpa [prefixWord, tailWord_7372925, baseEnd_7372925] using wordTrace_append hprefix tailTrace_7372925
  have hstable : (prefixWord ++ tailWord_7372925).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7372925).length < 2 ^ (prefixWord ++ tailWord_7372925).sum := by decide
  have hdescent : baseEnd_7372925 < baseStart_7372925 := by decide
  rcases family_descends (prefixWord ++ tailWord_7372925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7372992 : List Nat := [2, 1, 1, 2, 5, 1, 3, 2, 1, 5]
def baseStart_7372992 : Nat := 118140960795 + 7372992 * 2 ^ 59
def prefixEnd_7372992 : Nat := 4983230072969 + 3 ^ 40 * 7372992 * 2
def baseEnd_7372992 : Nat := 1261962919251507456197411

theorem tailTrace_7372992 : CollatzResearch.WordTrace tailWord_7372992 prefixEnd_7372992 1261962919251507456197411 := by
  unfold tailWord_7372992
  simp only [CollatzResearch.WordTrace]
  refine ⟨134457555252458332814068615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 179276740336611110418758153 134457555252458332814068615)
  ·
    refine ⟨201686332878687499221102923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134457555252458332814068615 201686332878687499221102923)
    ·
      refine ⟨302529499318031248831654385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 201686332878687499221102923 302529499318031248831654385)
      ·
        refine ⟨226897124488523436623740789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 302529499318031248831654385 226897124488523436623740789)
        ·
          refine ⟨21271605420799072183475699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 226897124488523436623740789 21271605420799072183475699)
          ·
            refine ⟨31907408131198608275213549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21271605420799072183475699 31907408131198608275213549)
            ·
              refine ⟨11965278049199478103205081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31907408131198608275213549 11965278049199478103205081)
              ·
                refine ⟨8973958536899608577403811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11965278049199478103205081 8973958536899608577403811)
                ·
                  refine ⟨13460937805349412866105717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8973958536899608577403811 13460937805349412866105717)
                  ·
                    refine ⟨1261962919251507456197411, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13460937805349412866105717 1261962919251507456197411)
                    ·
                      rfl

theorem cell23_7372992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 1, 3, 2, 1, 5].length) (baseStart_7372992 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7372992 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7372992 prefixEnd_7372992 := by exact prefixLift 7372992
  have htrace : WordTrace (prefixWord ++ tailWord_7372992) baseStart_7372992 baseEnd_7372992 := by
    simpa [prefixWord, tailWord_7372992, baseEnd_7372992] using wordTrace_append hprefix tailTrace_7372992
  have hstable : (prefixWord ++ tailWord_7372992).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7372992).length < 2 ^ (prefixWord ++ tailWord_7372992).sum := by decide
  have hdescent : baseEnd_7372992 < baseStart_7372992 := by decide
  rcases family_descends (prefixWord ++ tailWord_7372992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7373008 : List Nat := [2, 1, 1, 1, 1, 2, 1, 1, 2, 5, 6]
def baseStart_7373008 : Nat := 118140960795 + 7373008 * 2 ^ 59
def prefixEnd_7373008 : Nat := 4983230072969 + 3 ^ 40 * 7373008 * 2
def baseEnd_7373008 : Nat := 3785896973444994305992159

theorem tailTrace_7373008 : CollatzResearch.WordTrace tailWord_7373008 prefixEnd_7373008 3785896973444994305992159 := by
  unfold tailWord_7373008
  simp only [CollatzResearch.WordTrace]
  refine ⟨134457847036429350180359839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 179277129381905800240479785 134457847036429350180359839)
  ·
    refine ⟨201686770554644025270539759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134457847036429350180359839 201686770554644025270539759)
    ·
      refine ⟨302530155831966037905809639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 201686770554644025270539759 302530155831966037905809639)
      ·
        refine ⟨453795233747949056858714459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 302530155831966037905809639 453795233747949056858714459)
        ·
          refine ⟨680692850621923585288071689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 453795233747949056858714459 680692850621923585288071689)
          ·
            refine ⟨510519637966442688966053767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 680692850621923585288071689 510519637966442688966053767)
            ·
              refine ⟨765779456949664033449080651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 510519637966442688966053767 765779456949664033449080651)
              ·
                refine ⟨1148669185424496050173620977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 765779456949664033449080651 1148669185424496050173620977)
                ·
                  refine ⟨861501889068372037630215733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1148669185424496050173620977 861501889068372037630215733)
                  ·
                    refine ⟨80765802100159878527832725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 861501889068372037630215733 80765802100159878527832725)
                    ·
                      refine ⟨3785896973444994305992159, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 80765802100159878527832725 3785896973444994305992159)
                      ·
                        rfl

theorem cell23_7373008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 1, 2, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 1, 2, 5, 6].length) (baseStart_7373008 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7373008 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7373008 prefixEnd_7373008 := by exact prefixLift 7373008
  have htrace : WordTrace (prefixWord ++ tailWord_7373008) baseStart_7373008 baseEnd_7373008 := by
    simpa [prefixWord, tailWord_7373008, baseEnd_7373008] using wordTrace_append hprefix tailTrace_7373008
  have hstable : (prefixWord ++ tailWord_7373008).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7373008).length < 2 ^ (prefixWord ++ tailWord_7373008).sum := by decide
  have hdescent : baseEnd_7373008 < baseStart_7373008 := by decide
  rcases family_descends (prefixWord ++ tailWord_7373008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7373025 : List Nat := [1, 2, 3, 1, 3, 1, 1, 2, 3, 2, 4]
def baseStart_7373025 : Nat := 118140960795 + 7373025 * 2 ^ 59
def prefixEnd_7373025 : Nat := 4983230072969 + 3 ^ 40 * 7373025 * 2
def baseEnd_7373025 : Nat := 3785905702616120739479581

theorem tailTrace_7373025 : CollatzResearch.WordTrace tailWord_7373025 prefixEnd_7373025 3785905702616120739479581 := by
  unfold tailWord_7373025
  simp only [CollatzResearch.WordTrace]
  refine ⟨268916314113797112264088529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179277542742531408176059019 268916314113797112264088529)
  ·
    refine ⟨201687235585347834198066397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 268916314113797112264088529 201687235585347834198066397)
    ·
      refine ⟨75632713344505437824274899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 201687235585347834198066397 75632713344505437824274899)
      ·
        refine ⟨113449070016758156736412349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75632713344505437824274899 113449070016758156736412349)
        ·
          refine ⟨42543401256284308776154631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 113449070016758156736412349 42543401256284308776154631)
          ·
            refine ⟨63815101884426463164231947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42543401256284308776154631 63815101884426463164231947)
            ·
              refine ⟨95722652826639694746347921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63815101884426463164231947 95722652826639694746347921)
              ·
                refine ⟨71791989619979771059760941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 95722652826639694746347921 71791989619979771059760941)
                ·
                  refine ⟨26921996107492414147410353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 71791989619979771059760941 26921996107492414147410353)
                  ·
                    refine ⟨20191497080619310610557765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26921996107492414147410353 20191497080619310610557765)
                    ·
                      refine ⟨3785905702616120739479581, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20191497080619310610557765 3785905702616120739479581)
                      ·
                        rfl

theorem cell23_7373025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 1, 2, 3, 2, 4].length) (baseStart_7373025 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7373025 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7373025 prefixEnd_7373025 := by exact prefixLift 7373025
  have htrace : WordTrace (prefixWord ++ tailWord_7373025) baseStart_7373025 baseEnd_7373025 := by
    simpa [prefixWord, tailWord_7373025, baseEnd_7373025] using wordTrace_append hprefix tailTrace_7373025
  have hstable : (prefixWord ++ tailWord_7373025).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7373025).length < 2 ^ (prefixWord ++ tailWord_7373025).sum := by decide
  have hdescent : baseEnd_7373025 < baseStart_7373025 := by decide
  rcases family_descends (prefixWord ++ tailWord_7373025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7373032 : List Nat := [2, 1, 4, 1, 2, 2, 1, 2, 3, 2, 3]
def baseStart_7373032 : Nat := 118140960795 + 7373032 * 2 ^ 59
def prefixEnd_7373032 : Nat := 4983230072969 + 3 ^ 40 * 7373032 * 2
def baseEnd_7373032 : Nat := 3785909296980702212092049

theorem tailTrace_7373032 : CollatzResearch.WordTrace tailWord_7373032 prefixEnd_7373032 3785909296980702212092049 := by
  unfold tailWord_7373032
  simp only [CollatzResearch.WordTrace]
  refine ⟨134458284712385876229796675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 179277712949847834973062233 134458284712385876229796675)
  ·
    refine ⟨201687427068578814344695013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134458284712385876229796675 201687427068578814344695013)
    ·
      refine ⟨37816392575358527689630315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 201687427068578814344695013 37816392575358527689630315)
      ·
        refine ⟨56724588863037791534445473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37816392575358527689630315 56724588863037791534445473)
        ·
          refine ⟨42543441647278343650834105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56724588863037791534445473 42543441647278343650834105)
          ·
            refine ⟨31907581235458757738125579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42543441647278343650834105 31907581235458757738125579)
            ·
              refine ⟨47861371853188136607188369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31907581235458757738125579 47861371853188136607188369)
              ·
                refine ⟨35896028889891102455391277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47861371853188136607188369 35896028889891102455391277)
                ·
                  refine ⟨13461010833709163420771729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35896028889891102455391277 13461010833709163420771729)
                  ·
                    refine ⟨10095758125281872565578797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13461010833709163420771729 10095758125281872565578797)
                    ·
                      refine ⟨3785909296980702212092049, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10095758125281872565578797 3785909296980702212092049)
                      ·
                        rfl

theorem cell23_7373032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 2, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 2, 1, 2, 3, 2, 3].length) (baseStart_7373032 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7373032 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7373032 prefixEnd_7373032 := by exact prefixLift 7373032
  have htrace : WordTrace (prefixWord ++ tailWord_7373032) baseStart_7373032 baseEnd_7373032 := by
    simpa [prefixWord, tailWord_7373032, baseEnd_7373032] using wordTrace_append hprefix tailTrace_7373032
  have hstable : (prefixWord ++ tailWord_7373032).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7373032).length < 2 ^ (prefixWord ++ tailWord_7373032).sum := by decide
  have hdescent : baseEnd_7373032 < baseStart_7373032 := by decide
  rcases family_descends (prefixWord ++ tailWord_7373032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7373042 : List Nat := [3, 2, 1, 3, 2, 1, 1, 3, 1, 2, 4]
def baseStart_7373042 : Nat := 118140960795 + 7373042 * 2 ^ 59
def prefixEnd_7373042 : Nat := 4983230072969 + 3 ^ 40 * 7373042 * 2
def baseEnd_7373042 : Nat := 3785914431787247172967003

theorem tailTrace_7373042 : CollatzResearch.WordTrace tailWord_7373042 prefixEnd_7373042 3785914431787247172967003 := by
  unfold tailWord_7373042
  simp only [CollatzResearch.WordTrace]
  refine ⟨67229233538683881041864345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 179277956103157016111638253 67229233538683881041864345)
  ·
    refine ⟨50421925154012910781398259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67229233538683881041864345 50421925154012910781398259)
    ·
      refine ⟨75632887731019366172097389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50421925154012910781398259 75632887731019366172097389)
      ·
        refine ⟨28362332899132262314536521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 75632887731019366172097389 28362332899132262314536521)
        ·
          refine ⟨21271749674349196735902391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28362332899132262314536521 21271749674349196735902391)
          ·
            refine ⟨31907624511523795103853587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21271749674349196735902391 31907624511523795103853587)
            ·
              refine ⟨47861436767285692655780381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31907624511523795103853587 47861436767285692655780381)
              ·
                refine ⟨17948038787732134745917643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 47861436767285692655780381 17948038787732134745917643)
                ·
                  refine ⟨26922058181598202118876465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17948038787732134745917643 26922058181598202118876465)
                  ·
                    refine ⟨20191543636198651589157349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26922058181598202118876465 20191543636198651589157349)
                    ·
                      refine ⟨3785914431787247172967003, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20191543636198651589157349 3785914431787247172967003)
                      ·
                        rfl

theorem cell23_7373042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 1, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 1, 1, 3, 1, 2, 4].length) (baseStart_7373042 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7373042 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7373042 prefixEnd_7373042 := by exact prefixLift 7373042
  have htrace : WordTrace (prefixWord ++ tailWord_7373042) baseStart_7373042 baseEnd_7373042 := by
    simpa [prefixWord, tailWord_7373042, baseEnd_7373042] using wordTrace_append hprefix tailTrace_7373042
  have hstable : (prefixWord ++ tailWord_7373042).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7373042).length < 2 ^ (prefixWord ++ tailWord_7373042).sum := by decide
  have hdescent : baseEnd_7373042 < baseStart_7373042 := by decide
  rcases family_descends (prefixWord ++ tailWord_7373042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7373052 : List Nat := [2, 2, 2, 1, 4, 2, 3, 7]
def baseStart_7373052 : Nat := 118140960795 + 7373052 * 2 ^ 59
def prefixEnd_7373052 : Nat := 4983230072969 + 3 ^ 40 * 7373052 * 2
def baseEnd_7373052 : Nat := 140219243207177486438591

theorem tailTrace_7373052 : CollatzResearch.WordTrace tailWord_7373052 prefixEnd_7373052 140219243207177486438591 := by
  unfold tailWord_7373052
  simp only [CollatzResearch.WordTrace]
  refine ⟨134458649442349647937660705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 179278199256466197250214273 134458649442349647937660705)
  ·
    refine ⟨100843987081762235953245529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 134458649442349647937660705 100843987081762235953245529)
    ·
      refine ⟨75632990311321676964934147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 100843987081762235953245529 75632990311321676964934147)
      ·
        refine ⟨113449485466982515447401221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75632990311321676964934147 113449485466982515447401221)
        ·
          refine ⟨21271778525059221646387729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 113449485466982515447401221 21271778525059221646387729)
          ·
            refine ⟨15953833893794416234790797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21271778525059221646387729 15953833893794416234790797)
            ·
              refine ⟨5982687710172906088046549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15953833893794416234790797 5982687710172906088046549)
              ·
                refine ⟨140219243207177486438591, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5982687710172906088046549 140219243207177486438591)
                ·
                  rfl

theorem cell23_7373052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 2, 3, 7].length) (baseStart_7373052 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7373052 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7373052 prefixEnd_7373052 := by exact prefixLift 7373052
  have htrace : WordTrace (prefixWord ++ tailWord_7373052) baseStart_7373052 baseEnd_7373052 := by
    simpa [prefixWord, tailWord_7373052, baseEnd_7373052] using wordTrace_append hprefix tailTrace_7373052
  have hstable : (prefixWord ++ tailWord_7373052).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7373052).length < 2 ^ (prefixWord ++ tailWord_7373052).sum := by decide
  have hdescent : baseEnd_7373052 < baseStart_7373052 := by decide
  rcases family_descends (prefixWord ++ tailWord_7373052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7373063 : List Nat := [1, 1, 4, 5, 1, 2, 2, 1, 1, 1, 4]
def baseStart_7373063 : Nat := 118140960795 + 7373063 * 2 ^ 59
def prefixEnd_7373063 : Nat := 4983230072969 + 3 ^ 40 * 7373063 * 2
def baseEnd_7373063 : Nat := 3785925214880991590804407

theorem tailTrace_7373063 : CollatzResearch.WordTrace tailWord_7373063 prefixEnd_7373063 3785925214880991590804407 := by
  unfold tailWord_7373063
  simp only [CollatzResearch.WordTrace]
  refine ⟨268917700087659444753971843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179278466725106296502647895 268917700087659444753971843)
  ·
    refine ⟨403376550131489167130957765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 268917700087659444753971843 403376550131489167130957765)
    ·
      refine ⟨75633103149654218837054581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 403376550131489167130957765 75633103149654218837054581)
      ·
        refine ⟨7090603420280083015973867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 75633103149654218837054581 7090603420280083015973867)
        ·
          refine ⟨10635905130420124523960801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7090603420280083015973867 10635905130420124523960801)
          ·
            refine ⟨7976928847815093392970601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10635905130420124523960801 7976928847815093392970601)
            ·
              refine ⟨5982696635861320044727951, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7976928847815093392970601 5982696635861320044727951)
              ·
                refine ⟨8974044953791980067091927, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5982696635861320044727951 8974044953791980067091927)
                ·
                  refine ⟨13461067430687970100637891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8974044953791980067091927 13461067430687970100637891)
                  ·
                    refine ⟨20191601146031955150956837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13461067430687970100637891 20191601146031955150956837)
                    ·
                      refine ⟨3785925214880991590804407, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20191601146031955150956837 3785925214880991590804407)
                      ·
                        rfl

theorem cell23_7373063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 1, 2, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 1, 2, 2, 1, 1, 1, 4].length) (baseStart_7373063 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7373063 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7373063 prefixEnd_7373063 := by exact prefixLift 7373063
  have htrace : WordTrace (prefixWord ++ tailWord_7373063) baseStart_7373063 baseEnd_7373063 := by
    simpa [prefixWord, tailWord_7373063, baseEnd_7373063] using wordTrace_append hprefix tailTrace_7373063
  have hstable : (prefixWord ++ tailWord_7373063).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7373063).length < 2 ^ (prefixWord ++ tailWord_7373063).sum := by decide
  have hdescent : baseEnd_7373063 < baseStart_7373063 := by decide
  rcases family_descends (prefixWord ++ tailWord_7373063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7373079 : List Nat := [1, 1, 3, 4, 1, 3, 1, 1, 4, 1, 3]
def baseStart_7373079 : Nat := 118140960795 + 7373079 * 2 ^ 59
def prefixEnd_7373079 : Nat := 4983230072969 + 3 ^ 40 * 7373079 * 2
def baseEnd_7373079 : Nat := 3785933430571463528204333

theorem tailTrace_7373079 : CollatzResearch.WordTrace tailWord_7373079 prefixEnd_7373079 3785933430571463528204333 := by
  unfold tailWord_7373079
  simp only [CollatzResearch.WordTrace]
  refine ⟨268918283655601479486554291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179278855770400986324369527 268918283655601479486554291)
  ·
    refine ⟨403377425483402219229831437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 268918283655601479486554291 403377425483402219229831437)
    ·
      refine ⟨151266534556275832211186789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 403377425483402219229831437 151266534556275832211186789)
      ·
        refine ⟨28362475229301718539597523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 151266534556275832211186789 28362475229301718539597523)
        ·
          refine ⟨42543712843952577809396285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28362475229301718539597523 42543712843952577809396285)
          ·
            refine ⟨15953892316482216678523607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42543712843952577809396285 15953892316482216678523607)
            ·
              refine ⟨23930838474723325017785411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15953892316482216678523607 23930838474723325017785411)
              ·
                refine ⟨35896257712084987526678117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23930838474723325017785411 35896257712084987526678117)
                ·
                  refine ⟨6730548321015935161252147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 35896257712084987526678117 6730548321015935161252147)
                  ·
                    refine ⟨10095822481523902741878221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6730548321015935161252147 10095822481523902741878221)
                    ·
                      refine ⟨3785933430571463528204333, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10095822481523902741878221 3785933430571463528204333)
                      ·
                        rfl

theorem cell23_7373079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 3, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 3, 1, 1, 4, 1, 3].length) (baseStart_7373079 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7373079 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7373079 prefixEnd_7373079 := by exact prefixLift 7373079
  have htrace : WordTrace (prefixWord ++ tailWord_7373079) baseStart_7373079 baseEnd_7373079 := by
    simpa [prefixWord, tailWord_7373079, baseEnd_7373079] using wordTrace_append hprefix tailTrace_7373079
  have hstable : (prefixWord ++ tailWord_7373079).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7373079).length < 2 ^ (prefixWord ++ tailWord_7373079).sum := by decide
  have hdescent : baseEnd_7373079 < baseStart_7373079 := by decide
  rcases family_descends (prefixWord ++ tailWord_7373079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7373096 : List Nat := [2, 1, 5, 1, 3, 2, 1, 1, 1, 3, 3]
def baseStart_7373096 : Nat := 118140960795 + 7373096 * 2 ^ 59
def prefixEnd_7373096 : Nat := 4983230072969 + 3 ^ 40 * 7373096 * 2
def baseEnd_7373096 : Nat := 3785942159742589961691755

theorem tailTrace_7373096 : CollatzResearch.WordTrace tailWord_7373096 prefixEnd_7373096 3785942159742589961691755 := by
  unfold tailWord_7373096
  simp only [CollatzResearch.WordTrace]
  refine ⟨134459451848269945694961571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 179279269131026594259948761 134459451848269945694961571)
  ·
    refine ⟨201689177772404918542442357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134459451848269945694961571 201689177772404918542442357)
    ·
      refine ⟨18908360416162961113353971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 201689177772404918542442357 18908360416162961113353971)
      ·
        refine ⟨28362540624244441670030957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18908360416162961113353971 28362540624244441670030957)
        ·
          refine ⟨10635952734091665626261609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28362540624244441670030957 10635952734091665626261609)
          ·
            refine ⟨7976964550568749219696207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10635952734091665626261609 7976964550568749219696207)
            ·
              refine ⟨11965446825853123829544311, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7976964550568749219696207 11965446825853123829544311)
              ·
                refine ⟨17948170238779685744316467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11965446825853123829544311 17948170238779685744316467)
                ·
                  refine ⟨26922255358169528616474701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17948170238779685744316467 26922255358169528616474701)
                  ·
                    refine ⟨10095845759313573231178013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 26922255358169528616474701 10095845759313573231178013)
                    ·
                      refine ⟨3785942159742589961691755, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10095845759313573231178013 3785942159742589961691755)
                      ·
                        rfl

theorem cell23_7373096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 3, 2, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 3, 2, 1, 1, 1, 3, 3].length) (baseStart_7373096 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7373096 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7373096 prefixEnd_7373096 := by exact prefixLift 7373096
  have htrace : WordTrace (prefixWord ++ tailWord_7373096) baseStart_7373096 baseEnd_7373096 := by
    simpa [prefixWord, tailWord_7373096, baseEnd_7373096] using wordTrace_append hprefix tailTrace_7373096
  have hstable : (prefixWord ++ tailWord_7373096).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7373096).length < 2 ^ (prefixWord ++ tailWord_7373096).sum := by decide
  have hdescent : baseEnd_7373096 < baseStart_7373096 := by decide
  rcases family_descends (prefixWord ++ tailWord_7373096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7373119 : List Nat := [1, 1, 2, 2, 4, 1, 1, 1, 6, 2, 2]
def baseStart_7373119 : Nat := 118140960795 + 7373119 * 2 ^ 59
def prefixEnd_7373119 : Nat := 4983230072969 + 3 ^ 40 * 7373119 * 2
def baseEnd_7373119 : Nat := 3785953969797643371704149

theorem tailTrace_7373119 : CollatzResearch.WordTrace tailWord_7373119 prefixEnd_7373119 3785953969797643371704149 := by
  unfold tailWord_7373119
  simp only [CollatzResearch.WordTrace]
  refine ⟨268919742575456566318010411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179279828383637710878673607 268919742575456566318010411)
  ·
    refine ⟨403379613863184849477015617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 268919742575456566318010411 403379613863184849477015617)
    ·
      refine ⟨302534710397388637107761713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 403379613863184849477015617 302534710397388637107761713)
      ·
        refine ⟨226901032798041477830821285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 302534710397388637107761713 226901032798041477830821285)
        ·
          refine ⟨42543943649632777093278991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 226901032798041477830821285 42543943649632777093278991)
          ·
            refine ⟨63815915474449165639918487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42543943649632777093278991 63815915474449165639918487)
            ·
              refine ⟨95723873211673748459877731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63815915474449165639918487 95723873211673748459877731)
              ·
                refine ⟨143585809817510622689816597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 95723873211673748459877731 143585809817510622689816597)
                ·
                  refine ⟨6730584835195810438585153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 143585809817510622689816597 6730584835195810438585153)
                  ·
                    refine ⟨5047938626396857828938865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6730584835195810438585153 5047938626396857828938865)
                    ·
                      refine ⟨3785953969797643371704149, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5047938626396857828938865 3785953969797643371704149)
                      ·
                        rfl

theorem cell23_7373119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 1, 1, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 1, 1, 6, 2, 2].length) (baseStart_7373119 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7373119 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7373119 prefixEnd_7373119 := by exact prefixLift 7373119
  have htrace : WordTrace (prefixWord ++ tailWord_7373119) baseStart_7373119 baseEnd_7373119 := by
    simpa [prefixWord, tailWord_7373119, baseEnd_7373119] using wordTrace_append hprefix tailTrace_7373119
  have hstable : (prefixWord ++ tailWord_7373119).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7373119).length < 2 ^ (prefixWord ++ tailWord_7373119).sum := by decide
  have hdescent : baseEnd_7373119 < baseStart_7373119 := by decide
  rcases family_descends (prefixWord ++ tailWord_7373119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7373209 : List Nat := [1, 2, 1, 2, 1, 4, 3, 1, 2, 4, 2]
def baseStart_7373209 : Nat := 118140960795 + 7373209 * 2 ^ 59
def prefixEnd_7373209 : Nat := 4983230072969 + 3 ^ 40 * 7373209 * 2
def baseEnd_7373209 : Nat := 3786000183056548019578735

theorem tailTrace_7373209 : CollatzResearch.WordTrace tailWord_7373209 prefixEnd_7373209 3786000183056548019578735 := by
  unfold tailWord_7373209
  simp only [CollatzResearch.WordTrace]
  refine ⟨268923025145130511688786681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179282016763420341125857787 268923025145130511688786681)
  ·
    refine ⟨201692268858847883766590011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 268923025145130511688786681 201692268858847883766590011)
    ·
      refine ⟨302538403288271825649885017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 201692268858847883766590011 302538403288271825649885017)
      ·
        refine ⟨226903802466203869237413763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 302538403288271825649885017 226903802466203869237413763)
        ·
          refine ⟨340355703699305803856120645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 226903802466203869237413763 340355703699305803856120645)
          ·
            refine ⟨63816694443619838223022621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 340355703699305803856120645 63816694443619838223022621)
            ·
              refine ⟨23931260416357439333633483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 63816694443619838223022621 23931260416357439333633483)
              ·
                refine ⟨35896890624536159000450225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23931260416357439333633483 35896890624536159000450225)
                ·
                  refine ⟨26922667968402119250337669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35896890624536159000450225 26922667968402119250337669)
                  ·
                    refine ⟨5048000244075397359438313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 26922667968402119250337669 5048000244075397359438313)
                    ·
                      refine ⟨3786000183056548019578735, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5048000244075397359438313 3786000183056548019578735)
                      ·
                        rfl

theorem cell23_7373209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 3, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 3, 1, 2, 4, 2].length) (baseStart_7373209 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7373209 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7373209 prefixEnd_7373209 := by exact prefixLift 7373209
  have htrace : WordTrace (prefixWord ++ tailWord_7373209) baseStart_7373209 baseEnd_7373209 := by
    simpa [prefixWord, tailWord_7373209, baseEnd_7373209] using wordTrace_append hprefix tailTrace_7373209
  have hstable : (prefixWord ++ tailWord_7373209).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7373209).length < 2 ^ (prefixWord ++ tailWord_7373209).sum := by decide
  have hdescent : baseEnd_7373209 < baseStart_7373209 := by decide
  rcases family_descends (prefixWord ++ tailWord_7373209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7373219 : List Nat := [1, 1, 1, 4, 1, 5, 1, 2, 3, 4]
def baseStart_7373219 : Nat := 118140960795 + 7373219 * 2 ^ 59
def prefixEnd_7373219 : Nat := 4983230072969 + 3 ^ 40 * 7373219 * 2
def baseEnd_7373219 : Nat := 1262001772621030993484563

theorem tailTrace_7373219 : CollatzResearch.WordTrace tailWord_7373219 prefixEnd_7373219 1262001772621030993484563 := by
  unfold tailWord_7373219
  simp only [CollatzResearch.WordTrace]
  refine ⟨268923389875094283396650711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179282259916729522264433807 268923389875094283396650711)
  ·
    refine ⟨403385084812641425094976067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 268923389875094283396650711 403385084812641425094976067)
    ·
      refine ⟨605077627218962137642464101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 403385084812641425094976067 605077627218962137642464101)
      ·
        refine ⟨113452055103555400807962019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 605077627218962137642464101 113452055103555400807962019)
        ·
          refine ⟨170178082655333101211943029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 113452055103555400807962019 170178082655333101211943029)
          ·
            refine ⟨15954195248937478238619659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 170178082655333101211943029 15954195248937478238619659)
            ·
              refine ⟨23931292873406217357929489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15954195248937478238619659 23931292873406217357929489)
              ·
                refine ⟨17948469655054663018447117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23931292873406217357929489 17948469655054663018447117)
                ·
                  refine ⟨6730676120645498631917669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17948469655054663018447117 6730676120645498631917669)
                  ·
                    refine ⟨1262001772621030993484563, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6730676120645498631917669 1262001772621030993484563)
                    ·
                      rfl

theorem cell23_7373219_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 5, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 5, 1, 2, 3, 4].length) (baseStart_7373219 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7373219 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7373219 prefixEnd_7373219 := by exact prefixLift 7373219
  have htrace : WordTrace (prefixWord ++ tailWord_7373219) baseStart_7373219 baseEnd_7373219 := by
    simpa [prefixWord, tailWord_7373219, baseEnd_7373219] using wordTrace_append hprefix tailTrace_7373219
  have hstable : (prefixWord ++ tailWord_7373219).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7373219).length < 2 ^ (prefixWord ++ tailWord_7373219).sum := by decide
  have hdescent : baseEnd_7373219 < baseStart_7373219 := by decide
  rcases family_descends (prefixWord ++ tailWord_7373219) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7373242 : List Nat := [3, 1, 1, 1, 2, 1, 1, 2, 1, 7, 3]
def baseStart_7373242 : Nat := 118140960795 + 7373242 * 2 ^ 59
def prefixEnd_7373242 : Nat := 4983230072969 + 3 ^ 40 * 7373242 * 2
def baseEnd_7373242 : Nat := 3786017127918146390466083

theorem tailTrace_7373242 : CollatzResearch.WordTrace tailWord_7373242 prefixEnd_7373242 3786017127918146390466083 := by
  unfold tailWord_7373242
  simp only [CollatzResearch.WordTrace]
  refine ⟨67231057188502739581184495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 179282819169340638883158653 67231057188502739581184495)
  ·
    refine ⟨100846585782754109371776743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67231057188502739581184495 100846585782754109371776743)
    ·
      refine ⟨151269878674131164057665115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100846585782754109371776743 151269878674131164057665115)
      ·
        refine ⟨226904818011196746086497673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 151269878674131164057665115 226904818011196746086497673)
        ·
          refine ⟨170178613508397559564873255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 226904818011196746086497673 170178613508397559564873255)
          ·
            refine ⟨255267920262596339347309883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 170178613508397559564873255 255267920262596339347309883)
            ·
              refine ⟨382901880393894509020964825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 255267920262596339347309883 382901880393894509020964825)
              ·
                refine ⟨287176410295420881765723619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 382901880393894509020964825 287176410295420881765723619)
                ·
                  refine ⟨430764615443131322648585429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 287176410295420881765723619 430764615443131322648585429)
                  ·
                    refine ⟨10096045674448390374576221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 430764615443131322648585429 10096045674448390374576221)
                    ·
                      refine ⟨3786017127918146390466083, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10096045674448390374576221 3786017127918146390466083)
                      ·
                        rfl

theorem cell23_7373242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 1, 2, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 1, 2, 1, 7, 3].length) (baseStart_7373242 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7373242 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7373242 prefixEnd_7373242 := by exact prefixLift 7373242
  have htrace : WordTrace (prefixWord ++ tailWord_7373242) baseStart_7373242 baseEnd_7373242 := by
    simpa [prefixWord, tailWord_7373242, baseEnd_7373242] using wordTrace_append hprefix tailTrace_7373242
  have hstable : (prefixWord ++ tailWord_7373242).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7373242).length < 2 ^ (prefixWord ++ tailWord_7373242).sum := by decide
  have hdescent : baseEnd_7373242 < baseStart_7373242 := by decide
  rcases family_descends (prefixWord ++ tailWord_7373242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7373279 : List Nat := [1, 1, 2, 3, 3, 2, 1, 4, 1, 5]
def baseStart_7373279 : Nat := 118140960795 + 7373279 * 2 ^ 59
def prefixEnd_7373279 : Nat := 4983230072969 + 3 ^ 40 * 7373279 * 2
def baseEnd_7373279 : Nat := 1262012042234120915234471

theorem tailTrace_7373279 : CollatzResearch.WordTrace tailWord_7373279 prefixEnd_7373279 1262012042234120915234471 := by
  unfold tailWord_7373279
  simp only [CollatzResearch.WordTrace]
  refine ⟨268925578254876913643834891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179283718836584609095889927 268925578254876913643834891)
  ·
    refine ⟨403388367382315370465752337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 268925578254876913643834891 403388367382315370465752337)
    ·
      refine ⟨302541275536736527849314253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 403388367382315370465752337 302541275536736527849314253)
      ·
        refine ⟨113452978326276197943492845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 302541275536736527849314253 113452978326276197943492845)
        ·
          refine ⟨42544866872353574228809817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 113452978326276197943492845 42544866872353574228809817)
          ·
            refine ⟨31908650154265180671607363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42544866872353574228809817 31908650154265180671607363)
            ·
              refine ⟨47862975231397771007411045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31908650154265180671607363 47862975231397771007411045)
              ·
                refine ⟨8974307855887082063889571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 47862975231397771007411045 8974307855887082063889571)
                ·
                  refine ⟨13461461783830623095834357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8974307855887082063889571 13461461783830623095834357)
                  ·
                    refine ⟨1262012042234120915234471, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13461461783830623095834357 1262012042234120915234471)
                    ·
                      rfl

theorem cell23_7373279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 2, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 2, 1, 4, 1, 5].length) (baseStart_7373279 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7373279 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7373279 prefixEnd_7373279 := by exact prefixLift 7373279
  have htrace : WordTrace (prefixWord ++ tailWord_7373279) baseStart_7373279 baseEnd_7373279 := by
    simpa [prefixWord, tailWord_7373279, baseEnd_7373279] using wordTrace_append hprefix tailTrace_7373279
  have hstable : (prefixWord ++ tailWord_7373279).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7373279).length < 2 ^ (prefixWord ++ tailWord_7373279).sum := by decide
  have hdescent : baseEnd_7373279 < baseStart_7373279 := by decide
  rcases family_descends (prefixWord ++ tailWord_7373279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7373292 : List Nat := [2, 2, 1, 1, 2, 1, 4, 1, 3, 6]
def baseStart_7373292 : Nat := 118140960795 + 7373292 * 2 ^ 59
def prefixEnd_7373292 : Nat := 4983230072969 + 3 ^ 40 * 7373292 * 2
def baseEnd_7373292 : Nat := 1262014267316957064946951

theorem tailTrace_7373292 : CollatzResearch.WordTrace tailWord_7373292 prefixEnd_7373292 1262014267316957064946951 := by
  unfold tailWord_7373292
  simp only [CollatzResearch.WordTrace]
  refine ⟨134463026201914908432029065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 179284034935886544576038753 134463026201914908432029065)
  ·
    refine ⟨100847269651436181324021799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 134463026201914908432029065 100847269651436181324021799)
    ·
      refine ⟨151270904477154271986032699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100847269651436181324021799 151270904477154271986032699)
      ·
        refine ⟨226906356715731407979049049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 151270904477154271986032699 226906356715731407979049049)
        ·
          refine ⟨170179767536798555984286787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 226906356715731407979049049 170179767536798555984286787)
          ·
            refine ⟨255269651305197833976430181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 170179767536798555984286787 255269651305197833976430181)
            ·
              refine ⟨47863059619724593870580659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 255269651305197833976430181 47863059619724593870580659)
              ·
                refine ⟨71794589429586890805870989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47863059619724593870580659 71794589429586890805870989)
                ·
                  refine ⟨26922971036095084052201621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 71794589429586890805870989 26922971036095084052201621)
                  ·
                    refine ⟨1262014267316957064946951, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26922971036095084052201621 1262014267316957064946951)
                    ·
                      rfl

theorem cell23_7373292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 6].length) (baseStart_7373292 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7373292 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7373292 prefixEnd_7373292 := by exact prefixLift 7373292
  have htrace : WordTrace (prefixWord ++ tailWord_7373292) baseStart_7373292 baseEnd_7373292 := by
    simpa [prefixWord, tailWord_7373292, baseEnd_7373292] using wordTrace_append hprefix tailTrace_7373292
  have hstable : (prefixWord ++ tailWord_7373292).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7373292).length < 2 ^ (prefixWord ++ tailWord_7373292).sum := by decide
  have hdescent : baseEnd_7373292 < baseStart_7373292 := by decide
  rcases family_descends (prefixWord ++ tailWord_7373292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7373299 : List Nat := [1, 1, 1, 2, 2, 2, 3, 5, 1, 1, 4]
def baseStart_7373299 : Nat := 118140960795 + 7373299 * 2 ^ 59
def prefixEnd_7373299 : Nat := 4983230072969 + 3 ^ 40 * 7373299 * 2
def baseEnd_7373299 : Nat := 3786046396315452667453321

theorem tailTrace_7373299 : CollatzResearch.WordTrace tailWord_7373299 prefixEnd_7373299 3786046396315452667453321 := by
  unfold tailWord_7373299
  simp only [CollatzResearch.WordTrace]
  refine ⟨268926307714804457059562951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179284205143202971373041967 268926307714804457059562951)
  ·
    refine ⟨403389461572206685589344427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 268926307714804457059562951 403389461572206685589344427)
    ·
      refine ⟨605084192358310028384016641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 403389461572206685589344427 605084192358310028384016641)
      ·
        refine ⟨453813144268732521288012481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 605084192358310028384016641 453813144268732521288012481)
        ·
          refine ⟨340359858201549390966009361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 453813144268732521288012481 340359858201549390966009361)
          ·
            refine ⟨255269893651162043224507021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 340359858201549390966009361 255269893651162043224507021)
            ·
              refine ⟨95726210119185766209190133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 255269893651162043224507021 95726210119185766209190133)
              ·
                refine ⟨8974332198673665582111575, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 95726210119185766209190133 8974332198673665582111575)
                ·
                  refine ⟨13461498298010498373167363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8974332198673665582111575 13461498298010498373167363)
                  ·
                    refine ⟨20192247447015747559751045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13461498298010498373167363 20192247447015747559751045)
                    ·
                      refine ⟨3786046396315452667453321, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20192247447015747559751045 3786046396315452667453321)
                      ·
                        rfl

theorem cell23_7373299_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 3, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 3, 5, 1, 1, 4].length) (baseStart_7373299 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7373299 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7373299 prefixEnd_7373299 := by exact prefixLift 7373299
  have htrace : WordTrace (prefixWord ++ tailWord_7373299) baseStart_7373299 baseEnd_7373299 := by
    simpa [prefixWord, tailWord_7373299, baseEnd_7373299] using wordTrace_append hprefix tailTrace_7373299
  have hstable : (prefixWord ++ tailWord_7373299).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7373299).length < 2 ^ (prefixWord ++ tailWord_7373299).sum := by decide
  have hdescent : baseEnd_7373299 < baseStart_7373299 := by decide
  rcases family_descends (prefixWord ++ tailWord_7373299) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7373309 : List Nat := [1, 4, 1, 1, 1, 3, 1, 3, 4, 4]
def baseStart_7373309 : Nat := 118140960795 + 7373309 * 2 ^ 59
def prefixEnd_7373309 : Nat := 4983230072969 + 3 ^ 40 * 7373309 * 2
def baseEnd_7373309 : Nat := 1262017177040665876109425

theorem tailTrace_7373309 : CollatzResearch.WordTrace tailWord_7373309 prefixEnd_7373309 1262017177040665876109425 := by
  unfold tailWord_7373309
  simp only [CollatzResearch.WordTrace]
  refine ⟨268926672444768228767426981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179284448296512152511617987 268926672444768228767426981)
  ·
    refine ⟨50423751083394042893892559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 268926672444768228767426981 50423751083394042893892559)
    ·
      refine ⟨75635626625091064340838839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50423751083394042893892559 75635626625091064340838839)
      ·
        refine ⟨113453439937636596511258259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75635626625091064340838839 113453439937636596511258259)
        ·
          refine ⟨170180159906454894766887389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 113453439937636596511258259 170180159906454894766887389)
          ·
            refine ⟨63817559964920585537582771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 170180159906454894766887389 63817559964920585537582771)
            ·
              refine ⟨95726339947380878306374157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63817559964920585537582771 95726339947380878306374157)
              ·
                refine ⟨35897377480267829364890309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 95726339947380878306374157 35897377480267829364890309)
                ·
                  refine ⟨6730758277550218005916933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 35897377480267829364890309 6730758277550218005916933)
                  ·
                    refine ⟨1262017177040665876109425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6730758277550218005916933 1262017177040665876109425)
                    ·
                      rfl

theorem cell23_7373309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 1, 3, 4, 4].length) (baseStart_7373309 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7373309 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7373309 prefixEnd_7373309 := by exact prefixLift 7373309
  have htrace : WordTrace (prefixWord ++ tailWord_7373309) baseStart_7373309 baseEnd_7373309 := by
    simpa [prefixWord, tailWord_7373309, baseEnd_7373309] using wordTrace_append hprefix tailTrace_7373309
  have hstable : (prefixWord ++ tailWord_7373309).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7373309).length < 2 ^ (prefixWord ++ tailWord_7373309).sum := by decide
  have hdescent : baseEnd_7373309 < baseStart_7373309 := by decide
  rcases family_descends (prefixWord ++ tailWord_7373309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7373336 : List Nat := [2, 1, 2, 3, 3, 2, 1, 1, 3, 2, 3]
def baseStart_7373336 : Nat := 118140960795 + 7373336 * 2 ^ 59
def prefixEnd_7373336 : Nat := 4983230072969 + 3 ^ 40 * 7373336 * 2
def baseEnd_7373336 : Nat := 3786065395099669022690651

theorem tailTrace_7373336 : CollatzResearch.WordTrace tailWord_7373336 prefixEnd_7373336 3786065395099669022690651 := by
  unfold tailWord_7373336
  simp only [CollatzResearch.WordTrace]
  refine ⟨134463828607835206189329931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 179285104810446941585773241 134463828607835206189329931)
  ·
    refine ⟨201695742911752809283994897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134463828607835206189329931 201695742911752809283994897)
    ·
      refine ⟨151271807183814606962996173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 201695742911752809283994897 151271807183814606962996173)
      ·
        refine ⟨56726927693930477611123565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 151271807183814606962996173 56726927693930477611123565)
        ·
          refine ⟨21272597885223929104171337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 56726927693930477611123565 21272597885223929104171337)
          ·
            refine ⟨15954448413917946828128503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21272597885223929104171337 15954448413917946828128503)
            ·
              refine ⟨23931672620876920242192755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15954448413917946828128503 23931672620876920242192755)
              ·
                refine ⟨35897508931315380363289133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23931672620876920242192755 35897508931315380363289133)
                ·
                  refine ⟨13461565849243267636233425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35897508931315380363289133 13461565849243267636233425)
                  ·
                    refine ⟨10096174386932450727175069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13461565849243267636233425 10096174386932450727175069)
                    ·
                      refine ⟨3786065395099669022690651, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10096174386932450727175069 3786065395099669022690651)
                      ·
                        rfl

theorem cell23_7373336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 2, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 2, 1, 1, 3, 2, 3].length) (baseStart_7373336 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7373336 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7373336 prefixEnd_7373336 := by exact prefixLift 7373336
  have htrace : WordTrace (prefixWord ++ tailWord_7373336) baseStart_7373336 baseEnd_7373336 := by
    simpa [prefixWord, tailWord_7373336, baseEnd_7373336] using wordTrace_append hprefix tailTrace_7373336
  have hstable : (prefixWord ++ tailWord_7373336).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7373336).length < 2 ^ (prefixWord ++ tailWord_7373336).sum := by decide
  have hdescent : baseEnd_7373336 < baseStart_7373336 := by decide
  rcases family_descends (prefixWord ++ tailWord_7373336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7373349 : List Nat := [1, 3, 1, 2, 2, 1, 3, 1, 3, 3, 3]
def baseStart_7373349 : Nat := 118140960795 + 7373349 * 2 ^ 59
def prefixEnd_7373349 : Nat := 4983230072969 + 3 ^ 40 * 7373349 * 2
def baseEnd_7373349 : Nat := 3786072070348177471828091

theorem tailTrace_7373349 : CollatzResearch.WordTrace tailWord_7373349 prefixEnd_7373349 3786072070348177471828091 := by
  unfold tailWord_7373349
  simp only [CollatzResearch.WordTrace]
  refine ⟨268928131364623315598883101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179285420909748877065922067 268928131364623315598883101)
  ·
    refine ⟨100848049261733743349581163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 268928131364623315598883101 100848049261733743349581163)
    ·
      refine ⟨151272073892600615024371745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100848049261733743349581163 151272073892600615024371745)
      ·
        refine ⟨113454055419450461268278809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 151272073892600615024371745 113454055419450461268278809)
        ·
          refine ⟨85090541564587845951209107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 113454055419450461268278809 85090541564587845951209107)
          ·
            refine ⟨127635812346881768926813661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85090541564587845951209107 127635812346881768926813661)
            ·
              refine ⟨47863429630080663347555123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 127635812346881768926813661 47863429630080663347555123)
              ·
                refine ⟨71795144445120995021332685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47863429630080663347555123 71795144445120995021332685)
                ·
                  refine ⟨26923179166920373132999757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 71795144445120995021332685 26923179166920373132999757)
                  ·
                    refine ⟨10096192187595139924874909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 26923179166920373132999757 10096192187595139924874909)
                    ·
                      refine ⟨3786072070348177471828091, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10096192187595139924874909 3786072070348177471828091)
                      ·
                        rfl

theorem cell23_7373349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 3, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 3, 1, 3, 3, 3].length) (baseStart_7373349 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7373349 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7373349 prefixEnd_7373349 := by exact prefixLift 7373349
  have htrace : WordTrace (prefixWord ++ tailWord_7373349) baseStart_7373349 baseEnd_7373349 := by
    simpa [prefixWord, tailWord_7373349, baseEnd_7373349] using wordTrace_append hprefix tailTrace_7373349
  have hstable : (prefixWord ++ tailWord_7373349).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7373349).length < 2 ^ (prefixWord ++ tailWord_7373349).sum := by decide
  have hdescent : baseEnd_7373349 < baseStart_7373349 := by decide
  rcases family_descends (prefixWord ++ tailWord_7373349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7373376 : List Nat := [2, 1, 1, 2, 2, 2, 3, 2, 3, 3, 2]
def baseStart_7373376 : Nat := 118140960795 + 7373376 * 2 ^ 59
def prefixEnd_7373376 : Nat := 4983230072969 + 3 ^ 40 * 7373376 * 2
def baseEnd_7373376 : Nat := 3786085934325848866190467

theorem tailTrace_7373376 : CollatzResearch.WordTrace tailWord_7373376 prefixEnd_7373376 3786085934325848866190467 := by
  unfold tailWord_7373376
  simp only [CollatzResearch.WordTrace]
  refine ⟨134464558067762749605057991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 179286077423683666140077321 134464558067762749605057991)
  ·
    refine ⟨201696837101644124407586987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134464558067762749605057991 201696837101644124407586987)
    ·
      refine ⟨302545255652466186611380481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 201696837101644124407586987 302545255652466186611380481)
      ·
        refine ⟨226908941739349639958535361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 302545255652466186611380481 226908941739349639958535361)
        ·
          refine ⟨170181706304512229968901521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 226908941739349639958535361 170181706304512229968901521)
          ·
            refine ⟨127636279728384172476676141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 170181706304512229968901521 127636279728384172476676141)
            ·
              refine ⟨47863604898144064678753553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 127636279728384172476676141 47863604898144064678753553)
              ·
                refine ⟨35897703673608048509065165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47863604898144064678753553 35897703673608048509065165)
                ·
                  refine ⟨13461638877603018190899437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35897703673608048509065165 13461638877603018190899437)
                  ·
                    refine ⟨5048114579101131821587289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13461638877603018190899437 5048114579101131821587289)
                    ·
                      refine ⟨3786085934325848866190467, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5048114579101131821587289 3786085934325848866190467)
                      ·
                        rfl

theorem cell23_7373376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 3, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 3, 2, 3, 3, 2].length) (baseStart_7373376 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7373376 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7373376 prefixEnd_7373376 := by exact prefixLift 7373376
  have htrace : WordTrace (prefixWord ++ tailWord_7373376) baseStart_7373376 baseEnd_7373376 := by
    simpa [prefixWord, tailWord_7373376, baseEnd_7373376] using wordTrace_append hprefix tailTrace_7373376
  have hstable : (prefixWord ++ tailWord_7373376).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7373376).length < 2 ^ (prefixWord ++ tailWord_7373376).sum := by decide
  have hdescent : baseEnd_7373376 < baseStart_7373376 := by decide
  rcases family_descends (prefixWord ++ tailWord_7373376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7373383 : List Nat := [1, 1, 4, 1, 4, 1, 2, 3, 2, 1, 3]
def baseStart_7373383 : Nat := 118140960795 + 7373383 * 2 ^ 59
def prefixEnd_7373383 : Nat := 4983230072969 + 3 ^ 40 * 7373383 * 2
def baseEnd_7373383 : Nat := 3786089528690430338802935

theorem tailTrace_7373383 : CollatzResearch.WordTrace tailWord_7373383 prefixEnd_7373383 3786089528690430338802935 := by
  unfold tailWord_7373383
  simp only [CollatzResearch.WordTrace]
  refine ⟨268929371446500139405620803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179286247631000092937080535 268929371446500139405620803)
  ·
    refine ⟨403394057169750209108431205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 268929371446500139405620803 403394057169750209108431205)
    ·
      refine ⟨75636385719328164207830851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 403394057169750209108431205 75636385719328164207830851)
      ·
        refine ⟨113454578578992246311746277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75636385719328164207830851 113454578578992246311746277)
        ·
          refine ⟨21272733483561046183452427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 113454578578992246311746277 21272733483561046183452427)
          ·
            refine ⟨31909100225341569275178641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21272733483561046183452427 31909100225341569275178641)
            ·
              refine ⟨23931825169006176956383981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31909100225341569275178641 23931825169006176956383981)
              ·
                refine ⟨8974434438377316358643993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23931825169006176956383981 8974434438377316358643993)
                ·
                  refine ⟨6730825828782987268982995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8974434438377316358643993 6730825828782987268982995)
                  ·
                    refine ⟨10096238743174480903474493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6730825828782987268982995 10096238743174480903474493)
                    ·
                      refine ⟨3786089528690430338802935, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10096238743174480903474493 3786089528690430338802935)
                      ·
                        rfl

theorem cell23_7373383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 1, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 1, 2, 3, 2, 1, 3].length) (baseStart_7373383 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7373383 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7373383 prefixEnd_7373383 := by exact prefixLift 7373383
  have htrace : WordTrace (prefixWord ++ tailWord_7373383) baseStart_7373383 baseEnd_7373383 := by
    simpa [prefixWord, tailWord_7373383, baseEnd_7373383] using wordTrace_append hprefix tailTrace_7373383
  have hstable : (prefixWord ++ tailWord_7373383).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7373383).length < 2 ^ (prefixWord ++ tailWord_7373383).sum := by decide
  have hdescent : baseEnd_7373383 < baseStart_7373383 := by decide
  rcases family_descends (prefixWord ++ tailWord_7373383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7373439 : List Nat := [1, 1, 2, 2, 1, 1, 1, 5, 1, 5, 3]
def baseStart_7373439 : Nat := 118140960795 + 7373439 * 2 ^ 59
def prefixEnd_7373439 : Nat := 4983230072969 + 3 ^ 40 * 7373439 * 2
def baseEnd_7373439 : Nat := 3786118283607082119702677

theorem tailTrace_7373439 : CollatzResearch.WordTrace tailWord_7373439 prefixEnd_7373439 3786118283607082119702677 := by
  unfold tailWord_7373439
  simp only [CollatzResearch.WordTrace]
  refine ⟨268931413934297260969659371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179287609289531507313106247 268931413934297260969659371)
  ·
    refine ⟨403397120901445891454489057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 268931413934297260969659371 403397120901445891454489057)
    ·
      refine ⟨302547840676084418590866793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 403397120901445891454489057 302547840676084418590866793)
      ·
        refine ⟨226910880507063313943150095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 302547840676084418590866793 226910880507063313943150095)
        ·
          refine ⟨340366320760594970914725143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 226910880507063313943150095 340366320760594970914725143)
          ·
            refine ⟨510549481140892456372087715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 340366320760594970914725143 510549481140892456372087715)
            ·
              refine ⟨765824221711338684558131573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 510549481140892456372087715 765824221711338684558131573)
              ·
                refine ⟨71796020785438001677324835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 765824221711338684558131573 71796020785438001677324835)
                ·
                  refine ⟨107694031178157002515987253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 71796020785438001677324835 107694031178157002515987253)
                  ·
                    refine ⟨10096315422952218985873805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 107694031178157002515987253 10096315422952218985873805)
                    ·
                      refine ⟨3786118283607082119702677, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10096315422952218985873805 3786118283607082119702677)
                      ·
                        rfl

theorem cell23_7373439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 5, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 5, 1, 5, 3].length) (baseStart_7373439 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7373439 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7373439 prefixEnd_7373439 := by exact prefixLift 7373439
  have htrace : WordTrace (prefixWord ++ tailWord_7373439) baseStart_7373439 baseEnd_7373439 := by
    simpa [prefixWord, tailWord_7373439, baseEnd_7373439] using wordTrace_append hprefix tailTrace_7373439
  have hstable : (prefixWord ++ tailWord_7373439).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7373439).length < 2 ^ (prefixWord ++ tailWord_7373439).sum := by decide
  have hdescent : baseEnd_7373439 < baseStart_7373439 := by decide
  rcases family_descends (prefixWord ++ tailWord_7373439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7373476 : List Nat := [2, 3, 1, 2, 2, 1, 3, 2, 2, 5]
def baseStart_7373476 : Nat := 118140960795 + 7373476 * 2 ^ 59
def prefixEnd_7373476 : Nat := 4983230072969 + 3 ^ 40 * 7373476 * 2
def baseEnd_7373476 : Nat := 1262045760797099491646669

theorem tailTrace_7373476 : CollatzResearch.WordTrace tailWord_7373476 prefixEnd_7373476 1262045760797099491646669 := by
  unfold tailWord_7373476
  simp only [CollatzResearch.WordTrace]
  refine ⟨134466381717581608144378141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 179288508956775477525837521 134466381717581608144378141)
  ·
    refine ⟨50424893144093103054141803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 134466381717581608144378141 50424893144093103054141803)
    ·
      refine ⟨75637339716139654581212705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50424893144093103054141803 75637339716139654581212705)
      ·
        refine ⟨56728004787104740935909529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 75637339716139654581212705 56728004787104740935909529)
        ·
          refine ⟨42546003590328555701932147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56728004787104740935909529 42546003590328555701932147)
          ·
            refine ⟨63819005385492833552898221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42546003590328555701932147 63819005385492833552898221)
            ·
              refine ⟨23932127019559812582336833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 63819005385492833552898221 23932127019559812582336833)
              ·
                refine ⟨17949095264669859436752625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23932127019559812582336833 17949095264669859436752625)
                ·
                  refine ⟨13461821448502394577564469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17949095264669859436752625 13461821448502394577564469)
                  ·
                    refine ⟨1262045760797099491646669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13461821448502394577564469 1262045760797099491646669)
                    ·
                      rfl

theorem cell23_7373476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 3, 2, 2, 5].length) (baseStart_7373476 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7373476 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7373476 prefixEnd_7373476 := by exact prefixLift 7373476
  have htrace : WordTrace (prefixWord ++ tailWord_7373476) baseStart_7373476 baseEnd_7373476 := by
    simpa [prefixWord, tailWord_7373476, baseEnd_7373476] using wordTrace_append hprefix tailTrace_7373476
  have hstable : (prefixWord ++ tailWord_7373476).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7373476).length < 2 ^ (prefixWord ++ tailWord_7373476).sum := by decide
  have hdescent : baseEnd_7373476 < baseStart_7373476 := by decide
  rcases family_descends (prefixWord ++ tailWord_7373476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7373540 : List Nat := [2, 3, 1, 1, 1, 5, 1, 4, 1, 4]
def baseStart_7373540 : Nat := 118140960795 + 7373540 * 2 ^ 59
def prefixEnd_7373540 : Nat := 4983230072969 + 3 ^ 40 * 7373540 * 2
def baseEnd_7373540 : Nat := 1262056715051062074846571

theorem tailTrace_7373540 : CollatzResearch.WordTrace tailWord_7373540 prefixEnd_7373540 1262056715051062074846571 := by
  unfold tailWord_7373540
  simp only [CollatzResearch.WordTrace]
  refine ⟨134467548853465677609543037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 179290065137954236812724049 134467548853465677609543037)
  ·
    refine ⟨50425330820049629103578639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 134467548853465677609543037 50425330820049629103578639)
    ·
      refine ⟨75637996230074443655367959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50425330820049629103578639 75637996230074443655367959)
      ·
        refine ⟨113456994345111665483051939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75637996230074443655367959 113456994345111665483051939)
        ·
          refine ⟨170185491517667498224577909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 113456994345111665483051939 170185491517667498224577909)
          ·
            refine ⟨15954889829781327958554179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 170185491517667498224577909 15954889829781327958554179)
            ·
              refine ⟨23932334744671991937831269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15954889829781327958554179 23932334744671991937831269)
              ·
                refine ⟨4487312764625998488343363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23932334744671991937831269 4487312764625998488343363)
                ·
                  refine ⟨6730969146938997732515045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4487312764625998488343363 6730969146938997732515045)
                  ·
                    refine ⟨1262056715051062074846571, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6730969146938997732515045 1262056715051062074846571)
                    ·
                      rfl

theorem cell23_7373540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 5, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 5, 1, 4, 1, 4].length) (baseStart_7373540 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7373540 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7373540 prefixEnd_7373540 := by exact prefixLift 7373540
  have htrace : WordTrace (prefixWord ++ tailWord_7373540) baseStart_7373540 baseEnd_7373540 := by
    simpa [prefixWord, tailWord_7373540, baseEnd_7373540] using wordTrace_append hprefix tailTrace_7373540
  have hstable : (prefixWord ++ tailWord_7373540).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7373540).length < 2 ^ (prefixWord ++ tailWord_7373540).sum := by decide
  have hdescent : baseEnd_7373540 < baseStart_7373540 := by decide
  rcases family_descends (prefixWord ++ tailWord_7373540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7373546 : List Nat := [3, 1, 3, 1, 1, 1, 1, 2, 2, 5, 3]
def baseStart_7373546 : Nat := 118140960795 + 7373546 * 2 ^ 59
def prefixEnd_7373546 : Nat := 4983230072969 + 3 ^ 40 * 7373546 * 2
def baseEnd_7373546 : Nat := 3786173226037113201064685

theorem tailTrace_7373546 : CollatzResearch.WordTrace tailWord_7373546 prefixEnd_7373546 3786173226037113201064685 := by
  unfold tailWord_7373546
  simp only [CollatzResearch.WordTrace]
  refine ⟨67233829136227404560951123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 179290211029939745495869661 67233829136227404560951123)
  ·
    refine ⟨100850743704341106841426685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67233829136227404560951123 100850743704341106841426685)
    ·
      refine ⟨37819028889127915065535007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 100850743704341106841426685 37819028889127915065535007)
      ·
        refine ⟨56728543333691872598302511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37819028889127915065535007 56728543333691872598302511)
        ·
          refine ⟨85092815000537808897453767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56728543333691872598302511 85092815000537808897453767)
          ·
            refine ⟨127639222500806713346180651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85092815000537808897453767 127639222500806713346180651)
            ·
              refine ⟨191458833751210070019270977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 127639222500806713346180651 191458833751210070019270977)
              ·
                refine ⟨143594125313407552514453233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 191458833751210070019270977 143594125313407552514453233)
                ·
                  refine ⟨107695593985055664385839925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 143594125313407552514453233 107695593985055664385839925)
                  ·
                    refine ⟨10096461936098968536172493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 107695593985055664385839925 10096461936098968536172493)
                    ·
                      refine ⟨3786173226037113201064685, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10096461936098968536172493 3786173226037113201064685)
                      ·
                        rfl

theorem cell23_7373546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 1, 2, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 1, 2, 2, 5, 3].length) (baseStart_7373546 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7373546 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7373546 prefixEnd_7373546 := by exact prefixLift 7373546
  have htrace : WordTrace (prefixWord ++ tailWord_7373546) baseStart_7373546 baseEnd_7373546 := by
    simpa [prefixWord, tailWord_7373546, baseEnd_7373546] using wordTrace_append hprefix tailTrace_7373546
  have hstable : (prefixWord ++ tailWord_7373546).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7373546).length < 2 ^ (prefixWord ++ tailWord_7373546).sum := by decide
  have hdescent : baseEnd_7373546 < baseStart_7373546 := by decide
  rcases family_descends (prefixWord ++ tailWord_7373546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7373559 : List Nat := [1, 1, 3, 1, 1, 1, 3, 1, 1, 3, 7]
def baseStart_7373559 : Nat := 118140960795 + 7373559 * 2 ^ 59
def prefixEnd_7373559 : Nat := 4983230072969 + 3 ^ 40 * 7373559 * 2
def baseEnd_7373559 : Nat := 3786179901285621650202125

theorem tailTrace_7373559 : CollatzResearch.WordTrace tailWord_7373559 prefixEnd_7373559 3786179901285621650202125 := by
  unfold tailWord_7373559
  simp only [CollatzResearch.WordTrace]
  refine ⟨268935790693862521464027731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179290527129241680976018487 268935790693862521464027731)
  ·
    refine ⟨403403686040793782196041597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 268935790693862521464027731 403403686040793782196041597)
    ·
      refine ⟨151276382265297668323515599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 403403686040793782196041597 151276382265297668323515599)
      ·
        refine ⟨226914573397946502485273399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 151276382265297668323515599 226914573397946502485273399)
        ·
          refine ⟨340371860096919753727910099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 226914573397946502485273399 340371860096919753727910099)
          ·
            refine ⟨510557790145379630591865149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 340371860096919753727910099 510557790145379630591865149)
            ·
              refine ⟨191459171304517361471949431, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 510557790145379630591865149 191459171304517361471949431)
              ·
                refine ⟨287188756956776042207924147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 191459171304517361471949431 287188756956776042207924147)
                ·
                  refine ⟨430783135435164063311886221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 287188756956776042207924147 430783135435164063311886221)
                  ·
                    refine ⟨161543675788186523741957333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 430783135435164063311886221 161543675788186523741957333)
                    ·
                      refine ⟨3786179901285621650202125, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 161543675788186523741957333 3786179901285621650202125)
                      ·
                        rfl

theorem cell23_7373559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 3, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 3, 1, 1, 3, 7].length) (baseStart_7373559 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7373559 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7373559 prefixEnd_7373559 := by exact prefixLift 7373559
  have htrace : WordTrace (prefixWord ++ tailWord_7373559) baseStart_7373559 baseEnd_7373559 := by
    simpa [prefixWord, tailWord_7373559, baseEnd_7373559] using wordTrace_append hprefix tailTrace_7373559
  have hstable : (prefixWord ++ tailWord_7373559).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7373559).length < 2 ^ (prefixWord ++ tailWord_7373559).sum := by decide
  have hdescent : baseEnd_7373559 < baseStart_7373559 := by decide
  rcases family_descends (prefixWord ++ tailWord_7373559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7373637 : List Nat := [1, 3, 1, 1, 1, 2, 2, 7, 1, 2, 2]
def baseStart_7373637 : Nat := 118140960795 + 7373637 * 2 ^ 59
def prefixEnd_7373637 : Nat := 4983230072969 + 3 ^ 40 * 7373637 * 2
def baseEnd_7373637 : Nat := 3786219952776672345026767

theorem tailTrace_7373637 : CollatzResearch.WordTrace tailWord_7373637 prefixEnd_7373637 3786219952776672345026767 := by
  unfold tailWord_7373637
  simp only [CollatzResearch.WordTrace]
  refine ⟨268938635587579940785367165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179292423725053293856911443 268938635587579940785367165)
  ·
    refine ⟨100851988345342477794512687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 268938635587579940785367165 100851988345342477794512687)
    ·
      refine ⟨151277982518013716691769031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100851988345342477794512687 151277982518013716691769031)
      ·
        refine ⟨226916973777020575037653547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 151277982518013716691769031 226916973777020575037653547)
        ·
          refine ⟨340375460665530862556480321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 226916973777020575037653547 340375460665530862556480321)
          ·
            refine ⟨255281595499148146917360241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 340375460665530862556480321 255281595499148146917360241)
            ·
              refine ⟨191461196624361110188020181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 255281595499148146917360241 191461196624361110188020181)
              ·
                refine ⟨4487371795883463520031723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 191461196624361110188020181 4487371795883463520031723)
                ·
                  refine ⟨6731057693825195280047585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4487371795883463520031723 6731057693825195280047585)
                  ·
                    refine ⟨5048293270368896460035689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6731057693825195280047585 5048293270368896460035689)
                    ·
                      refine ⟨3786219952776672345026767, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5048293270368896460035689 3786219952776672345026767)
                      ·
                        rfl

theorem cell23_7373637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 2, 7, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 2, 7, 1, 2, 2].length) (baseStart_7373637 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7373637 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7373637 prefixEnd_7373637 := by exact prefixLift 7373637
  have htrace : WordTrace (prefixWord ++ tailWord_7373637) baseStart_7373637 baseEnd_7373637 := by
    simpa [prefixWord, tailWord_7373637, baseEnd_7373637] using wordTrace_append hprefix tailTrace_7373637
  have hstable : (prefixWord ++ tailWord_7373637).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7373637).length < 2 ^ (prefixWord ++ tailWord_7373637).sum := by decide
  have hdescent : baseEnd_7373637 < baseStart_7373637 := by decide
  rcases family_descends (prefixWord ++ tailWord_7373637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7373696 : List Nat := [2, 1, 1, 2, 1, 2, 2, 3, 1, 3, 5]
def baseStart_7373696 : Nat := 118140960795 + 7373696 * 2 ^ 59
def prefixEnd_7373696 : Nat := 4983230072969 + 3 ^ 40 * 7373696 * 2
def baseEnd_7373696 : Nat := 3786250248135287614188995

theorem tailTrace_7373696 : CollatzResearch.WordTrace tailWord_7373696 prefixEnd_7373696 3786250248135287614188995 := by
  unfold tailWord_7373696
  simp only [CollatzResearch.WordTrace]
  refine ⟨134470393747183096930882471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 179293858329577462574509961 134470393747183096930882471)
  ·
    refine ⟨201705590620774645396323707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134470393747183096930882471 201705590620774645396323707)
    ·
      refine ⟨302558385931161968094485561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 201705590620774645396323707 302558385931161968094485561)
      ·
        refine ⟨226918789448371476070864171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 302558385931161968094485561 226918789448371476070864171)
        ·
          refine ⟨340378184172557214106296257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 226918789448371476070864171 340378184172557214106296257)
          ·
            refine ⟨255283638129417910579722193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 340378184172557214106296257 255283638129417910579722193)
            ·
              refine ⟨191462728597063432934791645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 255283638129417910579722193 191462728597063432934791645)
              ·
                refine ⟨71798523223898787350546867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 191462728597063432934791645 71798523223898787350546867)
                ·
                  refine ⟨107697784835848181025820301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 71798523223898787350546867 107697784835848181025820301)
                  ·
                    refine ⟨40386669313443067884682613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 107697784835848181025820301 40386669313443067884682613)
                    ·
                      refine ⟨3786250248135287614188995, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 40386669313443067884682613 3786250248135287614188995)
                      ·
                        rfl

theorem cell23_7373696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 2, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 2, 3, 1, 3, 5].length) (baseStart_7373696 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7373696 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7373696 prefixEnd_7373696 := by exact prefixLift 7373696
  have htrace : WordTrace (prefixWord ++ tailWord_7373696) baseStart_7373696 baseEnd_7373696 := by
    simpa [prefixWord, tailWord_7373696, baseEnd_7373696] using wordTrace_append hprefix tailTrace_7373696
  have hstable : (prefixWord ++ tailWord_7373696).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7373696).length < 2 ^ (prefixWord ++ tailWord_7373696).sum := by decide
  have hdescent : baseEnd_7373696 < baseStart_7373696 := by decide
  rcases family_descends (prefixWord ++ tailWord_7373696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7373727 : List Nat := [1, 1, 2, 5, 2, 2, 2, 1, 1, 4, 2]
def baseStart_7373727 : Nat := 118140960795 + 7373727 * 2 ^ 59
def prefixEnd_7373727 : Nat := 4983230072969 + 3 ^ 40 * 7373727 * 2
def baseEnd_7373727 : Nat := 3786266166035576992901353

theorem tailTrace_7373727 : CollatzResearch.WordTrace tailWord_7373727 prefixEnd_7373727 3786266166035576992901353 := by
  unfold tailWord_7373727
  simp only [CollatzResearch.WordTrace]
  refine ⟨268941918157253886156143435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179294612104835924104095623 268941918157253886156143435)
  ·
    refine ⟨403412877235880829234215153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 268941918157253886156143435 403412877235880829234215153)
    ·
      refine ⟨302559657926910621925661365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 403412877235880829234215153 302559657926910621925661365)
      ·
        refine ⟨28364967930647870805530753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 302559657926910621925661365 28364967930647870805530753)
        ·
          refine ⟨21273725947985903104148065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28364967930647870805530753 21273725947985903104148065)
          ·
            refine ⟨15955294460989427328111049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21273725947985903104148065 15955294460989427328111049)
            ·
              refine ⟨11966470845742070496083287, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15955294460989427328111049 11966470845742070496083287)
              ·
                refine ⟨17949706268613105744124931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11966470845742070496083287 17949706268613105744124931)
                ·
                  refine ⟨26924559402919658616187397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17949706268613105744124931 26924559402919658616187397)
                  ·
                    refine ⟨5048354888047435990535137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 26924559402919658616187397 5048354888047435990535137)
                    ·
                      refine ⟨3786266166035576992901353, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5048354888047435990535137 3786266166035576992901353)
                      ·
                        rfl

theorem cell23_7373727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 2, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 2, 2, 1, 1, 4, 2].length) (baseStart_7373727 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7373727 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7373727 prefixEnd_7373727 := by exact prefixLift 7373727
  have htrace : WordTrace (prefixWord ++ tailWord_7373727) baseStart_7373727 baseEnd_7373727 := by
    simpa [prefixWord, tailWord_7373727, baseEnd_7373727] using wordTrace_append hprefix tailTrace_7373727
  have hstable : (prefixWord ++ tailWord_7373727).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7373727).length < 2 ^ (prefixWord ++ tailWord_7373727).sum := by decide
  have hdescent : baseEnd_7373727 < baseStart_7373727 := by decide
  rcases family_descends (prefixWord ++ tailWord_7373727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7373748 : List Nat := [2, 5, 2, 1, 1, 3, 2, 1, 1, 3, 2]
def baseStart_7373748 : Nat := 118140960795 + 7373748 * 2 ^ 59
def prefixEnd_7373748 : Nat := 4983230072969 + 3 ^ 40 * 7373748 * 2
def baseEnd_7373748 : Nat := 3786276949129321410738757

theorem tailTrace_7373748 : CollatzResearch.WordTrace tailWord_7373748 prefixEnd_7373748 3786276949129321410738757 := by
  unfold tailWord_7373748
  simp only [CollatzResearch.WordTrace]
  refine ⟨134471342045088903371328949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 179295122726785204495105265 134471342045088903371328949)
  ·
    refine ⟨12606688316727084691062089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 134471342045088903371328949 12606688316727084691062089)
    ·
      refine ⟨9455016237545313518296567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12606688316727084691062089 9455016237545313518296567)
      ·
        refine ⟨14182524356317970277444851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9455016237545313518296567 14182524356317970277444851)
        ·
          refine ⟨21273786534476955416167277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14182524356317970277444851 21273786534476955416167277)
          ·
            refine ⟨7977669950428858281062729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21273786534476955416167277 7977669950428858281062729)
            ·
              refine ⟨5983252462821643710797047, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7977669950428858281062729 5983252462821643710797047)
              ·
                refine ⟨8974878694232465566195571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5983252462821643710797047 8974878694232465566195571)
                ·
                  refine ⟨13462318041348698349293357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8974878694232465566195571 13462318041348698349293357)
                  ·
                    refine ⟨5048369265505761880985009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13462318041348698349293357 5048369265505761880985009)
                    ·
                      refine ⟨3786276949129321410738757, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5048369265505761880985009 3786276949129321410738757)
                      ·
                        rfl

theorem cell23_7373748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 3, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 3, 2, 1, 1, 3, 2].length) (baseStart_7373748 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7373748 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7373748 prefixEnd_7373748 := by exact prefixLift 7373748
  have htrace : WordTrace (prefixWord ++ tailWord_7373748) baseStart_7373748 baseEnd_7373748 := by
    simpa [prefixWord, tailWord_7373748, baseEnd_7373748] using wordTrace_append hprefix tailTrace_7373748
  have hstable : (prefixWord ++ tailWord_7373748).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7373748).length < 2 ^ (prefixWord ++ tailWord_7373748).sum := by decide
  have hdescent : baseEnd_7373748 < baseStart_7373748 := by decide
  rcases family_descends (prefixWord ++ tailWord_7373748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7373783 : List Nat := [1, 1, 3, 2, 1, 1, 2, 1, 6, 1, 4]
def baseStart_7373783 : Nat := 118140960795 + 7373783 * 2 ^ 59
def prefixEnd_7373783 : Nat := 4983230072969 + 3 ^ 40 * 7373783 * 2
def baseEnd_7373783 : Nat := 3786294920952228773801095

theorem tailTrace_7373783 : CollatzResearch.WordTrace tailWord_7373783 prefixEnd_7373783 3786294920952228773801095 := by
  unfold tailWord_7373783
  simp only [CollatzResearch.WordTrace]
  refine ⟨268943960645051007720182003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179295973763367338480121335 268943960645051007720182003)
  ·
    refine ⟨403415940967576511580273005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 268943960645051007720182003 403415940967576511580273005)
    ·
      refine ⟨151280977862841191842602377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 403415940967576511580273005 151280977862841191842602377)
      ·
        refine ⟨113460733397130893881951783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 151280977862841191842602377 113460733397130893881951783)
        ·
          refine ⟨170191100095696340822927675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 113460733397130893881951783 170191100095696340822927675)
          ·
            refine ⟨255286650143544511234391513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 170191100095696340822927675 255286650143544511234391513)
            ·
              refine ⟨191464987607658383425793635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 255286650143544511234391513 191464987607658383425793635)
              ·
                refine ⟨287197481411487575138690453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 191464987607658383425793635 287197481411487575138690453)
                ·
                  refine ⟨13462381941163480084626115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 287197481411487575138690453 13462381941163480084626115)
                  ·
                    refine ⟨20193572911745220126939173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13462381941163480084626115 20193572911745220126939173)
                    ·
                      refine ⟨3786294920952228773801095, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20193572911745220126939173 3786294920952228773801095)
                      ·
                        rfl

theorem cell23_7373783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 2, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 2, 1, 6, 1, 4].length) (baseStart_7373783 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7373783 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7373783 prefixEnd_7373783 := by exact prefixLift 7373783
  have htrace : WordTrace (prefixWord ++ tailWord_7373783) baseStart_7373783 baseEnd_7373783 := by
    simpa [prefixWord, tailWord_7373783, baseEnd_7373783] using wordTrace_append hprefix tailTrace_7373783
  have hstable : (prefixWord ++ tailWord_7373783).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7373783).length < 2 ^ (prefixWord ++ tailWord_7373783).sum := by decide
  have hdescent : baseEnd_7373783 < baseStart_7373783 := by decide
  rcases family_descends (prefixWord ++ tailWord_7373783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7373800 : List Nat := [2, 1, 4, 1, 1, 1, 2, 2, 1, 6, 2]
def baseStart_7373800 : Nat := 118140960795 + 7373800 * 2 ^ 59
def prefixEnd_7373800 : Nat := 4983230072969 + 3 ^ 40 * 7373800 * 2
def baseEnd_7373800 : Nat := 3786303650123355207288517

theorem tailTrace_7373800 : CollatzResearch.WordTrace tailWord_7373800 prefixEnd_7373800 3786303650123355207288517 := by
  unfold tailWord_7373800
  simp only [CollatzResearch.WordTrace]
  refine ⟨134472290342994709811775427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 179296387123992946415700569 134472290342994709811775427)
  ·
    refine ⟨201708435514492064717663141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134472290342994709811775427 201708435514492064717663141)
    ·
      refine ⟨37820331658967262134561839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 201708435514492064717663141 37820331658967262134561839)
      ·
        refine ⟨56730497488450893201842759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37820331658967262134561839 56730497488450893201842759)
        ·
          refine ⟨85095746232676339802764139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56730497488450893201842759 85095746232676339802764139)
          ·
            refine ⟨127643619349014509704146209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85095746232676339802764139 127643619349014509704146209)
            ·
              refine ⟨95732714511760882278109657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 127643619349014509704146209 95732714511760882278109657)
              ·
                refine ⟨71799535883820661708582243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 95732714511760882278109657 71799535883820661708582243)
                ·
                  refine ⟨107699303825730992562873365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 71799535883820661708582243 107699303825730992562873365)
                  ·
                    refine ⟨5048404866831140276384689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 107699303825730992562873365 5048404866831140276384689)
                    ·
                      refine ⟨3786303650123355207288517, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5048404866831140276384689 3786303650123355207288517)
                      ·
                        rfl

theorem cell23_7373800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 2, 2, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 2, 2, 1, 6, 2].length) (baseStart_7373800 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7373800 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7373800 prefixEnd_7373800 := by exact prefixLift 7373800
  have htrace : WordTrace (prefixWord ++ tailWord_7373800) baseStart_7373800 baseEnd_7373800 := by
    simpa [prefixWord, tailWord_7373800, baseEnd_7373800] using wordTrace_append hprefix tailTrace_7373800
  have hstable : (prefixWord ++ tailWord_7373800).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7373800).length < 2 ^ (prefixWord ++ tailWord_7373800).sum := by decide
  have hdescent : baseEnd_7373800 < baseStart_7373800 := by decide
  rcases family_descends (prefixWord ++ tailWord_7373800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7373820 : List Nat := [2, 2, 2, 1, 2, 3, 1, 1, 4, 2, 3]
def baseStart_7373820 : Nat := 118140960795 + 7373820 * 2 ^ 59
def prefixEnd_7373820 : Nat := 4983230072969 + 3 ^ 40 * 7373820 * 2
def baseEnd_7373820 : Nat := 3786313919736445129038425

theorem tailTrace_7373820 : CollatzResearch.WordTrace tailWord_7373820 prefixEnd_7373820 3786313919736445129038425 := by
  unfold tailWord_7373820
  simp only [CollatzResearch.WordTrace]
  refine ⟨134472655072958481519639457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 179296873430611308692852609 134472655072958481519639457)
  ·
    refine ⟨100854491304718861139729593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 134472655072958481519639457 100854491304718861139729593)
    ·
      refine ⟨75640868478539145854797195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 100854491304718861139729593 75640868478539145854797195)
      ·
        refine ⟨113461302717808718782195793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75640868478539145854797195 113461302717808718782195793)
        ·
          refine ⟨85095977038356539086646845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 113461302717808718782195793 85095977038356539086646845)
          ·
            refine ⟨31910991389383702157492567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 85095977038356539086646845 31910991389383702157492567)
            ·
              refine ⟨47866487084075553236238851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31910991389383702157492567 47866487084075553236238851)
              ·
                refine ⟨71799730626113329854358277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47866487084075553236238851 71799730626113329854358277)
                ·
                  refine ⟨13462449492396249347692177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 71799730626113329854358277 13462449492396249347692177)
                  ·
                    refine ⟨10096837119297187010769133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13462449492396249347692177 10096837119297187010769133)
                    ·
                      refine ⟨3786313919736445129038425, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10096837119297187010769133 3786313919736445129038425)
                      ·
                        rfl

theorem cell23_7373820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 3, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 3, 1, 1, 4, 2, 3].length) (baseStart_7373820 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7373820 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7373820 prefixEnd_7373820 := by exact prefixLift 7373820
  have htrace : WordTrace (prefixWord ++ tailWord_7373820) baseStart_7373820 baseEnd_7373820 := by
    simpa [prefixWord, tailWord_7373820, baseEnd_7373820] using wordTrace_append hprefix tailTrace_7373820
  have hstable : (prefixWord ++ tailWord_7373820).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7373820).length < 2 ^ (prefixWord ++ tailWord_7373820).sum := by decide
  have hdescent : baseEnd_7373820 < baseStart_7373820 := by decide
  rcases family_descends (prefixWord ++ tailWord_7373820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7373878 : List Nat := [5, 1, 2, 1, 1, 4, 2, 2, 1, 4]
def baseStart_7373878 : Nat := 118140960795 + 7373878 * 2 ^ 59
def prefixEnd_7373878 : Nat := 4983230072969 + 3 ^ 40 * 7373878 * 2
def baseEnd_7373878 : Nat := 1262114567204801967371053

theorem tailTrace_7373878 : CollatzResearch.WordTrace tailWord_7373878 prefixEnd_7373878 1262114567204801967371053 := by
  unfold tailWord_7373878
  simp only [CollatzResearch.WordTrace]
  refine ⟨16809214098731677434055643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 179298283719804559296593525 16809214098731677434055643)
  ·
    refine ⟨25213821148097516151083465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16809214098731677434055643 25213821148097516151083465)
    ·
      refine ⟨18910365861073137113312599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25213821148097516151083465 18910365861073137113312599)
      ·
        refine ⟨28365548791609705669968899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18910365861073137113312599 28365548791609705669968899)
        ·
          refine ⟨42548323187414558504953349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28365548791609705669968899 42548323187414558504953349)
          ·
            refine ⟨7977810597640229719678753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 42548323187414558504953349 7977810597640229719678753)
            ·
              refine ⟨5983357948230172289759065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7977810597640229719678753 5983357948230172289759065)
              ·
                refine ⟨4487518461172629217319299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5983357948230172289759065 4487518461172629217319299)
                ·
                  refine ⟨6731277691758943825978949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4487518461172629217319299 6731277691758943825978949)
                  ·
                    refine ⟨1262114567204801967371053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6731277691758943825978949 1262114567204801967371053)
                    ·
                      rfl

theorem cell23_7373878_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 4, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 4, 2, 2, 1, 4].length) (baseStart_7373878 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7373878 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7373878 prefixEnd_7373878 := by exact prefixLift 7373878
  have htrace : WordTrace (prefixWord ++ tailWord_7373878) baseStart_7373878 baseEnd_7373878 := by
    simpa [prefixWord, tailWord_7373878, baseEnd_7373878] using wordTrace_append hprefix tailTrace_7373878
  have hstable : (prefixWord ++ tailWord_7373878).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7373878).length < 2 ^ (prefixWord ++ tailWord_7373878).sum := by decide
  have hdescent : baseEnd_7373878 < baseStart_7373878 := by decide
  rcases family_descends (prefixWord ++ tailWord_7373878) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7373900 : List Nat := [2, 2, 1, 3, 1, 1, 1, 2, 6, 4]
def baseStart_7373900 : Nat := 118140960795 + 7373900 * 2 ^ 59
def prefixEnd_7373900 : Nat := 4983230072969 + 3 ^ 40 * 7373900 * 2
def baseEnd_7373900 : Nat := 1262118332729601605346019

theorem tailTrace_7373900 : CollatzResearch.WordTrace tailWord_7373900 prefixEnd_7373900 1262118332729601605346019 := by
  unfold tailWord_7373900
  simp only [CollatzResearch.WordTrace]
  refine ⟨134474113992813568351095577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 179298818657084757801460769 134474113992813568351095577)
  ·
    refine ⟨100855585494610176263321683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 134474113992813568351095577 100855585494610176263321683)
    ·
      refine ⟨151283378241915264394982525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100855585494610176263321683 151283378241915264394982525)
      ·
        refine ⟨56731266840718224148118447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 151283378241915264394982525 56731266840718224148118447)
        ·
          refine ⟨85096900261077336222177671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56731266840718224148118447 85096900261077336222177671)
          ·
            refine ⟨127645350391616004333266507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85096900261077336222177671 127645350391616004333266507)
            ·
              refine ⟨191468025587424006499899761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 127645350391616004333266507 191468025587424006499899761)
              ·
                refine ⟨143601019190568004874924821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 191468025587424006499899761 143601019190568004874924821)
                ·
                  refine ⟨6731297774557875228512101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 143601019190568004874924821 6731297774557875228512101)
                  ·
                    refine ⟨1262118332729601605346019, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6731297774557875228512101 1262118332729601605346019)
                    ·
                      rfl

theorem cell23_7373900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 1, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 1, 2, 6, 4].length) (baseStart_7373900 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7373900 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7373900 prefixEnd_7373900 := by exact prefixLift 7373900
  have htrace : WordTrace (prefixWord ++ tailWord_7373900) baseStart_7373900 baseEnd_7373900 := by
    simpa [prefixWord, tailWord_7373900, baseEnd_7373900] using wordTrace_append hprefix tailTrace_7373900
  have hstable : (prefixWord ++ tailWord_7373900).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7373900).length < 2 ^ (prefixWord ++ tailWord_7373900).sum := by decide
  have hdescent : baseEnd_7373900 < baseStart_7373900 := by decide
  rcases family_descends (prefixWord ++ tailWord_7373900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7373907 : List Nat := [1, 1, 1, 2, 1, 1, 2, 5, 5, 2, 2]
def baseStart_7373907 : Nat := 118140960795 + 7373907 * 2 ^ 59
def prefixEnd_7373907 : Nat := 4983230072969 + 3 ^ 40 * 7373907 * 2
def baseEnd_7373907 : Nat := 3786358592553386288650525

theorem tailTrace_7373907 : CollatzResearch.WordTrace tailWord_7373907 prefixEnd_7373907 3786358592553386288650525 := by
  unfold tailWord_7373907
  simp only [CollatzResearch.WordTrace]
  refine ⟨268948483296601776897695975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179298988864401184598463983 268948483296601776897695975)
  ·
    refine ⟨403422724944902665346543963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 268948483296601776897695975 403422724944902665346543963)
    ·
      refine ⟨605134087417353998019815945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 403422724944902665346543963 605134087417353998019815945)
      ·
        refine ⟨453850565563015498514861959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 605134087417353998019815945 453850565563015498514861959)
        ·
          refine ⟨680775848344523247772292939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 453850565563015498514861959 680775848344523247772292939)
          ·
            refine ⟨1021163772516784871658439409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 680775848344523247772292939 1021163772516784871658439409)
            ·
              refine ⟨765872829387588653743829557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1021163772516784871658439409 765872829387588653743829557)
              ·
                refine ⟨71800577755086436288484021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 765872829387588653743829557 71800577755086436288484021)
                ·
                  refine ⟨6731304164539353402045377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 71800577755086436288484021 6731304164539353402045377)
                  ·
                    refine ⟨5048478123404515051534033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6731304164539353402045377 5048478123404515051534033)
                    ·
                      refine ⟨3786358592553386288650525, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5048478123404515051534033 3786358592553386288650525)
                      ·
                        rfl

theorem cell23_7373907_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 5, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 5, 5, 2, 2].length) (baseStart_7373907 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7373907 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7373907 prefixEnd_7373907 := by exact prefixLift 7373907
  have htrace : WordTrace (prefixWord ++ tailWord_7373907) baseStart_7373907 baseEnd_7373907 := by
    simpa [prefixWord, tailWord_7373907, baseEnd_7373907] using wordTrace_append hprefix tailTrace_7373907
  have hstable : (prefixWord ++ tailWord_7373907).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7373907).length < 2 ^ (prefixWord ++ tailWord_7373907).sum := by decide
  have hdescent : baseEnd_7373907 < baseStart_7373907 := by decide
  rcases family_descends (prefixWord ++ tailWord_7373907) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7373920 : List Nat := [2, 1, 1, 3, 2, 2, 1, 4, 1, 2, 4]
def baseStart_7373920 : Nat := 118140960795 + 7373920 * 2 ^ 59
def prefixEnd_7373920 : Nat := 4983230072969 + 3 ^ 40 * 7373920 * 2
def baseEnd_7373920 : Nat := 3786365267801894737787965

theorem tailTrace_7373920 : CollatzResearch.WordTrace tailWord_7373920 prefixEnd_7373920 3786365267801894737787965 := by
  unfold tailWord_7373920
  simp only [CollatzResearch.WordTrace]
  refine ⟨134474478722777340058959607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 179299304963703120078612809 134474478722777340058959607)
  ·
    refine ⟨201711718084166010088439411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134474478722777340058959607 201711718084166010088439411)
    ·
      refine ⟨302567577126249015132659117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 201711718084166010088439411 302567577126249015132659117)
      ·
        refine ⟨113462841422343380674747169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 302567577126249015132659117 113462841422343380674747169)
        ·
          refine ⟨85097131066757535506060377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 113462841422343380674747169 85097131066757535506060377)
          ·
            refine ⟨63822848300068151629545283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 85097131066757535506060377 63822848300068151629545283)
            ·
              refine ⟨95734272450102227444317925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63822848300068151629545283 95734272450102227444317925)
              ·
                refine ⟨17950176084394167645809611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 95734272450102227444317925 17950176084394167645809611)
                ·
                  refine ⟨26925264126591251468714417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17950176084394167645809611 26925264126591251468714417)
                  ·
                    refine ⟨20193948094943438601535813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26925264126591251468714417 20193948094943438601535813)
                    ·
                      refine ⟨3786365267801894737787965, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20193948094943438601535813 3786365267801894737787965)
                      ·
                        rfl

theorem cell23_7373920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 1, 4, 1, 2, 4].length) (baseStart_7373920 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7373920 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7373920 prefixEnd_7373920 := by exact prefixLift 7373920
  have htrace : WordTrace (prefixWord ++ tailWord_7373920) baseStart_7373920 baseEnd_7373920 := by
    simpa [prefixWord, tailWord_7373920, baseEnd_7373920] using wordTrace_append hprefix tailTrace_7373920
  have hstable : (prefixWord ++ tailWord_7373920).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7373920).length < 2 ^ (prefixWord ++ tailWord_7373920).sum := by decide
  have hdescent : baseEnd_7373920 < baseStart_7373920 := by decide
  rcases family_descends (prefixWord ++ tailWord_7373920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7373930 : List Nat := [3, 1, 3, 2, 2, 2, 10]
def baseStart_7373930 : Nat := 118140960795 + 7373930 * 2 ^ 59
def prefixEnd_7373930 : Nat := 4983230072969 + 3 ^ 40 * 7373930 * 2
def baseEnd_7373930 : Nat := 46745313612449872822999

theorem tailTrace_7373930 : CollatzResearch.WordTrace tailWord_7373930 prefixEnd_7373930 46745313612449872822999 := by
  unfold tailWord_7373930
  simp only [CollatzResearch.WordTrace]
  refine ⟨67237330543879612956445811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 179299548117012301217188829 67237330543879612956445811)
  ·
    refine ⟨100855995815819419434668717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67237330543879612956445811 100855995815819419434668717)
    ·
      refine ⟨37820998430932282288000769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 100855995815819419434668717 37820998430932282288000769)
      ·
        refine ⟨28365748823199211716000577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37820998430932282288000769 28365748823199211716000577)
        ·
          refine ⟨21274311617399408787000433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28365748823199211716000577 21274311617399408787000433)
          ·
            refine ⟨15955733713049556590250325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21274311617399408787000433 15955733713049556590250325)
            ·
              refine ⟨46745313612449872822999, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 15955733713049556590250325 46745313612449872822999)
              ·
                rfl

theorem cell23_7373930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 2, 10].length) (baseStart_7373930 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7373930 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7373930 prefixEnd_7373930 := by exact prefixLift 7373930
  have htrace : WordTrace (prefixWord ++ tailWord_7373930) baseStart_7373930 baseEnd_7373930 := by
    simpa [prefixWord, tailWord_7373930, baseEnd_7373930] using wordTrace_append hprefix tailTrace_7373930
  have hstable : (prefixWord ++ tailWord_7373930).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7373930).length < 2 ^ (prefixWord ++ tailWord_7373930).sum := by decide
  have hdescent : baseEnd_7373930 < baseStart_7373930 := by decide
  rcases family_descends (prefixWord ++ tailWord_7373930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7373934 : List Nat := [4, 1, 2, 2, 1, 2, 3, 2, 2, 4]
def baseStart_7373934 : Nat := 118140960795 + 7373934 * 2 ^ 59
def prefixEnd_7373934 : Nat := 4983230072969 + 3 ^ 40 * 7373934 * 2
def baseEnd_7373934 : Nat := 1262124152177019227670967

theorem tailTrace_7373934 : CollatzResearch.WordTrace tailWord_7373934 prefixEnd_7373934 1262124152177019227670967 := by
  unfold tailWord_7373934
  simp only [CollatzResearch.WordTrace]
  refine ⟨33618683508437995063616107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 179299645378335973672619237 33618683508437995063616107)
  ·
    refine ⟨50428025262656992595424161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33618683508437995063616107 50428025262656992595424161)
    ·
      refine ⟨37821018946992744446568121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50428025262656992595424161 37821018946992744446568121)
      ·
        refine ⟨28365764210244558334926091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37821018946992744446568121 28365764210244558334926091)
        ·
          refine ⟨42548646315366837502389137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28365764210244558334926091 42548646315366837502389137)
          ·
            refine ⟨31911484736525128126791853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42548646315366837502389137 31911484736525128126791853)
            ·
              refine ⟨11966806776196923047546945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31911484736525128126791853 11966806776196923047546945)
              ·
                refine ⟨8975105082147692285660209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11966806776196923047546945 8975105082147692285660209)
                ·
                  refine ⟨6731328811610769214245157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8975105082147692285660209 6731328811610769214245157)
                  ·
                    refine ⟨1262124152177019227670967, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6731328811610769214245157 1262124152177019227670967)
                    ·
                      rfl

theorem cell23_7373934_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 2, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 2, 3, 2, 2, 4].length) (baseStart_7373934 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7373934 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7373934 prefixEnd_7373934 := by exact prefixLift 7373934
  have htrace : WordTrace (prefixWord ++ tailWord_7373934) baseStart_7373934 baseEnd_7373934 := by
    simpa [prefixWord, tailWord_7373934, baseEnd_7373934] using wordTrace_append hprefix tailTrace_7373934
  have hstable : (prefixWord ++ tailWord_7373934).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7373934).length < 2 ^ (prefixWord ++ tailWord_7373934).sum := by decide
  have hdescent : baseEnd_7373934 < baseStart_7373934 := by decide
  rcases family_descends (prefixWord ++ tailWord_7373934) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7373984 : List Nat := [2, 1, 1, 4, 2, 1, 1, 5, 1, 3, 2]
def baseStart_7373984 : Nat := 118140960795 + 7373984 * 2 ^ 59
def prefixEnd_7373984 : Nat := 4983230072969 + 3 ^ 40 * 7373984 * 2
def baseEnd_7373984 : Nat := 3786398130563782487387671

theorem tailTrace_7373984 : CollatzResearch.WordTrace tailWord_7373984 prefixEnd_7373984 3786398130563782487387671 := by
  unfold tailWord_7373984
  simp only [CollatzResearch.WordTrace]
  refine ⟨134475645858661409524124503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 179300861144881879365499337 134475645858661409524124503)
  ·
    refine ⟨201713468787992114286186755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134475645858661409524124503 201713468787992114286186755)
    ·
      refine ⟨302570203181988171429280133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 201713468787992114286186755 302570203181988171429280133)
      ·
        refine ⟨56731913096622782142990025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 302570203181988171429280133 56731913096622782142990025)
        ·
          refine ⟨42548934822467086607242519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56731913096622782142990025 42548934822467086607242519)
          ·
            refine ⟨63823402233700629910863779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42548934822467086607242519 63823402233700629910863779)
            ·
              refine ⟨95735103350550944866295669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63823402233700629910863779 95735103350550944866295669)
              ·
                refine ⟨8975165939114151081215219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 95735103350550944866295669 8975165939114151081215219)
                ·
                  refine ⟨13462748908671226621822829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8975165939114151081215219 13462748908671226621822829)
                  ·
                    refine ⟨5048530840751709983183561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13462748908671226621822829 5048530840751709983183561)
                    ·
                      refine ⟨3786398130563782487387671, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5048530840751709983183561 3786398130563782487387671)
                      ·
                        rfl

theorem cell23_7373984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 1, 5, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 1, 5, 1, 3, 2].length) (baseStart_7373984 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7373984 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7373984 prefixEnd_7373984 := by exact prefixLift 7373984
  have htrace : WordTrace (prefixWord ++ tailWord_7373984) baseStart_7373984 baseEnd_7373984 := by
    simpa [prefixWord, tailWord_7373984, baseEnd_7373984] using wordTrace_append hprefix tailTrace_7373984
  have hstable : (prefixWord ++ tailWord_7373984).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7373984).length < 2 ^ (prefixWord ++ tailWord_7373984).sum := by decide
  have hdescent : baseEnd_7373984 < baseStart_7373984 := by decide
  rcases family_descends (prefixWord ++ tailWord_7373984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7374000 : List Nat := [2, 1, 1, 1, 2, 1, 2, 3, 1, 6, 3]
def baseStart_7374000 : Nat := 118140960795 + 7374000 * 2 ^ 59
def prefixEnd_7374000 : Nat := 4983230072969 + 3 ^ 40 * 7374000 * 2
def baseEnd_7374000 : Nat := 3786406346254254424787597

theorem tailTrace_7374000 : CollatzResearch.WordTrace tailWord_7374000 prefixEnd_7374000 3786406346254254424787597 := by
  unfold tailWord_7374000
  simp only [CollatzResearch.WordTrace]
  refine ⟨134475937642632426890415727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 179301250190176569187220969 134475937642632426890415727)
  ·
    refine ⟨201713906463948640335623591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134475937642632426890415727 201713906463948640335623591)
    ·
      refine ⟨302570859695922960503435387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 201713906463948640335623591 302570859695922960503435387)
      ·
        refine ⟨453856289543884440755153081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 302570859695922960503435387 453856289543884440755153081)
        ·
          refine ⟨340392217157913330566364811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 453856289543884440755153081 340392217157913330566364811)
          ·
            refine ⟨510588325736869995849547217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 340392217157913330566364811 510588325736869995849547217)
            ·
              refine ⟨382941244302652496887160413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 510588325736869995849547217 382941244302652496887160413)
              ·
                refine ⟨143602966613494686332685155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 382941244302652496887160413 143602966613494686332685155)
                ·
                  refine ⟨215404449920242029499027733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 143602966613494686332685155 215404449920242029499027733)
                  ·
                    refine ⟨10097083590011345132766925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 215404449920242029499027733 10097083590011345132766925)
                    ·
                      refine ⟨3786406346254254424787597, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10097083590011345132766925 3786406346254254424787597)
                      ·
                        rfl

theorem cell23_7374000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 2, 3, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 2, 3, 1, 6, 3].length) (baseStart_7374000 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7374000 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7374000 prefixEnd_7374000 := by exact prefixLift 7374000
  have htrace : WordTrace (prefixWord ++ tailWord_7374000) baseStart_7374000 baseEnd_7374000 := by
    simpa [prefixWord, tailWord_7374000, baseEnd_7374000] using wordTrace_append hprefix tailTrace_7374000
  have hstable : (prefixWord ++ tailWord_7374000).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7374000).length < 2 ^ (prefixWord ++ tailWord_7374000).sum := by decide
  have hdescent : baseEnd_7374000 < baseStart_7374000 := by decide
  rcases family_descends (prefixWord ++ tailWord_7374000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7374010 : List Nat := [3, 1, 1, 1, 2, 2, 1, 3, 1, 4, 4]
def baseStart_7374010 : Nat := 118140960795 + 7374010 * 2 ^ 59
def prefixEnd_7374010 : Nat := 4983230072969 + 3 ^ 40 * 7374010 * 2
def baseEnd_7374010 : Nat := 3786411481060799385662551

theorem tailTrace_7374010 : CollatzResearch.WordTrace tailWord_7374010 prefixEnd_7374010 3786411481060799385662551 := by
  unfold tailWord_7374010
  simp only [CollatzResearch.WordTrace]
  refine ⟨67238060003807156372173871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 179301493343485750325796989 67238060003807156372173871)
  ·
    refine ⟨100857090005710734558260807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67238060003807156372173871 100857090005710734558260807)
    ·
      refine ⟨151285635008566101837391211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100857090005710734558260807 151285635008566101837391211)
      ·
        refine ⟨226928452512849152756086817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 151285635008566101837391211 226928452512849152756086817)
        ·
          refine ⟨170196339384636864567065113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 226928452512849152756086817 170196339384636864567065113)
          ·
            refine ⟨127647254538477648425298835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 170196339384636864567065113 127647254538477648425298835)
            ·
              refine ⟨191470881807716472637948253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 127647254538477648425298835 191470881807716472637948253)
              ·
                refine ⟨71801580677893677239230595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 191470881807716472637948253 71801580677893677239230595)
                ·
                  refine ⟨107702371016840515858845893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 71801580677893677239230595 107702371016840515858845893)
                  ·
                    refine ⟨20194194565657596723533605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 107702371016840515858845893 20194194565657596723533605)
                    ·
                      refine ⟨3786411481060799385662551, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20194194565657596723533605 3786411481060799385662551)
                      ·
                        rfl

theorem cell23_7374010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 1, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 1, 3, 1, 4, 4].length) (baseStart_7374010 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7374010 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7374010 prefixEnd_7374010 := by exact prefixLift 7374010
  have htrace : WordTrace (prefixWord ++ tailWord_7374010) baseStart_7374010 baseEnd_7374010 := by
    simpa [prefixWord, tailWord_7374010, baseEnd_7374010] using wordTrace_append hprefix tailTrace_7374010
  have hstable : (prefixWord ++ tailWord_7374010).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7374010).length < 2 ^ (prefixWord ++ tailWord_7374010).sum := by decide
  have hdescent : baseEnd_7374010 < baseStart_7374010 := by decide
  rcases family_descends (prefixWord ++ tailWord_7374010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7374084 : List Nat := [2, 3, 2, 2, 2, 1, 3, 1, 2, 5]
def baseStart_7374084 : Nat := 118140960795 + 7374084 * 2 ^ 59
def prefixEnd_7374084 : Nat := 4983230072969 + 3 ^ 40 * 7374084 * 2
def baseEnd_7374084 : Nat := 1262149826209744032045737

theorem tailTrace_7374084 : CollatzResearch.WordTrace tailWord_7374084 prefixEnd_7374084 1262149826209744032045737 := by
  unfold tailWord_7374084
  simp only [CollatzResearch.WordTrace]
  refine ⟨134477469508480268063444653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 179303292677973690751259537 134477469508480268063444653)
  ·
    refine ⟨50429051065680100523791745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 134477469508480268063444653 50429051065680100523791745)
    ·
      refine ⟨37821788299260075392843809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50429051065680100523791745 37821788299260075392843809)
      ·
        refine ⟨28366341224445056544632857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37821788299260075392843809 28366341224445056544632857)
        ·
          refine ⟨21274755918333792408474643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28366341224445056544632857 21274755918333792408474643)
          ·
            refine ⟨31912133877500688612711965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21274755918333792408474643 31912133877500688612711965)
            ·
              refine ⟨11967050204062758229766987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31912133877500688612711965 11967050204062758229766987)
              ·
                refine ⟨17950575306094137344650481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11967050204062758229766987 17950575306094137344650481)
                ·
                  refine ⟨13462931479570603008487861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17950575306094137344650481 13462931479570603008487861)
                  ·
                    refine ⟨1262149826209744032045737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13462931479570603008487861 1262149826209744032045737)
                    ·
                      rfl

theorem cell23_7374084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 1, 3, 1, 2, 5].length) (baseStart_7374084 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7374084 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7374084 prefixEnd_7374084 := by exact prefixLift 7374084
  have htrace : WordTrace (prefixWord ++ tailWord_7374084) baseStart_7374084 baseEnd_7374084 := by
    simpa [prefixWord, tailWord_7374084, baseEnd_7374084] using wordTrace_append hprefix tailTrace_7374084
  have hstable : (prefixWord ++ tailWord_7374084).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7374084).length < 2 ^ (prefixWord ++ tailWord_7374084).sum := by decide
  have hdescent : baseEnd_7374084 < baseStart_7374084 := by decide
  rcases family_descends (prefixWord ++ tailWord_7374084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7374097 : List Nat := [1, 2, 2, 1, 1, 4, 1, 2, 5, 4]
def baseStart_7374097 : Nat := 118140960795 + 7374097 * 2 ^ 59
def prefixEnd_7374097 : Nat := 4983230072969 + 3 ^ 40 * 7374097 * 2
def baseEnd_7374097 : Nat := 1262152051292580181758217

theorem tailTrace_7374097 : CollatzResearch.WordTrace tailWord_7374097 prefixEnd_7374097 1262152051292580181758217 := by
  unfold tailWord_7374097
  simp only [CollatzResearch.WordTrace]
  refine ⟨268955413165913439347112545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179303608777275626231408363 268955413165913439347112545)
  ·
    refine ⟨201716559874435079510334409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 268955413165913439347112545 201716559874435079510334409)
    ·
      refine ⟨151287419905826309632750807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 201716559874435079510334409 151287419905826309632750807)
      ·
        refine ⟨226931129858739464449126211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 151287419905826309632750807 226931129858739464449126211)
        ·
          refine ⟨340396694788109196673689317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 226931129858739464449126211 340396694788109196673689317)
          ·
            refine ⟨63824380272770474376316747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 340396694788109196673689317 63824380272770474376316747)
            ·
              refine ⟨95736570409155711564475121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63824380272770474376316747 95736570409155711564475121)
              ·
                refine ⟨71802427806866783673356341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 95736570409155711564475121 71802427806866783673356341)
                ·
                  refine ⟨6731477606893760969377157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 71802427806866783673356341 6731477606893760969377157)
                  ·
                    refine ⟨1262152051292580181758217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6731477606893760969377157 1262152051292580181758217)
                    ·
                      rfl

theorem cell23_7374097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 1, 2, 5, 4].length) (baseStart_7374097 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7374097 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7374097 prefixEnd_7374097 := by exact prefixLift 7374097
  have htrace : WordTrace (prefixWord ++ tailWord_7374097) baseStart_7374097 baseEnd_7374097 := by
    simpa [prefixWord, tailWord_7374097, baseEnd_7374097] using wordTrace_append hprefix tailTrace_7374097
  have hstable : (prefixWord ++ tailWord_7374097).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7374097).length < 2 ^ (prefixWord ++ tailWord_7374097).sum := by decide
  have hdescent : baseEnd_7374097 < baseStart_7374097 := by decide
  rcases family_descends (prefixWord ++ tailWord_7374097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7374104 : List Nat := [2, 1, 2, 3, 1, 3, 1, 2, 2, 4, 2]
def baseStart_7374104 : Nat := 118140960795 + 7374104 * 2 ^ 59
def prefixEnd_7374104 : Nat := 4983230072969 + 3 ^ 40 * 7374104 * 2
def baseEnd_7374104 : Nat := 3786459748242322017887119

theorem tailTrace_7374104 : CollatzResearch.WordTrace tailWord_7374104 prefixEnd_7374104 3786459748242322017887119 := by
  unfold tailWord_7374104
  simp only [CollatzResearch.WordTrace]
  refine ⟨134477834238444039771308683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 179303778984592053028411577 134477834238444039771308683)
  ·
    refine ⟨201716751357666059656963025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134477834238444039771308683 201716751357666059656963025)
    ·
      refine ⟨151287563518249544742722269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 201716751357666059656963025 151287563518249544742722269)
      ·
        refine ⟨56732836319343579278520851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 151287563518249544742722269 56732836319343579278520851)
        ·
          refine ⟨85099254479015368917781277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56732836319343579278520851 85099254479015368917781277)
          ·
            refine ⟨31912220429630763344167979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 85099254479015368917781277 31912220429630763344167979)
            ·
              refine ⟨47868330644446145016251969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31912220429630763344167979 47868330644446145016251969)
              ·
                refine ⟨35901247983334608762188977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47868330644446145016251969 35901247983334608762188977)
                ·
                  refine ⟨26925935987500956571641733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35901247983334608762188977 26925935987500956571641733)
                  ·
                    refine ⟨5048612997656429357182825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 26925935987500956571641733 5048612997656429357182825)
                    ·
                      refine ⟨3786459748242322017887119, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5048612997656429357182825 3786459748242322017887119)
                      ·
                        rfl

theorem cell23_7374104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 3, 1, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 3, 1, 2, 2, 4, 2].length) (baseStart_7374104 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7374104 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7374104 prefixEnd_7374104 := by exact prefixLift 7374104
  have htrace : WordTrace (prefixWord ++ tailWord_7374104) baseStart_7374104 baseEnd_7374104 := by
    simpa [prefixWord, tailWord_7374104, baseEnd_7374104] using wordTrace_append hprefix tailTrace_7374104
  have hstable : (prefixWord ++ tailWord_7374104).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7374104).length < 2 ^ (prefixWord ++ tailWord_7374104).sum := by decide
  have hdescent : baseEnd_7374104 < baseStart_7374104 := by decide
  rcases family_descends (prefixWord ++ tailWord_7374104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7374107 : List Nat := [1, 1, 1, 1, 1, 1, 5, 3, 4, 2, 3]
def baseStart_7374107 : Nat := 118140960795 + 7374107 * 2 ^ 59
def prefixEnd_7374107 : Nat := 4983230072969 + 3 ^ 40 * 7374107 * 2
def baseEnd_7374107 : Nat := 3786461288684285506149605

theorem tailTrace_7374107 : CollatzResearch.WordTrace tailWord_7374107 prefixEnd_7374107 3786461288684285506149605 := by
  unfold tailWord_7374107
  simp only [CollatzResearch.WordTrace]
  refine ⟨268955777895877211054976575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179303851930584807369984383 268955777895877211054976575)
  ·
    refine ⟨403433666843815816582464863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 268955777895877211054976575 403433666843815816582464863)
    ·
      refine ⟨605150500265723724873697295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 403433666843815816582464863 605150500265723724873697295)
      ·
        refine ⟨907725750398585587310545943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 605150500265723724873697295 907725750398585587310545943)
        ·
          refine ⟨1361588625597878380965818915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 907725750398585587310545943 1361588625597878380965818915)
          ·
            refine ⟨2042382938396817571448728373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1361588625597878380965818915 2042382938396817571448728373)
            ·
              refine ⟨191473400474701647323318285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 2042382938396817571448728373 191473400474701647323318285)
              ·
                refine ⟨71802525178013117746244357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 191473400474701647323318285 71802525178013117746244357)
                ·
                  refine ⟨13462973470877459577420817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 71802525178013117746244357 13462973470877459577420817)
                  ·
                    refine ⟨10097230103158094683065613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13462973470877459577420817 10097230103158094683065613)
                    ·
                      refine ⟨3786461288684285506149605, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10097230103158094683065613 3786461288684285506149605)
                      ·
                        rfl

theorem cell23_7374107_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 5, 3, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 5, 3, 4, 2, 3].length) (baseStart_7374107 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7374107 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7374107 prefixEnd_7374107 := by exact prefixLift 7374107
  have htrace : WordTrace (prefixWord ++ tailWord_7374107) baseStart_7374107 baseEnd_7374107 := by
    simpa [prefixWord, tailWord_7374107, baseEnd_7374107] using wordTrace_append hprefix tailTrace_7374107
  have hstable : (prefixWord ++ tailWord_7374107).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7374107).length < 2 ^ (prefixWord ++ tailWord_7374107).sum := by decide
  have hdescent : baseEnd_7374107 < baseStart_7374107 := by decide
  rcases family_descends (prefixWord ++ tailWord_7374107) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7374154 : List Nat := [3, 1, 2, 1, 1, 1, 1, 4, 5, 1, 3]
def baseStart_7374154 : Nat := 118140960795 + 7374154 * 2 ^ 59
def prefixEnd_7374154 : Nat := 4983230072969 + 3 ^ 40 * 7374154 * 2
def baseEnd_7374154 : Nat := 3786485422275046822261889

theorem tailTrace_7374154 : CollatzResearch.WordTrace tailWord_7374154 prefixEnd_7374154 3786485422275046822261889 := by
  unfold tailWord_7374154
  simp only [CollatzResearch.WordTrace]
  refine ⟨67239373031676734520484379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 179304994751137958721291677 67239373031676734520484379)
  ·
    refine ⟨100859059547515101780726569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67239373031676734520484379 100859059547515101780726569)
    ·
      refine ⟨75644294660636326335544927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 100859059547515101780726569 75644294660636326335544927)
      ·
        refine ⟨113466441990954489503317391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75644294660636326335544927 113466441990954489503317391)
        ·
          refine ⟨170199662986431734254976087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 113466441990954489503317391 170199662986431734254976087)
          ·
            refine ⟨255299494479647601382464131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 170199662986431734254976087 255299494479647601382464131)
            ·
              refine ⟨382949241719471402073696197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 255299494479647601382464131 382949241719471402073696197)
              ·
                refine ⟨71802982822400887888818037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 382949241719471402073696197 71802982822400887888818037)
                ·
                  refine ⟨6731529639600083239576691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 71802982822400887888818037 6731529639600083239576691)
                  ·
                    refine ⟨10097294459400124859365037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6731529639600083239576691 10097294459400124859365037)
                    ·
                      refine ⟨3786485422275046822261889, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10097294459400124859365037 3786485422275046822261889)
                      ·
                        rfl

theorem cell23_7374154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 1, 4, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 1, 4, 5, 1, 3].length) (baseStart_7374154 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7374154 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7374154 prefixEnd_7374154 := by exact prefixLift 7374154
  have htrace : WordTrace (prefixWord ++ tailWord_7374154) baseStart_7374154 baseEnd_7374154 := by
    simpa [prefixWord, tailWord_7374154, baseEnd_7374154] using wordTrace_append hprefix tailTrace_7374154
  have hstable : (prefixWord ++ tailWord_7374154).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7374154).length < 2 ^ (prefixWord ++ tailWord_7374154).sum := by decide
  have hdescent : baseEnd_7374154 < baseStart_7374154 := by decide
  rcases family_descends (prefixWord ++ tailWord_7374154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7374194 : List Nat := [3, 2, 1, 2, 1, 2, 3, 1, 3, 1, 4]
def baseStart_7374194 : Nat := 118140960795 + 7374194 * 2 ^ 59
def prefixEnd_7374194 : Nat := 4983230072969 + 3 ^ 40 * 7374194 * 2
def baseEnd_7374194 : Nat := 3786505961501226665761705

theorem tailTrace_7374194 : CollatzResearch.WordTrace tailWord_7374194 prefixEnd_7374194 3786505961501226665761705 := by
  unfold tailWord_7374194
  simp only [CollatzResearch.WordTrace]
  refine ⟨67239737761640506228348409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 179305967364374683275595757 67239737761640506228348409)
  ·
    refine ⟨50429803321230379671261307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67239737761640506228348409 50429803321230379671261307)
    ·
      refine ⟨75644704981845569506891961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50429803321230379671261307 75644704981845569506891961)
      ·
        refine ⟨56733528736384177130168971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 75644704981845569506891961 56733528736384177130168971)
        ·
          refine ⟨85100293104576265695253457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56733528736384177130168971 85100293104576265695253457)
          ·
            refine ⟨63825219828432199271440093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 85100293104576265695253457 63825219828432199271440093)
            ·
              refine ⟨23934457435662074726790035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 63825219828432199271440093 23934457435662074726790035)
              ·
                refine ⟨35901686153493112090185053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23934457435662074726790035 35901686153493112090185053)
                ·
                  refine ⟨13463132307559917033819395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35901686153493112090185053 13463132307559917033819395)
                  ·
                    refine ⟨20194698461339875550729093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13463132307559917033819395 20194698461339875550729093)
                    ·
                      refine ⟨3786505961501226665761705, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20194698461339875550729093 3786505961501226665761705)
                      ·
                        rfl

theorem cell23_7374194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 3, 1, 3, 1, 4].length) (baseStart_7374194 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7374194 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7374194 prefixEnd_7374194 := by exact prefixLift 7374194
  have htrace : WordTrace (prefixWord ++ tailWord_7374194) baseStart_7374194 baseEnd_7374194 := by
    simpa [prefixWord, tailWord_7374194, baseEnd_7374194] using wordTrace_append hprefix tailTrace_7374194
  have hstable : (prefixWord ++ tailWord_7374194).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7374194).length < 2 ^ (prefixWord ++ tailWord_7374194).sum := by decide
  have hdescent : baseEnd_7374194 < baseStart_7374194 := by decide
  rcases family_descends (prefixWord ++ tailWord_7374194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7374217 : List Nat := [1, 2, 1, 1, 7, 11]
def baseStart_7374217 : Nat := 118140960795 + 7374217 * 2 ^ 59
def prefixEnd_7374217 : Nat := 4983230072969 + 3 ^ 40 * 7374217 * 2
def baseEnd_7374217 : Nat := 15582377660725432410593

theorem tailTrace_7374217 : CollatzResearch.WordTrace tailWord_7374217 prefixEnd_7374217 15582377660725432410593 := by
  unfold tailWord_7374217
  simp only [CollatzResearch.WordTrace]
  refine ⟨268959789925478699841480905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179306526616985799894320603 268959789925478699841480905)
  ·
    refine ⟨201719842444109024881110679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 268959789925478699841480905 201719842444109024881110679)
    ·
      refine ⟨302579763666163537321666019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 201719842444109024881110679 302579763666163537321666019)
      ·
        refine ⟨453869645499245305982499029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 302579763666163537321666019 453869645499245305982499029)
        ·
          refine ⟨10637569816388561858964821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 453869645499245305982499029 10637569816388561858964821)
          ·
            refine ⟨15582377660725432410593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 10637569816388561858964821 15582377660725432410593)
            ·
              rfl

theorem cell23_7374217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 7, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 7, 11].length) (baseStart_7374217 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7374217 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7374217 prefixEnd_7374217 := by exact prefixLift 7374217
  have htrace : WordTrace (prefixWord ++ tailWord_7374217) baseStart_7374217 baseEnd_7374217 := by
    simpa [prefixWord, tailWord_7374217, baseEnd_7374217] using wordTrace_append hprefix tailTrace_7374217
  have hstable : (prefixWord ++ tailWord_7374217).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7374217).length < 2 ^ (prefixWord ++ tailWord_7374217).sum := by decide
  have hdescent : baseEnd_7374217 < baseStart_7374217 := by decide
  rcases family_descends (prefixWord ++ tailWord_7374217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7374238 : List Nat := [4, 3, 1, 2, 2, 1, 2, 1, 1, 6]
def baseStart_7374238 : Nat := 118140960795 + 7374238 * 2 ^ 59
def prefixEnd_7374238 : Nat := 4983230072969 + 3 ^ 40 * 7374238 * 2
def baseEnd_7374238 : Nat := 1262176184883341497870501

theorem tailTrace_7374238 : CollatzResearch.WordTrace tailWord_7374238 prefixEnd_7374238 1262176184883341497870501 := by
  unfold tailWord_7374238
  simp only [CollatzResearch.WordTrace]
  refine ⟨33620069482300327553499421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 179307037238935080285330245 33620069482300327553499421)
  ·
    refine ⟨12607526055862622832562283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33620069482300327553499421 12607526055862622832562283)
    ·
      refine ⟨18911289083793934248843425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12607526055862622832562283 18911289083793934248843425)
      ·
        refine ⟨14183466812845450686632569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18911289083793934248843425 14183466812845450686632569)
        ·
          refine ⟨10637600109634088014974427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14183466812845450686632569 10637600109634088014974427)
          ·
            refine ⟨15956400164451132022461641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10637600109634088014974427 15956400164451132022461641)
            ·
              refine ⟨11967300123338349016846231, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15956400164451132022461641 11967300123338349016846231)
              ·
                refine ⟨17950950185007523525269347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11967300123338349016846231 17950950185007523525269347)
                ·
                  refine ⟨26926425277511285287904021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17950950185007523525269347 26926425277511285287904021)
                  ·
                    refine ⟨1262176184883341497870501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26926425277511285287904021 1262176184883341497870501)
                    ·
                      rfl

theorem cell23_7374238_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 2, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 2, 1, 2, 1, 1, 6].length) (baseStart_7374238 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7374238 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7374238 prefixEnd_7374238 := by exact prefixLift 7374238
  have htrace : WordTrace (prefixWord ++ tailWord_7374238) baseStart_7374238 baseEnd_7374238 := by
    simpa [prefixWord, tailWord_7374238, baseEnd_7374238] using wordTrace_append hprefix tailTrace_7374238
  have hstable : (prefixWord ++ tailWord_7374238).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7374238).length < 2 ^ (prefixWord ++ tailWord_7374238).sum := by decide
  have hdescent : baseEnd_7374238 < baseStart_7374238 := by decide
  rcases family_descends (prefixWord ++ tailWord_7374238) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7374261 : List Nat := [1, 3, 3, 2, 2, 1, 2, 2, 1, 3, 3]
def baseStart_7374261 : Nat := 118140960795 + 7374261 * 2 ^ 59
def prefixEnd_7374261 : Nat := 4983230072969 + 3 ^ 40 * 7374261 * 2
def baseEnd_7374261 : Nat := 3786540364705077903623897

theorem tailTrace_7374261 : CollatzResearch.WordTrace tailWord_7374261 prefixEnd_7374261 3786540364705077903623897 := by
  unfold tailWord_7374261
  simp only [CollatzResearch.WordTrace]
  refine ⟨268961394737319295356082637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179307596491546196904055091 268961394737319295356082637)
  ·
    refine ⟨100860523026494735758530989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 268961394737319295356082637 100860523026494735758530989)
    ·
      refine ⟨37822696134935525909449121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 100860523026494735758530989 37822696134935525909449121)
      ·
        refine ⟨28367022101201644432086841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37822696134935525909449121 28367022101201644432086841)
        ·
          refine ⟨21275266575901233324065131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28367022101201644432086841 21275266575901233324065131)
          ·
            refine ⟨31912899863851849986097697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21275266575901233324065131 31912899863851849986097697)
            ·
              refine ⟨23934674897888887489573273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31912899863851849986097697 23934674897888887489573273)
              ·
                refine ⟨17951006173416665617179955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23934674897888887489573273 17951006173416665617179955)
                ·
                  refine ⟨26926509260124998425769933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17951006173416665617179955 26926509260124998425769933)
                  ·
                    refine ⟨10097440972546874409663725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 26926509260124998425769933 10097440972546874409663725)
                    ·
                      refine ⟨3786540364705077903623897, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10097440972546874409663725 3786540364705077903623897)
                      ·
                        rfl

theorem cell23_7374261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 1, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 1, 2, 2, 1, 3, 3].length) (baseStart_7374261 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7374261 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7374261 prefixEnd_7374261 := by exact prefixLift 7374261
  have htrace : WordTrace (prefixWord ++ tailWord_7374261) baseStart_7374261 baseEnd_7374261 := by
    simpa [prefixWord, tailWord_7374261, baseEnd_7374261] using wordTrace_append hprefix tailTrace_7374261
  have hstable : (prefixWord ++ tailWord_7374261).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7374261).length < 2 ^ (prefixWord ++ tailWord_7374261).sum := by decide
  have hdescent : baseEnd_7374261 < baseStart_7374261 := by decide
  rcases family_descends (prefixWord ++ tailWord_7374261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7374265 : List Nat := [1, 2, 1, 4, 4, 2, 2, 1, 1, 2, 3]
def baseStart_7374265 : Nat := 118140960795 + 7374265 * 2 ^ 59
def prefixEnd_7374265 : Nat := 4983230072969 + 3 ^ 40 * 7374265 * 2
def baseEnd_7374265 : Nat := 3786542418627695887973879

theorem tailTrace_7374265 : CollatzResearch.WordTrace tailWord_7374265 prefixEnd_7374265 3786542418627695887973879 := by
  unfold tailWord_7374265
  simp only [CollatzResearch.WordTrace]
  refine ⟨268961540629304804039228249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179307693752869869359485499 268961540629304804039228249)
  ·
    refine ⟨201721155471978603029421187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 268961540629304804039228249 201721155471978603029421187)
    ·
      refine ⟨302581733207967904544131781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 201721155471978603029421187 302581733207967904544131781)
      ·
        refine ⟨56734074976493982102024709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 302581733207967904544131781 56734074976493982102024709)
        ·
          refine ⟨10637639058092621644129633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 56734074976493982102024709 10637639058092621644129633)
          ·
            refine ⟨7978229293569466233097225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10637639058092621644129633 7978229293569466233097225)
            ·
              refine ⟨5983671970177099674822919, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7978229293569466233097225 5983671970177099674822919)
              ·
                refine ⟨8975507955265649512234379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5983671970177099674822919 8975507955265649512234379)
                ·
                  refine ⟨13463261932898474268351569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8975507955265649512234379 13463261932898474268351569)
                  ·
                    refine ⟨10097446449673855701263677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13463261932898474268351569 10097446449673855701263677)
                    ·
                      refine ⟨3786542418627695887973879, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10097446449673855701263677 3786542418627695887973879)
                      ·
                        rfl

theorem cell23_7374265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 4, 2, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 4, 2, 2, 1, 1, 2, 3].length) (baseStart_7374265 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7374265 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7374265 prefixEnd_7374265 := by exact prefixLift 7374265
  have htrace : WordTrace (prefixWord ++ tailWord_7374265) baseStart_7374265 baseEnd_7374265 := by
    simpa [prefixWord, tailWord_7374265, baseEnd_7374265] using wordTrace_append hprefix tailTrace_7374265
  have hstable : (prefixWord ++ tailWord_7374265).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7374265).length < 2 ^ (prefixWord ++ tailWord_7374265).sum := by decide
  have hdescent : baseEnd_7374265 < baseStart_7374265 := by decide
  rcases family_descends (prefixWord ++ tailWord_7374265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7374318 : List Nat := [4, 1, 2, 1, 2, 1, 1, 1, 6, 2, 2]
def baseStart_7374318 : Nat := 118140960795 + 7374318 * 2 ^ 59
def prefixEnd_7374318 : Nat := 4983230072969 + 3 ^ 40 * 7374318 * 2
def baseEnd_7374318 : Nat := 3786569633102384180611135

theorem tailTrace_7374318 : CollatzResearch.WordTrace tailWord_7374318 prefixEnd_7374318 3786569633102384180611135 := by
  unfold tailWord_7374318
  simp only [CollatzResearch.WordTrace]
  refine ⟨33620434212264099261363451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 179308982465408529393938405 33620434212264099261363451)
  ·
    refine ⟨50430651318396148892045177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33620434212264099261363451 50430651318396148892045177)
    ·
      refine ⟨37822988488797111669033883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50430651318396148892045177 37822988488797111669033883)
      ·
        refine ⟨56734482733195667503550825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37822988488797111669033883 56734482733195667503550825)
        ·
          refine ⟨42550862049896750627663119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56734482733195667503550825 42550862049896750627663119)
          ·
            refine ⟨63826293074845125941494679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42550862049896750627663119 63826293074845125941494679)
            ·
              refine ⟨95739439612267688912242019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63826293074845125941494679 95739439612267688912242019)
              ·
                refine ⟨143609159418401533368363029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 95739439612267688912242019 143609159418401533368363029)
                ·
                  refine ⟨6731679347737571876642017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 143609159418401533368363029 6731679347737571876642017)
                  ·
                    refine ⟨5048759510803178907481513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6731679347737571876642017 5048759510803178907481513)
                    ·
                      refine ⟨3786569633102384180611135, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5048759510803178907481513 3786569633102384180611135)
                      ·
                        rfl

theorem cell23_7374318_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 1, 1, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 1, 1, 6, 2, 2].length) (baseStart_7374318 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7374318 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7374318 prefixEnd_7374318 := by exact prefixLift 7374318
  have htrace : WordTrace (prefixWord ++ tailWord_7374318) baseStart_7374318 baseEnd_7374318 := by
    simpa [prefixWord, tailWord_7374318, baseEnd_7374318] using wordTrace_append hprefix tailTrace_7374318
  have hstable : (prefixWord ++ tailWord_7374318).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7374318).length < 2 ^ (prefixWord ++ tailWord_7374318).sum := by decide
  have hdescent : baseEnd_7374318 < baseStart_7374318 := by decide
  rcases family_descends (prefixWord ++ tailWord_7374318) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7374364 : List Nat := [2, 2, 3, 1, 2, 1, 1, 2, 1, 1, 7]
def baseStart_7374364 : Nat := 118140960795 + 7374364 * 2 ^ 59
def prefixEnd_7374364 : Nat := 4983230072969 + 3 ^ 40 * 7374364 * 2
def baseEnd_7374364 : Nat := 3786593253212491000635923

theorem tailTrace_7374364 : CollatzResearch.WordTrace tailWord_7374364 prefixEnd_7374364 3786593253212491000635923 := by
  unfold tailWord_7374364
  simp only [CollatzResearch.WordTrace]
  refine ⟨134482575727973071973541073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 179310100970630762631388097 134482575727973071973541073)
  ·
    refine ⟨100861931795979803980155805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 134482575727973071973541073 100861931795979803980155805)
    ·
      refine ⟨37823224423492426492558427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 100861931795979803980155805 37823224423492426492558427)
      ·
        refine ⟨56734836635238639738837641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37823224423492426492558427 56734836635238639738837641)
        ·
          refine ⟨42551127476428979804128231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56734836635238639738837641 42551127476428979804128231)
          ·
            refine ⟨63826691214643469706192347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42551127476428979804128231 63826691214643469706192347)
            ·
              refine ⟨95740036821965204559288521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63826691214643469706192347 95740036821965204559288521)
              ·
                refine ⟨71805027616473903419466391, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 95740036821965204559288521 71805027616473903419466391)
                ·
                  refine ⟨107707541424710855129199587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 71805027616473903419466391 107707541424710855129199587)
                  ·
                    refine ⟨161561312137066282693799381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 107707541424710855129199587 161561312137066282693799381)
                    ·
                      refine ⟨3786593253212491000635923, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 161561312137066282693799381 3786593253212491000635923)
                      ·
                        rfl

theorem cell23_7374364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 1, 2, 1, 1, 7].length) (baseStart_7374364 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7374364 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7374364 prefixEnd_7374364 := by exact prefixLift 7374364
  have htrace : WordTrace (prefixWord ++ tailWord_7374364) baseStart_7374364 baseEnd_7374364 := by
    simpa [prefixWord, tailWord_7374364, baseEnd_7374364] using wordTrace_append hprefix tailTrace_7374364
  have hstable : (prefixWord ++ tailWord_7374364).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7374364).length < 2 ^ (prefixWord ++ tailWord_7374364).sum := by decide
  have hdescent : baseEnd_7374364 < baseStart_7374364 := by decide
  rcases family_descends (prefixWord ++ tailWord_7374364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7374391 : List Nat := [1, 1, 3, 1, 2, 4, 2, 2, 2, 1, 4]
def baseStart_7374391 : Nat := 118140960795 + 7374391 * 2 ^ 59
def prefixEnd_7374391 : Nat := 4983230072969 + 3 ^ 40 * 7374391 * 2
def baseEnd_7374391 : Nat := 3786607117190162394998299

theorem tailTrace_7374391 : CollatzResearch.WordTrace tailWord_7374391 prefixEnd_7374391 3786607117190162394998299 := by
  unfold tailWord_7374391
  simp only [CollatzResearch.WordTrace]
  refine ⟨268966136226848327558315027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179310757484565551705543351 268966136226848327558315027)
  ·
    refine ⟨403449204340272491337472541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 268966136226848327558315027 403449204340272491337472541)
    ·
      refine ⟨151293451627602184251552203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 403449204340272491337472541 151293451627602184251552203)
      ·
        refine ⟨226940177441403276377328305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 151293451627602184251552203 226940177441403276377328305)
        ·
          refine ⟨170205133081052457282996229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 226940177441403276377328305 170205133081052457282996229)
          ·
            refine ⟨31913462452697335740561793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 170205133081052457282996229 31913462452697335740561793)
            ·
              refine ⟨23935096839523001805421345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31913462452697335740561793 23935096839523001805421345)
              ·
                refine ⟨17951322629642251354066009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23935096839523001805421345 17951322629642251354066009)
                ·
                  refine ⟨13463491972231688515549507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17951322629642251354066009 13463491972231688515549507)
                  ·
                    refine ⟨20195237958347532773324261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13463491972231688515549507 20195237958347532773324261)
                    ·
                      refine ⟨3786607117190162394998299, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20195237958347532773324261 3786607117190162394998299)
                      ·
                        rfl

theorem cell23_7374391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 4, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 4, 2, 2, 2, 1, 4].length) (baseStart_7374391 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7374391 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7374391 prefixEnd_7374391 := by exact prefixLift 7374391
  have htrace : WordTrace (prefixWord ++ tailWord_7374391) baseStart_7374391 baseEnd_7374391 := by
    simpa [prefixWord, tailWord_7374391, baseEnd_7374391] using wordTrace_append hprefix tailTrace_7374391
  have hstable : (prefixWord ++ tailWord_7374391).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7374391).length < 2 ^ (prefixWord ++ tailWord_7374391).sum := by decide
  have hdescent : baseEnd_7374391 < baseStart_7374391 := by decide
  rcases family_descends (prefixWord ++ tailWord_7374391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7374394 : List Nat := [3, 1, 1, 1, 3, 2, 1, 1, 2, 3, 5]
def baseStart_7374394 : Nat := 118140960795 + 7374394 * 2 ^ 59
def prefixEnd_7374394 : Nat := 4983230072969 + 3 ^ 40 * 7374394 * 2
def baseEnd_7374394 : Nat := 3786608657632125883260785

theorem tailTrace_7374394 : CollatzResearch.WordTrace tailWord_7374394 prefixEnd_7374394 3786608657632125883260785 := by
  unfold tailWord_7374394
  simp only [CollatzResearch.WordTrace]
  refine ⟨67241561411459364767668559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 179310830430558306047116157 67241561411459364767668559)
  ·
    refine ⟨100862342117189047151502839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67241561411459364767668559 100862342117189047151502839)
    ·
      refine ⟨151293513175783570727254259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100862342117189047151502839 151293513175783570727254259)
      ·
        refine ⟨226940269763675356090881389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 151293513175783570727254259 226940269763675356090881389)
        ·
          refine ⟨85102601161378258534080521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 226940269763675356090881389 85102601161378258534080521)
          ·
            refine ⟨63826950871033693900560391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 85102601161378258534080521 63826950871033693900560391)
            ·
              refine ⟨95740426306550540850840587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63826950871033693900560391 95740426306550540850840587)
              ·
                refine ⟨143610639459825811276260881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 95740426306550540850840587 143610639459825811276260881)
                ·
                  refine ⟨107707979594869358457195661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 143610639459825811276260881 107707979594869358457195661)
                  ·
                    refine ⟨40390492348076009421448373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 107707979594869358457195661 40390492348076009421448373)
                    ·
                      refine ⟨3786608657632125883260785, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 40390492348076009421448373 3786608657632125883260785)
                      ·
                        rfl

theorem cell23_7374394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 1, 1, 2, 3, 5].length) (baseStart_7374394 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7374394 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7374394 prefixEnd_7374394 := by exact prefixLift 7374394
  have htrace : WordTrace (prefixWord ++ tailWord_7374394) baseStart_7374394 baseEnd_7374394 := by
    simpa [prefixWord, tailWord_7374394, baseEnd_7374394] using wordTrace_append hprefix tailTrace_7374394
  have hstable : (prefixWord ++ tailWord_7374394).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7374394).length < 2 ^ (prefixWord ++ tailWord_7374394).sum := by decide
  have hdescent : baseEnd_7374394 < baseStart_7374394 := by decide
  rcases family_descends (prefixWord ++ tailWord_7374394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7374414 : List Nat := [4, 1, 1, 1, 1, 2, 1, 2, 10]
def baseStart_7374414 : Nat := 118140960795 + 7374414 * 2 ^ 59
def prefixEnd_7374414 : Nat := 4983230072969 + 3 ^ 40 * 7374414 * 2
def baseEnd_7374414 : Nat := 420735436360579533890077

theorem tailTrace_7374414 : CollatzResearch.WordTrace tailWord_7374414 prefixEnd_7374414 420735436360579533890077 := by
  unfold tailWord_7374414
  simp only [CollatzResearch.WordTrace]
  refine ⟨33620871888220625310800287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 179311316737176668324268197 33620871888220625310800287)
  ·
    refine ⟨50431307832330937966200431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33620871888220625310800287 50431307832330937966200431)
    ·
      refine ⟨75646961748496406949300647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50431307832330937966200431 75646961748496406949300647)
      ·
        refine ⟨113470442622744610423950971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75646961748496406949300647 113470442622744610423950971)
        ·
          refine ⟨170205663934116915635926457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 113470442622744610423950971 170205663934116915635926457)
          ·
            refine ⟨127654247950587686726944843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 170205663934116915635926457 127654247950587686726944843)
            ·
              refine ⟨191481371925881530090417265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 127654247950587686726944843 191481371925881530090417265)
              ·
                refine ⟨143611028944411147567812949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 191481371925881530090417265 143611028944411147567812949)
                ·
                  refine ⟨420735436360579533890077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 143611028944411147567812949 420735436360579533890077)
                  ·
                    rfl

theorem cell23_7374414_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 1, 2, 10].length) (baseStart_7374414 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7374414 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7374414 prefixEnd_7374414 := by exact prefixLift 7374414
  have htrace : WordTrace (prefixWord ++ tailWord_7374414) baseStart_7374414 baseEnd_7374414 := by
    simpa [prefixWord, tailWord_7374414, baseEnd_7374414] using wordTrace_append hprefix tailTrace_7374414
  have hstable : (prefixWord ++ tailWord_7374414).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7374414).length < 2 ^ (prefixWord ++ tailWord_7374414).sum := by decide
  have hdescent : baseEnd_7374414 < baseStart_7374414 := by decide
  rcases family_descends (prefixWord ++ tailWord_7374414) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7374418 : List Nat := [3, 2, 2, 1, 2, 3, 1, 2, 3, 4]
def baseStart_7374418 : Nat := 118140960795 + 7374418 * 2 ^ 59
def prefixEnd_7374418 : Nat := 4983230072969 + 3 ^ 40 * 7374418 * 2
def baseEnd_7374418 : Nat := 1262206993722611263120225

theorem tailTrace_7374418 : CollatzResearch.WordTrace tailWord_7374418 prefixEnd_7374418 1262206993722611263120225 := by
  unfold tailWord_7374418
  simp only [CollatzResearch.WordTrace]
  refine ⟨67241780249437627792386977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 179311413998500340779698605 67241780249437627792386977)
  ·
    refine ⟨50431335187078220844290233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67241780249437627792386977 50431335187078220844290233)
    ·
      refine ⟨37823501390308665633217675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50431335187078220844290233 37823501390308665633217675)
      ·
        refine ⟨56735252085462998449826513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37823501390308665633217675 56735252085462998449826513)
        ·
          refine ⟨42551439064097248837369885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56735252085462998449826513 42551439064097248837369885)
          ·
            refine ⟨15956789649036468314013707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42551439064097248837369885 15956789649036468314013707)
            ·
              refine ⟨23935184473554702471020561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15956789649036468314013707 23935184473554702471020561)
              ·
                refine ⟨17951388355166026853265421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23935184473554702471020561 17951388355166026853265421)
                ·
                  refine ⟨6731770633187260069974533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17951388355166026853265421 6731770633187260069974533)
                  ·
                    refine ⟨1262206993722611263120225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6731770633187260069974533 1262206993722611263120225)
                    ·
                      rfl

theorem cell23_7374418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 3, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 3, 1, 2, 3, 4].length) (baseStart_7374418 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7374418 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7374418 prefixEnd_7374418 := by exact prefixLift 7374418
  have htrace : WordTrace (prefixWord ++ tailWord_7374418) baseStart_7374418 baseEnd_7374418 := by
    simpa [prefixWord, tailWord_7374418, baseEnd_7374418] using wordTrace_append hprefix tailTrace_7374418
  have hstable : (prefixWord ++ tailWord_7374418).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7374418).length < 2 ^ (prefixWord ++ tailWord_7374418).sum := by decide
  have hdescent : baseEnd_7374418 < baseStart_7374418 := by decide
  rcases family_descends (prefixWord ++ tailWord_7374418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7374428 : List Nat := [2, 2, 4, 1, 2, 2, 1, 1, 1, 4, 3]
def baseStart_7374428 : Nat := 118140960795 + 7374428 * 2 ^ 59
def prefixEnd_7374428 : Nat := 4983230072969 + 3 ^ 40 * 7374428 * 2
def baseEnd_7374428 : Nat := 3786626115974378750235629

theorem tailTrace_7374428 : CollatzResearch.WordTrace tailWord_7374428 prefixEnd_7374428 3786626115974378750235629 := by
  unfold tailWord_7374428
  simp only [CollatzResearch.WordTrace]
  refine ⟨134483742863857141438705969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 179311657151809521918274625 134483742863857141438705969)
  ·
    refine ⟨100862807147892856079029477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 134483742863857141438705969 100862807147892856079029477)
    ·
      refine ⟨18911776340229910514818027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 100862807147892856079029477 18911776340229910514818027)
      ·
        refine ⟨28367664510344865772227041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18911776340229910514818027 28367664510344865772227041)
        ·
          refine ⟨21275748382758649329170281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28367664510344865772227041 21275748382758649329170281)
          ·
            refine ⟨15956811287068986996877711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21275748382758649329170281 15956811287068986996877711)
            ·
              refine ⟨23935216930603480495316567, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15956811287068986996877711 23935216930603480495316567)
              ·
                refine ⟨35902825395905220742974851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23935216930603480495316567 35902825395905220742974851)
                ·
                  refine ⟨53854238093857831114462277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35902825395905220742974851 53854238093857831114462277)
                  ·
                    refine ⟨10097669642598343333961677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 53854238093857831114462277 10097669642598343333961677)
                    ·
                      refine ⟨3786626115974378750235629, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10097669642598343333961677 3786626115974378750235629)
                      ·
                        rfl

theorem cell23_7374428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 2, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 2, 1, 1, 1, 4, 3].length) (baseStart_7374428 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7374428 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7374428 prefixEnd_7374428 := by exact prefixLift 7374428
  have htrace : WordTrace (prefixWord ++ tailWord_7374428) baseStart_7374428 baseEnd_7374428 := by
    simpa [prefixWord, tailWord_7374428, baseEnd_7374428] using wordTrace_append hprefix tailTrace_7374428
  have hstable : (prefixWord ++ tailWord_7374428).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7374428).length < 2 ^ (prefixWord ++ tailWord_7374428).sum := by decide
  have hdescent : baseEnd_7374428 < baseStart_7374428 := by decide
  rcases family_descends (prefixWord ++ tailWord_7374428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7374435 : List Nat := [1, 1, 1, 5, 1, 4, 2, 3, 1, 4]
def baseStart_7374435 : Nat := 118140960795 + 7374435 * 2 ^ 59
def prefixEnd_7374435 : Nat := 4983230072969 + 3 ^ 40 * 7374435 * 2
def baseEnd_7374435 : Nat := 1262209903446320074282699

theorem tailTrace_7374435 : CollatzResearch.WordTrace tailWord_7374435 prefixEnd_7374435 1262209903446320074282699 := by
  unfold tailWord_7374435
  simp only [CollatzResearch.WordTrace]
  refine ⟨268967741038688923072916759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179311827359125948715277839 268967741038688923072916759)
  ·
    refine ⟨403451611558033384609375139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 268967741038688923072916759 403451611558033384609375139)
    ·
      refine ⟨605177417337050076914062709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 403451611558033384609375139 605177417337050076914062709)
      ·
        refine ⟨56735382875348444710693379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 605177417337050076914062709 56735382875348444710693379)
        ·
          refine ⟨85103074313022667066040069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56735382875348444710693379 85103074313022667066040069)
          ·
            refine ⟨15956826433691750074882513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 85103074313022667066040069 15956826433691750074882513)
            ·
              refine ⟨11967619825268812556161885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15956826433691750074882513 11967619825268812556161885)
              ·
                refine ⟨4487857434475804708560707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11967619825268812556161885 4487857434475804708560707)
                ·
                  refine ⟨6731786151713707062841061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4487857434475804708560707 6731786151713707062841061)
                  ·
                    refine ⟨1262209903446320074282699, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6731786151713707062841061 1262209903446320074282699)
                    ·
                      rfl

theorem cell23_7374435_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 4, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 4, 2, 3, 1, 4].length) (baseStart_7374435 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7374435 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7374435 prefixEnd_7374435 := by exact prefixLift 7374435
  have htrace : WordTrace (prefixWord ++ tailWord_7374435) baseStart_7374435 baseEnd_7374435 := by
    simpa [prefixWord, tailWord_7374435, baseEnd_7374435] using wordTrace_append hprefix tailTrace_7374435
  have hstable : (prefixWord ++ tailWord_7374435).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7374435).length < 2 ^ (prefixWord ++ tailWord_7374435).sum := by decide
  have hdescent : baseEnd_7374435 < baseStart_7374435 := by decide
  rcases family_descends (prefixWord ++ tailWord_7374435) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7374448 : List Nat := [2, 1, 1, 1, 6, 3, 1, 2, 6]
def baseStart_7374448 : Nat := 118140960795 + 7374448 * 2 ^ 59
def prefixEnd_7374448 : Nat := 4983230072969 + 3 ^ 40 * 7374448 * 2
def baseEnd_7374448 : Nat := 420737376176385407998393

theorem tailTrace_7374448 : CollatzResearch.WordTrace tailWord_7374448 prefixEnd_7374448 420737376176385407998393 := by
  unfold tailWord_7374448
  simp only [CollatzResearch.WordTrace]
  refine ⟨134484107593820913146569999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 179312143458427884195426665 134484107593820913146569999)
  ·
    refine ⟨201726161390731369719854999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134484107593820913146569999 201726161390731369719854999)
    ·
      refine ⟨302589242086097054579782499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 201726161390731369719854999 302589242086097054579782499)
      ·
        refine ⟨453883863129145581869673749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 302589242086097054579782499 453883863129145581869673749)
        ·
          refine ⟨21275806084178699150140957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 453883863129145581869673749 21275806084178699150140957)
          ·
            refine ⟨7978427281567012181302859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21275806084178699150140957 7978427281567012181302859)
            ·
              refine ⟨11967640922350518271954289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7978427281567012181302859 11967640922350518271954289)
              ·
                refine ⟨8975730691762888703965717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11967640922350518271954289 8975730691762888703965717)
                ·
                  refine ⟨420737376176385407998393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8975730691762888703965717 420737376176385407998393)
                  ·
                    rfl

theorem cell23_7374448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 3, 1, 2, 6].length) (baseStart_7374448 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7374448 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7374448 prefixEnd_7374448 := by exact prefixLift 7374448
  have htrace : WordTrace (prefixWord ++ tailWord_7374448) baseStart_7374448 baseEnd_7374448 := by
    simpa [prefixWord, tailWord_7374448, baseEnd_7374448] using wordTrace_append hprefix tailTrace_7374448
  have hstable : (prefixWord ++ tailWord_7374448).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7374448).length < 2 ^ (prefixWord ++ tailWord_7374448).sum := by decide
  have hdescent : baseEnd_7374448 < baseStart_7374448 := by decide
  rcases family_descends (prefixWord ++ tailWord_7374448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7374478 : List Nat := [4, 1, 1, 3, 1, 2, 1, 4, 1, 5]
def baseStart_7374478 : Nat := 118140960795 + 7374478 * 2 ^ 59
def prefixEnd_7374478 : Nat := 4983230072969 + 3 ^ 40 * 7374478 * 2
def baseEnd_7374478 : Nat := 1262217263335701184870133

theorem tailTrace_7374478 : CollatzResearch.WordTrace tailWord_7374478 prefixEnd_7374478 1262217263335701184870133 := by
  unfold tailWord_7374478
  simp only [CollatzResearch.WordTrace]
  refine ⟨33621163672191642677091511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 179312872918355427611154725 33621163672191642677091511)
  ·
    refine ⟨50431745508287464015637267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33621163672191642677091511 50431745508287464015637267)
    ·
      refine ⟨75647618262431196023455901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50431745508287464015637267 75647618262431196023455901)
      ·
        refine ⟨28367856848411698508795963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 75647618262431196023455901 28367856848411698508795963)
        ·
          refine ⟨42551785272617547763193945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28367856848411698508795963 42551785272617547763193945)
          ·
            refine ⟨31913838954463160822395459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42551785272617547763193945 31913838954463160822395459)
            ·
              refine ⟨47870758431694741233593189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31913838954463160822395459 47870758431694741233593189)
              ·
                refine ⟨8975767205942763981298723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 47870758431694741233593189 8975767205942763981298723)
                ·
                  refine ⟨13463650808914145971948085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8975767205942763981298723 13463650808914145971948085)
                  ·
                    refine ⟨1262217263335701184870133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13463650808914145971948085 1262217263335701184870133)
                    ·
                      rfl

theorem cell23_7374478_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 2, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 2, 1, 4, 1, 5].length) (baseStart_7374478 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7374478 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7374478 prefixEnd_7374478 := by exact prefixLift 7374478
  have htrace : WordTrace (prefixWord ++ tailWord_7374478) baseStart_7374478 baseEnd_7374478 := by
    simpa [prefixWord, tailWord_7374478, baseEnd_7374478] using wordTrace_append hprefix tailTrace_7374478
  have hstable : (prefixWord ++ tailWord_7374478).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7374478).length < 2 ^ (prefixWord ++ tailWord_7374478).sum := by decide
  have hdescent : baseEnd_7374478 < baseStart_7374478 := by decide
  rcases family_descends (prefixWord ++ tailWord_7374478) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7374501 : List Nat := [1, 3, 1, 2, 1, 2, 3, 3, 1, 1, 5]
def baseStart_7374501 : Nat := 118140960795 + 7374501 * 2 ^ 59
def prefixEnd_7374501 : Nat := 4983230072969 + 3 ^ 40 * 7374501 * 2
def baseEnd_7374501 : Nat := 3786663600062156964622793

theorem tailTrace_7374501 : CollatzResearch.WordTrace tailWord_7374501 prefixEnd_7374501 3786663600062156964622793 := by
  unfold tailWord_7374501
  simp only [CollatzResearch.WordTrace]
  refine ⟨268970148256449816344819357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179313432170966544229879571 268970148256449816344819357)
  ·
    refine ⟨100863805596168681129307259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 268970148256449816344819357 100863805596168681129307259)
    ·
      refine ⟨151295708394253021693960889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100863805596168681129307259 151295708394253021693960889)
      ·
        refine ⟨113471781295689766270470667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 151295708394253021693960889 113471781295689766270470667)
        ·
          refine ⟨170207671943534649405706001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 113471781295689766270470667 170207671943534649405706001)
          ·
            refine ⟨127655753957650987054279501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 170207671943534649405706001 127655753957650987054279501)
            ·
              refine ⟨47870907734119120145354813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 127655753957650987054279501 47870907734119120145354813)
              ·
                refine ⟨17951590400294670054508055, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 47870907734119120145354813 17951590400294670054508055)
                ·
                  refine ⟨26927385600442005081762083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17951590400294670054508055 26927385600442005081762083)
                  ·
                    refine ⟨40391078400663007622643125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 26927385600442005081762083 40391078400663007622643125)
                    ·
                      refine ⟨3786663600062156964622793, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 40391078400663007622643125 3786663600062156964622793)
                      ·
                        rfl

theorem cell23_7374501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 3, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 3, 3, 1, 1, 5].length) (baseStart_7374501 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7374501 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7374501 prefixEnd_7374501 := by exact prefixLift 7374501
  have htrace : WordTrace (prefixWord ++ tailWord_7374501) baseStart_7374501 baseEnd_7374501 := by
    simpa [prefixWord, tailWord_7374501, baseEnd_7374501] using wordTrace_append hprefix tailTrace_7374501
  have hstable : (prefixWord ++ tailWord_7374501).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7374501).length < 2 ^ (prefixWord ++ tailWord_7374501).sum := by decide
  have hdescent : baseEnd_7374501 < baseStart_7374501 := by decide
  rcases family_descends (prefixWord ++ tailWord_7374501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7374509 : List Nat := [1, 5, 2, 1, 1, 1, 5, 2, 1, 1, 3]
def baseStart_7374509 : Nat := 118140960795 + 7374509 * 2 ^ 59
def prefixEnd_7374509 : Nat := 4983230072969 + 3 ^ 40 * 7374509 * 2
def baseEnd_7374509 : Nat := 3786667707907392933322757

theorem tailTrace_7374509 : CollatzResearch.WordTrace tailWord_7374509 prefixEnd_7374509 3786667707907392933322757 := by
  unfold tailWord_7374509
  simp only [CollatzResearch.WordTrace]
  refine ⟨268970440040420833711110581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179313626693613889140740387 268970440040420833711110581)
  ·
    refine ⟨25215978753789453160416617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 268970440040420833711110581 25215978753789453160416617)
    ·
      refine ⟨18911984065342089870312463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25215978753789453160416617 18911984065342089870312463)
      ·
        refine ⟨28367976098013134805468695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18911984065342089870312463 28367976098013134805468695)
        ·
          refine ⟨42551964147019702208203043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28367976098013134805468695 42551964147019702208203043)
          ·
            refine ⟨63827946220529553312304565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42551964147019702208203043 63827946220529553312304565)
            ·
              refine ⟨5983869958174645623028553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 63827946220529553312304565 5983869958174645623028553)
              ·
                refine ⟨4487902468630984217271415, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5983869958174645623028553 4487902468630984217271415)
                ·
                  refine ⟨6731853702946476325907123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4487902468630984217271415 6731853702946476325907123)
                  ·
                    refine ⟨10097780554419714488860685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6731853702946476325907123 10097780554419714488860685)
                    ·
                      refine ⟨3786667707907392933322757, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10097780554419714488860685 3786667707907392933322757)
                      ·
                        rfl

theorem cell23_7374509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 5, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 5, 2, 1, 1, 3].length) (baseStart_7374509 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7374509 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7374509 prefixEnd_7374509 := by exact prefixLift 7374509
  have htrace : WordTrace (prefixWord ++ tailWord_7374509) baseStart_7374509 baseEnd_7374509 := by
    simpa [prefixWord, tailWord_7374509, baseEnd_7374509] using wordTrace_append hprefix tailTrace_7374509
  have hstable : (prefixWord ++ tailWord_7374509).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7374509).length < 2 ^ (prefixWord ++ tailWord_7374509).sum := by decide
  have hdescent : baseEnd_7374509 < baseStart_7374509 := by decide
  rcases family_descends (prefixWord ++ tailWord_7374509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7374531 : List Nat := [1, 1, 1, 3, 1, 1, 1, 1, 7, 3, 3]
def baseStart_7374531 : Nat := 118140960795 + 7374531 * 2 ^ 59
def prefixEnd_7374531 : Nat := 4983230072969 + 3 ^ 40 * 7374531 * 2
def baseEnd_7374531 : Nat := 3786679004481791847247655

theorem tailTrace_7374531 : CollatzResearch.WordTrace tailWord_7374531 prefixEnd_7374531 3786679004481791847247655 := by
  unfold tailWord_7374531
  simp only [CollatzResearch.WordTrace]
  refine ⟨268971242446341131468411447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179314161630894087645607631 268971242446341131468411447)
  ·
    refine ⟨403456863669511697202617171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 268971242446341131468411447 403456863669511697202617171)
    ·
      refine ⟨605185295504267545803925757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 403456863669511697202617171 605185295504267545803925757)
      ·
        refine ⟨226944485814100329676472159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 605185295504267545803925757 226944485814100329676472159)
        ·
          refine ⟨340416728721150494514708239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 226944485814100329676472159 340416728721150494514708239)
          ·
            refine ⟨510625093081725741772062359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 340416728721150494514708239 510625093081725741772062359)
            ·
              refine ⟨765937639622588612658093539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 510625093081725741772062359 765937639622588612658093539)
              ·
                refine ⟨1148906459433882918987140309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 765937639622588612658093539 1148906459433882918987140309)
                ·
                  refine ⟨26927495142981630913761101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1148906459433882918987140309 26927495142981630913761101)
                  ·
                    refine ⟨10097810678618111592660413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 26927495142981630913761101 10097810678618111592660413)
                    ·
                      refine ⟨3786679004481791847247655, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10097810678618111592660413 3786679004481791847247655)
                      ·
                        rfl

theorem cell23_7374531_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 1, 7, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 1, 7, 3, 3].length) (baseStart_7374531 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7374531 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7374531 prefixEnd_7374531 := by exact prefixLift 7374531
  have htrace : WordTrace (prefixWord ++ tailWord_7374531) baseStart_7374531 baseEnd_7374531 := by
    simpa [prefixWord, tailWord_7374531, baseEnd_7374531] using wordTrace_append hprefix tailTrace_7374531
  have hstable : (prefixWord ++ tailWord_7374531).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7374531).length < 2 ^ (prefixWord ++ tailWord_7374531).sum := by decide
  have hdescent : baseEnd_7374531 < baseStart_7374531 := by decide
  rcases family_descends (prefixWord ++ tailWord_7374531) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7374571 : List Nat := [1, 1, 1, 1, 2, 4, 3, 1, 2, 3, 4]
def baseStart_7374571 : Nat := 118140960795 + 7374571 * 2 ^ 59
def prefixEnd_7374571 : Nat := 4983230072969 + 3 ^ 40 * 7374571 * 2
def baseEnd_7374571 : Nat := 3786699543707971690747471

theorem tailTrace_7374571 : CollatzResearch.WordTrace tailWord_7374571 prefixEnd_7374571 3786699543707971690747471 := by
  unfold tailWord_7374571
  simp only [CollatzResearch.WordTrace]
  refine ⟨268972701366196218299867567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179315134244130812199911711 268972701366196218299867567)
  ·
    refine ⟨403459052049294327449801351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 268972701366196218299867567 403459052049294327449801351)
    ·
      refine ⟨605188578073941491174702027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 403459052049294327449801351 605188578073941491174702027)
      ·
        refine ⟨907782867110912236762053041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 605188578073941491174702027 907782867110912236762053041)
        ·
          refine ⟨680837150333184177571539781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 907782867110912236762053041 680837150333184177571539781)
          ·
            refine ⟨127656965687472033294663709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 680837150333184177571539781 127656965687472033294663709)
            ·
              refine ⟨47871362132802012485498891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 127656965687472033294663709 47871362132802012485498891)
              ·
                refine ⟨71807043199203018728248337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47871362132802012485498891 71807043199203018728248337)
                ·
                  refine ⟨53855282399402264046186253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 71807043199203018728248337 53855282399402264046186253)
                  ·
                    refine ⟨20195730899775849017319845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 53855282399402264046186253 20195730899775849017319845)
                    ·
                      refine ⟨3786699543707971690747471, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20195730899775849017319845 3786699543707971690747471)
                      ·
                        rfl

theorem cell23_7374571_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 3, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 3, 1, 2, 3, 4].length) (baseStart_7374571 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7374571 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7374571 prefixEnd_7374571 := by exact prefixLift 7374571
  have htrace : WordTrace (prefixWord ++ tailWord_7374571) baseStart_7374571 baseEnd_7374571 := by
    simpa [prefixWord, tailWord_7374571, baseEnd_7374571] using wordTrace_append hprefix tailTrace_7374571
  have hstable : (prefixWord ++ tailWord_7374571).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7374571).length < 2 ^ (prefixWord ++ tailWord_7374571).sum := by decide
  have hdescent : baseEnd_7374571 < baseStart_7374571 := by decide
  rcases family_descends (prefixWord ++ tailWord_7374571) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7374582 : List Nat := [5, 1, 1, 1, 1, 3, 2, 3, 2, 1, 3]
def baseStart_7374582 : Nat := 118140960795 + 7374582 * 2 ^ 59
def prefixEnd_7374582 : Nat := 4983230072969 + 3 ^ 40 * 7374582 * 2
def baseEnd_7374582 : Nat := 3786705191995171147709921

theorem tailTrace_7374582 : CollatzResearch.WordTrace tailWord_7374582 prefixEnd_7374582 3786705191995171147709921 := by
  unfold tailWord_7374582
  simp only [CollatzResearch.WordTrace]
  refine ⟨16810818910572272948657375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 179315401712770911452345333 16810818910572272948657375)
  ·
    refine ⟨25216228365858409422986063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16810818910572272948657375 25216228365858409422986063)
    ·
      refine ⟨37824342548787614134479095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25216228365858409422986063 37824342548787614134479095)
      ·
        refine ⟨56736513823181421201718643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37824342548787614134479095 56736513823181421201718643)
        ·
          refine ⟨85104770734772131802577965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56736513823181421201718643 85104770734772131802577965)
          ·
            refine ⟨31914289025539549425966737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 85104770734772131802577965 31914289025539549425966737)
            ·
              refine ⟨23935716769154662069475053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31914289025539549425966737 23935716769154662069475053)
              ·
                refine ⟨8975893788432998276053145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23935716769154662069475053 8975893788432998276053145)
                ·
                  refine ⟨6731920341324748707039859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8975893788432998276053145 6731920341324748707039859)
                  ·
                    refine ⟨10097880511987123060559789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6731920341324748707039859 10097880511987123060559789)
                    ·
                      refine ⟨3786705191995171147709921, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10097880511987123060559789 3786705191995171147709921)
                      ·
                        rfl

theorem cell23_7374582_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 3, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 3, 2, 3, 2, 1, 3].length) (baseStart_7374582 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7374582 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7374582 prefixEnd_7374582 := by exact prefixLift 7374582
  have htrace : WordTrace (prefixWord ++ tailWord_7374582) baseStart_7374582 baseEnd_7374582 := by
    simpa [prefixWord, tailWord_7374582, baseEnd_7374582] using wordTrace_append hprefix tailTrace_7374582
  have hstable : (prefixWord ++ tailWord_7374582).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7374582).length < 2 ^ (prefixWord ++ tailWord_7374582).sum := by decide
  have hdescent : baseEnd_7374582 < baseStart_7374582 := by decide
  rcases family_descends (prefixWord ++ tailWord_7374582) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7374591 : List Nat := [1, 1, 2, 2, 1, 3, 2, 1, 4, 1, 5]
def baseStart_7374591 : Nat := 118140960795 + 7374591 * 2 ^ 59
def prefixEnd_7374591 : Nat := 4983230072969 + 3 ^ 40 * 7374591 * 2
def baseEnd_7374591 : Nat := 3786709813321061612497379

theorem tailTrace_7374591 : CollatzResearch.WordTrace tailWord_7374591 prefixEnd_7374591 3786709813321061612497379 := by
  unfold tailWord_7374591
  simp only [CollatzResearch.WordTrace]
  refine ⟨268973430826123761715595627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179315620550749174477063751 268973430826123761715595627)
  ·
    refine ⟨403460146239185642573393441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 268973430826123761715595627 403460146239185642573393441)
    ·
      refine ⟨302595109679389231930045081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 403460146239185642573393441 302595109679389231930045081)
      ·
        refine ⟨226946332259541923947533811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 302595109679389231930045081 226946332259541923947533811)
        ·
          refine ⟨340419498389312885921300717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 226946332259541923947533811 340419498389312885921300717)
          ·
            refine ⟨127657311895992332220487769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 340419498389312885921300717 127657311895992332220487769)
            ·
              refine ⟨95742983921994249165365827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 127657311895992332220487769 95742983921994249165365827)
              ·
                refine ⟨143614475882991373748048741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 95742983921994249165365827 143614475882991373748048741)
                ·
                  refine ⟨26927714228060882577759139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 143614475882991373748048741 26927714228060882577759139)
                  ·
                    refine ⟨40391571342091323866638709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 26927714228060882577759139 40391571342091323866638709)
                    ·
                      refine ⟨3786709813321061612497379, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 40391571342091323866638709 3786709813321061612497379)
                      ·
                        rfl

theorem cell23_7374591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 2, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 2, 1, 4, 1, 5].length) (baseStart_7374591 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7374591 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7374591 prefixEnd_7374591 := by exact prefixLift 7374591
  have htrace : WordTrace (prefixWord ++ tailWord_7374591) baseStart_7374591 baseEnd_7374591 := by
    simpa [prefixWord, tailWord_7374591, baseEnd_7374591] using wordTrace_append hprefix tailTrace_7374591
  have hstable : (prefixWord ++ tailWord_7374591).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7374591).length < 2 ^ (prefixWord ++ tailWord_7374591).sum := by decide
  have hdescent : baseEnd_7374591 < baseStart_7374591 := by decide
  rcases family_descends (prefixWord ++ tailWord_7374591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7374601 : List Nat := [1, 2, 1, 1, 3, 2, 1, 1, 3, 4, 4]
def baseStart_7374601 : Nat := 118140960795 + 7374601 * 2 ^ 59
def prefixEnd_7374601 : Nat := 4983230072969 + 3 ^ 40 * 7374601 * 2
def baseEnd_7374601 : Nat := 3786714948127606573372333

theorem tailTrace_7374601 : CollatzResearch.WordTrace tailWord_7374601 prefixEnd_7374601 3786714948127606573372333 := by
  unfold tailWord_7374601
  simp only [CollatzResearch.WordTrace]
  refine ⟨268973795556087533423459657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179315863704058355615639771 268973795556087533423459657)
  ·
    refine ⟨201730346667065650067594743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 268973795556087533423459657 201730346667065650067594743)
    ·
      refine ⟨302595520000598475101392115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 201730346667065650067594743 302595520000598475101392115)
      ·
        refine ⟨453893280000897712652088173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 302595520000598475101392115 453893280000897712652088173)
        ·
          refine ⟨170209980000336642244533065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 453893280000897712652088173 170209980000336642244533065)
          ·
            refine ⟨127657485000252481683399799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 170209980000336642244533065 127657485000252481683399799)
            ·
              refine ⟨191486227500378722525099699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 127657485000252481683399799 191486227500378722525099699)
              ·
                refine ⟨287229341250568083787649549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 191486227500378722525099699 287229341250568083787649549)
                ·
                  refine ⟨107711002968963031420368581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 287229341250568083787649549 107711002968963031420368581)
                  ·
                    refine ⟨20195813056680568391319109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 107711002968963031420368581 20195813056680568391319109)
                    ·
                      refine ⟨3786714948127606573372333, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20195813056680568391319109 3786714948127606573372333)
                      ·
                        rfl

theorem cell23_7374601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 1, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 1, 1, 3, 4, 4].length) (baseStart_7374601 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7374601 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7374601 prefixEnd_7374601 := by exact prefixLift 7374601
  have htrace : WordTrace (prefixWord ++ tailWord_7374601) baseStart_7374601 baseEnd_7374601 := by
    simpa [prefixWord, tailWord_7374601, baseEnd_7374601] using wordTrace_append hprefix tailTrace_7374601
  have hstable : (prefixWord ++ tailWord_7374601).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7374601).length < 2 ^ (prefixWord ++ tailWord_7374601).sum := by decide
  have hdescent : baseEnd_7374601 < baseStart_7374601 := by decide
  rcases family_descends (prefixWord ++ tailWord_7374601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7374618 : List Nat := [3, 1, 1, 3, 2, 2, 1, 2, 2, 2, 4]
def baseStart_7374618 : Nat := 118140960795 + 7374618 * 2 ^ 59
def prefixEnd_7374618 : Nat := 4983230072969 + 3 ^ 40 * 7374618 * 2
def baseEnd_7374618 : Nat := 3786723677298733006859755

theorem tailTrace_7374618 : CollatzResearch.WordTrace tailWord_7374618 prefixEnd_7374618 3786723677298733006859755 := by
  unfold tailWord_7374618
  simp only [CollatzResearch.WordTrace]
  refine ⟨67243603899256486331707127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 179316277064683963551219005 67243603899256486331707127)
  ·
    refine ⟨100865405848884729497560691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67243603899256486331707127 100865405848884729497560691)
    ·
      refine ⟨151298108773327094246341037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100865405848884729497560691 151298108773327094246341037)
      ·
        refine ⟨56736790789997660342377889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 151298108773327094246341037 56736790789997660342377889)
        ·
          refine ⟨42552593092498245256783417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56736790789997660342377889 42552593092498245256783417)
          ·
            refine ⟨31914444819373683942587563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42552593092498245256783417 31914444819373683942587563)
            ·
              refine ⟨47871667229060525913881345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31914444819373683942587563 47871667229060525913881345)
              ·
                refine ⟨35903750421795394435411009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47871667229060525913881345 35903750421795394435411009)
                ·
                  refine ⟨26927812816346545826558257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35903750421795394435411009 26927812816346545826558257)
                  ·
                    refine ⟨20195859612259909369918693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26927812816346545826558257 20195859612259909369918693)
                    ·
                      refine ⟨3786723677298733006859755, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20195859612259909369918693 3786723677298733006859755)
                      ·
                        rfl

theorem cell23_7374618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 2, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 2, 1, 2, 2, 2, 4].length) (baseStart_7374618 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7374618 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7374618 prefixEnd_7374618 := by exact prefixLift 7374618
  have htrace : WordTrace (prefixWord ++ tailWord_7374618) baseStart_7374618 baseEnd_7374618 := by
    simpa [prefixWord, tailWord_7374618, baseEnd_7374618] using wordTrace_append hprefix tailTrace_7374618
  have hstable : (prefixWord ++ tailWord_7374618).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7374618).length < 2 ^ (prefixWord ++ tailWord_7374618).sum := by decide
  have hdescent : baseEnd_7374618 < baseStart_7374618 := by decide
  rcases family_descends (prefixWord ++ tailWord_7374618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7374628 : List Nat := [2, 3, 1, 3, 2, 1, 1, 3, 7]
def baseStart_7374628 : Nat := 118140960795 + 7374628 * 2 ^ 59
def prefixEnd_7374628 : Nat := 4983230072969 + 3 ^ 40 * 7374628 * 2
def baseEnd_7374628 : Nat := 420747645789475329748301

theorem tailTrace_7374628 : CollatzResearch.WordTrace tailWord_7374628 prefixEnd_7374628 420747645789475329748301 := by
  unfold tailWord_7374628
  simp only [CollatzResearch.WordTrace]
  refine ⟨134487390163494858517346269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 179316520217993144689795025 134487390163494858517346269)
  ·
    refine ⟨50432771311310571944004851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 134487390163494858517346269 50432771311310571944004851)
    ·
      refine ⟨75649156966965857916007277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50432771311310571944004851 75649156966965857916007277)
      ·
        refine ⟨28368433862612196718502729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 75649156966965857916007277 28368433862612196718502729)
        ·
          refine ⟨21276325396959147538877047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28368433862612196718502729 21276325396959147538877047)
          ·
            refine ⟨31914488095438721308315571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21276325396959147538877047 31914488095438721308315571)
            ·
              refine ⟨47871732143158081962473357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31914488095438721308315571 47871732143158081962473357)
              ·
                refine ⟨17951899553684280735927509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 47871732143158081962473357 17951899553684280735927509)
                ·
                  refine ⟨420747645789475329748301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17951899553684280735927509 420747645789475329748301)
                  ·
                    rfl

theorem cell23_7374628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 1, 1, 3, 7].length) (baseStart_7374628 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7374628 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7374628 prefixEnd_7374628 := by exact prefixLift 7374628
  have htrace : WordTrace (prefixWord ++ tailWord_7374628) baseStart_7374628 baseEnd_7374628 := by
    simpa [prefixWord, tailWord_7374628, baseEnd_7374628] using wordTrace_append hprefix tailTrace_7374628
  have hstable : (prefixWord ++ tailWord_7374628).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7374628).length < 2 ^ (prefixWord ++ tailWord_7374628).sum := by decide
  have hdescent : baseEnd_7374628 < baseStart_7374628 := by decide
  rcases family_descends (prefixWord ++ tailWord_7374628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7374695 : List Nat := [1, 1, 5, 1, 2, 1, 2, 1, 1, 6, 2]
def baseStart_7374695 : Nat := 118140960795 + 7374695 * 2 ^ 59
def prefixEnd_7374695 : Nat := 4983230072969 + 3 ^ 40 * 7374695 * 2
def baseEnd_7374695 : Nat := 3786763215309129205596901

theorem tailTrace_7374695 : CollatzResearch.WordTrace tailWord_7374695 prefixEnd_7374695 3786763215309129205596901 := by
  unfold tailWord_7374695
  simp only [CollatzResearch.WordTrace]
  refine ⟨268977224017746987477381539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179318149345164658318254359 268977224017746987477381539)
  ·
    refine ⟨403465836026620481216072309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 268977224017746987477381539 403465836026620481216072309)
    ·
      refine ⟨37824922127495670114006779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 403465836026620481216072309 37824922127495670114006779)
      ·
        refine ⟨56737383191243505171010169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37824922127495670114006779 56737383191243505171010169)
        ·
          refine ⟨42553037393432628878257627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56737383191243505171010169 42553037393432628878257627)
          ·
            refine ⟨63829556090148943317386441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42553037393432628878257627 63829556090148943317386441)
            ·
              refine ⟨47872167067611707488039831, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 63829556090148943317386441 47872167067611707488039831)
              ·
                refine ⟨71808250601417561232059747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47872167067611707488039831 71808250601417561232059747)
                ·
                  refine ⟨107712375902126341848089621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 71808250601417561232059747 107712375902126341848089621)
                  ·
                    refine ⟨5049017620412172274129201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 107712375902126341848089621 5049017620412172274129201)
                    ·
                      refine ⟨3786763215309129205596901, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5049017620412172274129201 3786763215309129205596901)
                      ·
                        rfl

theorem cell23_7374695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 2, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 2, 1, 1, 6, 2].length) (baseStart_7374695 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7374695 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7374695 prefixEnd_7374695 := by exact prefixLift 7374695
  have htrace : WordTrace (prefixWord ++ tailWord_7374695) baseStart_7374695 baseEnd_7374695 := by
    simpa [prefixWord, tailWord_7374695, baseEnd_7374695] using wordTrace_append hprefix tailTrace_7374695
  have hstable : (prefixWord ++ tailWord_7374695).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7374695).length < 2 ^ (prefixWord ++ tailWord_7374695).sum := by decide
  have hdescent : baseEnd_7374695 < baseStart_7374695 := by decide
  rcases family_descends (prefixWord ++ tailWord_7374695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7374755 : List Nat := [1, 1, 1, 4, 1, 2, 1, 4, 1, 5, 2]
def baseStart_7374755 : Nat := 118140960795 + 7374755 * 2 ^ 59
def prefixEnd_7374755 : Nat := 4983230072969 + 3 ^ 40 * 7374755 * 2
def baseEnd_7374755 : Nat := 3786794024148398970846625

theorem tailTrace_7374755 : CollatzResearch.WordTrace tailWord_7374755 prefixEnd_7374755 3786794024148398970846625 := by
  unfold tailWord_7374755
  simp only [CollatzResearch.WordTrace]
  refine ⟨268979412397529617724565719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179319608265019745149710479 268979412397529617724565719)
  ·
    refine ⟨403469118596294426586848579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 268979412397529617724565719 403469118596294426586848579)
    ·
      refine ⟨605203677894441639880272869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 403469118596294426586848579 605203677894441639880272869)
      ·
        refine ⟨113475689605207807477551163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 605203677894441639880272869 113475689605207807477551163)
        ·
          refine ⟨170213534407811711216326745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 113475689605207807477551163 170213534407811711216326745)
          ·
            refine ⟨127660150805858783412245059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 170213534407811711216326745 127660150805858783412245059)
            ·
              refine ⟨191490226208788175118367589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 127660150805858783412245059 191490226208788175118367589)
              ·
                refine ⟨35904417414147782834693923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 191490226208788175118367589 35904417414147782834693923)
                ·
                  refine ⟨53856626121221674252040885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35904417414147782834693923 53856626121221674252040885)
                  ·
                    refine ⟨5049058698864531961128833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 53856626121221674252040885 5049058698864531961128833)
                    ·
                      refine ⟨3786794024148398970846625, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5049058698864531961128833 3786794024148398970846625)
                      ·
                        rfl

theorem cell23_7374755_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 1, 4, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 1, 4, 1, 5, 2].length) (baseStart_7374755 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7374755 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7374755 prefixEnd_7374755 := by exact prefixLift 7374755
  have htrace : WordTrace (prefixWord ++ tailWord_7374755) baseStart_7374755 baseEnd_7374755 := by
    simpa [prefixWord, tailWord_7374755, baseEnd_7374755] using wordTrace_append hprefix tailTrace_7374755
  have hstable : (prefixWord ++ tailWord_7374755).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7374755).length < 2 ^ (prefixWord ++ tailWord_7374755).sum := by decide
  have hdescent : baseEnd_7374755 < baseStart_7374755 := by decide
  rcases family_descends (prefixWord ++ tailWord_7374755) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7374766 : List Nat := [4, 1, 5, 1, 1, 1, 1, 1, 1, 4, 3]
def baseStart_7374766 : Nat := 118140960795 + 7374766 * 2 ^ 59
def prefixEnd_7374766 : Nat := 4983230072969 + 3 ^ 40 * 7374766 * 2
def baseEnd_7374766 : Nat := 3786799672435598427809075

theorem tailTrace_7374766 : CollatzResearch.WordTrace tailWord_7374766 prefixEnd_7374766 3786799672435598427809075 := by
  unfold tailWord_7374766
  simp only [CollatzResearch.WordTrace]
  refine ⟨33622476700061220825402019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 179319875733659844402144101 33622476700061220825402019)
  ·
    refine ⟨50433715050091831238103029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33622476700061220825402019 50433715050091831238103029)
    ·
      refine ⟨4728160785946109178572159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 50433715050091831238103029 4728160785946109178572159)
      ·
        refine ⟨7092241178919163767858239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4728160785946109178572159 7092241178919163767858239)
        ·
          refine ⟨10638361768378745651787359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7092241178919163767858239 10638361768378745651787359)
          ·
            refine ⟨15957542652568118477681039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10638361768378745651787359 15957542652568118477681039)
            ·
              refine ⟨23936313978852177716521559, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15957542652568118477681039 23936313978852177716521559)
              ·
                refine ⟨35904470968278266574782339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23936313978852177716521559 35904470968278266574782339)
                ·
                  refine ⟨53856706452417399862173509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35904470968278266574782339 53856706452417399862173509)
                  ·
                    refine ⟨10098132459828262474157533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 53856706452417399862173509 10098132459828262474157533)
                    ·
                      refine ⟨3786799672435598427809075, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10098132459828262474157533 3786799672435598427809075)
                      ·
                        rfl

theorem cell23_7374766_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 1, 1, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 1, 1, 1, 1, 1, 4, 3].length) (baseStart_7374766 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7374766 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7374766 prefixEnd_7374766 := by exact prefixLift 7374766
  have htrace : WordTrace (prefixWord ++ tailWord_7374766) baseStart_7374766 baseEnd_7374766 := by
    simpa [prefixWord, tailWord_7374766, baseEnd_7374766] using wordTrace_append hprefix tailTrace_7374766
  have hstable : (prefixWord ++ tailWord_7374766).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7374766).length < 2 ^ (prefixWord ++ tailWord_7374766).sum := by decide
  have hdescent : baseEnd_7374766 < baseStart_7374766 := by decide
  rcases family_descends (prefixWord ++ tailWord_7374766) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7374778 : List Nat := [3, 1, 1, 1, 2, 1, 2, 3, 3, 6]
def baseStart_7374778 : Nat := 118140960795 + 7374778 * 2 ^ 59
def prefixEnd_7374778 : Nat := 4983230072969 + 3 ^ 40 * 7374778 * 2
def baseEnd_7374778 : Nat := 1262268611401150793619673

theorem tailTrace_7374778 : CollatzResearch.WordTrace tailWord_7374778 prefixEnd_7374778 1262268611401150793619673 := by
  unfold tailWord_7374778
  simp only [CollatzResearch.WordTrace]
  refine ⟨67245062819111573163163247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 179320167517630861768435325 67245062819111573163163247)
  ·
    refine ⟨100867594228667359744744871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67245062819111573163163247 100867594228667359744744871)
    ·
      refine ⟨151301391343001039617117307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100867594228667359744744871 151301391343001039617117307)
      ·
        refine ⟨226952087014501559425675961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 151301391343001039617117307 226952087014501559425675961)
        ·
          refine ⟨170214065260876169569256971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 226952087014501559425675961 170214065260876169569256971)
          ·
            refine ⟨255321097891314254353885457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 170214065260876169569256971 255321097891314254353885457)
            ·
              refine ⟨191490823418485690765414093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 255321097891314254353885457 191490823418485690765414093)
              ·
                refine ⟨71809058781932134037030285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 191490823418485690765414093 71809058781932134037030285)
                ·
                  refine ⟨26928397043224550263886357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 71809058781932134037030285 26928397043224550263886357)
                  ·
                    refine ⟨1262268611401150793619673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26928397043224550263886357 1262268611401150793619673)
                    ·
                      rfl

theorem cell23_7374778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 2, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 2, 3, 3, 6].length) (baseStart_7374778 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7374778 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7374778 prefixEnd_7374778 := by exact prefixLift 7374778
  have htrace : WordTrace (prefixWord ++ tailWord_7374778) baseStart_7374778 baseEnd_7374778 := by
    simpa [prefixWord, tailWord_7374778, baseEnd_7374778] using wordTrace_append hprefix tailTrace_7374778
  have hstable : (prefixWord ++ tailWord_7374778).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7374778).length < 2 ^ (prefixWord ++ tailWord_7374778).sum := by decide
  have hdescent : baseEnd_7374778 < baseStart_7374778 := by decide
  rcases family_descends (prefixWord ++ tailWord_7374778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7374782 : List Nat := [4, 2, 1, 1, 1, 4, 1, 3, 1, 5]
def baseStart_7374782 : Nat := 118140960795 + 7374782 * 2 ^ 59
def prefixEnd_7374782 : Nat := 4983230072969 + 3 ^ 40 * 7374782 * 2
def baseEnd_7374782 : Nat := 1262269296042023455069667

theorem tailTrace_7374782 : CollatzResearch.WordTrace tailWord_7374782 prefixEnd_7374782 1262269296042023455069667 := by
  unfold tailWord_7374782
  simp only [CollatzResearch.WordTrace]
  refine ⟨33622549646053975166974825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 179320264778954534223865733 33622549646053975166974825)
  ·
    refine ⟨25216912234540481375231119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33622549646053975166974825 25216912234540481375231119)
    ·
      refine ⟨37825368351810722062846679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25216912234540481375231119 37825368351810722062846679)
      ·
        refine ⟨56738052527716083094270019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37825368351810722062846679 56738052527716083094270019)
        ·
          refine ⟨85107078791574124641405029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56738052527716083094270019 85107078791574124641405029)
          ·
            refine ⟨15957577273420148370263443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 85107078791574124641405029 15957577273420148370263443)
            ·
              refine ⟨23936365910130222555395165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15957577273420148370263443 23936365910130222555395165)
              ·
                refine ⟨8976137216298833458273187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23936365910130222555395165 8976137216298833458273187)
                ·
                  refine ⟨13464205824448250187409781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8976137216298833458273187 13464205824448250187409781)
                  ·
                    refine ⟨1262269296042023455069667, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13464205824448250187409781 1262269296042023455069667)
                    ·
                      rfl

theorem cell23_7374782_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 4, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 4, 1, 3, 1, 5].length) (baseStart_7374782 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7374782 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7374782 prefixEnd_7374782 := by exact prefixLift 7374782
  have htrace : WordTrace (prefixWord ++ tailWord_7374782) baseStart_7374782 baseEnd_7374782 := by
    simpa [prefixWord, tailWord_7374782, baseEnd_7374782] using wordTrace_append hprefix tailTrace_7374782
  have hstable : (prefixWord ++ tailWord_7374782).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7374782).length < 2 ^ (prefixWord ++ tailWord_7374782).sum := by decide
  have hdescent : baseEnd_7374782 < baseStart_7374782 := by decide
  rcases family_descends (prefixWord ++ tailWord_7374782) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7374795 : List Nat := [1, 1, 1, 1, 3, 4, 3, 1, 4, 4]
def baseStart_7374795 : Nat := 118140960795 + 7374795 * 2 ^ 59
def prefixEnd_7374795 : Nat := 4983230072969 + 3 ^ 40 * 7374795 * 2
def baseEnd_7374795 : Nat := 1262271521124859604782147

theorem tailTrace_7374795 : CollatzResearch.WordTrace tailWord_7374795 prefixEnd_7374795 1262271521124859604782147 := by
  unfold tailWord_7374795
  simp only [CollatzResearch.WordTrace]
  refine ⟨268980871317384704556021839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179320580878256469704014559 268980871317384704556021839)
  ·
    refine ⟨403471306976077056834032759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 268980871317384704556021839 403471306976077056834032759)
    ·
      refine ⟨605206960464115585251049139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 403471306976077056834032759 605206960464115585251049139)
      ·
        refine ⟨907810440696173377876573709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 605206960464115585251049139 907810440696173377876573709)
        ·
          refine ⟨340428915261065016703715141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 907810440696173377876573709 340428915261065016703715141)
          ·
            refine ⟨63830421611449690631946589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 340428915261065016703715141 63830421611449690631946589)
            ·
              refine ⟨23936408104293633986979971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 63830421611449690631946589 23936408104293633986979971)
              ·
                refine ⟨35904612156440450980469957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23936408104293633986979971 35904612156440450980469957)
                ·
                  refine ⟨6732114779332584558838117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 35904612156440450980469957 6732114779332584558838117)
                  ·
                    refine ⟨1262271521124859604782147, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6732114779332584558838117 1262271521124859604782147)
                    ·
                      rfl

theorem cell23_7374795_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 3, 1, 4, 4].length) (baseStart_7374795 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7374795 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7374795 prefixEnd_7374795 := by exact prefixLift 7374795
  have htrace : WordTrace (prefixWord ++ tailWord_7374795) baseStart_7374795 baseEnd_7374795 := by
    simpa [prefixWord, tailWord_7374795, baseEnd_7374795] using wordTrace_append hprefix tailTrace_7374795
  have hstable : (prefixWord ++ tailWord_7374795).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7374795).length < 2 ^ (prefixWord ++ tailWord_7374795).sum := by decide
  have hdescent : baseEnd_7374795 < baseStart_7374795 := by decide
  rcases family_descends (prefixWord ++ tailWord_7374795) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7374805 : List Nat := [1, 3, 2, 3, 2, 1, 1, 1, 3, 1, 5]
def baseStart_7374805 : Nat := 118140960795 + 7374805 * 2 ^ 59
def prefixEnd_7374805 : Nat := 4983230072969 + 3 ^ 40 * 7374805 * 2
def baseEnd_7374805 : Nat := 3786819698181123775221395

theorem tailTrace_7374805 : CollatzResearch.WordTrace tailWord_7374805 prefixEnd_7374805 3786819698181123775221395 := by
  unfold tailWord_7374805
  simp only [CollatzResearch.WordTrace]
  refine ⟨268981236047348476263885869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179320824031565650842590579 268981236047348476263885869)
  ·
    refine ⟨100867963517755678598957201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 268981236047348476263885869 100867963517755678598957201)
    ·
      refine ⟨75650972638316758949217901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 100867963517755678598957201 75650972638316758949217901)
      ·
        refine ⟨28369114739368784605956713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 75650972638316758949217901 28369114739368784605956713)
        ·
          refine ⟨21276836054526588454467535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28369114739368784605956713 21276836054526588454467535)
          ·
            refine ⟨31915254081789882681701303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21276836054526588454467535 31915254081789882681701303)
            ·
              refine ⟨47872881122684824022551955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31915254081789882681701303 47872881122684824022551955)
              ·
                refine ⟨71809321684027236033827933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47872881122684824022551955 71809321684027236033827933)
                ·
                  refine ⟨26928495631510213512685475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 71809321684027236033827933 26928495631510213512685475)
                  ·
                    refine ⟨40392743447265320269028213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 26928495631510213512685475 40392743447265320269028213)
                    ·
                      refine ⟨3786819698181123775221395, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 40392743447265320269028213 3786819698181123775221395)
                      ·
                        rfl

theorem cell23_7374805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 1, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 1, 1, 1, 3, 1, 5].length) (baseStart_7374805 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7374805 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7374805 prefixEnd_7374805 := by exact prefixLift 7374805
  have htrace : WordTrace (prefixWord ++ tailWord_7374805) baseStart_7374805 baseEnd_7374805 := by
    simpa [prefixWord, tailWord_7374805, baseEnd_7374805] using wordTrace_append hprefix tailTrace_7374805
  have hstable : (prefixWord ++ tailWord_7374805).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7374805).length < 2 ^ (prefixWord ++ tailWord_7374805).sum := by decide
  have hdescent : baseEnd_7374805 < baseStart_7374805 := by decide
  rcases family_descends (prefixWord ++ tailWord_7374805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7374808 : List Nat := [2, 1, 2, 2, 2, 2, 2, 10]
def baseStart_7374808 : Nat := 118140960795 + 7374808 * 2 ^ 59
def prefixEnd_7374808 : Nat := 4983230072969 + 3 ^ 40 * 7374808 * 2
def baseEnd_7374808 : Nat := 140252638467521750499403

theorem tailTrace_7374808 : CollatzResearch.WordTrace tailWord_7374808 prefixEnd_7374808 140252638467521750499403 := by
  unfold tailWord_7374808
  simp only [CollatzResearch.WordTrace]
  refine ⟨134490672733168803888122539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 179320896977558405184163385 134490672733168803888122539)
  ·
    refine ⟨201736009099753205832183809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134490672733168803888122539 201736009099753205832183809)
    ·
      refine ⟨151302006824814904374137857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 201736009099753205832183809 151302006824814904374137857)
      ·
        refine ⟨113476505118611178280603393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 151302006824814904374137857 113476505118611178280603393)
        ·
          refine ⟨85107378838958383710452545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 113476505118611178280603393 85107378838958383710452545)
          ·
            refine ⟨63830534129218787782839409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 85107378838958383710452545 63830534129218787782839409)
            ·
              refine ⟨47872900596914090837129557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 63830534129218787782839409 47872900596914090837129557)
              ·
                refine ⟨140252638467521750499403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 47872900596914090837129557 140252638467521750499403)
                ·
                  rfl

theorem cell23_7374808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 2, 10].length) (baseStart_7374808 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7374808 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7374808 prefixEnd_7374808 := by exact prefixLift 7374808
  have htrace : WordTrace (prefixWord ++ tailWord_7374808) baseStart_7374808 baseEnd_7374808 := by
    simpa [prefixWord, tailWord_7374808, baseEnd_7374808] using wordTrace_append hprefix tailTrace_7374808
  have hstable : (prefixWord ++ tailWord_7374808).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7374808).length < 2 ^ (prefixWord ++ tailWord_7374808).sum := by decide
  have hdescent : baseEnd_7374808 < baseStart_7374808 := by decide
  rcases family_descends (prefixWord ++ tailWord_7374808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7374815 : List Nat := [1, 1, 2, 3, 4, 2, 1, 1, 1, 1, 6]
def baseStart_7374815 : Nat := 118140960795 + 7374815 * 2 ^ 59
def prefixEnd_7374815 : Nat := 4983230072969 + 3 ^ 40 * 7374815 * 2
def baseEnd_7374815 : Nat := 3786824832987668736096349

theorem tailTrace_7374815 : CollatzResearch.WordTrace tailWord_7374815 prefixEnd_7374815 3786824832987668736096349 := by
  unfold tailWord_7374815
  simp only [CollatzResearch.WordTrace]
  refine ⟨268981600777312247971749899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179321067184874831981166599 268981600777312247971749899)
  ·
    refine ⟨403472401165968371957624849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 268981600777312247971749899 403472401165968371957624849)
    ·
      refine ⟨302604300874476278968218637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 403472401165968371957624849 302604300874476278968218637)
      ·
        refine ⟨113476612827928604613081989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 302604300874476278968218637 113476612827928604613081989)
        ·
          refine ⟨21276864905236613364952873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 113476612827928604613081989 21276864905236613364952873)
          ·
            refine ⟨15957648678927460023714655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21276864905236613364952873 15957648678927460023714655)
            ·
              refine ⟨23936473018391190035571983, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15957648678927460023714655 23936473018391190035571983)
              ·
                refine ⟨35904709527586785053357975, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23936473018391190035571983 35904709527586785053357975)
                ·
                  refine ⟨53857064291380177580036963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35904709527586785053357975 53857064291380177580036963)
                  ·
                    refine ⟨80785596437070266370055445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 53857064291380177580036963 80785596437070266370055445)
                    ·
                      refine ⟨3786824832987668736096349, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 80785596437070266370055445 3786824832987668736096349)
                      ·
                        rfl

theorem cell23_7374815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 2, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 2, 1, 1, 1, 1, 6].length) (baseStart_7374815 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7374815 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7374815 prefixEnd_7374815 := by exact prefixLift 7374815
  have htrace : WordTrace (prefixWord ++ tailWord_7374815) baseStart_7374815 baseEnd_7374815 := by
    simpa [prefixWord, tailWord_7374815, baseEnd_7374815] using wordTrace_append hprefix tailTrace_7374815
  have hstable : (prefixWord ++ tailWord_7374815).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7374815).length < 2 ^ (prefixWord ++ tailWord_7374815).sum := by decide
  have hdescent : baseEnd_7374815 < baseStart_7374815 := by decide
  rcases family_descends (prefixWord ++ tailWord_7374815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7374819 : List Nat := [1, 1, 1, 6, 1, 2, 2, 2, 3, 2, 2]
def baseStart_7374819 : Nat := 118140960795 + 7374819 * 2 ^ 59
def prefixEnd_7374819 : Nat := 4983230072969 + 3 ^ 40 * 7374819 * 2
def baseEnd_7374819 : Nat := 3786826886910286720446331

theorem tailTrace_7374819 : CollatzResearch.WordTrace tailWord_7374819 prefixEnd_7374819 3786826886910286720446331 := by
  unfold tailWord_7374819
  simp only [CollatzResearch.WordTrace]
  refine ⟨268981746669297756654895511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179321164446198504436597007 268981746669297756654895511)
  ·
    refine ⟨403472620003946634982343267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 268981746669297756654895511 403472620003946634982343267)
    ·
      refine ⟨605208930005919952473514901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 403472620003946634982343267 605208930005919952473514901)
      ·
        refine ⟨28369168594027497772196011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 605208930005919952473514901 28369168594027497772196011)
        ·
          refine ⟨42553752891041246658294017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28369168594027497772196011 42553752891041246658294017)
          ·
            refine ⟨31915314668280934993720513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42553752891041246658294017 31915314668280934993720513)
            ·
              refine ⟨23936486001210701245290385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31915314668280934993720513 23936486001210701245290385)
              ·
                refine ⟨17952364500908025933967789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23936486001210701245290385 17952364500908025933967789)
                ·
                  refine ⟨6732136687840509725237921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17952364500908025933967789 6732136687840509725237921)
                  ·
                    refine ⟨5049102515880382293928441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6732136687840509725237921 5049102515880382293928441)
                    ·
                      refine ⟨3786826886910286720446331, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5049102515880382293928441 3786826886910286720446331)
                      ·
                        rfl

theorem cell23_7374819_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 2, 2, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 2, 2, 2, 3, 2, 2].length) (baseStart_7374819 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7374819 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7374819 prefixEnd_7374819 := by exact prefixLift 7374819
  have htrace : WordTrace (prefixWord ++ tailWord_7374819) baseStart_7374819 baseEnd_7374819 := by
    simpa [prefixWord, tailWord_7374819, baseEnd_7374819] using wordTrace_append hprefix tailTrace_7374819
  have hstable : (prefixWord ++ tailWord_7374819).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7374819).length < 2 ^ (prefixWord ++ tailWord_7374819).sum := by decide
  have hdescent : baseEnd_7374819 < baseStart_7374819 := by decide
  rcases family_descends (prefixWord ++ tailWord_7374819) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7374828 : List Nat := [2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 6]
def baseStart_7374828 : Nat := 118140960795 + 7374828 * 2 ^ 59
def prefixEnd_7374828 : Nat := 4983230072969 + 3 ^ 40 * 7374828 * 2
def baseEnd_7374828 : Nat := 3786831508236177185233789

theorem tailTrace_7374828 : CollatzResearch.WordTrace tailWord_7374828 prefixEnd_7374828 3786831508236177185233789 := by
  unfold tailWord_7374828
  simp only [CollatzResearch.WordTrace]
  refine ⟨134491037463132575595986569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 179321383284176767461315425 134491037463132575595986569)
  ·
    refine ⟨100868278097349431696989927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 134491037463132575595986569 100868278097349431696989927)
    ·
      refine ⟨151302417146024147545484891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100868278097349431696989927 151302417146024147545484891)
      ·
        refine ⟨226953625719036221318227337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 151302417146024147545484891 226953625719036221318227337)
        ·
          refine ⟨170215219289277165988670503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 226953625719036221318227337 170215219289277165988670503)
          ·
            refine ⟨255322828933915748983005755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 170215219289277165988670503 255322828933915748983005755)
            ·
              refine ⟨382984243400873623474508633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 255322828933915748983005755 382984243400873623474508633)
              ·
                refine ⟨287238182550655217605881475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 382984243400873623474508633 287238182550655217605881475)
                ·
                  refine ⟨430857273825982826408822213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 287238182550655217605881475 430857273825982826408822213)
                  ·
                    refine ⟨80785738842371779951654165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 430857273825982826408822213 80785738842371779951654165)
                    ·
                      refine ⟨3786831508236177185233789, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 80785738842371779951654165 3786831508236177185233789)
                      ·
                        rfl

theorem cell23_7374828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 6].length) (baseStart_7374828 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7374828 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7374828 prefixEnd_7374828 := by exact prefixLift 7374828
  have htrace : WordTrace (prefixWord ++ tailWord_7374828) baseStart_7374828 baseEnd_7374828 := by
    simpa [prefixWord, tailWord_7374828, baseEnd_7374828] using wordTrace_append hprefix tailTrace_7374828
  have hstable : (prefixWord ++ tailWord_7374828).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7374828).length < 2 ^ (prefixWord ++ tailWord_7374828).sum := by decide
  have hdescent : baseEnd_7374828 < baseStart_7374828 := by decide
  rcases family_descends (prefixWord ++ tailWord_7374828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7374835 : List Nat := [1, 1, 1, 2, 2, 2, 1, 6, 1, 3, 3]
def baseStart_7374835 : Nat := 118140960795 + 7374835 * 2 ^ 59
def prefixEnd_7374835 : Nat := 4983230072969 + 3 ^ 40 * 7374835 * 2
def baseEnd_7374835 : Nat := 3786835102600758657846257

theorem tailTrace_7374835 : CollatzResearch.WordTrace tailWord_7374835 prefixEnd_7374835 3786835102600758657846257 := by
  unfold tailWord_7374835
  simp only [CollatzResearch.WordTrace]
  refine ⟨268982330237239791387477959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179321553491493194258318639 268982330237239791387477959)
  ·
    refine ⟨403473495355859687081216939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 268982330237239791387477959 403473495355859687081216939)
    ·
      refine ⟨605210243033789530621825409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 403473495355859687081216939 605210243033789530621825409)
      ·
        refine ⟨453907682275342147966369057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 605210243033789530621825409 453907682275342147966369057)
        ·
          refine ⟨340430761706506610974776793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 453907682275342147966369057 340430761706506610974776793)
          ·
            refine ⟨255323071279879958231082595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 340430761706506610974776793 255323071279879958231082595)
            ·
              refine ⟨382984606919819937346623893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 255323071279879958231082595 382984606919819937346623893)
              ·
                refine ⟨17952403449366559563122995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 382984606919819937346623893 17952403449366559563122995)
                ·
                  refine ⟨26928605174049839344684493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17952403449366559563122995 26928605174049839344684493)
                  ·
                    refine ⟨10098226940268689754256685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 26928605174049839344684493 10098226940268689754256685)
                    ·
                      refine ⟨3786835102600758657846257, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10098226940268689754256685 3786835102600758657846257)
                      ·
                        rfl

theorem cell23_7374835_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 1, 6, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 1, 6, 1, 3, 3].length) (baseStart_7374835 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7374835 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7374835 prefixEnd_7374835 := by exact prefixLift 7374835
  have htrace : WordTrace (prefixWord ++ tailWord_7374835) baseStart_7374835 baseEnd_7374835 := by
    simpa [prefixWord, tailWord_7374835, baseEnd_7374835] using wordTrace_append hprefix tailTrace_7374835
  have hstable : (prefixWord ++ tailWord_7374835).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7374835).length < 2 ^ (prefixWord ++ tailWord_7374835).sum := by decide
  have hdescent : baseEnd_7374835 < baseStart_7374835 := by decide
  rcases family_descends (prefixWord ++ tailWord_7374835) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7374853 : List Nat := [1, 3, 1, 1, 2, 5, 3, 2, 1, 2, 2]
def baseStart_7374853 : Nat := 118140960795 + 7374853 * 2 ^ 59
def prefixEnd_7374853 : Nat := 4983230072969 + 3 ^ 40 * 7374853 * 2
def baseEnd_7374853 : Nat := 3786844345252539587421175

theorem tailTrace_7374853 : CollatzResearch.WordTrace tailWord_7374853 prefixEnd_7374853 3786844345252539587421175 := by
  unfold tailWord_7374853
  simp only [CollatzResearch.WordTrace]
  refine ⟨268982986751174580461633213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179321991167449720307755475 268982986751174580461633213)
  ·
    refine ⟨100868620031690467673112455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 268982986751174580461633213 100868620031690467673112455)
    ·
      refine ⟨151302930047535701509668683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100868620031690467673112455 151302930047535701509668683)
      ·
        refine ⟨226954395071303552264503025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 151302930047535701509668683 226954395071303552264503025)
        ·
          refine ⟨170215796303477664198377269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 226954395071303552264503025 170215796303477664198377269)
          ·
            refine ⟨15957730903451031018597869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 170215796303477664198377269 15957730903451031018597869)
            ·
              refine ⟨5984149088794136631974201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15957730903451031018597869 5984149088794136631974201)
              ·
                refine ⟨4488111816595602473980651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5984149088794136631974201 4488111816595602473980651)
                ·
                  refine ⟨6732167724893403710970977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4488111816595602473980651 6732167724893403710970977)
                  ·
                    refine ⟨5049125793670052783228233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6732167724893403710970977 5049125793670052783228233)
                    ·
                      refine ⟨3786844345252539587421175, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5049125793670052783228233 3786844345252539587421175)
                      ·
                        rfl

theorem cell23_7374853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 5, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 5, 3, 2, 1, 2, 2].length) (baseStart_7374853 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7374853 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7374853 prefixEnd_7374853 := by exact prefixLift 7374853
  have htrace : WordTrace (prefixWord ++ tailWord_7374853) baseStart_7374853 baseEnd_7374853 := by
    simpa [prefixWord, tailWord_7374853, baseEnd_7374853] using wordTrace_append hprefix tailTrace_7374853
  have hstable : (prefixWord ++ tailWord_7374853).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7374853).length < 2 ^ (prefixWord ++ tailWord_7374853).sum := by decide
  have hdescent : baseEnd_7374853 < baseStart_7374853 := by decide
  rcases family_descends (prefixWord ++ tailWord_7374853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7374896 : List Nat := [2, 1, 1, 1, 2, 6, 3, 1, 1, 3, 2]
def baseStart_7374896 : Nat := 118140960795 + 7374896 * 2 ^ 59
def prefixEnd_7374896 : Nat := 4983230072969 + 3 ^ 40 * 7374896 * 2
def baseEnd_7374896 : Nat := 3786866424920682919183477

theorem tailTrace_7374896 : CollatzResearch.WordTrace tailWord_7374896 prefixEnd_7374896 3786866424920682919183477 := by
  unfold tailWord_7374896
  simp only [CollatzResearch.WordTrace]
  refine ⟨134492277545009399402724271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 179323036726679199203632361 134492277545009399402724271)
  ·
    refine ⟨201738416317514099104086407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134492277545009399402724271 201738416317514099104086407)
    ·
      refine ⟨302607624476271148656129611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 201738416317514099104086407 302607624476271148656129611)
      ·
        refine ⟨453911436714406722984194417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 302607624476271148656129611 453911436714406722984194417)
        ·
          refine ⟨340433577535805042238145813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 453911436714406722984194417 340433577535805042238145813)
          ·
            refine ⟨15957823946990861354913085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 340433577535805042238145813 15957823946990861354913085)
            ·
              refine ⟨5984183980121573008092407, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15957823946990861354913085 5984183980121573008092407)
              ·
                refine ⟨8976275970182359512138611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5984183980121573008092407 8976275970182359512138611)
                ·
                  refine ⟨13464413955273539268207917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8976275970182359512138611 13464413955273539268207917)
                  ·
                    refine ⟨5049155233227577225577969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13464413955273539268207917 5049155233227577225577969)
                    ·
                      refine ⟨3786866424920682919183477, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5049155233227577225577969 3786866424920682919183477)
                      ·
                        rfl

theorem cell23_7374896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 6, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 6, 3, 1, 1, 3, 2].length) (baseStart_7374896 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7374896 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7374896 prefixEnd_7374896 := by exact prefixLift 7374896
  have htrace : WordTrace (prefixWord ++ tailWord_7374896) baseStart_7374896 baseEnd_7374896 := by
    simpa [prefixWord, tailWord_7374896, baseEnd_7374896] using wordTrace_append hprefix tailTrace_7374896
  have hstable : (prefixWord ++ tailWord_7374896).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7374896).length < 2 ^ (prefixWord ++ tailWord_7374896).sum := by decide
  have hdescent : baseEnd_7374896 < baseStart_7374896 := by decide
  rcases family_descends (prefixWord ++ tailWord_7374896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7374902 : List Nat := [5, 1, 2, 1, 1, 1, 2, 2, 2, 6]
def baseStart_7374902 : Nat := 118140960795 + 7374902 * 2 ^ 59
def prefixEnd_7374902 : Nat := 4983230072969 + 3 ^ 40 * 7374902 * 2
def baseEnd_7374902 : Nat := 1262289835268203298569483

theorem tailTrace_7374902 : CollatzResearch.WordTrace tailWord_7374902 prefixEnd_7374902 1262289835268203298569483 := by
  unfold tailWord_7374902
  simp only [CollatzResearch.WordTrace]
  refine ⟨16811548370499816364385435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 179323182618664707886777973 16811548370499816364385435)
  ·
    refine ⟨25217322555749724546578153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16811548370499816364385435 25217322555749724546578153)
    ·
      refine ⟨18912991916812293409933615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25217322555749724546578153 18912991916812293409933615)
      ·
        refine ⟨28369487875218440114900423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18912991916812293409933615 28369487875218440114900423)
        ·
          refine ⟨42554231812827660172350635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28369487875218440114900423 42554231812827660172350635)
          ·
            refine ⟨63831347719241490258525953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42554231812827660172350635 63831347719241490258525953)
            ·
              refine ⟨47873510789431117693894465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 63831347719241490258525953 47873510789431117693894465)
              ·
                refine ⟨35905133092073338270420849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47873510789431117693894465 35905133092073338270420849)
                ·
                  refine ⟨26928849819055003702815637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35905133092073338270420849 26928849819055003702815637)
                  ·
                    refine ⟨1262289835268203298569483, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26928849819055003702815637 1262289835268203298569483)
                    ·
                      rfl

theorem cell23_7374902_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 2, 2, 2, 6].length) (baseStart_7374902 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7374902 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7374902 prefixEnd_7374902 := by exact prefixLift 7374902
  have htrace : WordTrace (prefixWord ++ tailWord_7374902) baseStart_7374902 baseEnd_7374902 := by
    simpa [prefixWord, tailWord_7374902, baseEnd_7374902] using wordTrace_append hprefix tailTrace_7374902
  have hstable : (prefixWord ++ tailWord_7374902).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7374902).length < 2 ^ (prefixWord ++ tailWord_7374902).sum := by decide
  have hdescent : baseEnd_7374902 < baseStart_7374902 := by decide
  rcases family_descends (prefixWord ++ tailWord_7374902) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7374926 : List Nat := [4, 1, 1, 1, 1, 4, 2, 3, 2, 2, 2]
def baseStart_7374926 : Nat := 118140960795 + 7374926 * 2 ^ 59
def prefixEnd_7374926 : Nat := 4983230072969 + 3 ^ 40 * 7374926 * 2
def baseEnd_7374926 : Nat := 3786881829340317801808339

theorem tailTrace_7374926 : CollatzResearch.WordTrace tailWord_7374926 prefixEnd_7374926 3786881829340317801808339 := by
  unfold tailWord_7374926
  simp only [CollatzResearch.WordTrace]
  refine ⟨33623206159988764241130079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 179323766186606742619360421 33623206159988764241130079)
  ·
    refine ⟨50434809239983146361695119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33623206159988764241130079 50434809239983146361695119)
    ·
      refine ⟨75652213859974719542542679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50434809239983146361695119 75652213859974719542542679)
      ·
        refine ⟨113478320789962079313814019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75652213859974719542542679 113478320789962079313814019)
        ·
          refine ⟨170217481184943118970721029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 113478320789962079313814019 170217481184943118970721029)
          ·
            refine ⟨31915777722176834807010193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 170217481184943118970721029 31915777722176834807010193)
            ·
              refine ⟨23936833291632626105257645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31915777722176834807010193 23936833291632626105257645)
              ·
                refine ⟨8976312484362234789471617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23936833291632626105257645 8976312484362234789471617)
                ·
                  refine ⟨6732234363271676092103713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8976312484362234789471617 6732234363271676092103713)
                  ·
                    refine ⟨5049175772453757069077785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6732234363271676092103713 5049175772453757069077785)
                    ·
                      refine ⟨3786881829340317801808339, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5049175772453757069077785 3786881829340317801808339)
                      ·
                        rfl

theorem cell23_7374926_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 4, 2, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 4, 2, 3, 2, 2, 2].length) (baseStart_7374926 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7374926 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7374926 prefixEnd_7374926 := by exact prefixLift 7374926
  have htrace : WordTrace (prefixWord ++ tailWord_7374926) baseStart_7374926 baseEnd_7374926 := by
    simpa [prefixWord, tailWord_7374926, baseEnd_7374926] using wordTrace_append hprefix tailTrace_7374926
  have hstable : (prefixWord ++ tailWord_7374926).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7374926).length < 2 ^ (prefixWord ++ tailWord_7374926).sum := by decide
  have hdescent : baseEnd_7374926 < baseStart_7374926 := by decide
  rcases family_descends (prefixWord ++ tailWord_7374926) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7374949 : List Nat := [1, 3, 1, 3, 2, 3, 2, 3, 5]
def baseStart_7374949 : Nat := 118140960795 + 7374949 * 2 ^ 59
def prefixEnd_7374949 : Nat := 4983230072969 + 3 ^ 40 * 7374949 * 2
def baseEnd_7374949 : Nat := 420765959932819023535637

theorem tailTrace_7374949 : CollatzResearch.WordTrace tailWord_7374949 prefixEnd_7374949 420765959932819023535637 := by
  unfold tailWord_7374949
  simp only [CollatzResearch.WordTrace]
  refine ⟨268986488158826788857127901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179324325439217859238085267 268986488158826788857127901)
  ·
    refine ⟨100869933059560045821422963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 268986488158826788857127901 100869933059560045821422963)
    ·
      refine ⟨151304899589340068732134445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100869933059560045821422963 151304899589340068732134445)
      ·
        refine ⟨56739337346002525774550417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 151304899589340068732134445 56739337346002525774550417)
        ·
          refine ⟨42554503009501894330912813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56739337346002525774550417 42554503009501894330912813)
          ·
            refine ⟨15957938628563210374092305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42554503009501894330912813 15957938628563210374092305)
            ·
              refine ⟨11968453971422407780569229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15957938628563210374092305 11968453971422407780569229)
              ·
                refine ⟨4488170239283402917713461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11968453971422407780569229 4488170239283402917713461)
                ·
                  refine ⟨420765959932819023535637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4488170239283402917713461 420765959932819023535637)
                  ·
                    rfl

theorem cell23_7374949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 3, 2, 3, 5].length) (baseStart_7374949 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7374949 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7374949 prefixEnd_7374949 := by exact prefixLift 7374949
  have htrace : WordTrace (prefixWord ++ tailWord_7374949) baseStart_7374949 baseEnd_7374949 := by
    simpa [prefixWord, tailWord_7374949, baseEnd_7374949] using wordTrace_append hprefix tailTrace_7374949
  have hstable : (prefixWord ++ tailWord_7374949).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7374949).length < 2 ^ (prefixWord ++ tailWord_7374949).sum := by decide
  have hdescent : baseEnd_7374949 < baseStart_7374949 := by decide
  rcases family_descends (prefixWord ++ tailWord_7374949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7374992 : List Nat := [2, 1, 1, 1, 1, 1, 5, 4, 3, 4]
def baseStart_7374992 : Nat := 118140960795 + 7374992 * 2 ^ 59
def prefixEnd_7374992 : Nat := 4983230072969 + 3 ^ 40 * 7374992 * 2
def baseEnd_7374992 : Nat := 1262305239687838181194345

theorem tailTrace_7374992 : CollatzResearch.WordTrace tailWord_7374992 prefixEnd_7374992 1262305239687838181194345 := by
  unfold tailWord_7374992
  simp only [CollatzResearch.WordTrace]
  refine ⟨134494028248835503600471615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 179325370998447338133962153 134494028248835503600471615)
  ·
    refine ⟨201741042373253255400707423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134494028248835503600471615 201741042373253255400707423)
    ·
      refine ⟨302611563559879883101061135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 201741042373253255400707423 302611563559879883101061135)
      ·
        refine ⟨453917345339819824651591703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 302611563559879883101061135 453917345339819824651591703)
        ·
          refine ⟨680876018009729736977387555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 453917345339819824651591703 680876018009729736977387555)
          ·
            refine ⟨1021314027014594605466081333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 680876018009729736977387555 1021314027014594605466081333)
            ·
              refine ⟨95748190032618244262445125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1021314027014594605466081333 95748190032618244262445125)
              ·
                refine ⟨17952785631115920799208461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 95748190032618244262445125 17952785631115920799208461)
                ·
                  refine ⟨6732294611668470299703173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17952785631115920799208461 6732294611668470299703173)
                  ·
                    refine ⟨1262305239687838181194345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6732294611668470299703173 1262305239687838181194345)
                    ·
                      rfl

theorem cell23_7374992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 5, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 5, 4, 3, 4].length) (baseStart_7374992 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7374992 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7374992 prefixEnd_7374992 := by exact prefixLift 7374992
  have htrace : WordTrace (prefixWord ++ tailWord_7374992) baseStart_7374992 baseEnd_7374992 := by
    simpa [prefixWord, tailWord_7374992, baseEnd_7374992] using wordTrace_append hprefix tailTrace_7374992
  have hstable : (prefixWord ++ tailWord_7374992).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7374992).length < 2 ^ (prefixWord ++ tailWord_7374992).sum := by decide
  have hdescent : baseEnd_7374992 < baseStart_7374992 := by decide
  rcases family_descends (prefixWord ++ tailWord_7374992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7374995 : List Nat := [1, 1, 1, 2, 1, 2, 3, 1, 1, 6, 4]
def baseStart_7374995 : Nat := 118140960795 + 7374995 * 2 ^ 59
def prefixEnd_7374995 : Nat := 4983230072969 + 3 ^ 40 * 7374995 * 2
def baseEnd_7374995 : Nat := 3786917259505478031845521

theorem tailTrace_7374995 : CollatzResearch.WordTrace tailWord_7374995 prefixEnd_7374995 3786917259505478031845521 := by
  unfold tailWord_7374995
  simp only [CollatzResearch.WordTrace]
  refine ⟨268988165916660138713302439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179325443944440092475534959 268988165916660138713302439)
  ·
    refine ⟨403482248874990208069953659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 268988165916660138713302439 403482248874990208069953659)
    ·
      refine ⟨605223373312485312104930489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 403482248874990208069953659 605223373312485312104930489)
      ·
        refine ⟨453917529984363984078697867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 605223373312485312104930489 453917529984363984078697867)
        ·
          refine ⟨680876294976545976118046801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 453917529984363984078697867 680876294976545976118046801)
          ·
            refine ⟨510657221232409482088535101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 680876294976545976118046801 510657221232409482088535101)
            ·
              refine ⟨191496457962153555783200663, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 510657221232409482088535101 191496457962153555783200663)
              ·
                refine ⟨287244686943230333674800995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 191496457962153555783200663 287244686943230333674800995)
                ·
                  refine ⟨430867030414845500512201493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 287244686943230333674800995 430867030414845500512201493)
                  ·
                    refine ⟨20196892050695882836509445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 430867030414845500512201493 20196892050695882836509445)
                    ·
                      refine ⟨3786917259505478031845521, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20196892050695882836509445 3786917259505478031845521)
                      ·
                        rfl

theorem cell23_7374995_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 3, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 3, 1, 1, 6, 4].length) (baseStart_7374995 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7374995 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7374995 prefixEnd_7374995 := by exact prefixLift 7374995
  have htrace : WordTrace (prefixWord ++ tailWord_7374995) baseStart_7374995 baseEnd_7374995 := by
    simpa [prefixWord, tailWord_7374995, baseEnd_7374995] using wordTrace_append hprefix tailTrace_7374995
  have hstable : (prefixWord ++ tailWord_7374995).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7374995).length < 2 ^ (prefixWord ++ tailWord_7374995).sum := by decide
  have hdescent : baseEnd_7374995 < baseStart_7374995 := by decide
  rcases family_descends (prefixWord ++ tailWord_7374995) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7375082 : List Nat := [3, 1, 3, 1, 1, 2, 1, 2, 3, 6]
def baseStart_7375082 : Nat := 118140960795 + 7375082 * 2 ^ 59
def prefixEnd_7375082 : Nat := 4983230072969 + 3 ^ 40 * 7375082 * 2
def baseEnd_7375082 : Nat := 1262320644107473063819207

theorem tailTrace_7375082 : CollatzResearch.WordTrace tailWord_7375082 prefixEnd_7375082 1262320644107473063819207 := by
  unfold tailWord_7375082
  simp only [CollatzResearch.WordTrace]
  refine ⟨67247834766836238142929875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 179327559378229968381146333 67247834766836238142929875)
  ·
    refine ⟨100871752150254357214394813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67247834766836238142929875 100871752150254357214394813)
    ·
      refine ⟨37826907056345383955398055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 100871752150254357214394813 37826907056345383955398055)
      ·
        refine ⟨56740360584518075933097083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37826907056345383955398055 56740360584518075933097083)
        ·
          refine ⟨85110540876777113899645625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56740360584518075933097083 85110540876777113899645625)
          ·
            refine ⟨63832905657582835424734219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 85110540876777113899645625 63832905657582835424734219)
            ·
              refine ⟨95749358486374253137101329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63832905657582835424734219 95749358486374253137101329)
              ·
                refine ⟨71812018864780689852825997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 95749358486374253137101329 71812018864780689852825997)
                ·
                  refine ⟨26929507074292758694809749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 71812018864780689852825997 26929507074292758694809749)
                  ·
                    refine ⟨1262320644107473063819207, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26929507074292758694809749 1262320644107473063819207)
                    ·
                      rfl

theorem cell23_7375082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 1, 2, 3, 6].length) (baseStart_7375082 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7375082 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7375082 prefixEnd_7375082 := by exact prefixLift 7375082
  have htrace : WordTrace (prefixWord ++ tailWord_7375082) baseStart_7375082 baseEnd_7375082 := by
    simpa [prefixWord, tailWord_7375082, baseEnd_7375082] using wordTrace_append hprefix tailTrace_7375082
  have hstable : (prefixWord ++ tailWord_7375082).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7375082).length < 2 ^ (prefixWord ++ tailWord_7375082).sum := by decide
  have hdescent : baseEnd_7375082 < baseStart_7375082 := by decide
  rcases family_descends (prefixWord ++ tailWord_7375082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7375106 : List Nat := [3, 4, 1, 1, 2, 1, 2, 1, 3, 1, 4]
def baseStart_7375106 : Nat := 118140960795 + 7375106 * 2 ^ 59
def prefixEnd_7375106 : Nat := 4983230072969 + 3 ^ 40 * 7375106 * 2
def baseEnd_7375106 : Nat := 3786974255858127097557511

theorem tailTrace_7375106 : CollatzResearch.WordTrace tailWord_7375106 prefixEnd_7375106 3786974255858127097557511 := by
  unfold tailWord_7375106
  simp only [CollatzResearch.WordTrace]
  refine ⟨67248053604814501167648293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 179328142946172003113728781 67248053604814501167648293)
  ·
    refine ⟨12609010050902718968934055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 67248053604814501167648293 12609010050902718968934055)
    ·
      refine ⟨18913515076354078453401083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12609010050902718968934055 18913515076354078453401083)
      ·
        refine ⟨28370272614531117680101625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18913515076354078453401083 28370272614531117680101625)
        ·
          refine ⟨21277704460898338260076219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28370272614531117680101625 21277704460898338260076219)
          ·
            refine ⟨31916556691347507390114329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21277704460898338260076219 31916556691347507390114329)
            ·
              refine ⟨23937417518510630542585747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31916556691347507390114329 23937417518510630542585747)
              ·
                refine ⟨35906126277765945813878621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23937417518510630542585747 35906126277765945813878621)
                ·
                  refine ⟨13464797354162229680204483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35906126277765945813878621 13464797354162229680204483)
                  ·
                    refine ⟨20197196031243344520306725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13464797354162229680204483 20197196031243344520306725)
                    ·
                      refine ⟨3786974255858127097557511, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20197196031243344520306725 3786974255858127097557511)
                      ·
                        rfl

theorem cell23_7375106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 1, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 1, 2, 1, 3, 1, 4].length) (baseStart_7375106 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7375106 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7375106 prefixEnd_7375106 := by exact prefixLift 7375106
  have htrace : WordTrace (prefixWord ++ tailWord_7375106) baseStart_7375106 baseEnd_7375106 := by
    simpa [prefixWord, tailWord_7375106, baseEnd_7375106] using wordTrace_append hprefix tailTrace_7375106
  have hstable : (prefixWord ++ tailWord_7375106).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7375106).length < 2 ^ (prefixWord ++ tailWord_7375106).sum := by decide
  have hdescent : baseEnd_7375106 < baseStart_7375106 := by decide
  rcases family_descends (prefixWord ++ tailWord_7375106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7375132 : List Nat := [2, 2, 3, 1, 1, 1, 1, 2, 2, 2, 6]
def baseStart_7375132 : Nat := 118140960795 + 7375132 * 2 ^ 59
def prefixEnd_7375132 : Nat := 4983230072969 + 3 ^ 40 * 7375132 * 2
def baseEnd_7375132 : Nat := 3786987606355143995832391

theorem tailTrace_7375132 : CollatzResearch.WordTrace tailWord_7375132 prefixEnd_7375132 3786987606355143995832391 := by
  unfold tailWord_7375132
  simp only [CollatzResearch.WordTrace]
  refine ⟨134496581358581905555519825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 179328775144775874074026433 134496581358581905555519825)
  ·
    refine ⟨100872436018936429166639869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 134496581358581905555519825 100872436018936429166639869)
    ·
      refine ⟨37827163507101160937489951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 100872436018936429166639869 37827163507101160937489951)
      ·
        refine ⟨56740745260651741406234927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37827163507101160937489951 56740745260651741406234927)
        ·
          refine ⟨85111117890977612109352391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56740745260651741406234927 85111117890977612109352391)
          ·
            refine ⟨127666676836466418164028587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85111117890977612109352391 127666676836466418164028587)
            ·
              refine ⟨191500015254699627246042881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 127666676836466418164028587 191500015254699627246042881)
              ·
                refine ⟨143625011441024720434532161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 191500015254699627246042881 143625011441024720434532161)
                ·
                  refine ⟨107718758580768540325899121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 143625011441024720434532161 107718758580768540325899121)
                  ·
                    refine ⟨80789068935576405244424341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 107718758580768540325899121 80789068935576405244424341)
                    ·
                      refine ⟨3786987606355143995832391, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 80789068935576405244424341 3786987606355143995832391)
                      ·
                        rfl

theorem cell23_7375132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 1, 2, 2, 2, 6].length) (baseStart_7375132 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7375132 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7375132 prefixEnd_7375132 := by exact prefixLift 7375132
  have htrace : WordTrace (prefixWord ++ tailWord_7375132) baseStart_7375132 baseEnd_7375132 := by
    simpa [prefixWord, tailWord_7375132, baseEnd_7375132] using wordTrace_append hprefix tailTrace_7375132
  have hstable : (prefixWord ++ tailWord_7375132).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7375132).length < 2 ^ (prefixWord ++ tailWord_7375132).sum := by decide
  have hdescent : baseEnd_7375132 < baseStart_7375132 := by decide
  rcases family_descends (prefixWord ++ tailWord_7375132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7375140 : List Nat := [2, 3, 1, 3, 1, 2, 2, 4, 1, 2, 2]
def baseStart_7375140 : Nat := 118140960795 + 7375140 * 2 ^ 59
def prefixEnd_7375140 : Nat := 4983230072969 + 3 ^ 40 * 7375140 * 2
def baseEnd_7375140 : Nat := 3786991714200379964532355

theorem tailTrace_7375140 : CollatzResearch.WordTrace tailWord_7375140 prefixEnd_7375140 3786991714200379964532355 := by
  unfold tailWord_7375140
  simp only [CollatzResearch.WordTrace]
  refine ⟨134496727250567414238665437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 179328969667423218984887249 134496727250567414238665437)
  ·
    refine ⟨50436272718962780339499539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 134496727250567414238665437 50436272718962780339499539)
    ·
      refine ⟨75654409078444170509249309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50436272718962780339499539 75654409078444170509249309)
      ·
        refine ⟨28370403404416563940968491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 75654409078444170509249309 28370403404416563940968491)
        ·
          refine ⟨42555605106624845911452737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28370403404416563940968491 42555605106624845911452737)
          ·
            refine ⟨31916703829968634433589553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42555605106624845911452737 31916703829968634433589553)
            ·
              refine ⟨23937527872476475825192165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31916703829968634433589553 23937527872476475825192165)
              ·
                refine ⟨4488286476089339217223531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23937527872476475825192165 4488286476089339217223531)
                ·
                  refine ⟨6732429714134008825835297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4488286476089339217223531 6732429714134008825835297)
                  ·
                    refine ⟨5049322285600506619376473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6732429714134008825835297 5049322285600506619376473)
                    ·
                      refine ⟨3786991714200379964532355, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5049322285600506619376473 3786991714200379964532355)
                      ·
                        rfl

theorem cell23_7375140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 2, 2, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 2, 2, 4, 1, 2, 2].length) (baseStart_7375140 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7375140 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7375140 prefixEnd_7375140 := by exact prefixLift 7375140
  have htrace : WordTrace (prefixWord ++ tailWord_7375140) baseStart_7375140 baseEnd_7375140 := by
    simpa [prefixWord, tailWord_7375140, baseEnd_7375140] using wordTrace_append hprefix tailTrace_7375140
  have hstable : (prefixWord ++ tailWord_7375140).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7375140).length < 2 ^ (prefixWord ++ tailWord_7375140).sum := by decide
  have hdescent : baseEnd_7375140 < baseStart_7375140 := by decide
  rcases family_descends (prefixWord ++ tailWord_7375140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
