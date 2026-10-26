import V185TrunkScan23Chunk1399

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_8293182 : List Nat := [4, 2, 1, 2, 3, 2, 2, 2, 1, 1, 3]
def baseStart_8293182 : Nat := 118140960795 + 8293182 * 2 ^ 59
def prefixEnd_8293182 : Nat := 4983230072969 + 3 ^ 40 * 8293182 * 2
def baseEnd_8293182 : Nat := 4258388521215277120985357

theorem tailTrace_8293182 : CollatzResearch.WordTrace tailWord_8293182 prefixEnd_8293182 4258388521215277120985357 := by
  unfold tailWord_8293182
  simp only [CollatzResearch.WordTrace]
  refine ⟨37809649630153181446039225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 201651464694150301045542533 37809649630153181446039225)
  ·
    refine ⟨28357237222614886084529419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37809649630153181446039225 28357237222614886084529419)
    ·
      refine ⟨42535855833922329126794129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28357237222614886084529419 42535855833922329126794129)
      ·
        refine ⟨31901891875441746845095597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42535855833922329126794129 31901891875441746845095597)
        ·
          refine ⟨11963209453290655066910849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31901891875441746845095597 11963209453290655066910849)
          ·
            refine ⟨8972407089967991300183137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11963209453290655066910849 8972407089967991300183137)
            ·
              refine ⟨6729305317475993475137353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8972407089967991300183137 6729305317475993475137353)
              ·
                refine ⟨5046978988106995106353015, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6729305317475993475137353 5046978988106995106353015)
                ·
                  refine ⟨7570468482160492659529523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5046978988106995106353015 7570468482160492659529523)
                  ·
                    refine ⟨11355702723240738989294285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7570468482160492659529523 11355702723240738989294285)
                    ·
                      refine ⟨4258388521215277120985357, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11355702723240738989294285 4258388521215277120985357)
                      ·
                        rfl

theorem cell23_8293182_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 3, 2, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 3, 2, 2, 2, 1, 1, 3].length) (baseStart_8293182 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8293182 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8293182 prefixEnd_8293182 := by exact prefixLift 8293182
  have htrace : WordTrace (prefixWord ++ tailWord_8293182) baseStart_8293182 baseEnd_8293182 := by
    simpa [prefixWord, tailWord_8293182, baseEnd_8293182] using wordTrace_append hprefix tailTrace_8293182
  have hstable : (prefixWord ++ tailWord_8293182).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8293182).length < 2 ^ (prefixWord ++ tailWord_8293182).sum := by decide
  have hdescent : baseEnd_8293182 < baseStart_8293182 := by decide
  rcases family_descends (prefixWord ++ tailWord_8293182) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8293187 : List Nat := [1, 1, 1, 3, 1, 4, 1, 2, 3, 3, 3]
def baseStart_8293187 : Nat := 118140960795 + 8293187 * 2 ^ 59
def prefixEnd_8293187 : Nat := 4983230072969 + 3 ^ 40 * 8293187 * 2
def baseEnd_8293187 : Nat := 4258391088618549601422833

theorem tailTrace_8293187 : CollatzResearch.WordTrace tailWord_8293187 prefixEnd_8293187 4258391088618549601422833 := by
  unfold tailWord_8293187
  simp only [CollatzResearch.WordTrace]
  refine ⟨302477379406207337422245815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201651586270804891614830543 302477379406207337422245815)
  ·
    refine ⟨453716069109311006133368723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 302477379406207337422245815 453716069109311006133368723)
    ·
      refine ⟨680574103663966509200053085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 453716069109311006133368723 680574103663966509200053085)
      ·
        refine ⟨255215288873987440950019907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 680574103663966509200053085 255215288873987440950019907)
        ·
          refine ⟨382822933310981161425029861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 255215288873987440950019907 382822933310981161425029861)
          ·
            refine ⟨71779299995808967767193099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 382822933310981161425029861 71779299995808967767193099)
            ·
              refine ⟨107668949993713451650789649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71779299995808967767193099 107668949993713451650789649)
              ·
                refine ⟨80751712495285088738092237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 107668949993713451650789649 80751712495285088738092237)
                ·
                  refine ⟨30281892185731908276784589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 80751712495285088738092237 30281892185731908276784589)
                  ·
                    refine ⟨11355709569649465603794221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 30281892185731908276784589 11355709569649465603794221)
                    ·
                      refine ⟨4258391088618549601422833, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11355709569649465603794221 4258391088618549601422833)
                      ·
                        rfl

theorem cell23_8293187_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 1, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 1, 2, 3, 3, 3].length) (baseStart_8293187 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8293187 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8293187 prefixEnd_8293187 := by exact prefixLift 8293187
  have htrace : WordTrace (prefixWord ++ tailWord_8293187) baseStart_8293187 baseEnd_8293187 := by
    simpa [prefixWord, tailWord_8293187, baseEnd_8293187] using wordTrace_append hprefix tailTrace_8293187
  have hstable : (prefixWord ++ tailWord_8293187).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8293187).length < 2 ^ (prefixWord ++ tailWord_8293187).sum := by decide
  have hdescent : baseEnd_8293187 < baseStart_8293187 := by decide
  rcases family_descends (prefixWord ++ tailWord_8293187) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8293238 : List Nat := [5, 1, 1, 3, 1, 2, 1, 1, 4, 1, 3]
def baseStart_8293238 : Nat := 118140960795 + 8293238 * 2 ^ 59
def prefixEnd_8293238 : Nat := 4983230072969 + 3 ^ 40 * 8293238 * 2
def baseEnd_8293238 : Nat := 4258417276131928901885099

theorem tailTrace_8293238 : CollatzResearch.WordTrace tailWord_8293238 prefixEnd_8293238 4258417276131928901885099 := by
  unfold tailWord_8293238
  simp only [CollatzResearch.WordTrace]
  refine ⟨18904952470563910820772023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 201652826352681715421568245 18904952470563910820772023)
  ·
    refine ⟨28357428705845866231158035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18904952470563910820772023 28357428705845866231158035)
    ·
      refine ⟨42536143058768799346737053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28357428705845866231158035 42536143058768799346737053)
      ·
        refine ⟨15951053647038299755026395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42536143058768799346737053 15951053647038299755026395)
        ·
          refine ⟨23926580470557449632539593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15951053647038299755026395 23926580470557449632539593)
          ·
            refine ⟨17944935352918087224404695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23926580470557449632539593 17944935352918087224404695)
            ·
              refine ⟨26917403029377130836607043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17944935352918087224404695 26917403029377130836607043)
              ·
                refine ⟨40376104544065696254910565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26917403029377130836607043 40376104544065696254910565)
                ·
                  refine ⟨7570519602012318047795731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 40376104544065696254910565 7570519602012318047795731)
                  ·
                    refine ⟨11355779403018477071693597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7570519602012318047795731 11355779403018477071693597)
                    ·
                      refine ⟨4258417276131928901885099, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11355779403018477071693597 4258417276131928901885099)
                      ·
                        rfl

theorem cell23_8293238_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 2, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 2, 1, 1, 4, 1, 3].length) (baseStart_8293238 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8293238 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8293238 prefixEnd_8293238 := by exact prefixLift 8293238
  have htrace : WordTrace (prefixWord ++ tailWord_8293238) baseStart_8293238 baseEnd_8293238 := by
    simpa [prefixWord, tailWord_8293238, baseEnd_8293238] using wordTrace_append hprefix tailTrace_8293238
  have hstable : (prefixWord ++ tailWord_8293238).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8293238).length < 2 ^ (prefixWord ++ tailWord_8293238).sum := by decide
  have hdescent : baseEnd_8293238 < baseStart_8293238 := by decide
  rcases family_descends (prefixWord ++ tailWord_8293238) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8293244 : List Nat := [2, 2, 2, 1, 1, 1, 1, 4, 3, 4, 2]
def baseStart_8293244 : Nat := 118140960795 + 8293244 * 2 ^ 59
def prefixEnd_8293244 : Nat := 4983230072969 + 3 ^ 40 * 8293244 * 2
def baseEnd_8293244 : Nat := 4258420357015855878410071

theorem tailTrace_8293244 : CollatzResearch.WordTrace tailWord_8293244 prefixEnd_8293244 4258420357015855878410071 := by
  unfold tailWord_8293244
  simp only [CollatzResearch.WordTrace]
  refine ⟨151239729183500418078535393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 201652972244667224104713857 151239729183500418078535393)
  ·
    refine ⟨113429796887625313558901545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 151239729183500418078535393 113429796887625313558901545)
    ·
      refine ⟨85072347665718985169176159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 113429796887625313558901545 85072347665718985169176159)
      ·
        refine ⟨127608521498578477753764239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85072347665718985169176159 127608521498578477753764239)
        ·
          refine ⟨191412782247867716630646359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 127608521498578477753764239 191412782247867716630646359)
          ·
            refine ⟨287119173371801574945969539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 191412782247867716630646359 287119173371801574945969539)
            ·
              refine ⟨430678760057702362418954309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 287119173371801574945969539 430678760057702362418954309)
              ·
                refine ⟨80752267510819192953553933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 430678760057702362418954309 80752267510819192953553933)
                ·
                  refine ⟨30282100316557197357582725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 80752267510819192953553933 30282100316557197357582725)
                  ·
                    refine ⟨5677893809354474504546761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 30282100316557197357582725 5677893809354474504546761)
                    ·
                      refine ⟨4258420357015855878410071, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5677893809354474504546761 4258420357015855878410071)
                      ·
                        rfl

theorem cell23_8293244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 1, 4, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 1, 4, 3, 4, 2].length) (baseStart_8293244 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8293244 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8293244 prefixEnd_8293244 := by exact prefixLift 8293244
  have htrace : WordTrace (prefixWord ++ tailWord_8293244) baseStart_8293244 baseEnd_8293244 := by
    simpa [prefixWord, tailWord_8293244, baseEnd_8293244] using wordTrace_append hprefix tailTrace_8293244
  have hstable : (prefixWord ++ tailWord_8293244).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8293244).length < 2 ^ (prefixWord ++ tailWord_8293244).sum := by decide
  have hdescent : baseEnd_8293244 < baseStart_8293244 := by decide
  rcases family_descends (prefixWord ++ tailWord_8293244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8293247 : List Nat := [1, 1, 2, 2, 1, 1, 4, 1, 1, 6, 3]
def baseStart_8293247 : Nat := 118140960795 + 8293247 * 2 ^ 59
def prefixEnd_8293247 : Nat := 4983230072969 + 3 ^ 40 * 8293247 * 2
def baseEnd_8293247 : Nat := 4258421897457819366672557

theorem tailTrace_8293247 : CollatzResearch.WordTrace tailWord_8293247 prefixEnd_8293247 4258421897457819366672557 := by
  unfold tailWord_8293247
  simp only [CollatzResearch.WordTrace]
  refine ⟨302479567785989967669429995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201653045190659978446286663 302479567785989967669429995)
  ·
    refine ⟨453719351678984951504144993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 302479567785989967669429995 453719351678984951504144993)
    ·
      refine ⟨340289513759238713628108745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 453719351678984951504144993 340289513759238713628108745)
      ·
        refine ⟨255217135319429035221081559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 340289513759238713628108745 255217135319429035221081559)
        ·
          refine ⟨382825702979143552831622339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 255217135319429035221081559 382825702979143552831622339)
          ·
            refine ⟨574238554468715329247433509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 382825702979143552831622339 574238554468715329247433509)
            ·
              refine ⟨107669728962884124233893783, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 574238554468715329247433509 107669728962884124233893783)
              ·
                refine ⟨161504593444326186350840675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 107669728962884124233893783 161504593444326186350840675)
                ·
                  refine ⟨242256890166489279526261013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 161504593444326186350840675 242256890166489279526261013)
                  ·
                    refine ⟨11355791726554184977793485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 242256890166489279526261013 11355791726554184977793485)
                    ·
                      refine ⟨4258421897457819366672557, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11355791726554184977793485 4258421897457819366672557)
                      ·
                        rfl

theorem cell23_8293247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 4, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 4, 1, 1, 6, 3].length) (baseStart_8293247 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8293247 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8293247 prefixEnd_8293247 := by exact prefixLift 8293247
  have htrace : WordTrace (prefixWord ++ tailWord_8293247) baseStart_8293247 baseEnd_8293247 := by
    simpa [prefixWord, tailWord_8293247, baseEnd_8293247] using wordTrace_append hprefix tailTrace_8293247
  have hstable : (prefixWord ++ tailWord_8293247).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8293247).length < 2 ^ (prefixWord ++ tailWord_8293247).sum := by decide
  have hdescent : baseEnd_8293247 < baseStart_8293247 := by decide
  rcases family_descends (prefixWord ++ tailWord_8293247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8293351 : List Nat := [1, 1, 5, 2, 2, 1, 2, 2, 2, 1, 4]
def baseStart_8293351 : Nat := 118140960795 + 8293351 * 2 ^ 59
def prefixEnd_8293351 : Nat := 4983230072969 + 3 ^ 40 * 8293351 * 2
def baseEnd_8293351 : Nat := 4258475299445886959772079

theorem tailTrace_8293351 : CollatzResearch.WordTrace tailWord_8293351 prefixEnd_8293351 4258475299445886959772079 := by
  unfold tailWord_8293351
  simp only [CollatzResearch.WordTrace]
  refine ⟨302483360977613193431215907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201655573985075462287477271 302483360977613193431215907)
  ·
    refine ⟨453725041466419790146823861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 302483360977613193431215907 453725041466419790146823861)
    ·
      refine ⟨42536722637476855326264737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 453725041466419790146823861 42536722637476855326264737)
      ·
        refine ⟨31902541978107641494698553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42536722637476855326264737 31902541978107641494698553)
        ·
          refine ⟨23926906483580731121023915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31902541978107641494698553 23926906483580731121023915)
          ·
            refine ⟨35890359725371096681535873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23926906483580731121023915 35890359725371096681535873)
            ·
              refine ⟨26917769794028322511151905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35890359725371096681535873 26917769794028322511151905)
              ·
                refine ⟨20188327345521241883363929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26917769794028322511151905 20188327345521241883363929)
                ·
                  refine ⟨15141245509140931412522947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20188327345521241883363929 15141245509140931412522947)
                  ·
                    refine ⟨22711868263711397118784421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15141245509140931412522947 22711868263711397118784421)
                    ·
                      refine ⟨4258475299445886959772079, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22711868263711397118784421 4258475299445886959772079)
                      ·
                        rfl

theorem cell23_8293351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 1, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 1, 2, 2, 2, 1, 4].length) (baseStart_8293351 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8293351 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8293351 prefixEnd_8293351 := by exact prefixLift 8293351
  have htrace : WordTrace (prefixWord ++ tailWord_8293351) baseStart_8293351 baseEnd_8293351 := by
    simpa [prefixWord, tailWord_8293351, baseEnd_8293351] using wordTrace_append hprefix tailTrace_8293351
  have hstable : (prefixWord ++ tailWord_8293351).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8293351).length < 2 ^ (prefixWord ++ tailWord_8293351).sum := by decide
  have hdescent : baseEnd_8293351 < baseStart_8293351 := by decide
  rcases family_descends (prefixWord ++ tailWord_8293351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8293388 : List Nat := [2, 2, 1, 2, 3, 4, 1, 1, 2, 2, 3]
def baseStart_8293388 : Nat := 118140960795 + 8293388 * 2 ^ 59
def prefixEnd_8293388 : Nat := 4983230072969 + 3 ^ 40 * 8293388 * 2
def baseEnd_8293388 : Nat := 4258494298230103315009409

theorem tailTrace_8293388 : CollatzResearch.WordTrace tailWord_8293388 prefixEnd_8293388 4258494298230103315009409 := by
  unfold tailWord_8293388
  simp only [CollatzResearch.WordTrace]
  refine ⟨151242355239239574375156409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 201656473652319432500208545 151242355239239574375156409)
  ·
    refine ⟨113431766429429680781367307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 151242355239239574375156409 113431766429429680781367307)
    ·
      refine ⟨170147649644144521172050961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113431766429429680781367307 170147649644144521172050961)
      ·
        refine ⟨127610737233108390879038221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 170147649644144521172050961 127610737233108390879038221)
        ·
          refine ⟨47854026462415646579639333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 127610737233108390879038221 47854026462415646579639333)
          ·
            refine ⟨8972629961702933733682375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 47854026462415646579639333 8972629961702933733682375)
            ·
              refine ⟨13458944942554400600523563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8972629961702933733682375 13458944942554400600523563)
              ·
                refine ⟨20188417413831600900785345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13458944942554400600523563 20188417413831600900785345)
                ·
                  refine ⟨15141313060373700675589009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20188417413831600900785345 15141313060373700675589009)
                  ·
                    refine ⟨11355984795280275506691757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15141313060373700675589009 11355984795280275506691757)
                    ·
                      refine ⟨4258494298230103315009409, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11355984795280275506691757 4258494298230103315009409)
                      ·
                        rfl

theorem cell23_8293388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 4, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 4, 1, 1, 2, 2, 3].length) (baseStart_8293388 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8293388 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8293388 prefixEnd_8293388 := by exact prefixLift 8293388
  have htrace : WordTrace (prefixWord ++ tailWord_8293388) baseStart_8293388 baseEnd_8293388 := by
    simpa [prefixWord, tailWord_8293388, baseEnd_8293388] using wordTrace_append hprefix tailTrace_8293388
  have hstable : (prefixWord ++ tailWord_8293388).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8293388).length < 2 ^ (prefixWord ++ tailWord_8293388).sum := by decide
  have hdescent : baseEnd_8293388 < baseStart_8293388 := by decide
  rcases family_descends (prefixWord ++ tailWord_8293388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8293438 : List Nat := [4, 2, 1, 3, 1, 1, 1, 4, 1, 5]
def baseStart_8293438 : Nat := 118140960795 + 8293438 * 2 ^ 59
def prefixEnd_8293438 : Nat := 4983230072969 + 3 ^ 40 * 8293438 * 2
def baseEnd_8293438 : Nat := 1419506657420942706461393

theorem tailTrace_8293438 : CollatzResearch.WordTrace tailWord_8293438 prefixEnd_8293438 1419506657420942706461393 := by
  unfold tailWord_8293438
  simp only [CollatzResearch.WordTrace]
  refine ⟨37810816766037250911204121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 201657689418865338193088645 37810816766037250911204121)
  ·
    refine ⟨28358112574527938183403091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37810816766037250911204121 28358112574527938183403091)
    ·
      refine ⟨42537168861791907275104637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28358112574527938183403091 42537168861791907275104637)
      ·
        refine ⟨15951438323171965228164239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42537168861791907275104637 15951438323171965228164239)
        ·
          refine ⟨23927157484757947842246359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15951438323171965228164239 23927157484757947842246359)
          ·
            refine ⟨35890736227136921763369539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23927157484757947842246359 35890736227136921763369539)
            ·
              refine ⟨53836104340705382645054309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35890736227136921763369539 53836104340705382645054309)
              ·
                refine ⟨10094269563882259245947683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 53836104340705382645054309 10094269563882259245947683)
                ·
                  refine ⟨15141404345823388868921525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10094269563882259245947683 15141404345823388868921525)
                  ·
                    refine ⟨1419506657420942706461393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15141404345823388868921525 1419506657420942706461393)
                    ·
                      rfl

theorem cell23_8293438_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 1, 1, 4, 1, 5].length) (baseStart_8293438 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8293438 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8293438 prefixEnd_8293438 := by exact prefixLift 8293438
  have htrace : WordTrace (prefixWord ++ tailWord_8293438) baseStart_8293438 baseEnd_8293438 := by
    simpa [prefixWord, tailWord_8293438, baseEnd_8293438] using wordTrace_append hprefix tailTrace_8293438
  have hstable : (prefixWord ++ tailWord_8293438).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8293438).length < 2 ^ (prefixWord ++ tailWord_8293438).sum := by decide
  have hdescent : baseEnd_8293438 < baseStart_8293438 := by decide
  rcases family_descends (prefixWord ++ tailWord_8293438) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8293458 : List Nat := [3, 2, 2, 1, 3, 1, 2, 3, 1, 1, 4]
def baseStart_8293458 : Nat := 118140960795 + 8293458 * 2 ^ 59
def prefixEnd_8293458 : Nat := 4983230072969 + 3 ^ 40 * 8293458 * 2
def baseEnd_8293458 : Nat := 4258530241875918041134087

theorem tailTrace_8293458 : CollatzResearch.WordTrace tailWord_8293458 prefixEnd_8293458 4258530241875918041134087 := by
  unfold tailWord_8293458
  simp only [CollatzResearch.WordTrace]
  refine ⟨75621815897056387676340257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 201658175725483700470240685 75621815897056387676340257)
  ·
    refine ⟨56716361922792290757255193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75621815897056387676340257 56716361922792290757255193)
    ·
      refine ⟨42537271442094218067941395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56716361922792290757255193 42537271442094218067941395)
      ·
        refine ⟨63805907163141327101912093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42537271442094218067941395 63805907163141327101912093)
        ·
          refine ⟨23927215186177997663217035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 63805907163141327101912093 23927215186177997663217035)
          ·
            refine ⟨35890822779266996494825553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23927215186177997663217035 35890822779266996494825553)
            ·
              refine ⟨26918117084450247371119165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35890822779266996494825553 26918117084450247371119165)
              ·
                refine ⟨10094293906668842764169687, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26918117084450247371119165 10094293906668842764169687)
                ·
                  refine ⟨15141440860003264146254531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10094293906668842764169687 15141440860003264146254531)
                  ·
                    refine ⟨22712161290004896219381797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15141440860003264146254531 22712161290004896219381797)
                    ·
                      refine ⟨4258530241875918041134087, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22712161290004896219381797 4258530241875918041134087)
                      ·
                        rfl

theorem cell23_8293458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 1, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 1, 2, 3, 1, 1, 4].length) (baseStart_8293458 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8293458 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8293458 prefixEnd_8293458 := by exact prefixLift 8293458
  have htrace : WordTrace (prefixWord ++ tailWord_8293458) baseStart_8293458 baseEnd_8293458 := by
    simpa [prefixWord, tailWord_8293458, baseEnd_8293458] using wordTrace_append hprefix tailTrace_8293458
  have hstable : (prefixWord ++ tailWord_8293458).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8293458).length < 2 ^ (prefixWord ++ tailWord_8293458).sum := by decide
  have hdescent : baseEnd_8293458 < baseStart_8293458 := by decide
  rcases family_descends (prefixWord ++ tailWord_8293458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8293461 : List Nat := [1, 3, 2, 2, 1, 2, 4, 1, 1, 1, 5]
def baseStart_8293461 : Nat := 118140960795 + 8293461 * 2 ^ 59
def prefixEnd_8293461 : Nat := 4983230072969 + 3 ^ 40 * 8293461 * 2
def baseEnd_8293461 : Nat := 4258531782317881529396573

theorem tailTrace_8293461 : CollatzResearch.WordTrace tailWord_8293461 prefixEnd_8293461 4258531782317881529396573 := by
  unfold tailWord_8293461
  simp only [CollatzResearch.WordTrace]
  refine ⟨302487373007214682217720237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201658248671476454811813491 302487373007214682217720237)
  ·
    refine ⟨113432764877705505831645089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 302487373007214682217720237 113432764877705505831645089)
    ·
      refine ⟨85074573658279129373733817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 113432764877705505831645089 85074573658279129373733817)
      ·
        refine ⟨63805930243709347030300363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85074573658279129373733817 63805930243709347030300363)
        ·
          refine ⟨95708895365564020545450545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63805930243709347030300363 95708895365564020545450545)
          ·
            refine ⟨71781671524173015409087909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 95708895365564020545450545 71781671524173015409087909)
            ·
              refine ⟨13459063410782440389203983, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 71781671524173015409087909 13459063410782440389203983)
              ·
                refine ⟨20188595116173660583805975, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13459063410782440389203983 20188595116173660583805975)
                ·
                  refine ⟨30282892674260490875708963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20188595116173660583805975 30282892674260490875708963)
                  ·
                    refine ⟨45424339011390736313563445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 30282892674260490875708963 45424339011390736313563445)
                    ·
                      refine ⟨4258531782317881529396573, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 45424339011390736313563445 4258531782317881529396573)
                      ·
                        rfl

theorem cell23_8293461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 4, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 4, 1, 1, 1, 5].length) (baseStart_8293461 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8293461 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8293461 prefixEnd_8293461 := by exact prefixLift 8293461
  have htrace : WordTrace (prefixWord ++ tailWord_8293461) baseStart_8293461 baseEnd_8293461 := by
    simpa [prefixWord, tailWord_8293461, baseEnd_8293461] using wordTrace_append hprefix tailTrace_8293461
  have hstable : (prefixWord ++ tailWord_8293461).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8293461).length < 2 ^ (prefixWord ++ tailWord_8293461).sum := by decide
  have hdescent : baseEnd_8293461 < baseStart_8293461 := by decide
  rcases family_descends (prefixWord ++ tailWord_8293461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8293468 : List Nat := [2, 2, 4, 1, 1, 1, 2, 4, 2, 4]
def baseStart_8293468 : Nat := 118140960795 + 8293468 * 2 ^ 59
def prefixEnd_8293468 : Nat := 4983230072969 + 3 ^ 40 * 8293468 * 2
def baseEnd_8293468 : Nat := 1419511792227487667336347

theorem tailTrace_8293468 : CollatzResearch.WordTrace tailWord_8293468 prefixEnd_8293468 1419511792227487667336347 := by
  unfold tailWord_8293468
  simp only [CollatzResearch.WordTrace]
  refine ⟨151243814159094661206612529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 201658418878792881608816705 151243814159094661206612529)
  ·
    refine ⟨113432860619320995904959397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 151243814159094661206612529 113432860619320995904959397)
    ·
      refine ⟨21268661366122686732179887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 113432860619320995904959397 21268661366122686732179887)
      ·
        refine ⟨31902992049184030098269831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21268661366122686732179887 31902992049184030098269831)
        ·
          refine ⟨47854488073776045147404747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31902992049184030098269831 47854488073776045147404747)
          ·
            refine ⟨71781732110664067721107121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47854488073776045147404747 71781732110664067721107121)
            ·
              refine ⟨53836299082998050790830341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 71781732110664067721107121 53836299082998050790830341)
              ·
                refine ⟨10094306078062134523280689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 53836299082998050790830341 10094306078062134523280689)
                ·
                  refine ⟨7570729558546600892460517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10094306078062134523280689 7570729558546600892460517)
                  ·
                    refine ⟨1419511792227487667336347, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7570729558546600892460517 1419511792227487667336347)
                    ·
                      rfl

theorem cell23_8293468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 2, 4, 2, 4].length) (baseStart_8293468 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8293468 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8293468 prefixEnd_8293468 := by exact prefixLift 8293468
  have htrace : WordTrace (prefixWord ++ tailWord_8293468) baseStart_8293468 baseEnd_8293468 := by
    simpa [prefixWord, tailWord_8293468, baseEnd_8293468] using wordTrace_append hprefix tailTrace_8293468
  have hstable : (prefixWord ++ tailWord_8293468).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8293468).length < 2 ^ (prefixWord ++ tailWord_8293468).sum := by decide
  have hdescent : baseEnd_8293468 < baseStart_8293468 := by decide
  rcases family_descends (prefixWord ++ tailWord_8293468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8293469 : List Nat := [1, 4, 4, 1, 3, 1, 1, 1, 3, 1, 3]
def baseStart_8293469 : Nat := 118140960795 + 8293469 * 2 ^ 59
def prefixEnd_8293469 : Nat := 4983230072969 + 3 ^ 40 * 8293469 * 2
def baseEnd_8293469 : Nat := 4258535890163117498096537

theorem tailTrace_8293469 : CollatzResearch.WordTrace tailWord_8293469 prefixEnd_8293469 4258535890163117498096537 := by
  unfold tailWord_8293469
  simp only [CollatzResearch.WordTrace]
  refine ⟨302487664791185699584011461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201658443194123799722674307 302487664791185699584011461)
  ·
    refine ⟨56716437148347318672002149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 302487664791185699584011461 56716437148347318672002149)
    ·
      refine ⟨10634331965315122251000403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 56716437148347318672002149 10634331965315122251000403)
      ·
        refine ⟨15951497947972683376500605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10634331965315122251000403 15951497947972683376500605)
        ·
          refine ⟨5981811730489756266187727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15951497947972683376500605 5981811730489756266187727)
          ·
            refine ⟨8972717595734634399281591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5981811730489756266187727 8972717595734634399281591)
            ·
              refine ⟨13459076393601951598922387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8972717595734634399281591 13459076393601951598922387)
              ·
                refine ⟨20188614590402927398383581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13459076393601951598922387 20188614590402927398383581)
                ·
                  refine ⟨7570730471401097774393843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20188614590402927398383581 7570730471401097774393843)
                  ·
                    refine ⟨11356095707101646661590765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7570730471401097774393843 11356095707101646661590765)
                    ·
                      refine ⟨4258535890163117498096537, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11356095707101646661590765 4258535890163117498096537)
                      ·
                        rfl

theorem cell23_8293469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 3, 1, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 3, 1, 1, 1, 3, 1, 3].length) (baseStart_8293469 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8293469 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8293469 prefixEnd_8293469 := by exact prefixLift 8293469
  have htrace : WordTrace (prefixWord ++ tailWord_8293469) baseStart_8293469 baseEnd_8293469 := by
    simpa [prefixWord, tailWord_8293469, baseEnd_8293469] using wordTrace_append hprefix tailTrace_8293469
  have hstable : (prefixWord ++ tailWord_8293469).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8293469).length < 2 ^ (prefixWord ++ tailWord_8293469).sum := by decide
  have hdescent : baseEnd_8293469 < baseStart_8293469 := by decide
  rcases family_descends (prefixWord ++ tailWord_8293469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8293484 : List Nat := [2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 6]
def baseStart_8293484 : Nat := 118140960795 + 8293484 * 2 ^ 59
def prefixEnd_8293484 : Nat := 4983230072969 + 3 ^ 40 * 8293484 * 2
def baseEnd_8293484 : Nat := 4258543592372934939408967

theorem tailTrace_8293484 : CollatzResearch.WordTrace tailWord_8293484 prefixEnd_8293484 4258543592372934939408967 := by
  unfold tailWord_8293484
  simp only [CollatzResearch.WordTrace]
  refine ⟨151244105943065678572903753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 201658807924087571430538337 151244105943065678572903753)
  ·
    refine ⟨113433079457299258929677815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 151244105943065678572903753 113433079457299258929677815)
    ·
      refine ⟨170149619185948888394516723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113433079457299258929677815 170149619185948888394516723)
      ·
        refine ⟨255224428778923332591775085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 170149619185948888394516723 255224428778923332591775085)
        ·
          refine ⟨95709160792096249721915657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 255224428778923332591775085 95709160792096249721915657)
          ·
            refine ⟨71781870594072187291436743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 95709160792096249721915657 71781870594072187291436743)
            ·
              refine ⟨107672805891108280937155115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71781870594072187291436743 107672805891108280937155115)
              ·
                refine ⟨161509208836662421405732673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 107672805891108280937155115 161509208836662421405732673)
                ·
                  refine ⟨121131906627496816054299505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 161509208836662421405732673 121131906627496816054299505)
                  ·
                    refine ⟨90848929970622612040724629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 121131906627496816054299505 90848929970622612040724629)
                    ·
                      refine ⟨4258543592372934939408967, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 90848929970622612040724629 4258543592372934939408967)
                      ·
                        rfl

theorem cell23_8293484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 6].length) (baseStart_8293484 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8293484 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8293484 prefixEnd_8293484 := by exact prefixLift 8293484
  have htrace : WordTrace (prefixWord ++ tailWord_8293484) baseStart_8293484 baseEnd_8293484 := by
    simpa [prefixWord, tailWord_8293484, baseEnd_8293484] using wordTrace_append hprefix tailTrace_8293484
  have hstable : (prefixWord ++ tailWord_8293484).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8293484).length < 2 ^ (prefixWord ++ tailWord_8293484).sum := by decide
  have hdescent : baseEnd_8293484 < baseStart_8293484 := by decide
  rcases family_descends (prefixWord ++ tailWord_8293484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8293485 : List Nat := [1, 5, 1, 1, 2, 2, 4, 1, 2, 4]
def baseStart_8293485 : Nat := 118140960795 + 8293485 * 2 ^ 59
def prefixEnd_8293485 : Nat := 4983230072969 + 3 ^ 40 * 8293485 * 2
def baseEnd_8293485 : Nat := 1419514701951196478498821

theorem tailTrace_8293485 : CollatzResearch.WordTrace tailWord_8293485 prefixEnd_8293485 1419514701951196478498821 := by
  unfold tailWord_8293485
  simp only [CollatzResearch.WordTrace]
  refine ⟨302488248359127734316593909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201658832239418489544395939 302488248359127734316593909)
  ·
    refine ⟨28358273283668225092180679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 302488248359127734316593909 28358273283668225092180679)
    ·
      refine ⟨42537409925502337638271019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28358273283668225092180679 42537409925502337638271019)
      ·
        refine ⟨63806114888253506457406529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42537409925502337638271019 63806114888253506457406529)
        ·
          refine ⟨47854586166190129843054897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63806114888253506457406529 47854586166190129843054897)
          ·
            refine ⟨35890939624642597382291173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47854586166190129843054897 35890939624642597382291173)
            ·
              refine ⟨6729551179620487009179595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 35890939624642597382291173 6729551179620487009179595)
              ·
                refine ⟨10094326769430730513769393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6729551179620487009179595 10094326769430730513769393)
                ·
                  refine ⟨7570745077073047885327045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10094326769430730513769393 7570745077073047885327045)
                  ·
                    refine ⟨1419514701951196478498821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7570745077073047885327045 1419514701951196478498821)
                    ·
                      rfl

theorem cell23_8293485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 2, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 2, 4, 1, 2, 4].length) (baseStart_8293485 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8293485 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8293485 prefixEnd_8293485 := by exact prefixLift 8293485
  have htrace : WordTrace (prefixWord ++ tailWord_8293485) baseStart_8293485 baseEnd_8293485 := by
    simpa [prefixWord, tailWord_8293485, baseEnd_8293485] using wordTrace_append hprefix tailTrace_8293485
  have hstable : (prefixWord ++ tailWord_8293485).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8293485).length < 2 ^ (prefixWord ++ tailWord_8293485).sum := by decide
  have hdescent : baseEnd_8293485 < baseStart_8293485 := by decide
  rcases family_descends (prefixWord ++ tailWord_8293485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8293502 : List Nat := [4, 2, 4, 1, 1, 1, 1, 2, 1, 6]
def baseStart_8293502 : Nat := 118140960795 + 8293502 * 2 ^ 59
def prefixEnd_8293502 : Nat := 4983230072969 + 3 ^ 40 * 8293502 * 2
def baseEnd_8293502 : Nat := 1419517611674905289661295

theorem tailTrace_8293502 : CollatzResearch.WordTrace tailWord_8293502 prefixEnd_8293502 1419517611674905289661295 := by
  unfold tailWord_8293502
  simp only [CollatzResearch.WordTrace]
  refine ⟨37811108550008268277495345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 201659245600044097479975173 37811108550008268277495345)
  ·
    refine ⟨28358331412506201208121509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37811108550008268277495345 28358331412506201208121509)
    ·
      refine ⟨5317187139844912726522783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 28358331412506201208121509 5317187139844912726522783)
      ·
        refine ⟨7975780709767369089784175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5317187139844912726522783 7975780709767369089784175)
        ·
          refine ⟨11963671064651053634676263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7975780709767369089784175 11963671064651053634676263)
          ·
            refine ⟨17945506596976580452014395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11963671064651053634676263 17945506596976580452014395)
            ·
              refine ⟨26918259895464870678021593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17945506596976580452014395 26918259895464870678021593)
              ·
                refine ⟨20188694921598653008516195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26918259895464870678021593 20188694921598653008516195)
                ·
                  refine ⟨30283042382397979512774293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20188694921598653008516195 30283042382397979512774293)
                  ·
                    refine ⟨1419517611674905289661295, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 30283042382397979512774293 1419517611674905289661295)
                    ·
                      rfl

theorem cell23_8293502_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 1, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 1, 1, 1, 2, 1, 6].length) (baseStart_8293502 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8293502 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8293502 prefixEnd_8293502 := by exact prefixLift 8293502
  have htrace : WordTrace (prefixWord ++ tailWord_8293502) baseStart_8293502 baseEnd_8293502 := by
    simpa [prefixWord, tailWord_8293502, baseEnd_8293502] using wordTrace_append hprefix tailTrace_8293502
  have hstable : (prefixWord ++ tailWord_8293502).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8293502).length < 2 ^ (prefixWord ++ tailWord_8293502).sum := by decide
  have hdescent : baseEnd_8293502 < baseStart_8293502 := by decide
  rcases family_descends (prefixWord ++ tailWord_8293502) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8293504 : List Nat := [2, 1, 1, 2, 1, 3, 2, 1, 1, 4, 5]
def baseStart_8293504 : Nat := 118140960795 + 8293504 * 2 ^ 59
def prefixEnd_8293504 : Nat := 4983230072969 + 3 ^ 40 * 8293504 * 2
def baseEnd_8293504 : Nat := 4258553861986024861158875

theorem tailTrace_8293504 : CollatzResearch.WordTrace tailWord_8293504 prefixEnd_8293504 4258553861986024861158875 := by
  unfold tailWord_8293504
  simp only [CollatzResearch.WordTrace]
  refine ⟨151244470673029450280767783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 201659294230705933707690377 151244470673029450280767783)
  ·
    refine ⟨226866706009544175421151675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151244470673029450280767783 226866706009544175421151675)
    ·
      refine ⟨340300059014316263131727513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 226866706009544175421151675 340300059014316263131727513)
      ·
        refine ⟨255225044260737197348795635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 340300059014316263131727513 255225044260737197348795635)
        ·
          refine ⟨382837566391105796023193453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 255225044260737197348795635 382837566391105796023193453)
          ·
            refine ⟨143564087396664673508697545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 382837566391105796023193453 143564087396664673508697545)
            ·
              refine ⟨107673065547498505131523159, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 143564087396664673508697545 107673065547498505131523159)
              ·
                refine ⟨161509598321247757697284739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 107673065547498505131523159 161509598321247757697284739)
                ·
                  refine ⟨242264397481871636545927109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 161509598321247757697284739 242264397481871636545927109)
                  ·
                    refine ⟨45424574527850931852361333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 242264397481871636545927109 45424574527850931852361333)
                    ·
                      refine ⟨4258553861986024861158875, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 45424574527850931852361333 4258553861986024861158875)
                      ·
                        rfl

theorem cell23_8293504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 2, 1, 1, 4, 5].length) (baseStart_8293504 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8293504 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8293504 prefixEnd_8293504 := by exact prefixLift 8293504
  have htrace : WordTrace (prefixWord ++ tailWord_8293504) baseStart_8293504 baseEnd_8293504 := by
    simpa [prefixWord, tailWord_8293504, baseEnd_8293504] using wordTrace_append hprefix tailTrace_8293504
  have hstable : (prefixWord ++ tailWord_8293504).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8293504).length < 2 ^ (prefixWord ++ tailWord_8293504).sum := by decide
  have hdescent : baseEnd_8293504 < baseStart_8293504 := by decide
  rcases family_descends (prefixWord ++ tailWord_8293504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8293508 : List Nat := [2, 3, 2, 1, 2, 3, 1, 2, 1, 3, 3]
def baseStart_8293508 : Nat := 118140960795 + 8293508 * 2 ^ 59
def prefixEnd_8293508 : Nat := 4983230072969 + 3 ^ 40 * 8293508 * 2
def baseEnd_8293508 : Nat := 4258555915908642845508857

theorem tailTrace_8293508 : CollatzResearch.WordTrace tailWord_8293508 prefixEnd_8293508 4258555915908642845508857 := by
  unfold tailWord_8293508
  simp only [CollatzResearch.WordTrace]
  refine ⟨151244543619022204622340589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 201659391492029606163120785 151244543619022204622340589)
  ·
    refine ⟨56716703857133326733377721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 151244543619022204622340589 56716703857133326733377721)
    ·
      refine ⟨42537527892849995050033291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56716703857133326733377721 42537527892849995050033291)
      ·
        refine ⟨63806291839274992575049937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42537527892849995050033291 63806291839274992575049937)
        ·
          refine ⟨47854718879456244431287453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63806291839274992575049937 47854718879456244431287453)
          ·
            refine ⟨17945519579796091661732795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 47854718879456244431287453 17945519579796091661732795)
            ·
              refine ⟨26918279369694137492599193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17945519579796091661732795 26918279369694137492599193)
              ·
                refine ⟨20188709527270603119449395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26918279369694137492599193 20188709527270603119449395)
                ·
                  refine ⟨30283064290905904679174093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20188709527270603119449395 30283064290905904679174093)
                  ·
                    refine ⟨11356149109089714254690285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 30283064290905904679174093 11356149109089714254690285)
                    ·
                      refine ⟨4258555915908642845508857, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11356149109089714254690285 4258555915908642845508857)
                      ·
                        rfl

theorem cell23_8293508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 3, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 3, 1, 2, 1, 3, 3].length) (baseStart_8293508 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8293508 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8293508 prefixEnd_8293508 := by exact prefixLift 8293508
  have htrace : WordTrace (prefixWord ++ tailWord_8293508) baseStart_8293508 baseEnd_8293508 := by
    simpa [prefixWord, tailWord_8293508, baseEnd_8293508] using wordTrace_append hprefix tailTrace_8293508
  have hstable : (prefixWord ++ tailWord_8293508).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8293508).length < 2 ^ (prefixWord ++ tailWord_8293508).sum := by decide
  have hdescent : baseEnd_8293508 < baseStart_8293508 := by decide
  rcases family_descends (prefixWord ++ tailWord_8293508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8293512 : List Nat := [2, 1, 3, 4, 2, 1, 3, 1, 1, 2, 3]
def baseStart_8293512 : Nat := 118140960795 + 8293512 * 2 ^ 59
def prefixEnd_8293512 : Nat := 4983230072969 + 3 ^ 40 * 8293512 * 2
def baseEnd_8293512 : Nat := 4258557969831260829858839

theorem tailTrace_8293512 : CollatzResearch.WordTrace tailWord_8293512 prefixEnd_8293512 4258557969831260829858839 := by
  unfold tailWord_8293512
  simp only [CollatzResearch.WordTrace]
  refine ⟨151244616565014958963913395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 201659488753353278618551193 151244616565014958963913395)
  ·
    refine ⟨226866924847522438445870093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151244616565014958963913395 226866924847522438445870093)
    ·
      refine ⟨85075096817820914417201285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 226866924847522438445870093 85075096817820914417201285)
      ·
        refine ⟨15951580653341421453225241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 85075096817820914417201285 15951580653341421453225241)
        ·
          refine ⟨11963685490006066089918931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15951580653341421453225241 11963685490006066089918931)
          ·
            refine ⟨17945528235009099134878397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11963685490006066089918931 17945528235009099134878397)
            ·
              refine ⟨6729573088128412175579399, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17945528235009099134878397 6729573088128412175579399)
              ·
                refine ⟨10094359632192618263369099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6729573088128412175579399 10094359632192618263369099)
                ·
                  refine ⟨15141539448288927395053649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10094359632192618263369099 15141539448288927395053649)
                  ·
                    refine ⟨11356154586216695546290237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15141539448288927395053649 11356154586216695546290237)
                    ·
                      refine ⟨4258557969831260829858839, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11356154586216695546290237 4258557969831260829858839)
                      ·
                        rfl

theorem cell23_8293512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 2, 1, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 2, 1, 3, 1, 1, 2, 3].length) (baseStart_8293512 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8293512 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8293512 prefixEnd_8293512 := by exact prefixLift 8293512
  have htrace : WordTrace (prefixWord ++ tailWord_8293512) baseStart_8293512 baseEnd_8293512 := by
    simpa [prefixWord, tailWord_8293512, baseEnd_8293512] using wordTrace_append hprefix tailTrace_8293512
  have hstable : (prefixWord ++ tailWord_8293512).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8293512).length < 2 ^ (prefixWord ++ tailWord_8293512).sum := by decide
  have hdescent : baseEnd_8293512 < baseStart_8293512 := by decide
  rcases family_descends (prefixWord ++ tailWord_8293512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8293531 : List Nat := [1, 1, 1, 1, 1, 1, 2, 3, 2, 8, 2]
def baseStart_8293531 : Nat := 118140960795 + 8293531 * 2 ^ 59
def prefixEnd_8293531 : Nat := 4983230072969 + 3 ^ 40 * 8293531 * 2
def baseEnd_8293531 : Nat := 4258567725963696255521251

theorem tailTrace_8293531 : CollatzResearch.WordTrace tailWord_8293531 prefixEnd_8293531 4258567725963696255521251 := by
  unfold tailWord_8293531
  simp only [CollatzResearch.WordTrace]
  refine ⟨302489926116961084172768447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201659950744640722781845631 302489926116961084172768447)
  ·
    refine ⟨453734889175441626259152671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 302489926116961084172768447 453734889175441626259152671)
    ·
      refine ⟨680602333763162439388729007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 453734889175441626259152671 680602333763162439388729007)
      ·
        refine ⟨1020903500644743659083093511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 680602333763162439388729007 1020903500644743659083093511)
        ·
          refine ⟨1531355250967115488624640267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1020903500644743659083093511 1531355250967115488624640267)
          ·
            refine ⟨2297032876450673232936960401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1531355250967115488624640267 2297032876450673232936960401)
            ·
              refine ⟨1722774657338004924702720301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2297032876450673232936960401 1722774657338004924702720301)
              ·
                refine ⟨646040496501751846763520113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1722774657338004924702720301 646040496501751846763520113)
                ·
                  refine ⟨484530372376313885072640085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 646040496501751846763520113 484530372376313885072640085)
                  ·
                    refine ⟨5678090301284928340695001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 484530372376313885072640085 5678090301284928340695001)
                    ·
                      refine ⟨4258567725963696255521251, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5678090301284928340695001 4258567725963696255521251)
                      ·
                        rfl

theorem cell23_8293531_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 3, 2, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 3, 2, 8, 2].length) (baseStart_8293531 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8293531 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8293531 prefixEnd_8293531 := by exact prefixLift 8293531
  have htrace : WordTrace (prefixWord ++ tailWord_8293531) baseStart_8293531 baseEnd_8293531 := by
    simpa [prefixWord, tailWord_8293531, baseEnd_8293531] using wordTrace_append hprefix tailTrace_8293531
  have hstable : (prefixWord ++ tailWord_8293531).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8293531).length < 2 ^ (prefixWord ++ tailWord_8293531).sum := by decide
  have hdescent : baseEnd_8293531 < baseStart_8293531 := by decide
  rcases family_descends (prefixWord ++ tailWord_8293531) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8293541 : List Nat := [1, 3, 1, 2, 1, 5, 1, 1, 2, 6]
def baseStart_8293541 : Nat := 118140960795 + 8293541 * 2 ^ 59
def prefixEnd_8293541 : Nat := 4983230072969 + 3 ^ 40 * 8293541 * 2
def baseEnd_8293541 : Nat := 1419524286923413738798735

theorem tailTrace_8293541 : CollatzResearch.WordTrace tailWord_8293541 prefixEnd_8293541 1419524286923413738798735 := by
  unfold tailWord_8293541
  simp only [CollatzResearch.WordTrace]
  refine ⟨302490290846924855880632477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201660193897949903920421651 302490290846924855880632477)
  ·
    refine ⟨113433859067596820955237179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 302490290846924855880632477 113433859067596820955237179)
    ·
      refine ⟨170150788601395231432855769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113433859067596820955237179 170150788601395231432855769)
      ·
        refine ⟨127613091451046423574641827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 170150788601395231432855769 127613091451046423574641827)
        ·
          refine ⟨191419637176569635361962741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 127613091451046423574641827 191419637176569635361962741)
          ·
            refine ⟨17945590985303403315184007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 191419637176569635361962741 17945590985303403315184007)
            ·
              refine ⟨26918386477955104972776011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17945590985303403315184007 26918386477955104972776011)
              ·
                refine ⟨40377579716932657459164017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26918386477955104972776011 40377579716932657459164017)
                ·
                  refine ⟨30283184787699493094373013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40377579716932657459164017 30283184787699493094373013)
                  ·
                    refine ⟨1419524286923413738798735, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 30283184787699493094373013 1419524286923413738798735)
                    ·
                      rfl

theorem cell23_8293541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 5, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 5, 1, 1, 2, 6].length) (baseStart_8293541 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8293541 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8293541 prefixEnd_8293541 := by exact prefixLift 8293541
  have htrace : WordTrace (prefixWord ++ tailWord_8293541) baseStart_8293541 baseEnd_8293541 := by
    simpa [prefixWord, tailWord_8293541, baseEnd_8293541] using wordTrace_append hprefix tailTrace_8293541
  have hstable : (prefixWord ++ tailWord_8293541).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8293541).length < 2 ^ (prefixWord ++ tailWord_8293541).sum := by decide
  have hdescent : baseEnd_8293541 < baseStart_8293541 := by decide
  rcases family_descends (prefixWord ++ tailWord_8293541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8293569 : List Nat := [1, 2, 6, 1, 1, 1, 4, 1, 1, 3, 2]
def baseStart_8293569 : Nat := 118140960795 + 8293569 * 2 ^ 59
def prefixEnd_8293569 : Nat := 4983230072969 + 3 ^ 40 * 8293569 * 2
def baseEnd_8293569 : Nat := 4258587238228567106846077

theorem tailTrace_8293569 : CollatzResearch.WordTrace tailWord_8293569 prefixEnd_8293569 4258587238228567106846077 := by
  unfold tailWord_8293569
  simp only [CollatzResearch.WordTrace]
  refine ⟨302491312090823416662651761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201660874727215611108434507 302491312090823416662651761)
  ·
    refine ⟨226868484068117562496988821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 302491312090823416662651761 226868484068117562496988821)
    ·
      refine ⟨10634460190693010742046351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 226868484068117562496988821 10634460190693010742046351)
      ·
        refine ⟨15951690286039516113069527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10634460190693010742046351 15951690286039516113069527)
        ·
          refine ⟨23927535429059274169604291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15951690286039516113069527 23927535429059274169604291)
          ·
            refine ⟨35891303143588911254406437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23927535429059274169604291 35891303143588911254406437)
            ·
              refine ⟨6729619339422920860201207, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 35891303143588911254406437 6729619339422920860201207)
              ·
                refine ⟨10094429009134381290301811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6729619339422920860201207 10094429009134381290301811)
                ·
                  refine ⟨15141643513701571935452717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10094429009134381290301811 15141643513701571935452717)
                  ·
                    refine ⟨5678116317638089475794769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15141643513701571935452717 5678116317638089475794769)
                    ·
                      refine ⟨4258587238228567106846077, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5678116317638089475794769 4258587238228567106846077)
                      ·
                        rfl

theorem cell23_8293569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 1, 4, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 1, 4, 1, 1, 3, 2].length) (baseStart_8293569 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8293569 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8293569 prefixEnd_8293569 := by exact prefixLift 8293569
  have htrace : WordTrace (prefixWord ++ tailWord_8293569) baseStart_8293569 baseEnd_8293569 := by
    simpa [prefixWord, tailWord_8293569, baseEnd_8293569] using wordTrace_append hprefix tailTrace_8293569
  have hstable : (prefixWord ++ tailWord_8293569).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8293569).length < 2 ^ (prefixWord ++ tailWord_8293569).sum := by decide
  have hdescent : baseEnd_8293569 < baseStart_8293569 := by decide
  rcases family_descends (prefixWord ++ tailWord_8293569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8293582 : List Nat := [4, 1, 1, 1, 5, 1, 1, 1, 4, 2, 2]
def baseStart_8293582 : Nat := 118140960795 + 8293582 * 2 ^ 59
def prefixEnd_8293582 : Nat := 4983230072969 + 3 ^ 40 * 8293582 * 2
def baseEnd_8293582 : Nat := 4258593913477075555983517

theorem tailTrace_8293582 : CollatzResearch.WordTrace tailWord_8293582 prefixEnd_8293582 4258593913477075555983517 := by
  unfold tailWord_8293582
  simp only [CollatzResearch.WordTrace]
  refine ⟨37811473279972039985359375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 201661190826517546588583333 37811473279972039985359375)
  ·
    refine ⟨56717209919958059978039063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37811473279972039985359375 56717209919958059978039063)
    ·
      refine ⟨85075814879937089967058595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56717209919958059978039063 85075814879937089967058595)
      ·
        refine ⟨127613722319905634950587893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85075814879937089967058595 127613722319905634950587893)
        ·
          refine ⟨11963786467491153276617615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 127613722319905634950587893 11963786467491153276617615)
          ·
            refine ⟨17945679701236729914926423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11963786467491153276617615 17945679701236729914926423)
            ·
              refine ⟨26918519551855094872389635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17945679701236729914926423 26918519551855094872389635)
              ·
                refine ⟨40377779327782642308584453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26918519551855094872389635 40377779327782642308584453)
                ·
                  refine ⟨7570833623959245432859585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 40377779327782642308584453 7570833623959245432859585)
                  ·
                    refine ⟨5678125217969434074644689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7570833623959245432859585 5678125217969434074644689)
                    ·
                      refine ⟨4258593913477075555983517, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5678125217969434074644689 4258593913477075555983517)
                      ·
                        rfl

theorem cell23_8293582_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 5, 1, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 5, 1, 1, 1, 4, 2, 2].length) (baseStart_8293582 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8293582 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8293582 prefixEnd_8293582 := by exact prefixLift 8293582
  have htrace : WordTrace (prefixWord ++ tailWord_8293582) baseStart_8293582 baseEnd_8293582 := by
    simpa [prefixWord, tailWord_8293582, baseEnd_8293582] using wordTrace_append hprefix tailTrace_8293582
  have hstable : (prefixWord ++ tailWord_8293582).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8293582).length < 2 ^ (prefixWord ++ tailWord_8293582).sum := by decide
  have hdescent : baseEnd_8293582 < baseStart_8293582 := by decide
  rcases family_descends (prefixWord ++ tailWord_8293582) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8293601 : List Nat := [1, 2, 3, 1, 3, 2, 1, 2, 1, 7]
def baseStart_8293601 : Nat := 118140960795 + 8293601 * 2 ^ 59
def prefixEnd_8293601 : Nat := 4983230072969 + 3 ^ 40 * 8293601 * 2
def baseEnd_8293601 : Nat := 1419534556536503660548643

theorem tailTrace_8293601 : CollatzResearch.WordTrace tailWord_8293601 prefixEnd_8293601 1419534556536503660548643 := by
  unfold tailWord_8293601
  simp only [CollatzResearch.WordTrace]
  refine ⟨302492479226707486127816657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201661652817804990751877771 302492479226707486127816657)
  ·
    refine ⟨226869359420030614595862493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 302492479226707486127816657 226869359420030614595862493)
    ·
      refine ⟨85076009782511480473448435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 226869359420030614595862493 85076009782511480473448435)
      ·
        refine ⟨127614014673767220710172653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85076009782511480473448435 127614014673767220710172653)
        ·
          refine ⟨47855255502662707766314745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 127614014673767220710172653 47855255502662707766314745)
          ·
            refine ⟨35891441626997030824736059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47855255502662707766314745 35891441626997030824736059)
            ·
              refine ⟨53837162440495546237104089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35891441626997030824736059 53837162440495546237104089)
              ·
                refine ⟨40377871830371659677828067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53837162440495546237104089 40377871830371659677828067)
                ·
                  refine ⟨60566807745557489516742101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40377871830371659677828067 60566807745557489516742101)
                  ·
                    refine ⟨1419534556536503660548643, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 60566807745557489516742101 1419534556536503660548643)
                    ·
                      rfl

theorem cell23_8293601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 2, 1, 2, 1, 7].length) (baseStart_8293601 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8293601 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8293601 prefixEnd_8293601 := by exact prefixLift 8293601
  have htrace : WordTrace (prefixWord ++ tailWord_8293601) baseStart_8293601 baseEnd_8293601 := by
    simpa [prefixWord, tailWord_8293601, baseEnd_8293601] using wordTrace_append hprefix tailTrace_8293601
  have hstable : (prefixWord ++ tailWord_8293601).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8293601).length < 2 ^ (prefixWord ++ tailWord_8293601).sum := by decide
  have hdescent : baseEnd_8293601 < baseStart_8293601 := by decide
  rcases family_descends (prefixWord ++ tailWord_8293601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8293650 : List Nat := [3, 2, 4, 2, 2, 1, 2, 1, 2, 2, 2]
def baseStart_8293650 : Nat := 118140960795 + 8293650 * 2 ^ 59
def prefixEnd_8293650 : Nat := 4983230072969 + 3 ^ 40 * 8293650 * 2
def baseEnd_8293650 : Nat := 4258628830161581289933205

theorem tailTrace_8293650 : CollatzResearch.WordTrace tailWord_8293650 prefixEnd_8293650 4258628830161581289933205 := by
  unfold tailWord_8293650
  simp only [CollatzResearch.WordTrace]
  refine ⟨75623566600882491874087601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 201662844269019978330900269 75623566600882491874087601)
  ·
    refine ⟨56717674950661868905565701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75623566600882491874087601 56717674950661868905565701)
    ·
      refine ⟨10634564053249100419793569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 56717674950661868905565701 10634564053249100419793569)
      ·
        refine ⟨7975923039936825314845177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10634564053249100419793569 7975923039936825314845177)
        ·
          refine ⟨5981942279952618986133883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7975923039936825314845177 5981942279952618986133883)
          ·
            refine ⟨8972913419928928479200825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5981942279952618986133883 8972913419928928479200825)
            ·
              refine ⟨6729685064946696359400619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8972913419928928479200825 6729685064946696359400619)
              ·
                refine ⟨10094527597420044539100929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6729685064946696359400619 10094527597420044539100929)
                ·
                  refine ⟨7570895698065033404325697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10094527597420044539100929 7570895698065033404325697)
                  ·
                    refine ⟨5678171773548775053244273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7570895698065033404325697 5678171773548775053244273)
                    ·
                      refine ⟨4258628830161581289933205, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5678171773548775053244273 4258628830161581289933205)
                      ·
                        rfl

theorem cell23_8293650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 2, 1, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 2, 1, 2, 1, 2, 2, 2].length) (baseStart_8293650 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8293650 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8293650 prefixEnd_8293650 := by exact prefixLift 8293650
  have htrace : WordTrace (prefixWord ++ tailWord_8293650) baseStart_8293650 baseEnd_8293650 := by
    simpa [prefixWord, tailWord_8293650, baseEnd_8293650] using wordTrace_append hprefix tailTrace_8293650
  have hstable : (prefixWord ++ tailWord_8293650).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8293650).length < 2 ^ (prefixWord ++ tailWord_8293650).sum := by decide
  have hdescent : baseEnd_8293650 < baseStart_8293650 := by decide
  rcases family_descends (prefixWord ++ tailWord_8293650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8293701 : List Nat := [1, 3, 1, 1, 1, 2, 1, 2, 2, 4, 5]
def baseStart_8293701 : Nat := 118140960795 + 8293701 * 2 ^ 59
def prefixEnd_8293701 : Nat := 4983230072969 + 3 ^ 40 * 8293701 * 2
def baseEnd_8293701 : Nat := 4258655017674960590395469

theorem tailTrace_8293701 : CollatzResearch.WordTrace tailWord_8293701 prefixEnd_8293701 4258655017674960590395469 := by
  unfold tailWord_8293701
  simp only [CollatzResearch.WordTrace]
  refine ⟨302496126526345203206456957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201664084350896802137637971 302496126526345203206456957)
  ·
    refine ⟨113436047447379451202421359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 302496126526345203206456957 113436047447379451202421359)
    ·
      refine ⟨170154071171069176803632039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113436047447379451202421359 170154071171069176803632039)
      ·
        refine ⟨255231106756603765205448059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 170154071171069176803632039 255231106756603765205448059)
        ·
          refine ⟨382846660134905647808172089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 255231106756603765205448059 382846660134905647808172089)
          ·
            refine ⟨287134995101179235856129067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 382846660134905647808172089 287134995101179235856129067)
            ·
              refine ⟨430702492651768853784193601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 287134995101179235856129067 430702492651768853784193601)
              ·
                refine ⟨323026869488826640338145201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 430702492651768853784193601 323026869488826640338145201)
                ·
                  refine ⟨242270152116619980253608901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 323026869488826640338145201 242270152116619980253608901)
                  ·
                    refine ⟨45425653521866246297551669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 242270152116619980253608901 45425653521866246297551669)
                    ·
                      refine ⟨4258655017674960590395469, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 45425653521866246297551669 4258655017674960590395469)
                      ·
                        rfl

theorem cell23_8293701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 1, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 1, 2, 2, 4, 5].length) (baseStart_8293701 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8293701 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8293701 prefixEnd_8293701 := by exact prefixLift 8293701
  have htrace : WordTrace (prefixWord ++ tailWord_8293701) baseStart_8293701 baseEnd_8293701 := by
    simpa [prefixWord, tailWord_8293701, baseEnd_8293701] using wordTrace_append hprefix tailTrace_8293701
  have hstable : (prefixWord ++ tailWord_8293701).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8293701).length < 2 ^ (prefixWord ++ tailWord_8293701).sum := by decide
  have hdescent : baseEnd_8293701 < baseStart_8293701 := by decide
  rcases family_descends (prefixWord ++ tailWord_8293701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8293708 : List Nat := [2, 2, 1, 3, 2, 2, 1, 2, 3, 5]
def baseStart_8293708 : Nat := 118140960795 + 8293708 * 2 ^ 59
def prefixEnd_8293708 : Nat := 4983230072969 + 3 ^ 40 * 8293708 * 2
def baseEnd_8293708 : Nat := 1419552870679847354335979

theorem tailTrace_8293708 : CollatzResearch.WordTrace tailWord_8293708 prefixEnd_8293708 1419552870679847354335979 := by
  unfold tailWord_8293708
  simp only [CollatzResearch.WordTrace]
  refine ⟨151248190918659921700980889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 201664254558213228934641185 151248190918659921700980889)
  ·
    refine ⟨113436143188994941275735667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 151248190918659921700980889 113436143188994941275735667)
    ·
      refine ⟨170154214783492411913603501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113436143188994941275735667 170154214783492411913603501)
      ·
        refine ⟨63807830543809654467601313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 170154214783492411913603501 63807830543809654467601313)
        ·
          refine ⟨47855872907857240850700985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63807830543809654467601313 47855872907857240850700985)
          ·
            refine ⟨35891904680892930638025739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47855872907857240850700985 35891904680892930638025739)
            ·
              refine ⟨53837857021339395957038609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35891904680892930638025739 53837857021339395957038609)
              ·
                refine ⟨40378392766004546967778957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53837857021339395957038609 40378392766004546967778957)
                ·
                  refine ⟨15141897287251705112917109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 40378392766004546967778957 15141897287251705112917109)
                  ·
                    refine ⟨1419552870679847354335979, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15141897287251705112917109 1419552870679847354335979)
                    ·
                      rfl

theorem cell23_8293708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 2, 1, 2, 3, 5].length) (baseStart_8293708 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8293708 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8293708 prefixEnd_8293708 := by exact prefixLift 8293708
  have htrace : WordTrace (prefixWord ++ tailWord_8293708) baseStart_8293708 baseEnd_8293708 := by
    simpa [prefixWord, tailWord_8293708, baseEnd_8293708] using wordTrace_append hprefix tailTrace_8293708
  have hstable : (prefixWord ++ tailWord_8293708).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8293708).length < 2 ^ (prefixWord ++ tailWord_8293708).sum := by decide
  have hdescent : baseEnd_8293708 < baseStart_8293708 := by decide
  rcases family_descends (prefixWord ++ tailWord_8293708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8293732 : List Nat := [2, 3, 1, 1, 3, 2, 3, 1, 2, 3, 2]
def baseStart_8293732 : Nat := 118140960795 + 8293732 * 2 ^ 59
def prefixEnd_8293732 : Nat := 4983230072969 + 3 ^ 40 * 8293732 * 2
def baseEnd_8293732 : Nat := 4258670935575249969107827

theorem tailTrace_8293732 : CollatzResearch.WordTrace tailWord_8293732 prefixEnd_8293732 4258670935575249969107827 := by
  unfold tailWord_8293732
  simp only [CollatzResearch.WordTrace]
  refine ⟨151248628594616447750417725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 201664838126155263667223633 151248628594616447750417725)
  ·
    refine ⟨56718235722981167906406647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 151248628594616447750417725 56718235722981167906406647)
    ·
      refine ⟨85077353584471751859609971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56718235722981167906406647 85077353584471751859609971)
      ·
        refine ⟨127616030376707627789414957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85077353584471751859609971 127616030376707627789414957)
        ·
          refine ⟨47856011391265360421030609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 127616030376707627789414957 47856011391265360421030609)
          ·
            refine ⟨35892008543449020315772957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47856011391265360421030609 35892008543449020315772957)
            ·
              refine ⟨13459503203793382618414859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35892008543449020315772957 13459503203793382618414859)
              ·
                refine ⟨20189254805690073927622289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13459503203793382618414859 20189254805690073927622289)
                ·
                  refine ⟨15141941104267555445716717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20189254805690073927622289 15141941104267555445716717)
                  ·
                    refine ⟨5678227914100333292143769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15141941104267555445716717 5678227914100333292143769)
                    ·
                      refine ⟨4258670935575249969107827, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5678227914100333292143769 4258670935575249969107827)
                      ·
                        rfl

theorem cell23_8293732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 2, 3, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 2, 3, 1, 2, 3, 2].length) (baseStart_8293732 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8293732 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8293732 prefixEnd_8293732 := by exact prefixLift 8293732
  have htrace : WordTrace (prefixWord ++ tailWord_8293732) baseStart_8293732 baseEnd_8293732 := by
    simpa [prefixWord, tailWord_8293732, baseEnd_8293732] using wordTrace_append hprefix tailTrace_8293732
  have hstable : (prefixWord ++ tailWord_8293732).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8293732).length < 2 ^ (prefixWord ++ tailWord_8293732).sum := by decide
  have hdescent : baseEnd_8293732 < baseStart_8293732 := by decide
  rcases family_descends (prefixWord ++ tailWord_8293732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8293751 : List Nat := [1, 1, 3, 1, 1, 2, 14]
def baseStart_8293751 : Nat := 118140960795 + 8293751 * 2 ^ 59
def prefixEnd_8293751 : Nat := 4983230072969 + 3 ^ 40 * 8293751 * 2
def baseEnd_8293751 : Nat := 52576304835897350552719

theorem tailTrace_8293751 : CollatzResearch.WordTrace tailWord_8293751 prefixEnd_8293751 52576304835897350552719 := by
  unfold tailWord_8293751
  simp only [CollatzResearch.WordTrace]
  refine ⟨302497950176164061745777107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201665300117442707830518071 302497950176164061745777107)
  ·
    refine ⟨453746925264246092618665661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 302497950176164061745777107 453746925264246092618665661)
    ·
      refine ⟨170155096974092284731999623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 453746925264246092618665661 170155096974092284731999623)
      ·
        refine ⟨255232645461138427097999435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 170155096974092284731999623 255232645461138427097999435)
        ·
          refine ⟨382848968191707640646999153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 255232645461138427097999435 382848968191707640646999153)
          ·
            refine ⟨287136726143780730485249365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 382848968191707640646999153 287136726143780730485249365)
            ·
              refine ⟨52576304835897350552719, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 14 287136726143780730485249365 52576304835897350552719)
              ·
                rfl

theorem cell23_8293751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 14].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 14].length) (baseStart_8293751 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8293751 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8293751 prefixEnd_8293751 := by exact prefixLift 8293751
  have htrace : WordTrace (prefixWord ++ tailWord_8293751) baseStart_8293751 baseEnd_8293751 := by
    simpa [prefixWord, tailWord_8293751, baseEnd_8293751] using wordTrace_append hprefix tailTrace_8293751
  have hstable : (prefixWord ++ tailWord_8293751).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8293751).length < 2 ^ (prefixWord ++ tailWord_8293751).sum := by decide
  have hdescent : baseEnd_8293751 < baseStart_8293751 := by decide
  rcases family_descends (prefixWord ++ tailWord_8293751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8293772 : List Nat := [2, 2, 1, 2, 1, 3, 5, 1, 2, 4]
def baseStart_8293772 : Nat := 118140960795 + 8293772 * 2 ^ 59
def prefixEnd_8293772 : Nat := 4983230072969 + 3 ^ 40 * 8293772 * 2
def baseEnd_8293772 : Nat := 1419563824933809937535881

theorem tailTrace_8293772 : CollatzResearch.WordTrace tailWord_8293772 prefixEnd_8293772 1419563824933809937535881 := by
  unfold tailWord_8293772
  simp only [CollatzResearch.WordTrace]
  refine ⟨151249358054543991166145785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 201665810739391988221527713 151249358054543991166145785)
  ·
    refine ⟨113437018540907993374609339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 151249358054543991166145785 113437018540907993374609339)
    ·
      refine ⟨170155527811361990061914009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113437018540907993374609339 170155527811361990061914009)
      ·
        refine ⟨127616645858521492546435507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 170155527811361990061914009 127616645858521492546435507)
        ·
          refine ⟨191424968787782238819653261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 127616645858521492546435507 191424968787782238819653261)
          ·
            refine ⟨71784363295418339557369973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 191424968787782238819653261 71784363295418339557369973)
            ·
              refine ⟨6729784058945469333503435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 71784363295418339557369973 6729784058945469333503435)
              ·
                refine ⟨10094676088418204000255153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6729784058945469333503435 10094676088418204000255153)
                ·
                  refine ⟨7571007066313653000191365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10094676088418204000255153 7571007066313653000191365)
                  ·
                    refine ⟨1419563824933809937535881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7571007066313653000191365 1419563824933809937535881)
                    ·
                      rfl

theorem cell23_8293772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 5, 1, 2, 4].length) (baseStart_8293772 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8293772 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8293772 prefixEnd_8293772 := by exact prefixLift 8293772
  have htrace : WordTrace (prefixWord ++ tailWord_8293772) baseStart_8293772 baseEnd_8293772 := by
    simpa [prefixWord, tailWord_8293772, baseEnd_8293772] using wordTrace_append hprefix tailTrace_8293772
  have hstable : (prefixWord ++ tailWord_8293772).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8293772).length < 2 ^ (prefixWord ++ tailWord_8293772).sum := by decide
  have hdescent : baseEnd_8293772 < baseStart_8293772 := by decide
  rcases family_descends (prefixWord ++ tailWord_8293772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8293785 : List Nat := [1, 2, 1, 2, 1, 7, 2, 7]
def baseStart_8293785 : Nat := 118140960795 + 8293785 * 2 ^ 59
def prefixEnd_8293785 : Nat := 4983230072969 + 3 ^ 40 * 8293785 * 2
def baseEnd_8293785 : Nat := 157729561112960676360929

theorem tailTrace_8293785 : CollatzResearch.WordTrace tailWord_8293785 prefixEnd_8293785 157729561112960676360929 := by
  unfold tailWord_8293785
  simp only [CollatzResearch.WordTrace]
  refine ⟨302499190258040885552514809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201666126838693923701676539 302499190258040885552514809)
  ·
    refine ⟨226874392693530664164386107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 302499190258040885552514809 226874392693530664164386107)
    ·
      refine ⟨340311589040295996246579161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 226874392693530664164386107 340311589040295996246579161)
      ·
        refine ⟨255233691780221997184934371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 340311589040295996246579161 255233691780221997184934371)
        ·
          refine ⟨382850537670332995777401557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 255233691780221997184934371 382850537670332995777401557)
          ·
            refine ⟨8973059476648429588532849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 382850537670332995777401557 8973059476648429588532849)
            ·
              refine ⟨6729794607486322191399637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8973059476648429588532849 6729794607486322191399637)
              ·
                refine ⟨157729561112960676360929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6729794607486322191399637 157729561112960676360929)
                ·
                  rfl

theorem cell23_8293785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 7, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 7, 2, 7].length) (baseStart_8293785 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8293785 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8293785 prefixEnd_8293785 := by exact prefixLift 8293785
  have htrace : WordTrace (prefixWord ++ tailWord_8293785) baseStart_8293785 baseEnd_8293785 := by
    simpa [prefixWord, tailWord_8293785, baseEnd_8293785] using wordTrace_append hprefix tailTrace_8293785
  have hstable : (prefixWord ++ tailWord_8293785).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8293785).length < 2 ^ (prefixWord ++ tailWord_8293785).sum := by decide
  have hdescent : baseEnd_8293785 < baseStart_8293785 := by decide
  rcases family_descends (prefixWord ++ tailWord_8293785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8293790 : List Nat := [4, 3, 1, 2, 3, 1, 1, 3, 1, 1, 3]
def baseStart_8293790 : Nat := 118140960795 + 8293790 * 2 ^ 59
def prefixEnd_8293790 : Nat := 4983230072969 + 3 ^ 40 * 8293790 * 2
def baseEnd_8293790 : Nat := 4258700717453210742182561

theorem tailTrace_8293790 : CollatzResearch.WordTrace tailWord_8293790 prefixEnd_8293790 4258700717453210742182561 := by
  unfold tailWord_8293790
  simp only [CollatzResearch.WordTrace]
  refine ⟨37812421577877846425805853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 201666248415348514270964549 37812421577877846425805853)
  ·
    refine ⟨14179658091704192409677195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37812421577877846425805853 14179658091704192409677195)
    ·
      refine ⟨21269487137556288614515793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14179658091704192409677195 21269487137556288614515793)
      ·
        refine ⟨15952115353167216460886845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21269487137556288614515793 15952115353167216460886845)
        ·
          refine ⟨5982043257437706172832567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15952115353167216460886845 5982043257437706172832567)
          ·
            refine ⟨8973064886156559259248851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5982043257437706172832567 8973064886156559259248851)
            ·
              refine ⟨13459597329234838888873277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8973064886156559259248851 13459597329234838888873277)
              ·
                refine ⟨5047348998463064583327479, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13459597329234838888873277 5047348998463064583327479)
                ·
                  refine ⟨7571023497694596874991219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5047348998463064583327479 7571023497694596874991219)
                  ·
                    refine ⟨11356535246541895312486829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7571023497694596874991219 11356535246541895312486829)
                    ·
                      refine ⟨4258700717453210742182561, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11356535246541895312486829 4258700717453210742182561)
                      ·
                        rfl

theorem cell23_8293790_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 3, 1, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 3, 1, 1, 3, 1, 1, 3].length) (baseStart_8293790 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8293790 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8293790 prefixEnd_8293790 := by exact prefixLift 8293790
  have htrace : WordTrace (prefixWord ++ tailWord_8293790) baseStart_8293790 baseEnd_8293790 := by
    simpa [prefixWord, tailWord_8293790, baseEnd_8293790] using wordTrace_append hprefix tailTrace_8293790
  have hstable : (prefixWord ++ tailWord_8293790).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8293790).length < 2 ^ (prefixWord ++ tailWord_8293790).sum := by decide
  have hdescent : baseEnd_8293790 < baseStart_8293790 := by decide
  rcases family_descends (prefixWord ++ tailWord_8293790) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8293795 : List Nat := [1, 1, 1, 4, 1, 3, 1, 1, 6, 1, 3]
def baseStart_8293795 : Nat := 118140960795 + 8293795 * 2 ^ 59
def prefixEnd_8293795 : Nat := 4983230072969 + 3 ^ 40 * 8293795 * 2
def baseEnd_8293795 : Nat := 4258703284856483222620037

theorem tailTrace_8293795 : CollatzResearch.WordTrace tailWord_8293795 prefixEnd_8293795 4258703284856483222620037 := by
  unfold tailWord_8293795
  simp only [CollatzResearch.WordTrace]
  refine ⟨302499554988004657260378839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201666369992003104840252559 302499554988004657260378839)
  ·
    refine ⟨453749332482006985890568259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 302499554988004657260378839 453749332482006985890568259)
    ·
      refine ⟨680623998723010478835852389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 453749332482006985890568259 680623998723010478835852389)
      ·
        refine ⟨127616999760564464781722323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 680623998723010478835852389 127616999760564464781722323)
        ·
          refine ⟨191425499640846697172583485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 127616999760564464781722323 191425499640846697172583485)
          ·
            refine ⟨71784562365317511439718807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 191425499640846697172583485 71784562365317511439718807)
            ·
              refine ⟨107676843547976267159578211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71784562365317511439718807 107676843547976267159578211)
              ·
                refine ⟨161515265321964400739367317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 107676843547976267159578211 161515265321964400739367317)
                ·
                  refine ⟨7571028061967081284657843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 161515265321964400739367317 7571028061967081284657843)
                  ·
                    refine ⟨11356542092950621926986765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7571028061967081284657843 11356542092950621926986765)
                    ·
                      refine ⟨4258703284856483222620037, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11356542092950621926986765 4258703284856483222620037)
                      ·
                        rfl

theorem cell23_8293795_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 1, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 1, 1, 6, 1, 3].length) (baseStart_8293795 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8293795 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8293795 prefixEnd_8293795 := by exact prefixLift 8293795
  have htrace : WordTrace (prefixWord ++ tailWord_8293795) baseStart_8293795 baseEnd_8293795 := by
    simpa [prefixWord, tailWord_8293795, baseEnd_8293795] using wordTrace_append hprefix tailTrace_8293795
  have hstable : (prefixWord ++ tailWord_8293795).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8293795).length < 2 ^ (prefixWord ++ tailWord_8293795).sum := by decide
  have hdescent : baseEnd_8293795 < baseStart_8293795 := by decide
  rcases family_descends (prefixWord ++ tailWord_8293795) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8293813 : List Nat := [1, 3, 3, 2, 2, 2, 3, 2, 1, 2, 2]
def baseStart_8293813 : Nat := 118140960795 + 8293813 * 2 ^ 59
def prefixEnd_8293813 : Nat := 4983230072969 + 3 ^ 40 * 8293813 * 2
def baseEnd_8293813 : Nat := 4258712527508264152194955

theorem tailTrace_8293813 : CollatzResearch.WordTrace tailWord_8293813 prefixEnd_8293813 4258712527508264152194955 := by
  unfold tailWord_8293813
  simp only [CollatzResearch.WordTrace]
  refine ⟨302500211501939446334534093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201666807667959630889689395 302500211501939446334534093)
  ·
    refine ⟨113437579313227292375450285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 302500211501939446334534093 113437579313227292375450285)
    ·
      refine ⟨42539092242460234640793857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 113437579313227292375450285 42539092242460234640793857)
      ·
        refine ⟨31904319181845175980595393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42539092242460234640793857 31904319181845175980595393)
        ·
          refine ⟨23928239386383881985446545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31904319181845175980595393 23928239386383881985446545)
          ·
            refine ⟨17946179539787911489084909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23928239386383881985446545 17946179539787911489084909)
            ·
              refine ⟨6729817327420466808406841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17946179539787911489084909 6729817327420466808406841)
              ·
                refine ⟨5047362995565350106305131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6729817327420466808406841 5047362995565350106305131)
                ·
                  refine ⟨7571044493348025159457697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5047362995565350106305131 7571044493348025159457697)
                  ·
                    refine ⟨5678283370011018869593273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7571044493348025159457697 5678283370011018869593273)
                    ·
                      refine ⟨4258712527508264152194955, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5678283370011018869593273 4258712527508264152194955)
                      ·
                        rfl

theorem cell23_8293813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 2, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 2, 3, 2, 1, 2, 2].length) (baseStart_8293813 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8293813 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8293813 prefixEnd_8293813 := by exact prefixLift 8293813
  have htrace : WordTrace (prefixWord ++ tailWord_8293813) baseStart_8293813 baseEnd_8293813 := by
    simpa [prefixWord, tailWord_8293813, baseEnd_8293813] using wordTrace_append hprefix tailTrace_8293813
  have hstable : (prefixWord ++ tailWord_8293813).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8293813).length < 2 ^ (prefixWord ++ tailWord_8293813).sum := by decide
  have hdescent : baseEnd_8293813 < baseStart_8293813 := by decide
  rcases family_descends (prefixWord ++ tailWord_8293813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8293822 : List Nat := [4, 2, 1, 1, 1, 1, 1, 4, 3, 3, 2]
def baseStart_8293822 : Nat := 118140960795 + 8293822 * 2 ^ 59
def prefixEnd_8293822 : Nat := 4983230072969 + 3 ^ 40 * 8293822 * 2
def baseEnd_8293822 : Nat := 4258717148834154616982413

theorem tailTrace_8293822 : CollatzResearch.WordTrace tailWord_8293822 prefixEnd_8293822 4258717148834154616982413 := by
  unfold tailWord_8293822
  simp only [CollatzResearch.WordTrace]
  refine ⟨37812567469863355108951465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 201667026505937893914407813 37812567469863355108951465)
  ·
    refine ⟨28359425602397516331713599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37812567469863355108951465 28359425602397516331713599)
    ·
      refine ⟨42539138403596274497570399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28359425602397516331713599 42539138403596274497570399)
      ·
        refine ⟨63808707605394411746355599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42539138403596274497570399 63808707605394411746355599)
        ·
          refine ⟨95713061408091617619533399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63808707605394411746355599 95713061408091617619533399)
          ·
            refine ⟨143569592112137426429300099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 95713061408091617619533399 143569592112137426429300099)
            ·
              refine ⟨215354388168206139643950149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 143569592112137426429300099 215354388168206139643950149)
              ·
                refine ⟨40378947781538651183240653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 215354388168206139643950149 40378947781538651183240653)
                ·
                  refine ⟨15142105418076994193715245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 40378947781538651183240653 15142105418076994193715245)
                  ·
                    refine ⟨5678289531778872822643217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15142105418076994193715245 5678289531778872822643217)
                    ·
                      refine ⟨4258717148834154616982413, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5678289531778872822643217 4258717148834154616982413)
                      ·
                        rfl

theorem cell23_8293822_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 1, 4, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 1, 4, 3, 3, 2].length) (baseStart_8293822 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8293822 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8293822 prefixEnd_8293822 := by exact prefixLift 8293822
  have htrace : WordTrace (prefixWord ++ tailWord_8293822) baseStart_8293822 baseEnd_8293822 := by
    simpa [prefixWord, tailWord_8293822, baseEnd_8293822] using wordTrace_append hprefix tailTrace_8293822
  have hstable : (prefixWord ++ tailWord_8293822).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8293822).length < 2 ^ (prefixWord ++ tailWord_8293822).sum := by decide
  have hdescent : baseEnd_8293822 < baseStart_8293822 := by decide
  rcases family_descends (prefixWord ++ tailWord_8293822) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8293885 : List Nat := [1, 4, 1, 1, 1, 4, 1, 1, 1, 5, 3]
def baseStart_8293885 : Nat := 118140960795 + 8293885 * 2 ^ 59
def prefixEnd_8293885 : Nat := 4983230072969 + 3 ^ 40 * 8293885 * 2
def baseEnd_8293885 : Nat := 4258749498115387870494623

theorem tailTrace_8293885 : CollatzResearch.WordTrace tailWord_8293885 prefixEnd_8293885 4258749498115387870494623 := by
  unfold tailWord_8293885
  simp only [CollatzResearch.WordTrace]
  refine ⟨302502837557678602631155109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201668558371785735087436739 302502837557678602631155109)
  ·
    refine ⟨56719282042064737993341583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 302502837557678602631155109 56719282042064737993341583)
    ·
      refine ⟨85078923063097106990012375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56719282042064737993341583 85078923063097106990012375)
      ·
        refine ⟨127618384594645660485018563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85078923063097106990012375 127618384594645660485018563)
        ·
          refine ⟨191427576891968490727527845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 127618384594645660485018563 191427576891968490727527845)
          ·
            refine ⟨35892670667244092011411471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 191427576891968490727527845 35892670667244092011411471)
            ·
              refine ⟨53839006000866138017117207, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35892670667244092011411471 53839006000866138017117207)
              ·
                refine ⟨80758509001299207025675811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53839006000866138017117207 80758509001299207025675811)
                ·
                  refine ⟨121137763501948810538513717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 80758509001299207025675811 121137763501948810538513717)
                  ·
                    refine ⟨11356665328307700987985661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 121137763501948810538513717 11356665328307700987985661)
                    ·
                      refine ⟨4258749498115387870494623, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11356665328307700987985661 4258749498115387870494623)
                      ·
                        rfl

theorem cell23_8293885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 4, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 4, 1, 1, 1, 5, 3].length) (baseStart_8293885 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8293885 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8293885 prefixEnd_8293885 := by exact prefixLift 8293885
  have htrace : WordTrace (prefixWord ++ tailWord_8293885) baseStart_8293885 baseEnd_8293885 := by
    simpa [prefixWord, tailWord_8293885, baseEnd_8293885] using wordTrace_append hprefix tailTrace_8293885
  have hstable : (prefixWord ++ tailWord_8293885).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8293885).length < 2 ^ (prefixWord ++ tailWord_8293885).sum := by decide
  have hdescent : baseEnd_8293885 < baseStart_8293885 := by decide
  rcases family_descends (prefixWord ++ tailWord_8293885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8293892 : List Nat := [2, 3, 2, 3, 2, 1, 1, 2, 7]
def baseStart_8293892 : Nat := 118140960795 + 8293892 * 2 ^ 59
def prefixEnd_8293892 : Nat := 4983230072969 + 3 ^ 40 * 8293892 * 2
def baseEnd_8293892 : Nat := 473194788053329927011899

theorem tailTrace_8293892 : CollatzResearch.WordTrace tailWord_8293892 prefixEnd_8293892 473194788053329927011899 := by
  unfold tailWord_8293892
  simp only [CollatzResearch.WordTrace]
  refine ⟨151251546434326621413329965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 201668728579102161884439953 151251546434326621413329965)
  ·
    refine ⟨56719329912872483029998737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 151251546434326621413329965 56719329912872483029998737)
    ·
      refine ⟨42539497434654362272499053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56719329912872483029998737 42539497434654362272499053)
      ·
        refine ⟨15952311537995385852187145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42539497434654362272499053 15952311537995385852187145)
        ·
          refine ⟨11964233653496539389140359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15952311537995385852187145 11964233653496539389140359)
          ·
            refine ⟨17946350480244809083710539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11964233653496539389140359 17946350480244809083710539)
            ·
              refine ⟨26919525720367213625565809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17946350480244809083710539 26919525720367213625565809)
              ·
                refine ⟨20189644290275410219174357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26919525720367213625565809 20189644290275410219174357)
                ·
                  refine ⟨473194788053329927011899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 20189644290275410219174357 473194788053329927011899)
                  ·
                    rfl

theorem cell23_8293892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 2, 1, 1, 2, 7].length) (baseStart_8293892 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8293892 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8293892 prefixEnd_8293892 := by exact prefixLift 8293892
  have htrace : WordTrace (prefixWord ++ tailWord_8293892) baseStart_8293892 baseEnd_8293892 := by
    simpa [prefixWord, tailWord_8293892, baseEnd_8293892] using wordTrace_append hprefix tailTrace_8293892
  have hstable : (prefixWord ++ tailWord_8293892).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8293892).length < 2 ^ (prefixWord ++ tailWord_8293892).sum := by decide
  have hdescent : baseEnd_8293892 < baseStart_8293892 := by decide
  rcases family_descends (prefixWord ++ tailWord_8293892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8293925 : List Nat := [1, 3, 1, 2, 2, 1, 1, 3, 4, 1, 4]
def baseStart_8293925 : Nat := 118140960795 + 8293925 * 2 ^ 59
def prefixEnd_8293925 : Nat := 4983230072969 + 3 ^ 40 * 8293925 * 2
def baseEnd_8293925 : Nat := 4258770037341567713994439

theorem tailTrace_8293925 : CollatzResearch.WordTrace tailWord_8293925 prefixEnd_8293925 4258770037341567713994439 := by
  unfold tailWord_8293925
  simp only [CollatzResearch.WordTrace]
  refine ⟨302504296477533689462611229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201669530985022459641740819 302504296477533689462611229)
  ·
    refine ⟨113439111179075133548479211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 302504296477533689462611229 113439111179075133548479211)
    ·
      refine ⟨170158666768612700322718817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113439111179075133548479211 170158666768612700322718817)
      ·
        refine ⟨127619000076459525242039113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 170158666768612700322718817 127619000076459525242039113)
        ·
          refine ⟨95714250057344643931529335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 127619000076459525242039113 95714250057344643931529335)
          ·
            refine ⟨143571375086016965897294003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 95714250057344643931529335 143571375086016965897294003)
            ·
              refine ⟨215357062629025448845941005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 143571375086016965897294003 215357062629025448845941005)
              ·
                refine ⟨80758898485884543317227877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 215357062629025448845941005 80758898485884543317227877)
                ·
                  refine ⟨15142293466103351871980227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 80758898485884543317227877 15142293466103351871980227)
                  ·
                    refine ⟨22713440199155027807970341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15142293466103351871980227 22713440199155027807970341)
                    ·
                      refine ⟨4258770037341567713994439, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22713440199155027807970341 4258770037341567713994439)
                      ·
                        rfl

theorem cell23_8293925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 1, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 1, 3, 4, 1, 4].length) (baseStart_8293925 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8293925 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8293925 prefixEnd_8293925 := by exact prefixLift 8293925
  have htrace : WordTrace (prefixWord ++ tailWord_8293925) baseStart_8293925 baseEnd_8293925 := by
    simpa [prefixWord, tailWord_8293925, baseEnd_8293925] using wordTrace_append hprefix tailTrace_8293925
  have hstable : (prefixWord ++ tailWord_8293925).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8293925).length < 2 ^ (prefixWord ++ tailWord_8293925).sum := by decide
  have hdescent : baseEnd_8293925 < baseStart_8293925 := by decide
  rcases family_descends (prefixWord ++ tailWord_8293925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8293962 : List Nat := [3, 1, 2, 1, 1, 3, 2, 3, 2, 2, 3]
def baseStart_8293962 : Nat := 118140960795 + 8293962 * 2 ^ 59
def prefixEnd_8293962 : Nat := 4983230072969 + 3 ^ 40 * 8293962 * 2
def baseEnd_8293962 : Nat := 4258789036125784069231769

theorem tailTrace_8293962 : CollatzResearch.WordTrace tailWord_8293962 prefixEnd_8293962 4258789036125784069231769 := by
  unfold tailWord_8293962
  simp only [CollatzResearch.WordTrace]
  refine ⟨75626411494599911195427035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 201670430652266429854472093 75626411494599911195427035)
  ·
    refine ⟨113439617241899866793140553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75626411494599911195427035 113439617241899866793140553)
    ·
      refine ⟨85079712931424900094855415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 113439617241899866793140553 85079712931424900094855415)
      ·
        refine ⟨127619569397137350142283123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85079712931424900094855415 127619569397137350142283123)
        ·
          refine ⟨191429354095706025213424685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 127619569397137350142283123 191429354095706025213424685)
          ·
            refine ⟨71786007785889759455034257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 191429354095706025213424685 71786007785889759455034257)
            ·
              refine ⟨53839505839417319591275693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 71786007785889759455034257 53839505839417319591275693)
              ·
                refine ⟨20189814689781494846728385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 53839505839417319591275693 20189814689781494846728385)
                ·
                  refine ⟨15142361017336121135046289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20189814689781494846728385 15142361017336121135046289)
                  ·
                    refine ⟨11356770763002090851284717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15142361017336121135046289 11356770763002090851284717)
                    ·
                      refine ⟨4258789036125784069231769, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11356770763002090851284717 4258789036125784069231769)
                      ·
                        rfl

theorem cell23_8293962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 2, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 2, 3, 2, 2, 3].length) (baseStart_8293962 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8293962 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8293962 prefixEnd_8293962 := by exact prefixLift 8293962
  have htrace : WordTrace (prefixWord ++ tailWord_8293962) baseStart_8293962 baseEnd_8293962 := by
    simpa [prefixWord, tailWord_8293962, baseEnd_8293962] using wordTrace_append hprefix tailTrace_8293962
  have hstable : (prefixWord ++ tailWord_8293962).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8293962).length < 2 ^ (prefixWord ++ tailWord_8293962).sum := by decide
  have hdescent : baseEnd_8293962 < baseStart_8293962 := by decide
  rcases family_descends (prefixWord ++ tailWord_8293962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8294025 : List Nat := [1, 2, 1, 1, 4, 1, 3, 1, 3, 6]
def baseStart_8294025 : Nat := 118140960795 + 8294025 * 2 ^ 59
def prefixEnd_8294025 : Nat := 4983230072969 + 3 ^ 40 * 8294025 * 2
def baseEnd_8294025 : Nat := 1419607128469005774247993

theorem tailTrace_8294025 : CollatzResearch.WordTrace tailWord_8294025 prefixEnd_8294025 1419607128469005774247993 := by
  unfold tailWord_8294025
  simp only [CollatzResearch.WordTrace]
  refine ⟨302507943777171406541251529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201671962518114271027501019 302507943777171406541251529)
  ·
    refine ⟨226880957832878554905938647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 302507943777171406541251529 226880957832878554905938647)
    ·
      refine ⟨340321436749317832358907971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 226880957832878554905938647 340321436749317832358907971)
      ·
        refine ⟨510482155123976748538361957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 340321436749317832358907971 510482155123976748538361957)
        ·
          refine ⟨95715404085745640350942867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 510482155123976748538361957 95715404085745640350942867)
          ·
            refine ⟨143573106128618460526414301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 95715404085745640350942867 143573106128618460526414301)
            ·
              refine ⟨53839914798231922697405363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 143573106128618460526414301 53839914798231922697405363)
              ·
                refine ⟨80759872197347884046108045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53839914798231922697405363 80759872197347884046108045)
                ·
                  refine ⟨30284952074005456517290517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 80759872197347884046108045 30284952074005456517290517)
                  ·
                    refine ⟨1419607128469005774247993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 30284952074005456517290517 1419607128469005774247993)
                    ·
                      rfl

theorem cell23_8294025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 3, 1, 3, 6].length) (baseStart_8294025 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8294025 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8294025 prefixEnd_8294025 := by exact prefixLift 8294025
  have htrace : WordTrace (prefixWord ++ tailWord_8294025) baseStart_8294025 baseEnd_8294025 := by
    simpa [prefixWord, tailWord_8294025, baseEnd_8294025] using wordTrace_append hprefix tailTrace_8294025
  have hstable : (prefixWord ++ tailWord_8294025).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8294025).length < 2 ^ (prefixWord ++ tailWord_8294025).sum := by decide
  have hdescent : baseEnd_8294025 < baseStart_8294025 := by decide
  rcases family_descends (prefixWord ++ tailWord_8294025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8294032 : List Nat := [2, 1, 1, 1, 1, 1, 3, 7, 1, 1, 4]
def baseStart_8294032 : Nat := 118140960795 + 8294032 * 2 ^ 59
def prefixEnd_8294032 : Nat := 4983230072969 + 3 ^ 40 * 8294032 * 2
def baseEnd_8294032 : Nat := 4258824979771598795356447

theorem tailTrace_8294032 : CollatzResearch.WordTrace tailWord_8294032 prefixEnd_8294032 4258824979771598795356447 := by
  unfold tailWord_8294032
  simp only [CollatzResearch.WordTrace]
  refine ⟨151254099544073023368378175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 201672132725430697824504233 151254099544073023368378175)
  ·
    refine ⟨226881149316109535052567263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151254099544073023368378175 226881149316109535052567263)
    ·
      refine ⟨340321723974164302578850895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 226881149316109535052567263 340321723974164302578850895)
      ·
        refine ⟨510482585961246453868276343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 340321723974164302578850895 510482585961246453868276343)
        ·
          refine ⟨765723878941869680802414515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 510482585961246453868276343 765723878941869680802414515)
          ·
            refine ⟨1148585818412804521203621773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 765723878941869680802414515 1148585818412804521203621773)
            ·
              refine ⟨430719681904801695451358165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1148585818412804521203621773 430719681904801695451358165)
              ·
                refine ⟨10094992544643789737141207, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 430719681904801695451358165 10094992544643789737141207)
                ·
                  refine ⟨15142488816965684605711811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10094992544643789737141207 15142488816965684605711811)
                  ·
                    refine ⟨22713733225448526908567717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15142488816965684605711811 22713733225448526908567717)
                    ·
                      refine ⟨4258824979771598795356447, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22713733225448526908567717 4258824979771598795356447)
                      ·
                        rfl

theorem cell23_8294032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 3, 7, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 3, 7, 1, 1, 4].length) (baseStart_8294032 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8294032 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8294032 prefixEnd_8294032 := by exact prefixLift 8294032
  have htrace : WordTrace (prefixWord ++ tailWord_8294032) baseStart_8294032 baseEnd_8294032 := by
    simpa [prefixWord, tailWord_8294032, baseEnd_8294032] using wordTrace_append hprefix tailTrace_8294032
  have hstable : (prefixWord ++ tailWord_8294032).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8294032).length < 2 ^ (prefixWord ++ tailWord_8294032).sum := by decide
  have hdescent : baseEnd_8294032 < baseStart_8294032 := by decide
  rcases family_descends (prefixWord ++ tailWord_8294032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8294070 : List Nat := [5, 1, 3, 1, 1, 3, 1, 1, 2, 3, 2]
def baseStart_8294070 : Nat := 118140960795 + 8294070 * 2 ^ 59
def prefixEnd_8294070 : Nat := 4983230072969 + 3 ^ 40 * 8294070 * 2
def baseEnd_8294070 : Nat := 4258844492036469646681273

theorem tailTrace_8294070 : CollatzResearch.WordTrace tailWord_8294070 prefixEnd_8294070 4258844492036469646681273 := by
  unfold tailWord_8294070
  simp only [CollatzResearch.WordTrace]
  refine ⟨18906849066375523701664979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 201673056708005586151093109 18906849066375523701664979)
  ·
    refine ⟨28360273599563285552497469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18906849066375523701664979 28360273599563285552497469)
    ·
      refine ⟨10635102599836232082186551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28360273599563285552497469 10635102599836232082186551)
      ·
        refine ⟨15952653899754348123279827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10635102599836232082186551 15952653899754348123279827)
        ·
          refine ⟨23928980849631522184919741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15952653899754348123279827 23928980849631522184919741)
          ·
            refine ⟨8973367818611820819344903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23928980849631522184919741 8973367818611820819344903)
            ·
              refine ⟨13460051727917731229017355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8973367818611820819344903 13460051727917731229017355)
              ·
                refine ⟨20190077591876596843526033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13460051727917731229017355 20190077591876596843526033)
                ·
                  refine ⟨15142558193907447632644525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20190077591876596843526033 15142558193907447632644525)
                  ·
                    refine ⟨5678459322715292862241697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15142558193907447632644525 5678459322715292862241697)
                    ·
                      refine ⟨4258844492036469646681273, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5678459322715292862241697 4258844492036469646681273)
                      ·
                        rfl

theorem cell23_8294070_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 3, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 3, 1, 1, 2, 3, 2].length) (baseStart_8294070 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8294070 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8294070 prefixEnd_8294070 := by exact prefixLift 8294070
  have htrace : WordTrace (prefixWord ++ tailWord_8294070) baseStart_8294070 baseEnd_8294070 := by
    simpa [prefixWord, tailWord_8294070, baseEnd_8294070] using wordTrace_append hprefix tailTrace_8294070
  have hstable : (prefixWord ++ tailWord_8294070).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8294070).length < 2 ^ (prefixWord ++ tailWord_8294070).sum := by decide
  have hdescent : baseEnd_8294070 < baseStart_8294070 := by decide
  rcases family_descends (prefixWord ++ tailWord_8294070) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8294085 : List Nat := [1, 3, 1, 1, 1, 1, 2, 2, 4, 7]
def baseStart_8294085 : Nat := 118140960795 + 8294085 * 2 ^ 59
def prefixEnd_8294085 : Nat := 4983230072969 + 3 ^ 40 * 8294085 * 2
def baseEnd_8294085 : Nat := 1419617398082095695997901

theorem tailTrace_8294085 : CollatzResearch.WordTrace tailWord_8294085 prefixEnd_8294085 1419617398082095695997901 := by
  unfold tailWord_8294085
  simp only [CollatzResearch.WordTrace]
  refine ⟨302510132156954036788435709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201673421437969357858957139 302510132156954036788435709)
  ·
    refine ⟨113441299558857763795663391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 302510132156954036788435709 113441299558857763795663391)
    ·
      refine ⟨170161949338286645693495087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113441299558857763795663391 170161949338286645693495087)
      ·
        refine ⟨255242924007429968540242631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 170161949338286645693495087 255242924007429968540242631)
        ·
          refine ⟨382864386011144952810363947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 255242924007429968540242631 382864386011144952810363947)
          ·
            refine ⟨574296579016717429215545921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 382864386011144952810363947 574296579016717429215545921)
            ·
              refine ⟨430722434262538071911659441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 574296579016717429215545921 430722434262538071911659441)
              ·
                refine ⟨323041825696903553933744581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 430722434262538071911659441 323041825696903553933744581)
                ·
                  refine ⟨60570342318169416362577109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 323041825696903553933744581 60570342318169416362577109)
                  ·
                    refine ⟨1419617398082095695997901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 60570342318169416362577109 1419617398082095695997901)
                    ·
                      rfl

theorem cell23_8294085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 2, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 2, 2, 4, 7].length) (baseStart_8294085 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8294085 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8294085 prefixEnd_8294085 := by exact prefixLift 8294085
  have htrace : WordTrace (prefixWord ++ tailWord_8294085) baseStart_8294085 baseEnd_8294085 := by
    simpa [prefixWord, tailWord_8294085, baseEnd_8294085] using wordTrace_append hprefix tailTrace_8294085
  have hstable : (prefixWord ++ tailWord_8294085).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8294085).length < 2 ^ (prefixWord ++ tailWord_8294085).sum := by decide
  have hdescent : baseEnd_8294085 < baseStart_8294085 := by decide
  rcases family_descends (prefixWord ++ tailWord_8294085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8294093 : List Nat := [1, 6, 2, 1, 1, 1, 3, 2, 2, 4]
def baseStart_8294093 : Nat := 118140960795 + 8294093 * 2 ^ 59
def prefixEnd_8294093 : Nat := 4983230072969 + 3 ^ 40 * 8294093 * 2
def baseEnd_8294093 : Nat := 1419618767363841018897889

theorem tailTrace_8294093 : CollatzResearch.WordTrace tailWord_8294093 prefixEnd_8294093 1419618767363841018897889 := by
  unfold tailWord_8294093
  simp only [CollatzResearch.WordTrace]
  refine ⟨302510423940925054154726933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201673615960616702769817955 302510423940925054154726933)
  ·
    refine ⟨14180176122230861913502825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 302510423940925054154726933 14180176122230861913502825)
    ·
      refine ⟨10635132091673146435127119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14180176122230861913502825 10635132091673146435127119)
      ·
        refine ⟨15952698137509719652690679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10635132091673146435127119 15952698137509719652690679)
        ·
          refine ⟨23929047206264579479036019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15952698137509719652690679 23929047206264579479036019)
          ·
            refine ⟨35893570809396869218554029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23929047206264579479036019 35893570809396869218554029)
            ·
              refine ⟨13460089053523825956957761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35893570809396869218554029 13460089053523825956957761)
              ·
                refine ⟨10095066790142869467718321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13460089053523825956957761 10095066790142869467718321)
                ·
                  refine ⟨7571300092607152100788741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10095066790142869467718321 7571300092607152100788741)
                  ·
                    refine ⟨1419618767363841018897889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7571300092607152100788741 1419618767363841018897889)
                    ·
                      rfl

theorem cell23_8294093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 1, 3, 2, 2, 4].length) (baseStart_8294093 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8294093 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8294093 prefixEnd_8294093 := by exact prefixLift 8294093
  have htrace : WordTrace (prefixWord ++ tailWord_8294093) baseStart_8294093 baseEnd_8294093 := by
    simpa [prefixWord, tailWord_8294093, baseEnd_8294093] using wordTrace_append hprefix tailTrace_8294093
  have hstable : (prefixWord ++ tailWord_8294093).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8294093).length < 2 ^ (prefixWord ++ tailWord_8294093).sum := by decide
  have hdescent : baseEnd_8294093 < baseStart_8294093 := by decide
  rcases family_descends (prefixWord ++ tailWord_8294093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8294100 : List Nat := [2, 4, 1, 3, 1, 1, 2, 4, 1, 2, 2]
def baseStart_8294100 : Nat := 118140960795 + 8294100 * 2 ^ 59
def prefixEnd_8294100 : Nat := 4983230072969 + 3 ^ 40 * 8294100 * 2
def baseEnd_8294100 : Nat := 4258859896456104529306135

theorem tailTrace_8294100 : CollatzResearch.WordTrace tailWord_8294100 prefixEnd_8294100 4258859896456104529306135 := by
  unfold tailWord_8294100
  simp only [CollatzResearch.WordTrace]
  refine ⟨151255339625949847175115877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 201673786167933129566821169 151255339625949847175115877)
  ·
    refine ⟨28360376179865596345334227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 151255339625949847175115877 28360376179865596345334227)
    ·
      refine ⟨42540564269798394518001341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28360376179865596345334227 42540564269798394518001341)
      ·
        refine ⟨15952711601174397944250503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42540564269798394518001341 15952711601174397944250503)
        ·
          refine ⟨23929067401761596916375755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15952711601174397944250503 23929067401761596916375755)
          ·
            refine ⟨35893601102642395374563633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23929067401761596916375755 35893601102642395374563633)
            ·
              refine ⟨26920200826981796530922725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35893601102642395374563633 26920200826981796530922725)
              ·
                refine ⟨5047537655059086849548011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26920200826981796530922725 5047537655059086849548011)
                ·
                  refine ⟨7571306482588630274322017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5047537655059086849548011 7571306482588630274322017)
                  ·
                    refine ⟨5678479861941472705741513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7571306482588630274322017 5678479861941472705741513)
                    ·
                      refine ⟨4258859896456104529306135, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5678479861941472705741513 4258859896456104529306135)
                      ·
                        rfl

theorem cell23_8294100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 1, 2, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 1, 2, 4, 1, 2, 2].length) (baseStart_8294100 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8294100 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8294100 prefixEnd_8294100 := by exact prefixLift 8294100
  have htrace : WordTrace (prefixWord ++ tailWord_8294100) baseStart_8294100 baseEnd_8294100 := by
    simpa [prefixWord, tailWord_8294100, baseEnd_8294100] using wordTrace_append hprefix tailTrace_8294100
  have hstable : (prefixWord ++ tailWord_8294100).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8294100).length < 2 ^ (prefixWord ++ tailWord_8294100).sum := by decide
  have hdescent : baseEnd_8294100 < baseStart_8294100 := by decide
  rcases family_descends (prefixWord ++ tailWord_8294100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8294122 : List Nat := [3, 1, 3, 1, 1, 1, 2, 2, 2, 3, 4]
def baseStart_8294122 : Nat := 118140960795 + 8294122 * 2 ^ 59
def prefixEnd_8294122 : Nat := 4983230072969 + 3 ^ 40 * 8294122 * 2
def baseEnd_8294122 : Nat := 4258871193030503443231033

theorem tailTrace_8294122 : CollatzResearch.WordTrace tailWord_8294122 prefixEnd_8294122 4258871193030503443231033 := by
  unfold tailWord_8294122
  simp only [CollatzResearch.WordTrace]
  refine ⟨75627870414454998026883155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 201674321105213328071688413 75627870414454998026883155)
  ·
    refine ⟨113441805621682497040324733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75627870414454998026883155 113441805621682497040324733)
    ·
      refine ⟨42540677108130936390121775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 113441805621682497040324733 42540677108130936390121775)
      ·
        refine ⟨63811015662196404585182663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42540677108130936390121775 63811015662196404585182663)
        ·
          refine ⟨95716523493294606877773995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63811015662196404585182663 95716523493294606877773995)
          ·
            refine ⟨143574785239941910316660993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 95716523493294606877773995 143574785239941910316660993)
            ·
              refine ⟨107681088929956432737495745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 143574785239941910316660993 107681088929956432737495745)
              ·
                refine ⟨80760816697467324553121809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 107681088929956432737495745 80760816697467324553121809)
                ·
                  refine ⟨60570612523100493414841357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 80760816697467324553121809 60570612523100493414841357)
                  ·
                    refine ⟨22713979696162685030565509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 60570612523100493414841357 22713979696162685030565509)
                    ·
                      refine ⟨4258871193030503443231033, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22713979696162685030565509 4258871193030503443231033)
                      ·
                        rfl

theorem cell23_8294122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 2, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 2, 2, 2, 3, 4].length) (baseStart_8294122 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8294122 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8294122 prefixEnd_8294122 := by exact prefixLift 8294122
  have htrace : WordTrace (prefixWord ++ tailWord_8294122) baseStart_8294122 baseEnd_8294122 := by
    simpa [prefixWord, tailWord_8294122, baseEnd_8294122] using wordTrace_append hprefix tailTrace_8294122
  have hstable : (prefixWord ++ tailWord_8294122).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8294122).length < 2 ^ (prefixWord ++ tailWord_8294122).sum := by decide
  have hdescent : baseEnd_8294122 < baseStart_8294122 := by decide
  rcases family_descends (prefixWord ++ tailWord_8294122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8294156 : List Nat := [2, 2, 1, 2, 2, 1, 4, 1, 4, 2, 2]
def baseStart_8294156 : Nat := 118140960795 + 8294156 * 2 ^ 59
def prefixEnd_8294156 : Nat := 4983230072969 + 3 ^ 40 * 8294156 * 2
def baseEnd_8294156 : Nat := 4258888651372756310205877

theorem tailTrace_8294156 : CollatzResearch.WordTrace tailWord_8294156 prefixEnd_8294156 4258888651372756310205877 := by
  unfold tailWord_8294156
  simp only [CollatzResearch.WordTrace]
  refine ⟨151256360869848407957135161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 201675147826464543942846881 151256360869848407957135161)
  ·
    refine ⟨113442270652386305967851371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 151256360869848407957135161 113442270652386305967851371)
    ·
      refine ⟨170163405978579458951777057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113442270652386305967851371 170163405978579458951777057)
      ·
        refine ⟨127622554483934594213832793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 170163405978579458951777057 127622554483934594213832793)
        ·
          refine ⟨95716915862950945660374595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 127622554483934594213832793 95716915862950945660374595)
          ·
            refine ⟨143575373794426418490561893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 95716915862950945660374595 143575373794426418490561893)
            ·
              refine ⟨26920382586454953466980355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 143575373794426418490561893 26920382586454953466980355)
              ·
                refine ⟨40380573879682430200470533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26920382586454953466980355 40380573879682430200470533)
                ·
                  refine ⟨7571357602440455662588225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 40380573879682430200470533 7571357602440455662588225)
                  ·
                    refine ⟨5678518201830341746941169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7571357602440455662588225 5678518201830341746941169)
                    ·
                      refine ⟨4258888651372756310205877, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5678518201830341746941169 4258888651372756310205877)
                      ·
                        rfl

theorem cell23_8294156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 4, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 4, 1, 4, 2, 2].length) (baseStart_8294156 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8294156 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8294156 prefixEnd_8294156 := by exact prefixLift 8294156
  have htrace : WordTrace (prefixWord ++ tailWord_8294156) baseStart_8294156 baseEnd_8294156 := by
    simpa [prefixWord, tailWord_8294156, baseEnd_8294156] using wordTrace_append hprefix tailTrace_8294156
  have hstable : (prefixWord ++ tailWord_8294156).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8294156).length < 2 ^ (prefixWord ++ tailWord_8294156).sum := by decide
  have hdescent : baseEnd_8294156 < baseStart_8294156 := by decide
  rcases family_descends (prefixWord ++ tailWord_8294156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8294222 : List Nat := [4, 1, 1, 1, 1, 1, 1, 1, 4, 8]
def baseStart_8294222 : Nat := 118140960795 + 8294222 * 2 ^ 59
def prefixEnd_8294222 : Nat := 4983230072969 + 3 ^ 40 * 8294222 * 2
def baseEnd_8294222 : Nat := 1419640847031984350660191

theorem tailTrace_8294222 : CollatzResearch.WordTrace tailWord_8294222 prefixEnd_8294222 1419640847031984350660191 := by
  unfold tailWord_8294222
  simp only [CollatzResearch.WordTrace]
  refine ⟨37814391119682213648271615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 201676752638305139457448613 37814391119682213648271615)
  ·
    refine ⟨56721586679523320472407423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37814391119682213648271615 56721586679523320472407423)
    ·
      refine ⟨85082380019284980708611135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56721586679523320472407423 85082380019284980708611135)
      ·
        refine ⟨127623570028927471062916703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85082380019284980708611135 127623570028927471062916703)
        ·
          refine ⟨191435355043391206594375055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 127623570028927471062916703 191435355043391206594375055)
          ·
            refine ⟨287153032565086809891562583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 191435355043391206594375055 287153032565086809891562583)
            ·
              refine ⟨430729548847630214837343875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 287153032565086809891562583 430729548847630214837343875)
              ·
                refine ⟨646094323271445322256015813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 430729548847630214837343875 646094323271445322256015813)
                ·
                  refine ⟨121142685613395997923002965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 646094323271445322256015813 121142685613395997923002965)
                  ·
                    refine ⟨1419640847031984350660191, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 121142685613395997923002965 1419640847031984350660191)
                    ·
                      rfl

theorem cell23_8294222_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 1, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 1, 1, 4, 8].length) (baseStart_8294222 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8294222 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8294222 prefixEnd_8294222 := by exact prefixLift 8294222
  have htrace : WordTrace (prefixWord ++ tailWord_8294222) baseStart_8294222 baseEnd_8294222 := by
    simpa [prefixWord, tailWord_8294222, baseEnd_8294222] using wordTrace_append hprefix tailTrace_8294222
  have hstable : (prefixWord ++ tailWord_8294222).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8294222).length < 2 ^ (prefixWord ++ tailWord_8294222).sum := by decide
  have hdescent : baseEnd_8294222 < baseStart_8294222 := by decide
  rcases family_descends (prefixWord ++ tailWord_8294222) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8294239 : List Nat := [1, 1, 2, 3, 1, 4, 1, 1, 5, 4]
def baseStart_8294239 : Nat := 118140960795 + 8294239 * 2 ^ 59
def prefixEnd_8294239 : Nat := 4983230072969 + 3 ^ 40 * 8294239 * 2
def baseEnd_8294239 : Nat := 1419643756755693161822665

theorem tailTrace_8294239 : CollatzResearch.WordTrace tailWord_8294239 prefixEnd_8294239 1419643756755693161822665 := by
  unfold tailWord_8294239
  simp only [CollatzResearch.WordTrace]
  refine ⟨302515748998396121089541771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201677165998930747393027847 302515748998396121089541771)
  ·
    refine ⟨453773623497594181634312657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 302515748998396121089541771 453773623497594181634312657)
    ·
      refine ⟨340330217623195636225734493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 453773623497594181634312657 340330217623195636225734493)
      ·
        refine ⟨127623831608698363584650435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 340330217623195636225734493 127623831608698363584650435)
        ·
          refine ⟨191435747413047545376975653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 127623831608698363584650435 191435747413047545376975653)
          ·
            refine ⟨35894202639946414758182935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 191435747413047545376975653 35894202639946414758182935)
            ·
              refine ⟨53841303959919622137274403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35894202639946414758182935 53841303959919622137274403)
              ·
                refine ⟨80761955939879433205911605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53841303959919622137274403 80761955939879433205911605)
                ·
                  refine ⟨7571433369363696863054213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 80761955939879433205911605 7571433369363696863054213)
                  ·
                    refine ⟨1419643756755693161822665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7571433369363696863054213 1419643756755693161822665)
                    ·
                      rfl

theorem cell23_8294239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 4, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 4, 1, 1, 5, 4].length) (baseStart_8294239 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8294239 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8294239 prefixEnd_8294239 := by exact prefixLift 8294239
  have htrace : WordTrace (prefixWord ++ tailWord_8294239) baseStart_8294239 baseEnd_8294239 := by
    simpa [prefixWord, tailWord_8294239, baseEnd_8294239] using wordTrace_append hprefix tailTrace_8294239
  have hstable : (prefixWord ++ tailWord_8294239).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8294239).length < 2 ^ (prefixWord ++ tailWord_8294239).sum := by decide
  have hdescent : baseEnd_8294239 < baseStart_8294239 := by decide
  rcases family_descends (prefixWord ++ tailWord_8294239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8294243 : List Nat := [1, 1, 1, 5, 5, 1, 1, 1, 2, 5]
def baseStart_8294243 : Nat := 118140960795 + 8294243 * 2 ^ 59
def prefixEnd_8294243 : Nat := 4983230072969 + 3 ^ 40 * 8294243 * 2
def baseEnd_8294243 : Nat := 1419644441396565823272659

theorem tailTrace_8294243 : CollatzResearch.WordTrace tailWord_8294243 prefixEnd_8294243 1419644441396565823272659 := by
  unfold tailWord_8294243
  simp only [CollatzResearch.WordTrace]
  refine ⟨302515894890381629772687383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201677263260254419848458255 302515894890381629772687383)
  ·
    refine ⟨453773842335572444659031075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 302515894890381629772687383 453773842335572444659031075)
    ·
      refine ⟨680660763503358666988546613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 453773842335572444659031075 680660763503358666988546613)
      ·
        refine ⟨63811946578439875030176245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 680660763503358666988546613 63811946578439875030176245)
        ·
          refine ⟨5982369991728738284079023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 63811946578439875030176245 5982369991728738284079023)
          ·
            refine ⟨8973554987593107426118535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5982369991728738284079023 8973554987593107426118535)
            ·
              refine ⟨13460332481389661139177803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8973554987593107426118535 13460332481389661139177803)
              ·
                refine ⟨20190498722084491708766705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13460332481389661139177803 20190498722084491708766705)
                ·
                  refine ⟨15142874041563368781575029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20190498722084491708766705 15142874041563368781575029)
                  ·
                    refine ⟨1419644441396565823272659, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15142874041563368781575029 1419644441396565823272659)
                    ·
                      rfl

theorem cell23_8294243_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 5, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 5, 1, 1, 1, 2, 5].length) (baseStart_8294243 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8294243 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8294243 prefixEnd_8294243 := by exact prefixLift 8294243
  have htrace : WordTrace (prefixWord ++ tailWord_8294243) baseStart_8294243 baseEnd_8294243 := by
    simpa [prefixWord, tailWord_8294243, baseEnd_8294243] using wordTrace_append hprefix tailTrace_8294243
  have hstable : (prefixWord ++ tailWord_8294243).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8294243).length < 2 ^ (prefixWord ++ tailWord_8294243).sum := by decide
  have hdescent : baseEnd_8294243 < baseStart_8294243 := by decide
  rcases family_descends (prefixWord ++ tailWord_8294243) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8294272 : List Nat := [2, 1, 1, 2, 1, 2, 3, 1, 1, 1, 8]
def baseStart_8294272 : Nat := 118140960795 + 8294272 * 2 ^ 59
def prefixEnd_8294272 : Nat := 4983230072969 + 3 ^ 40 * 8294272 * 2
def baseEnd_8294272 : Nat := 4258948215128677856355343

theorem tailTrace_8294272 : CollatzResearch.WordTrace tailWord_8294272 prefixEnd_8294272 4258948215128677856355343 := by
  unfold tailWord_8294272
  simp only [CollatzResearch.WordTrace]
  refine ⟨151258476303638283862746535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 201677968404851045150328713 151258476303638283862746535)
  ·
    refine ⟨226887714455457425794119803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151258476303638283862746535 226887714455457425794119803)
    ·
      refine ⟨340331571683186138691179705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 226887714455457425794119803 340331571683186138691179705)
      ·
        refine ⟨255248678762389604018384779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 340331571683186138691179705 255248678762389604018384779)
        ·
          refine ⟨382873018143584406027577169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 255248678762389604018384779 382873018143584406027577169)
          ·
            refine ⟨287154763607688304520682877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 382873018143584406027577169 287154763607688304520682877)
            ·
              refine ⟨107683036352883114195256079, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 287154763607688304520682877 107683036352883114195256079)
              ·
                refine ⟨161524554529324671292884119, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 107683036352883114195256079 161524554529324671292884119)
                ·
                  refine ⟨242286831793987006939326179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 161524554529324671292884119 242286831793987006939326179)
                  ·
                    refine ⟨363430247690980510408989269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 242286831793987006939326179 363430247690980510408989269)
                    ·
                      refine ⟨4258948215128677856355343, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 363430247690980510408989269 4258948215128677856355343)
                      ·
                        rfl

theorem cell23_8294272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 3, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 3, 1, 1, 1, 8].length) (baseStart_8294272 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8294272 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8294272 prefixEnd_8294272 := by exact prefixLift 8294272
  have htrace : WordTrace (prefixWord ++ tailWord_8294272) baseStart_8294272 baseEnd_8294272 := by
    simpa [prefixWord, tailWord_8294272, baseEnd_8294272] using wordTrace_append hprefix tailTrace_8294272
  have hstable : (prefixWord ++ tailWord_8294272).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8294272).length < 2 ^ (prefixWord ++ tailWord_8294272).sum := by decide
  have hdescent : baseEnd_8294272 < baseStart_8294272 := by decide
  rcases family_descends (prefixWord ++ tailWord_8294272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8294313 : List Nat := [1, 2, 1, 1, 1, 1, 4, 7, 1, 1, 3]
def baseStart_8294313 : Nat := 118140960795 + 8294313 * 2 ^ 59
def prefixEnd_8294313 : Nat := 4983230072969 + 3 ^ 40 * 8294313 * 2
def baseEnd_8294313 : Nat := 4258969267835512195942655

theorem tailTrace_8294313 : CollatzResearch.WordTrace tailWord_8294313 prefixEnd_8294313 4258969267835512195942655 := by
  unfold tailWord_8294313
  simp only [CollatzResearch.WordTrace]
  refine ⟨302518448000128031727735593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201678965333418687818490395 302518448000128031727735593)
  ·
    refine ⟨226888836000096023795801695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 302518448000128031727735593 226888836000096023795801695)
    ·
      refine ⟨340333254000144035693702543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 226888836000096023795801695 340333254000144035693702543)
      ·
        refine ⟨510499881000216053540553815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 340333254000144035693702543 510499881000216053540553815)
        ·
          refine ⟨765749821500324080310830723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 510499881000216053540553815 765749821500324080310830723)
          ·
            refine ⟨1148624732250486120466246085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 765749821500324080310830723 1148624732250486120466246085)
            ·
              refine ⟨215367137296966147587421141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1148624732250486120466246085 215367137296966147587421141)
              ·
                refine ⟨5047667280397644084080183, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 215367137296966147587421141 5047667280397644084080183)
                ·
                  refine ⟨7571500920596466126120275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5047667280397644084080183 7571500920596466126120275)
                  ·
                    refine ⟨11357251380894699189180413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7571500920596466126120275 11357251380894699189180413)
                    ·
                      refine ⟨4258969267835512195942655, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11357251380894699189180413 4258969267835512195942655)
                      ·
                        rfl

theorem cell23_8294313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 4, 7, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 4, 7, 1, 1, 3].length) (baseStart_8294313 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8294313 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8294313 prefixEnd_8294313 := by exact prefixLift 8294313
  have htrace : WordTrace (prefixWord ++ tailWord_8294313) baseStart_8294313 baseEnd_8294313 := by
    simpa [prefixWord, tailWord_8294313, baseEnd_8294313] using wordTrace_append hprefix tailTrace_8294313
  have hstable : (prefixWord ++ tailWord_8294313).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8294313).length < 2 ^ (prefixWord ++ tailWord_8294313).sum := by decide
  have hdescent : baseEnd_8294313 < baseStart_8294313 := by decide
  rcases family_descends (prefixWord ++ tailWord_8294313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8294324 : List Nat := [2, 5, 2, 1, 2, 1, 3, 2, 1, 4]
def baseStart_8294324 : Nat := 118140960795 + 8294324 * 2 ^ 59
def prefixEnd_8294324 : Nat := 4983230072969 + 3 ^ 40 * 8294324 * 2
def baseEnd_8294324 : Nat := 1419658305374237217635035

theorem tailTrace_8294324 : CollatzResearch.WordTrace tailWord_8294324 prefixEnd_8294324 1419658305374237217635035 := by
  unfold tailWord_8294324
  simp only [CollatzResearch.WordTrace]
  refine ⟨151259424601544090303193013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 201679232802058787070924017 151259424601544090303193013)
  ·
    refine ⟨14180571056394758465924345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 151259424601544090303193013 14180571056394758465924345)
    ·
      refine ⟨10635428292296068849443259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14180571056394758465924345 10635428292296068849443259)
      ·
        refine ⟨15953142438444103274164889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10635428292296068849443259 15953142438444103274164889)
        ·
          refine ⟨11964856828833077455623667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15953142438444103274164889 11964856828833077455623667)
          ·
            refine ⟨17947285243249616183435501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11964856828833077455623667 17947285243249616183435501)
            ·
              refine ⟨6730231966218606068788313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17947285243249616183435501 6730231966218606068788313)
              ·
                refine ⟨5047673974663954551591235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6730231966218606068788313 5047673974663954551591235)
                ·
                  refine ⟨7571510961995931827386853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5047673974663954551591235 7571510961995931827386853)
                  ·
                    refine ⟨1419658305374237217635035, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7571510961995931827386853 1419658305374237217635035)
                    ·
                      rfl

theorem cell23_8294324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 2, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 2, 1, 3, 2, 1, 4].length) (baseStart_8294324 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8294324 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8294324 prefixEnd_8294324 := by exact prefixLift 8294324
  have htrace : WordTrace (prefixWord ++ tailWord_8294324) baseStart_8294324 baseEnd_8294324 := by
    simpa [prefixWord, tailWord_8294324, baseEnd_8294324] using wordTrace_append hprefix tailTrace_8294324
  have hstable : (prefixWord ++ tailWord_8294324).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8294324).length < 2 ^ (prefixWord ++ tailWord_8294324).sum := by decide
  have hdescent : baseEnd_8294324 < baseStart_8294324 := by decide
  rcases family_descends (prefixWord ++ tailWord_8294324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8294381 : List Nat := [1, 5, 1, 4, 1, 2, 2, 2, 1, 1, 3]
def baseStart_8294381 : Nat := 118140960795 + 8294381 * 2 ^ 59
def prefixEnd_8294381 : Nat := 4983230072969 + 3 ^ 40 * 8294381 * 2
def baseEnd_8294381 : Nat := 4259004184520017929892343

theorem tailTrace_8294381 : CollatzResearch.WordTrace tailWord_8294381 prefixEnd_8294381 4259004184520017929892343 := by
  unfold tailWord_8294381
  simp only [CollatzResearch.WordTrace]
  refine ⟨302520928163881679341210997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201680618775921119560807331 302520928163881679341210997)
  ·
    refine ⟨28361337015363907438238531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 302520928163881679341210997 28361337015363907438238531)
    ·
      refine ⟨42542005523045861157357797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28361337015363907438238531 42542005523045861157357797)
      ·
        refine ⟨7976626035571098967004587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 42542005523045861157357797 7976626035571098967004587)
        ·
          refine ⟨11964939053356648450506881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7976626035571098967004587 11964939053356648450506881)
          ·
            refine ⟨8973704290017486337880161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11964939053356648450506881 8973704290017486337880161)
            ·
              refine ⟨6730278217513114753410121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8973704290017486337880161 6730278217513114753410121)
              ·
                refine ⟨5047708663134836065057591, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6730278217513114753410121 5047708663134836065057591)
                ·
                  refine ⟨7571562994702254097586387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5047708663134836065057591 7571562994702254097586387)
                  ·
                    refine ⟨11357344492053381146379581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7571562994702254097586387 11357344492053381146379581)
                    ·
                      refine ⟨4259004184520017929892343, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11357344492053381146379581 4259004184520017929892343)
                      ·
                        rfl

theorem cell23_8294381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 1, 2, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 1, 2, 2, 2, 1, 1, 3].length) (baseStart_8294381 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8294381 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8294381 prefixEnd_8294381 := by exact prefixLift 8294381
  have htrace : WordTrace (prefixWord ++ tailWord_8294381) baseStart_8294381 baseEnd_8294381 := by
    simpa [prefixWord, tailWord_8294381, baseEnd_8294381] using wordTrace_append hprefix tailTrace_8294381
  have hstable : (prefixWord ++ tailWord_8294381).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8294381).length < 2 ^ (prefixWord ++ tailWord_8294381).sum := by decide
  have hdescent : baseEnd_8294381 < baseStart_8294381 := by decide
  rcases family_descends (prefixWord ++ tailWord_8294381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8294476 : List Nat := [2, 2, 1, 3, 1, 1, 2, 2, 1, 5, 3]
def baseStart_8294476 : Nat := 118140960795 + 8294476 * 2 ^ 59
def prefixEnd_8294476 : Nat := 4983230072969 + 3 ^ 40 * 8294476 * 2
def baseEnd_8294476 : Nat := 4259052965182195058204405

theorem tailTrace_8294476 : CollatzResearch.WordTrace tailWord_8294476 prefixEnd_8294476 4259052965182195058204405 := by
  unfold tailWord_8294476
  simp only [CollatzResearch.WordTrace]
  refine ⟨151262196549268755282959641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 201682928732358340377279521 151262196549268755282959641)
  ·
    refine ⟨113446647411951566462219731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 151262196549268755282959641 113446647411951566462219731)
    ·
      refine ⟨170169971117927349693329597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113446647411951566462219731 170169971117927349693329597)
      ·
        refine ⟨63813739169222756134998599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 170169971117927349693329597 63813739169222756134998599)
        ·
          refine ⟨95720608753834134202497899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63813739169222756134998599 95720608753834134202497899)
          ·
            refine ⟨143580913130751201303746849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 95720608753834134202497899 143580913130751201303746849)
            ·
              refine ⟨107685684848063400977810137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 143580913130751201303746849 107685684848063400977810137)
              ·
                refine ⟨80764263636047550733357603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 107685684848063400977810137 80764263636047550733357603)
                ·
                  refine ⟨121146395454071326100036405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 80764263636047550733357603 121146395454071326100036405)
                  ·
                    refine ⟨11357474573819186821878413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 121146395454071326100036405 11357474573819186821878413)
                    ·
                      refine ⟨4259052965182195058204405, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11357474573819186821878413 4259052965182195058204405)
                      ·
                        rfl

theorem cell23_8294476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 2, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 2, 2, 1, 5, 3].length) (baseStart_8294476 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8294476 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8294476 prefixEnd_8294476 := by exact prefixLift 8294476
  have htrace : WordTrace (prefixWord ++ tailWord_8294476) baseStart_8294476 baseEnd_8294476 := by
    simpa [prefixWord, tailWord_8294476, baseEnd_8294476] using wordTrace_append hprefix tailTrace_8294476
  have hstable : (prefixWord ++ tailWord_8294476).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8294476).length < 2 ^ (prefixWord ++ tailWord_8294476).sum := by decide
  have hdescent : baseEnd_8294476 < baseStart_8294476 := by decide
  rcases family_descends (prefixWord ++ tailWord_8294476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8294496 : List Nat := [2, 1, 1, 3, 2, 3, 1, 1, 4, 5]
def baseStart_8294496 : Nat := 118140960795 + 8294496 * 2 ^ 59
def prefixEnd_8294496 : Nat := 4983230072969 + 3 ^ 40 * 8294496 * 2
def baseEnd_8294496 : Nat := 1419687744931761659984771

theorem tailTrace_8294496 : CollatzResearch.WordTrace tailWord_8294496 prefixEnd_8294496 1419687744931761659984771 := by
  unfold tailWord_8294496
  simp only [CollatzResearch.WordTrace]
  refine ⟨151262561279232526990823671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 201683415038976702654431561 151262561279232526990823671)
  ·
    refine ⟨226893841918848790486235507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151262561279232526990823671 226893841918848790486235507)
    ·
      refine ⟨340340762878273185729353261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 226893841918848790486235507 340340762878273185729353261)
      ·
        refine ⟨127627786079352444648507473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 340340762878273185729353261 127627786079352444648507473)
        ·
          refine ⟨95720839559514333486380605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 127627786079352444648507473 95720839559514333486380605)
          ·
            refine ⟨35895314834817875057392727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 95720839559514333486380605 35895314834817875057392727)
            ·
              refine ⟨53842972252226812586089091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35895314834817875057392727 53842972252226812586089091)
              ·
                refine ⟨80764458378340218879133637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53842972252226812586089091 80764458378340218879133637)
                ·
                  refine ⟨15143335945938791039837557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 80764458378340218879133637 15143335945938791039837557)
                  ·
                    refine ⟨1419687744931761659984771, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15143335945938791039837557 1419687744931761659984771)
                    ·
                      rfl

theorem cell23_8294496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 3, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 3, 1, 1, 4, 5].length) (baseStart_8294496 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8294496 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8294496 prefixEnd_8294496 := by exact prefixLift 8294496
  have htrace : WordTrace (prefixWord ++ tailWord_8294496) baseStart_8294496 baseEnd_8294496 := by
    simpa [prefixWord, tailWord_8294496, baseEnd_8294496] using wordTrace_append hprefix tailTrace_8294496
  have hstable : (prefixWord ++ tailWord_8294496).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8294496).length < 2 ^ (prefixWord ++ tailWord_8294496).sum := by decide
  have hdescent : baseEnd_8294496 < baseStart_8294496 := by decide
  rcases family_descends (prefixWord ++ tailWord_8294496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8294503 : List Nat := [1, 1, 5, 1, 1, 2, 2, 1, 2, 5, 2]
def baseStart_8294503 : Nat := 118140960795 + 8294503 * 2 ^ 59
def prefixEnd_8294503 : Nat := 4983230072969 + 3 ^ 40 * 8294503 * 2
def baseEnd_8294503 : Nat := 4259066829159866452566781

theorem tailTrace_8294503 : CollatzResearch.WordTrace tailWord_8294503 prefixEnd_8294503 4259066829159866452566781 := by
  unfold tailWord_8294503
  simp only [CollatzResearch.WordTrace]
  refine ⟨302525377869439694177152163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201683585246293129451434775 302525377869439694177152163)
  ·
    refine ⟨453788066804159541265728245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 302525377869439694177152163 453788066804159541265728245)
    ·
      refine ⟨42542631262889956993662023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 453788066804159541265728245 42542631262889956993662023)
      ·
        refine ⟨63813946894334935490493035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42542631262889956993662023 63813946894334935490493035)
        ·
          refine ⟨95720920341502403235739553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63813946894334935490493035 95720920341502403235739553)
          ·
            refine ⟨71790690256126802426804665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 95720920341502403235739553 71790690256126802426804665)
            ·
              refine ⟨53843017692095101820103499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 71790690256126802426804665 53843017692095101820103499)
              ·
                refine ⟨80764526538142652730155249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53843017692095101820103499 80764526538142652730155249)
                ·
                  refine ⟨60573394903606989547616437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 80764526538142652730155249 60573394903606989547616437)
                  ·
                    refine ⟨5678755772213155270089041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 60573394903606989547616437 5678755772213155270089041)
                    ·
                      refine ⟨4259066829159866452566781, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5678755772213155270089041 4259066829159866452566781)
                      ·
                        rfl

theorem cell23_8294503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 2, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 2, 1, 2, 5, 2].length) (baseStart_8294503 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8294503 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8294503 prefixEnd_8294503 := by exact prefixLift 8294503
  have htrace : WordTrace (prefixWord ++ tailWord_8294503) baseStart_8294503 baseEnd_8294503 := by
    simpa [prefixWord, tailWord_8294503, baseEnd_8294503] using wordTrace_append hprefix tailTrace_8294503
  have hstable : (prefixWord ++ tailWord_8294503).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8294503).length < 2 ^ (prefixWord ++ tailWord_8294503).sum := by decide
  have hdescent : baseEnd_8294503 < baseStart_8294503 := by decide
  rcases family_descends (prefixWord ++ tailWord_8294503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8294533 : List Nat := [1, 3, 1, 1, 5, 1, 1, 3, 2, 1, 4]
def baseStart_8294533 : Nat := 118140960795 + 8294533 * 2 ^ 59
def prefixEnd_8294533 : Nat := 4983230072969 + 3 ^ 40 * 8294533 * 2
def baseEnd_8294533 : Nat := 4259082233579501335191643

theorem tailTrace_8294533 : CollatzResearch.WordTrace tailWord_8294533 prefixEnd_8294533 4259082233579501335191643 := by
  unfold tailWord_8294533
  simp only [CollatzResearch.WordTrace]
  refine ⟨302526472059331009300744253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201684314706220672867162835 302526472059331009300744253)
  ·
    refine ⟨113447427022249128487779095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 302526472059331009300744253 113447427022249128487779095)
    ·
      refine ⟨170171140533373692731668643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113447427022249128487779095 170171140533373692731668643)
      ·
        refine ⟨255256710800060539097502965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 170171140533373692731668643 255256710800060539097502965)
        ·
          refine ⟨23930316637505675540390903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 255256710800060539097502965 23930316637505675540390903)
          ·
            refine ⟨35895474956258513310586355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23930316637505675540390903 35895474956258513310586355)
            ·
              refine ⟨53843212434387769965879533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35895474956258513310586355 53843212434387769965879533)
              ·
                refine ⟨20191204662895413737204825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 53843212434387769965879533 20191204662895413737204825)
                ·
                  refine ⟨15143403497171560302903619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20191204662895413737204825 15143403497171560302903619)
                  ·
                    refine ⟨22715105245757340454355429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15143403497171560302903619 22715105245757340454355429)
                    ·
                      refine ⟨4259082233579501335191643, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22715105245757340454355429 4259082233579501335191643)
                      ·
                        rfl

theorem cell23_8294533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 1, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 1, 1, 3, 2, 1, 4].length) (baseStart_8294533 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8294533 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8294533 prefixEnd_8294533 := by exact prefixLift 8294533
  have htrace : WordTrace (prefixWord ++ tailWord_8294533) baseStart_8294533 baseEnd_8294533 := by
    simpa [prefixWord, tailWord_8294533, baseEnd_8294533] using wordTrace_append hprefix tailTrace_8294533
  have hstable : (prefixWord ++ tailWord_8294533).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8294533).length < 2 ^ (prefixWord ++ tailWord_8294533).sum := by decide
  have hdescent : baseEnd_8294533 < baseStart_8294533 := by decide
  rcases family_descends (prefixWord ++ tailWord_8294533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8294567 : List Nat := [1, 1, 6, 2, 2, 1, 1, 1, 2, 4, 2]
def baseStart_8294567 : Nat := 118140960795 + 8294567 * 2 ^ 59
def prefixEnd_8294567 : Nat := 4983230072969 + 3 ^ 40 * 8294567 * 2
def baseEnd_8294567 : Nat := 4259099691921754202166487

theorem tailTrace_8294567 : CollatzResearch.WordTrace tailWord_8294567 prefixEnd_8294567 4259099691921754202166487 := by
  unfold tailWord_8294567
  simp only [CollatzResearch.WordTrace]
  refine ⟨302527712141207833107481955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201685141427471888738321303 302527712141207833107481955)
  ·
    refine ⟨453791568211811749661222933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 302527712141207833107481955 453791568211811749661222933)
    ·
      refine ⟨21271479759928675765369825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 453791568211811749661222933 21271479759928675765369825)
      ·
        refine ⟨15953609819946506824027369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21271479759928675765369825 15953609819946506824027369)
        ·
          refine ⟨11965207364959880118020527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15953609819946506824027369 11965207364959880118020527)
          ·
            refine ⟨17947811047439820177030791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11965207364959880118020527 17947811047439820177030791)
            ·
              refine ⟨26921716571159730265546187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17947811047439820177030791 26921716571159730265546187)
              ·
                refine ⟨40382574856739595398319281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26921716571159730265546187 40382574856739595398319281)
                ·
                  refine ⟨30286931142554696548739461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40382574856739595398319281 30286931142554696548739461)
                  ·
                    refine ⟨5678799589229005602888649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 30286931142554696548739461 5678799589229005602888649)
                    ·
                      refine ⟨4259099691921754202166487, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5678799589229005602888649 4259099691921754202166487)
                      ·
                        rfl

theorem cell23_8294567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 2, 1, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 2, 1, 1, 1, 2, 4, 2].length) (baseStart_8294567 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8294567 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8294567 prefixEnd_8294567 := by exact prefixLift 8294567
  have htrace : WordTrace (prefixWord ++ tailWord_8294567) baseStart_8294567 baseEnd_8294567 := by
    simpa [prefixWord, tailWord_8294567, baseEnd_8294567] using wordTrace_append hprefix tailTrace_8294567
  have hstable : (prefixWord ++ tailWord_8294567).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8294567).length < 2 ^ (prefixWord ++ tailWord_8294567).sum := by decide
  have hdescent : baseEnd_8294567 < baseStart_8294567 := by decide
  rcases family_descends (prefixWord ++ tailWord_8294567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8294603 : List Nat := [1, 1, 1, 1, 3, 2, 5, 3, 1, 5]
def baseStart_8294603 : Nat := 118140960795 + 8294603 * 2 ^ 59
def prefixEnd_8294603 : Nat := 4983230072969 + 3 ^ 40 * 8294603 * 2
def baseEnd_8294603 : Nat := 1419706059075105353772107

theorem tailTrace_8294603 : CollatzResearch.WordTrace tailWord_8294603 prefixEnd_8294603 1419706059075105353772107 := by
  unfold tailWord_8294603
  simp only [CollatzResearch.WordTrace]
  refine ⟨302529025169077411255792463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201686016779384940837194975 302529025169077411255792463)
  ·
    refine ⟨453793537753616116883688695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 302529025169077411255792463 453793537753616116883688695)
    ·
      refine ⟨680690306630424175325533043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 453793537753616116883688695 680690306630424175325533043)
      ·
        refine ⟨1021035459945636262988299565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 680690306630424175325533043 1021035459945636262988299565)
        ·
          refine ⟨382888297479613598620612337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1021035459945636262988299565 382888297479613598620612337)
          ·
            refine ⟨287166223109710198965459253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 382888297479613598620612337 287166223109710198965459253)
            ·
              refine ⟨26921833416535331153011805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 287166223109710198965459253 26921833416535331153011805)
              ·
                refine ⟨10095687531200749182379427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26921833416535331153011805 10095687531200749182379427)
                ·
                  refine ⟨15143531296801123773569141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10095687531200749182379427 15143531296801123773569141)
                  ·
                    refine ⟨1419706059075105353772107, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15143531296801123773569141 1419706059075105353772107)
                    ·
                      rfl

theorem cell23_8294603_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 5, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 5, 3, 1, 5].length) (baseStart_8294603 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8294603 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8294603 prefixEnd_8294603 := by exact prefixLift 8294603
  have htrace : WordTrace (prefixWord ++ tailWord_8294603) baseStart_8294603 baseEnd_8294603 := by
    simpa [prefixWord, tailWord_8294603, baseEnd_8294603] using wordTrace_append hprefix tailTrace_8294603
  have hstable : (prefixWord ++ tailWord_8294603).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8294603).length < 2 ^ (prefixWord ++ tailWord_8294603).sum := by decide
  have hdescent : baseEnd_8294603 < baseStart_8294603 := by decide
  rcases family_descends (prefixWord ++ tailWord_8294603) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8294617 : List Nat := [1, 2, 1, 2, 3, 1, 4, 4, 1, 1, 3]
def baseStart_8294617 : Nat := 118140960795 + 8294617 * 2 ^ 59
def prefixEnd_8294617 : Nat := 4983230072969 + 3 ^ 40 * 8294617 * 2
def baseEnd_8294617 : Nat := 4259125365954479006541257

theorem tailTrace_8294617 : CollatzResearch.WordTrace tailWord_8294617 prefixEnd_8294617 4259125365954479006541257 := by
  unfold tailWord_8294617
  simp only [CollatzResearch.WordTrace]
  refine ⟨302529535791026691646802105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201686357194017794431201403 302529535791026691646802105)
  ·
    refine ⟨226897151843270018735101579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 302529535791026691646802105 226897151843270018735101579)
    ·
      refine ⟨340345727764905028102652369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 226897151843270018735101579 340345727764905028102652369)
      ·
        refine ⟨255259295823678771076989277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 340345727764905028102652369 255259295823678771076989277)
        ·
          refine ⟨95722235933879539153870979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 255259295823678771076989277 95722235933879539153870979)
          ·
            refine ⟨143583353900819308730806469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 95722235933879539153870979 143583353900819308730806469)
            ·
              refine ⟨26921878856403620387026213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 143583353900819308730806469 26921878856403620387026213)
              ·
                refine ⟨5047852285575678822567415, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26921878856403620387026213 5047852285575678822567415)
                ·
                  refine ⟨7571778428363518233851123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5047852285575678822567415 7571778428363518233851123)
                  ·
                    refine ⟨11357667642545277350776685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7571778428363518233851123 11357667642545277350776685)
                    ·
                      refine ⟨4259125365954479006541257, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11357667642545277350776685 4259125365954479006541257)
                      ·
                        rfl

theorem cell23_8294617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 4, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 4, 4, 1, 1, 3].length) (baseStart_8294617 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8294617 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8294617 prefixEnd_8294617 := by exact prefixLift 8294617
  have htrace : WordTrace (prefixWord ++ tailWord_8294617) baseStart_8294617 baseEnd_8294617 := by
    simpa [prefixWord, tailWord_8294617, baseEnd_8294617] using wordTrace_append hprefix tailTrace_8294617
  have hstable : (prefixWord ++ tailWord_8294617).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8294617).length < 2 ^ (prefixWord ++ tailWord_8294617).sum := by decide
  have hdescent : baseEnd_8294617 < baseStart_8294617 := by decide
  rcases family_descends (prefixWord ++ tailWord_8294617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8294637 : List Nat := [1, 5, 1, 2, 3, 1, 2, 2, 1, 5]
def baseStart_8294637 : Nat := 118140960795 + 8294637 * 2 ^ 59
def prefixEnd_8294637 : Nat := 4983230072969 + 3 ^ 40 * 8294637 * 2
def baseEnd_8294637 : Nat := 1419711878522522976097055

theorem tailTrace_8294637 : CollatzResearch.WordTrace tailWord_8294637 prefixEnd_8294637 1419711878522522976097055 := by
  unfold tailWord_8294637
  simp only [CollatzResearch.WordTrace]
  refine ⟨302530265250954235062530165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201686843500636156708353443 302530265250954235062530165)
  ·
    refine ⟨28362212367276959537112203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 302530265250954235062530165 28362212367276959537112203)
    ·
      refine ⟨42543318550915439305668305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28362212367276959537112203 42543318550915439305668305)
      ·
        refine ⟨31907488913186579479251229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42543318550915439305668305 31907488913186579479251229)
        ·
          refine ⟨11965308342444967304719211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31907488913186579479251229 11965308342444967304719211)
          ·
            refine ⟨17947962513667450957078817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11965308342444967304719211 17947962513667450957078817)
            ·
              refine ⟨13460971885250588217809113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17947962513667450957078817 13460971885250588217809113)
              ·
                refine ⟨10095728913937941163356835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13460971885250588217809113 10095728913937941163356835)
                ·
                  refine ⟨15143593370906911745035253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10095728913937941163356835 15143593370906911745035253)
                  ·
                    refine ⟨1419711878522522976097055, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15143593370906911745035253 1419711878522522976097055)
                    ·
                      rfl

theorem cell23_8294637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 3, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 3, 1, 2, 2, 1, 5].length) (baseStart_8294637 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8294637 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8294637 prefixEnd_8294637 := by exact prefixLift 8294637
  have htrace : WordTrace (prefixWord ++ tailWord_8294637) baseStart_8294637 baseEnd_8294637 := by
    simpa [prefixWord, tailWord_8294637, baseEnd_8294637] using wordTrace_append hprefix tailTrace_8294637
  have hstable : (prefixWord ++ tailWord_8294637).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8294637).length < 2 ^ (prefixWord ++ tailWord_8294637).sum := by decide
  have hdescent : baseEnd_8294637 < baseStart_8294637 := by decide
  rcases family_descends (prefixWord ++ tailWord_8294637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8294653 : List Nat := [1, 4, 1, 1, 1, 1, 1, 6, 1, 2, 4]
def baseStart_8294653 : Nat := 118140960795 + 8294653 * 2 ^ 59
def prefixEnd_8294653 : Nat := 4983230072969 + 3 ^ 40 * 8294653 * 2
def baseEnd_8294653 : Nat := 4259143851258040865691091

theorem tailTrace_8294653 : CollatzResearch.WordTrace tailWord_8294653 prefixEnd_8294653 4259143851258040865691091 := by
  unfold tailWord_8294653
  simp only [CollatzResearch.WordTrace]
  refine ⟨302530848818896269795112613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201687232545930846530075075 302530848818896269795112613)
  ·
    refine ⟨56724534153543050586583615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 302530848818896269795112613 56724534153543050586583615)
    ·
      refine ⟨85086801230314575879875423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56724534153543050586583615 85086801230314575879875423)
      ·
        refine ⟨127630201845471863819813135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85086801230314575879875423 127630201845471863819813135)
        ·
          refine ⟨191445302768207795729719703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 127630201845471863819813135 191445302768207795729719703)
          ·
            refine ⟨287167954152311693594579555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 191445302768207795729719703 287167954152311693594579555)
            ·
              refine ⟨430751931228467540391869333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 287167954152311693594579555 430751931228467540391869333)
              ·
                refine ⟨20191496776334415955868875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 430751931228467540391869333 20191496776334415955868875)
                ·
                  refine ⟨30287245164501623933803313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20191496776334415955868875 30287245164501623933803313)
                  ·
                    refine ⟨22715433873376217950352485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 30287245164501623933803313 22715433873376217950352485)
                    ·
                      refine ⟨4259143851258040865691091, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22715433873376217950352485 4259143851258040865691091)
                      ·
                        rfl

theorem cell23_8294653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 1, 6, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 1, 6, 1, 2, 4].length) (baseStart_8294653 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8294653 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8294653 prefixEnd_8294653 := by exact prefixLift 8294653
  have htrace : WordTrace (prefixWord ++ tailWord_8294653) baseStart_8294653 baseEnd_8294653 := by
    simpa [prefixWord, tailWord_8294653, baseEnd_8294653] using wordTrace_append hprefix tailTrace_8294653
  have hstable : (prefixWord ++ tailWord_8294653).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8294653).length < 2 ^ (prefixWord ++ tailWord_8294653).sum := by decide
  have hdescent : baseEnd_8294653 < baseStart_8294653 := by decide
  rcases family_descends (prefixWord ++ tailWord_8294653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8294740 : List Nat := [2, 4, 1, 1, 2, 3, 1, 1, 2, 6]
def baseStart_8294740 : Nat := 118140960795 + 8294740 * 2 ^ 59
def prefixEnd_8294740 : Nat := 4983230072969 + 3 ^ 40 * 8294740 * 2
def baseEnd_8294740 : Nat := 1419729508024994008434397

theorem tailTrace_8294740 : CollatzResearch.WordTrace tailWord_8294740 prefixEnd_8294740 1419729508024994008434397 := by
  unfold tailWord_8294740
  simp only [CollatzResearch.WordTrace]
  refine ⟨151267010984790541826764837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 201689347979720722435686449 151267010984790541826764837)
  ·
    refine ⟨28362564559648226592518407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 151267010984790541826764837 28362564559648226592518407)
    ·
      refine ⟨42543846839472339888777611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28362564559648226592518407 42543846839472339888777611)
      ·
        refine ⟨63815770259208509833166417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42543846839472339888777611 63815770259208509833166417)
        ·
          refine ⟨47861827694406382374874813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63815770259208509833166417 47861827694406382374874813)
          ·
            refine ⟨17948185385402393390578055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 47861827694406382374874813 17948185385402393390578055)
            ·
              refine ⟨26922278078103590085867083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17948185385402393390578055 26922278078103590085867083)
              ·
                refine ⟨40383417117155385128800625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26922278078103590085867083 40383417117155385128800625)
                ·
                  refine ⟨30287562837866538846600469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40383417117155385128800625 30287562837866538846600469)
                  ·
                    refine ⟨1419729508024994008434397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 30287562837866538846600469 1419729508024994008434397)
                    ·
                      rfl

theorem cell23_8294740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 3, 1, 1, 2, 6].length) (baseStart_8294740 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8294740 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8294740 prefixEnd_8294740 := by exact prefixLift 8294740
  have htrace : WordTrace (prefixWord ++ tailWord_8294740) baseStart_8294740 baseEnd_8294740 := by
    simpa [prefixWord, tailWord_8294740, baseEnd_8294740] using wordTrace_append hprefix tailTrace_8294740
  have hstable : (prefixWord ++ tailWord_8294740).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8294740).length < 2 ^ (prefixWord ++ tailWord_8294740).sum := by decide
  have hdescent : baseEnd_8294740 < baseStart_8294740 := by decide
  rcases family_descends (prefixWord ++ tailWord_8294740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8294781 : List Nat := [1, 4, 1, 1, 2, 5, 1, 2, 2, 2, 2]
def baseStart_8294781 : Nat := 118140960795 + 8294781 * 2 ^ 59
def prefixEnd_8294781 : Nat := 4983230072969 + 3 ^ 40 * 8294781 * 2
def baseEnd_8294781 : Nat := 4259209576781816364890503

theorem tailTrace_8294781 : CollatzResearch.WordTrace tailWord_8294781 prefixEnd_8294781 4259209576781816364890503 := by
  unfold tailWord_8294781
  simp only [CollatzResearch.WordTrace]
  refine ⟨302535517362432547655772197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201690344908288365103848131 302535517362432547655772197)
  ·
    refine ⟨56725409505456102685457287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 302535517362432547655772197 56725409505456102685457287)
    ·
      refine ⟨85088114258184154028185931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56725409505456102685457287 85088114258184154028185931)
      ·
        refine ⟨127632171387276231042278897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85088114258184154028185931 127632171387276231042278897)
        ·
          refine ⟨95724128540457173281709173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 127632171387276231042278897 95724128540457173281709173)
          ·
            refine ⟨8974137050667859995160235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 95724128540457173281709173 8974137050667859995160235)
            ·
              refine ⟨13461205576001789992740353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8974137050667859995160235 13461205576001789992740353)
              ·
                refine ⟨10095904182001342494555265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13461205576001789992740353 10095904182001342494555265)
                ·
                  refine ⟨7571928136501006870916449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10095904182001342494555265 7571928136501006870916449)
                  ·
                    refine ⟨5678946102375755153187337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7571928136501006870916449 5678946102375755153187337)
                    ·
                      refine ⟨4259209576781816364890503, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5678946102375755153187337 4259209576781816364890503)
                      ·
                        rfl

theorem cell23_8294781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 5, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 5, 1, 2, 2, 2, 2].length) (baseStart_8294781 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8294781 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8294781 prefixEnd_8294781 := by exact prefixLift 8294781
  have htrace : WordTrace (prefixWord ++ tailWord_8294781) baseStart_8294781 baseEnd_8294781 := by
    simpa [prefixWord, tailWord_8294781, baseEnd_8294781] using wordTrace_append hprefix tailTrace_8294781
  have hstable : (prefixWord ++ tailWord_8294781).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8294781).length < 2 ^ (prefixWord ++ tailWord_8294781).sum := by decide
  have hdescent : baseEnd_8294781 < baseStart_8294781 := by decide
  rcases family_descends (prefixWord ++ tailWord_8294781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8294798 : List Nat := [4, 1, 1, 4, 1, 2, 3, 1, 2, 2, 2]
def baseStart_8294798 : Nat := 118140960795 + 8294798 * 2 ^ 59
def prefixEnd_8294798 : Nat := 4983230072969 + 3 ^ 40 * 8294798 * 2
def baseEnd_8294798 : Nat := 4259218305952942798377925

theorem tailTrace_8294798 : CollatzResearch.WordTrace tailWord_8294798 prefixEnd_8294798 4259218305952942798377925 := by
  unfold tailWord_8294798
  simp only [CollatzResearch.WordTrace]
  refine ⟨37817017175421369944892631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 201690758268913973039427365 37817017175421369944892631)
  ·
    refine ⟨56725525763132054917338947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37817017175421369944892631 56725525763132054917338947)
    ·
      refine ⟨85088288644698082376008421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56725525763132054917338947 85088288644698082376008421)
      ·
        refine ⟨15954054120880890445501579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 85088288644698082376008421 15954054120880890445501579)
        ·
          refine ⟨23931081181321335668252369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15954054120880890445501579 23931081181321335668252369)
          ·
            refine ⟨17948310885991001751189277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23931081181321335668252369 17948310885991001751189277)
            ·
              refine ⟨6730616582246625656695979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17948310885991001751189277 6730616582246625656695979)
              ·
                refine ⟨10095924873369938485043969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6730616582246625656695979 10095924873369938485043969)
                ·
                  refine ⟨7571943655027453863782977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10095924873369938485043969 7571943655027453863782977)
                  ·
                    refine ⟨5678957741270590397837233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7571943655027453863782977 5678957741270590397837233)
                    ·
                      refine ⟨4259218305952942798377925, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5678957741270590397837233 4259218305952942798377925)
                      ·
                        rfl

theorem cell23_8294798_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 2, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 2, 3, 1, 2, 2, 2].length) (baseStart_8294798 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8294798 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8294798 prefixEnd_8294798 := by exact prefixLift 8294798
  have htrace : WordTrace (prefixWord ++ tailWord_8294798) baseStart_8294798 baseEnd_8294798 := by
    simpa [prefixWord, tailWord_8294798, baseEnd_8294798] using wordTrace_append hprefix tailTrace_8294798
  have hstable : (prefixWord ++ tailWord_8294798).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8294798).length < 2 ^ (prefixWord ++ tailWord_8294798).sum := by decide
  have hdescent : baseEnd_8294798 < baseStart_8294798 := by decide
  rcases family_descends (prefixWord ++ tailWord_8294798) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8294820 : List Nat := [2, 3, 1, 2, 1, 1, 4, 1, 1, 3, 4]
def baseStart_8294820 : Nat := 118140960795 + 8294820 * 2 ^ 59
def prefixEnd_8294820 : Nat := 4983230072969 + 3 ^ 40 * 8294820 * 2
def baseEnd_8294820 : Nat := 4259229602527341712302823

theorem tailTrace_8294820 : CollatzResearch.WordTrace tailWord_8294820 prefixEnd_8294820 4259229602527341712302823 := by
  unfold tailWord_8294820
  simp only [CollatzResearch.WordTrace]
  refine ⟨151268469904645628658220957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 201691293206194171544294609 151268469904645628658220957)
  ·
    refine ⟨56725676214242110746832859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 151268469904645628658220957 56725676214242110746832859)
    ·
      refine ⟨85088514321363166120249289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56725676214242110746832859 85088514321363166120249289)
      ·
        refine ⟨63816385741022374590186967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85088514321363166120249289 63816385741022374590186967)
        ·
          refine ⟨95724578611533561885280451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63816385741022374590186967 95724578611533561885280451)
          ·
            refine ⟨143586867917300342827920677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 95724578611533561885280451 143586867917300342827920677)
            ·
              refine ⟨26922537734493814280235127, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 143586867917300342827920677 26922537734493814280235127)
              ·
                refine ⟨40383806601740721420352691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26922537734493814280235127 40383806601740721420352691)
                ·
                  refine ⟨60575709902611082130529037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40383806601740721420352691 60575709902611082130529037)
                  ·
                    refine ⟨22715891213479155798948389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 60575709902611082130529037 22715891213479155798948389)
                    ·
                      refine ⟨4259229602527341712302823, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22715891213479155798948389 4259229602527341712302823)
                      ·
                        rfl

theorem cell23_8294820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 4, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 4, 1, 1, 3, 4].length) (baseStart_8294820 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8294820 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8294820 prefixEnd_8294820 := by exact prefixLift 8294820
  have htrace : WordTrace (prefixWord ++ tailWord_8294820) baseStart_8294820 baseEnd_8294820 := by
    simpa [prefixWord, tailWord_8294820, baseEnd_8294820] using wordTrace_append hprefix tailTrace_8294820
  have hstable : (prefixWord ++ tailWord_8294820).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8294820).length < 2 ^ (prefixWord ++ tailWord_8294820).sum := by decide
  have hdescent : baseEnd_8294820 < baseStart_8294820 := by decide
  rcases family_descends (prefixWord ++ tailWord_8294820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8294849 : List Nat := [1, 2, 7, 1, 2, 1, 2, 1, 2, 2, 2]
def baseStart_8294849 : Nat := 118140960795 + 8294849 * 2 ^ 59
def prefixEnd_8294849 : Nat := 4983230072969 + 3 ^ 40 * 8294849 * 2
def baseEnd_8294849 : Nat := 4259244493466322098840191

theorem tailTrace_8294849 : CollatzResearch.WordTrace tailWord_8294849 prefixEnd_8294849 4259244493466322098840191 := by
  unfold tailWord_8294849
  simp only [CollatzResearch.WordTrace]
  refine ⟨302537997526186195269247601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201691998350790796846165067 302537997526186195269247601)
  ·
    refine ⟨226903498144639646451935701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 302537997526186195269247601 226903498144639646451935701)
    ·
      refine ⟨5318050737764991713717243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 226903498144639646451935701 5318050737764991713717243)
      ·
        refine ⟨7977076106647487570575865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5318050737764991713717243 7977076106647487570575865)
        ·
          refine ⟨5982807079985615677931899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7977076106647487570575865 5982807079985615677931899)
          ·
            refine ⟨8974210619978423516897849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5982807079985615677931899 8974210619978423516897849)
            ·
              refine ⟨6730657964983817637673387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8974210619978423516897849 6730657964983817637673387)
              ·
                refine ⟨10095986947475726456510081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6730657964983817637673387 10095986947475726456510081)
                ·
                  refine ⟨7571990210606794842382561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10095986947475726456510081 7571990210606794842382561)
                  ·
                    refine ⟨5678992657955096131786921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7571990210606794842382561 5678992657955096131786921)
                    ·
                      refine ⟨4259244493466322098840191, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5678992657955096131786921 4259244493466322098840191)
                      ·
                        rfl

theorem cell23_8294849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 2, 1, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 2, 1, 2, 1, 2, 2, 2].length) (baseStart_8294849 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8294849 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8294849 prefixEnd_8294849 := by exact prefixLift 8294849
  have htrace : WordTrace (prefixWord ++ tailWord_8294849) baseStart_8294849 baseEnd_8294849 := by
    simpa [prefixWord, tailWord_8294849, baseEnd_8294849] using wordTrace_append hprefix tailTrace_8294849
  have hstable : (prefixWord ++ tailWord_8294849).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8294849).length < 2 ^ (prefixWord ++ tailWord_8294849).sum := by decide
  have hdescent : baseEnd_8294849 < baseStart_8294849 := by decide
  rcases family_descends (prefixWord ++ tailWord_8294849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8294941 : List Nat := [1, 4, 2, 2, 1, 4, 2, 1, 1, 5]
def baseStart_8294941 : Nat := 118140960795 + 8294941 * 2 ^ 59
def prefixEnd_8294941 : Nat := 4983230072969 + 3 ^ 40 * 8294941 * 2
def baseEnd_8294941 : Nat := 1419763911228845246296589

theorem tailTrace_8294941 : CollatzResearch.WordTrace tailWord_8294941 prefixEnd_8294941 1419763911228845246296589 := by
  unfold tailWord_8294941
  simp only [CollatzResearch.WordTrace]
  refine ⟨302541353041852894981596677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201694235361235263321064451 302541353041852894981596677)
  ·
    refine ⟨56726503695347417809049377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 302541353041852894981596677 56726503695347417809049377)
    ·
      refine ⟨42544877771510563356787033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56726503695347417809049377 42544877771510563356787033)
      ·
        refine ⟨31908658328632922517590275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42544877771510563356787033 31908658328632922517590275)
        ·
          refine ⟨47862987492949383776385413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31908658328632922517590275 47862987492949383776385413)
          ·
            refine ⟨8974310154928009458072265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 47862987492949383776385413 8974310154928009458072265)
            ·
              refine ⟨6730732616196007093554199, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8974310154928009458072265 6730732616196007093554199)
              ·
                refine ⟨10096098924294010640331299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6730732616196007093554199 10096098924294010640331299)
                ·
                  refine ⟨15144148386441015960496949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10096098924294010640331299 15144148386441015960496949)
                  ·
                    refine ⟨1419763911228845246296589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15144148386441015960496949 1419763911228845246296589)
                    ·
                      rfl

theorem cell23_8294941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 4, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 4, 2, 1, 1, 5].length) (baseStart_8294941 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8294941 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8294941 prefixEnd_8294941 := by exact prefixLift 8294941
  have htrace : WordTrace (prefixWord ++ tailWord_8294941) baseStart_8294941 baseEnd_8294941 := by
    simpa [prefixWord, tailWord_8294941, baseEnd_8294941] using wordTrace_append hprefix tailTrace_8294941
  have hstable : (prefixWord ++ tailWord_8294941).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8294941).length < 2 ^ (prefixWord ++ tailWord_8294941).sum := by decide
  have hdescent : baseEnd_8294941 < baseStart_8294941 := by decide
  rcases family_descends (prefixWord ++ tailWord_8294941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8294954 : List Nat := [3, 1, 4, 1, 1, 3, 1, 1, 4, 4]
def baseStart_8294954 : Nat := 118140960795 + 8294954 * 2 ^ 59
def prefixEnd_8294954 : Nat := 4983230072969 + 3 ^ 40 * 8294954 * 2
def baseEnd_8294954 : Nat := 1419766136311681396009069

theorem tailTrace_8294954 : CollatzResearch.WordTrace tailWord_8294954 prefixEnd_8294954 1419766136311681396009069 := by
  unfold tailWord_8294954
  simp only [CollatzResearch.WordTrace]
  refine ⟨75635456797701449550454979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 201694551460537198801213277 75635456797701449550454979)
  ·
    refine ⟨113453185196552174325682469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75635456797701449550454979 113453185196552174325682469)
    ·
      refine ⟨21272472224353532686065463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 113453185196552174325682469 21272472224353532686065463)
      ·
        refine ⟨31908708336530299029098195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21272472224353532686065463 31908708336530299029098195)
        ·
          refine ⟨47863062504795448543647293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31908708336530299029098195 47863062504795448543647293)
          ·
            refine ⟨17948648439298293203867735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 47863062504795448543647293 17948648439298293203867735)
            ·
              refine ⟨26922972658947439805801603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17948648439298293203867735 26922972658947439805801603)
              ·
                refine ⟨40384458988421159708702405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26922972658947439805801603 40384458988421159708702405)
                ·
                  refine ⟨7572086060328967445381701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 40384458988421159708702405 7572086060328967445381701)
                  ·
                    refine ⟨1419766136311681396009069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7572086060328967445381701 1419766136311681396009069)
                    ·
                      rfl

theorem cell23_8294954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 3, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 3, 1, 1, 4, 4].length) (baseStart_8294954 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8294954 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8294954 prefixEnd_8294954 := by exact prefixLift 8294954
  have htrace : WordTrace (prefixWord ++ tailWord_8294954) baseStart_8294954 baseEnd_8294954 := by
    simpa [prefixWord, tailWord_8294954, baseEnd_8294954] using wordTrace_append hprefix tailTrace_8294954
  have hstable : (prefixWord ++ tailWord_8294954).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8294954).length < 2 ^ (prefixWord ++ tailWord_8294954).sum := by decide
  have hdescent : baseEnd_8294954 < baseStart_8294954 := by decide
  rcases family_descends (prefixWord ++ tailWord_8294954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8294994 : List Nat := [3, 2, 2, 1, 2, 1, 1, 1, 6, 1, 3]
def baseStart_8294994 : Nat := 118140960795 + 8294994 * 2 ^ 59
def prefixEnd_8294994 : Nat := 4983230072969 + 3 ^ 40 * 8294994 * 2
def baseEnd_8294994 : Nat := 4259318948161224031527023

theorem tailTrace_8294994 : CollatzResearch.WordTrace tailWord_8294994 prefixEnd_8294994 4259318948161224031527023 := by
  unfold tailWord_8294994
  simp only [CollatzResearch.WordTrace]
  refine ⟨75635821527665221258319009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 201695524073773923355517357 75635821527665221258319009)
  ·
    refine ⟨56726866145748915943739257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75635821527665221258319009 56726866145748915943739257)
    ·
      refine ⟨42545149609311686957804443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56726866145748915943739257 42545149609311686957804443)
      ·
        refine ⟨63817724413967530436706665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42545149609311686957804443 63817724413967530436706665)
        ·
          refine ⟨47863293310475647827529999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63817724413967530436706665 47863293310475647827529999)
          ·
            refine ⟨71794939965713471741294999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47863293310475647827529999 71794939965713471741294999)
            ·
              refine ⟨107692409948570207611942499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71794939965713471741294999 107692409948570207611942499)
              ·
                refine ⟨161538614922855311417913749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 107692409948570207611942499 161538614922855311417913749)
                ·
                  refine ⟨7572122574508842722714707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 161538614922855311417913749 7572122574508842722714707)
                  ·
                    refine ⟨11358183861763264084072061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7572122574508842722714707 11358183861763264084072061)
                    ·
                      refine ⟨4259318948161224031527023, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11358183861763264084072061 4259318948161224031527023)
                      ·
                        rfl

theorem cell23_8294994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 1, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 1, 1, 6, 1, 3].length) (baseStart_8294994 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8294994 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8294994 prefixEnd_8294994 := by exact prefixLift 8294994
  have htrace : WordTrace (prefixWord ++ tailWord_8294994) baseStart_8294994 baseEnd_8294994 := by
    simpa [prefixWord, tailWord_8294994, baseEnd_8294994] using wordTrace_append hprefix tailTrace_8294994
  have hstable : (prefixWord ++ tailWord_8294994).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8294994).length < 2 ^ (prefixWord ++ tailWord_8294994).sum := by decide
  have hdescent : baseEnd_8294994 < baseStart_8294994 := by decide
  rcases family_descends (prefixWord ++ tailWord_8294994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8295068 : List Nat := [2, 2, 3, 2, 2, 1, 1, 4, 2, 2, 2]
def baseStart_8295068 : Nat := 118140960795 + 8295068 * 2 ^ 59
def prefixEnd_8295068 : Nat := 4983230072969 + 3 ^ 40 * 8295068 * 2
def baseEnd_8295068 : Nat := 4259356945729656742001683

theorem tailTrace_8295068 : CollatzResearch.WordTrace tailWord_8295068 prefixEnd_8295068 4259356945729656742001683 := by
  unfold tailWord_8295068
  simp only [CollatzResearch.WordTrace]
  refine ⟨151272992556196397835734929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 201697323408261863780979905 151272992556196397835734929)
  ·
    refine ⟨113454744417147298376801197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 151272992556196397835734929 113454744417147298376801197)
    ·
      refine ⟨42545529156430236891300449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 113454744417147298376801197 42545529156430236891300449)
      ·
        refine ⟨31909146867322677668475337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42545529156430236891300449 31909146867322677668475337)
        ·
          refine ⟨23931860150492008251356503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31909146867322677668475337 23931860150492008251356503)
          ·
            refine ⟨35897790225738012377034755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23931860150492008251356503 35897790225738012377034755)
            ·
              refine ⟨53846685338607018565552133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35897790225738012377034755 53846685338607018565552133)
              ·
                refine ⟨10096253500988815981041025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 53846685338607018565552133 10096253500988815981041025)
                ·
                  refine ⟨7572190125741611985780769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10096253500988815981041025 7572190125741611985780769)
                  ·
                    refine ⟨5679142594306208989335577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7572190125741611985780769 5679142594306208989335577)
                    ·
                      refine ⟨4259356945729656742001683, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5679142594306208989335577 4259356945729656742001683)
                      ·
                        rfl

theorem cell23_8295068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 1, 1, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 1, 1, 4, 2, 2, 2].length) (baseStart_8295068 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8295068 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8295068 prefixEnd_8295068 := by exact prefixLift 8295068
  have htrace : WordTrace (prefixWord ++ tailWord_8295068) baseStart_8295068 baseEnd_8295068 := by
    simpa [prefixWord, tailWord_8295068, baseEnd_8295068] using wordTrace_append hprefix tailTrace_8295068
  have hstable : (prefixWord ++ tailWord_8295068).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8295068).length < 2 ^ (prefixWord ++ tailWord_8295068).sum := by decide
  have hdescent : baseEnd_8295068 < baseStart_8295068 := by decide
  rcases family_descends (prefixWord ++ tailWord_8295068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8295104 : List Nat := [2, 1, 1, 2, 4, 2, 3, 1, 2, 5]
def baseStart_8295104 : Nat := 118140960795 + 8295104 * 2 ^ 59
def prefixEnd_8295104 : Nat := 4983230072969 + 3 ^ 40 * 8295104 * 2
def baseEnd_8295104 : Nat := 1419791810344406200383839

theorem tailTrace_8295104 : CollatzResearch.WordTrace tailWord_8295104 prefixEnd_8295104 1419791810344406200383839 := by
  unfold tailWord_8295104
  simp only [CollatzResearch.WordTrace]
  refine ⟨151273649070131186909890183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 201698198760174915879853577 151273649070131186909890183)
  ·
    refine ⟨226910473605196780364835275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151273649070131186909890183 226910473605196780364835275)
    ·
      refine ⟨340365710407795170547252913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 226910473605196780364835275 340365710407795170547252913)
      ·
        refine ⟨255274282805846377910439685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 340365710407795170547252913 255274282805846377910439685)
        ·
          refine ⟨47863928026096195858207441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 255274282805846377910439685 47863928026096195858207441)
          ·
            refine ⟨35897946019572146893655581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47863928026096195858207441 35897946019572146893655581)
            ·
              refine ⟨13461729757339555085120843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35897946019572146893655581 13461729757339555085120843)
              ·
                refine ⟨20192594636009332627681265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13461729757339555085120843 20192594636009332627681265)
                ·
                  refine ⟨15144445977006999470760949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20192594636009332627681265 15144445977006999470760949)
                  ·
                    refine ⟨1419791810344406200383839, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15144445977006999470760949 1419791810344406200383839)
                    ·
                      rfl

theorem cell23_8295104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 2, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 2, 3, 1, 2, 5].length) (baseStart_8295104 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8295104 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8295104 prefixEnd_8295104 := by exact prefixLift 8295104
  have htrace : WordTrace (prefixWord ++ tailWord_8295104) baseStart_8295104 baseEnd_8295104 := by
    simpa [prefixWord, tailWord_8295104, baseEnd_8295104] using wordTrace_append hprefix tailTrace_8295104
  have hstable : (prefixWord ++ tailWord_8295104).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8295104).length < 2 ^ (prefixWord ++ tailWord_8295104).sum := by decide
  have hdescent : baseEnd_8295104 < baseStart_8295104 := by decide
  rcases family_descends (prefixWord ++ tailWord_8295104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8295141 : List Nat := [1, 3, 1, 4, 1, 2, 2, 1, 2, 4, 2]
def baseStart_8295141 : Nat := 118140960795 + 8295141 * 2 ^ 59
def prefixEnd_8295141 : Nat := 4983230072969 + 3 ^ 40 * 8295141 * 2
def baseEnd_8295141 : Nat := 4259394429817434956388847

theorem tailTrace_8295141 : CollatzResearch.WordTrace tailWord_8295141 prefixEnd_8295141 4259394429817434956388847 := by
  unfold tailWord_8295141
  simp only [CollatzResearch.WordTrace]
  refine ⟨302548647641128329138877277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201699098427418886092584851 302548647641128329138877277)
  ·
    refine ⟨113455742865423123427078979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 302548647641128329138877277 113455742865423123427078979)
    ·
      refine ⟨170183614298134685140618469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113455742865423123427078979 170183614298134685140618469)
      ·
        refine ⟨31909427680900253463865963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 170183614298134685140618469 31909427680900253463865963)
        ·
          refine ⟨47864141521350380195798945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31909427680900253463865963 47864141521350380195798945)
          ·
            refine ⟨35898106141012785146849209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47864141521350380195798945 35898106141012785146849209)
            ·
              refine ⟨26923579605759588860136907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35898106141012785146849209 26923579605759588860136907)
              ·
                refine ⟨40385369408639383290205361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26923579605759588860136907 40385369408639383290205361)
                ·
                  refine ⟨30289027056479537467654021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40385369408639383290205361 30289027056479537467654021)
                  ·
                    refine ⟨5679192573089913275185129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 30289027056479537467654021 5679192573089913275185129)
                    ·
                      refine ⟨4259394429817434956388847, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5679192573089913275185129 4259394429817434956388847)
                      ·
                        rfl

theorem cell23_8295141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 2, 2, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 2, 2, 1, 2, 4, 2].length) (baseStart_8295141 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8295141 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8295141 prefixEnd_8295141 := by exact prefixLift 8295141
  have htrace : WordTrace (prefixWord ++ tailWord_8295141) baseStart_8295141 baseEnd_8295141 := by
    simpa [prefixWord, tailWord_8295141, baseEnd_8295141] using wordTrace_append hprefix tailTrace_8295141
  have hstable : (prefixWord ++ tailWord_8295141).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8295141).length < 2 ^ (prefixWord ++ tailWord_8295141).sum := by decide
  have hdescent : baseEnd_8295141 < baseStart_8295141 := by decide
  rcases family_descends (prefixWord ++ tailWord_8295141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8295184 : List Nat := [2, 1, 1, 1, 1, 1, 1, 1, 1, 11, 2]
def baseStart_8295184 : Nat := 118140960795 + 8295184 * 2 ^ 59
def prefixEnd_8295184 : Nat := 4983230072969 + 3 ^ 40 * 8295184 * 2
def baseEnd_8295184 : Nat := 4259416509485578288151149

theorem tailTrace_8295184 : CollatzResearch.WordTrace tailWord_8295184 prefixEnd_8295184 4259416509485578288151149 := by
  unfold tailWord_8295184
  simp only [CollatzResearch.WordTrace]
  refine ⟨151275107989986273741346303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 201700143986648364988461737 151275107989986273741346303)
  ·
    refine ⟨226912661984979410612019455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151275107989986273741346303 226912661984979410612019455)
    ·
      refine ⟨340368992977469115918029183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 226912661984979410612019455 340368992977469115918029183)
      ·
        refine ⟨510553489466203673877043775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 340368992977469115918029183 510553489466203673877043775)
        ·
          refine ⟨765830234199305510815565663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 510553489466203673877043775 765830234199305510815565663)
          ·
            refine ⟨1148745351298958266223348495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 765830234199305510815565663 1148745351298958266223348495)
            ·
              refine ⟨1723118026948437399335022743, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1148745351298958266223348495 1723118026948437399335022743)
              ·
                refine ⟨2584677040422656099002534115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1723118026948437399335022743 2584677040422656099002534115)
                ·
                  refine ⟨3877015560633984148503801173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2584677040422656099002534115 3877015560633984148503801173)
                  ·
                    refine ⟨5679222012647437717534865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 11 3877015560633984148503801173 5679222012647437717534865)
                    ·
                      refine ⟨4259416509485578288151149, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5679222012647437717534865 4259416509485578288151149)
                      ·
                        rfl

theorem cell23_8295184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 11, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 11, 2].length) (baseStart_8295184 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8295184 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8295184 prefixEnd_8295184 := by exact prefixLift 8295184
  have htrace : WordTrace (prefixWord ++ tailWord_8295184) baseStart_8295184 baseEnd_8295184 := by
    simpa [prefixWord, tailWord_8295184, baseEnd_8295184] using wordTrace_append hprefix tailTrace_8295184
  have hstable : (prefixWord ++ tailWord_8295184).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8295184).length < 2 ^ (prefixWord ++ tailWord_8295184).sum := by decide
  have hdescent : baseEnd_8295184 < baseStart_8295184 := by decide
  rcases family_descends (prefixWord ++ tailWord_8295184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8295194 : List Nat := [3, 1, 1, 3, 2, 1, 2, 2, 3, 5]
def baseStart_8295194 : Nat := 118140960795 + 8295194 * 2 ^ 59
def prefixEnd_8295194 : Nat := 4983230072969 + 3 ^ 40 * 8295194 * 2
def baseEnd_8295194 : Nat := 1419807214764041083008701

theorem tailTrace_8295194 : CollatzResearch.WordTrace tailWord_8295194 prefixEnd_8295194 1419807214764041083008701 := by
  unfold tailWord_8295194
  simp only [CollatzResearch.WordTrace]
  refine ⟨75637645177484079797639159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 201700387139957546127037757 75637645177484079797639159)
  ·
    refine ⟨113456467766226119696458739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75637645177484079797639159 113456467766226119696458739)
    ·
      refine ⟨170184701649339179544688109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113456467766226119696458739 170184701649339179544688109)
      ·
        refine ⟨63819263118502192329258041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 170184701649339179544688109 63819263118502192329258041)
        ·
          refine ⟨47864447338876644246943531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63819263118502192329258041 47864447338876644246943531)
          ·
            refine ⟨71796671008314966370415297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47864447338876644246943531 71796671008314966370415297)
            ·
              refine ⟨53847503256236224777811473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 71796671008314966370415297 53847503256236224777811473)
              ·
                refine ⟨40385627442177168583358605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53847503256236224777811473 40385627442177168583358605)
                ·
                  refine ⟨15144610290816438218759477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 40385627442177168583358605 15144610290816438218759477)
                  ·
                    refine ⟨1419807214764041083008701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15144610290816438218759477 1419807214764041083008701)
                    ·
                      rfl

theorem cell23_8295194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 2, 2, 3, 5].length) (baseStart_8295194 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8295194 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8295194 prefixEnd_8295194 := by exact prefixLift 8295194
  have htrace : WordTrace (prefixWord ++ tailWord_8295194) baseStart_8295194 baseEnd_8295194 := by
    simpa [prefixWord, tailWord_8295194, baseEnd_8295194] using wordTrace_append hprefix tailTrace_8295194
  have hstable : (prefixWord ++ tailWord_8295194).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8295194).length < 2 ^ (prefixWord ++ tailWord_8295194).sum := by decide
  have hdescent : baseEnd_8295194 < baseStart_8295194 := by decide
  rcases family_descends (prefixWord ++ tailWord_8295194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8295201 : List Nat := [1, 2, 3, 2, 1, 2, 1, 2, 4, 3, 2]
def baseStart_8295201 : Nat := 118140960795 + 8295201 * 2 ^ 59
def prefixEnd_8295201 : Nat := 4983230072969 + 3 ^ 40 * 8295201 * 2
def baseEnd_8295201 : Nat := 4259425238656704721638571

theorem tailTrace_8295201 : CollatzResearch.WordTrace tailWord_8295201 prefixEnd_8295201 4259425238656704721638571 := by
  unfold tailWord_8295201
  simp only [CollatzResearch.WordTrace]
  refine ⟨302550836020910959386061457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201700557347273972924040971 302550836020910959386061457)
  ·
    refine ⟨226913127015683219539546093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 302550836020910959386061457 226913127015683219539546093)
    ·
      refine ⟨85092422630881207327329785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 226913127015683219539546093 85092422630881207327329785)
      ·
        refine ⟨63819316973160905495497339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85092422630881207327329785 63819316973160905495497339)
        ·
          refine ⟨95728975459741358243246009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63819316973160905495497339 95728975459741358243246009)
          ·
            refine ⟨71796731594806018682434507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 95728975459741358243246009 71796731594806018682434507)
            ·
              refine ⟨107695097392209028023651761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71796731594806018682434507 107695097392209028023651761)
              ·
                refine ⟨80771323044156771017738821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 107695097392209028023651761 80771323044156771017738821)
                ·
                  refine ⟨15144623070779394565826029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 80771323044156771017738821 15144623070779394565826029)
                  ·
                    refine ⟨5679233651542272962184761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15144623070779394565826029 5679233651542272962184761)
                    ·
                      refine ⟨4259425238656704721638571, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5679233651542272962184761 4259425238656704721638571)
                      ·
                        rfl

theorem cell23_8295201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 1, 2, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 1, 2, 4, 3, 2].length) (baseStart_8295201 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8295201 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8295201 prefixEnd_8295201 := by exact prefixLift 8295201
  have htrace : WordTrace (prefixWord ++ tailWord_8295201) baseStart_8295201 baseEnd_8295201 := by
    simpa [prefixWord, tailWord_8295201, baseEnd_8295201] using wordTrace_append hprefix tailTrace_8295201
  have hstable : (prefixWord ++ tailWord_8295201).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8295201).length < 2 ^ (prefixWord ++ tailWord_8295201).sum := by decide
  have hdescent : baseEnd_8295201 < baseStart_8295201 := by decide
  rcases family_descends (prefixWord ++ tailWord_8295201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8295218 : List Nat := [3, 2, 1, 1, 3, 1, 4, 1, 2, 3, 2]
def baseStart_8295218 : Nat := 118140960795 + 8295218 * 2 ^ 59
def prefixEnd_8295218 : Nat := 4983230072969 + 3 ^ 40 * 8295218 * 2
def baseEnd_8295218 : Nat := 4259433967827831155125993

theorem tailTrace_8295218 : CollatzResearch.WordTrace tailWord_8295218 prefixEnd_8295218 4259433967827831155125993 := by
  unfold tailWord_8295218
  simp only [CollatzResearch.WordTrace]
  refine ⟨75637864015462342822357577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 201700970707899580859620205 75637864015462342822357577)
  ·
    refine ⟨56728398011596757116768183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75637864015462342822357577 56728398011596757116768183)
    ·
      refine ⟨85092597017395135675152275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56728398011596757116768183 85092597017395135675152275)
      ·
        refine ⟨127638895526092703512728413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85092597017395135675152275 127638895526092703512728413)
        ·
          refine ⟨47864585822284763817273155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 127638895526092703512728413 47864585822284763817273155)
          ·
            refine ⟨71796878733427145725909733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47864585822284763817273155 71796878733427145725909733)
            ·
              refine ⟨13461914762517589823608075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 71796878733427145725909733 13461914762517589823608075)
              ·
                refine ⟨20192872143776384735412113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13461914762517589823608075 20192872143776384735412113)
                ·
                  refine ⟨15144654107832288551559085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20192872143776384735412113 15144654107832288551559085)
                  ·
                    refine ⟨5679245290437108206834657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15144654107832288551559085 5679245290437108206834657)
                    ·
                      refine ⟨4259433967827831155125993, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5679245290437108206834657 4259433967827831155125993)
                      ·
                        rfl

theorem cell23_8295218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 4, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 4, 1, 2, 3, 2].length) (baseStart_8295218 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8295218 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8295218 prefixEnd_8295218 := by exact prefixLift 8295218
  have htrace : WordTrace (prefixWord ++ tailWord_8295218) baseStart_8295218 baseEnd_8295218 := by
    simpa [prefixWord, tailWord_8295218, baseEnd_8295218] using wordTrace_append hprefix tailTrace_8295218
  have hstable : (prefixWord ++ tailWord_8295218).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8295218).length < 2 ^ (prefixWord ++ tailWord_8295218).sum := by decide
  have hdescent : baseEnd_8295218 < baseStart_8295218 := by decide
  rcases family_descends (prefixWord ++ tailWord_8295218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8295224 : List Nat := [2, 1, 2, 1, 3, 2, 3, 2, 1, 6]
def baseStart_8295224 : Nat := 118140960795 + 8295224 * 2 ^ 59
def prefixEnd_8295224 : Nat := 4983230072969 + 3 ^ 40 * 8295224 * 2
def baseEnd_8295224 : Nat := 1419812349570586043883655

theorem tailTrace_8295224 : CollatzResearch.WordTrace tailWord_8295224 prefixEnd_8295224 1419812349570586043883655 := by
  unfold tailWord_8295224
  simp only [CollatzResearch.WordTrace]
  refine ⟨151275837449913817157074363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 201701116599885089542765817 151275837449913817157074363)
  ·
    refine ⟨226913756174870725735611545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151275837449913817157074363 226913756174870725735611545)
    ·
      refine ⟨170185317131153044301708659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 226913756174870725735611545 170185317131153044301708659)
      ·
        refine ⟨255277975696729566452562989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 170185317131153044301708659 255277975696729566452562989)
        ·
          refine ⟨95729240886273587419711121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 255277975696729566452562989 95729240886273587419711121)
          ·
            refine ⟨71796930664705190564783341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 95729240886273587419711121 71796930664705190564783341)
            ·
              refine ⟨26923848999264446461793753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 71796930664705190564783341 26923848999264446461793753)
              ·
                refine ⟨20192886749448334846345315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26923848999264446461793753 20192886749448334846345315)
                ·
                  refine ⟨30289330124172502269517973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20192886749448334846345315 30289330124172502269517973)
                  ·
                    refine ⟨1419812349570586043883655, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 30289330124172502269517973 1419812349570586043883655)
                    ·
                      rfl

theorem cell23_8295224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 3, 2, 1, 6].length) (baseStart_8295224 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8295224 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8295224 prefixEnd_8295224 := by exact prefixLift 8295224
  have htrace : WordTrace (prefixWord ++ tailWord_8295224) baseStart_8295224 baseEnd_8295224 := by
    simpa [prefixWord, tailWord_8295224, baseEnd_8295224] using wordTrace_append hprefix tailTrace_8295224
  have hstable : (prefixWord ++ tailWord_8295224).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8295224).length < 2 ^ (prefixWord ++ tailWord_8295224).sum := by decide
  have hdescent : baseEnd_8295224 < baseStart_8295224 := by decide
  rcases family_descends (prefixWord ++ tailWord_8295224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8295227 : List Nat := [1, 1, 1, 1, 1, 2, 1, 1, 1, 7, 6]
def baseStart_8295227 : Nat := 118140960795 + 8295227 * 2 ^ 59
def prefixEnd_8295227 : Nat := 4983230072969 + 3 ^ 40 * 8295227 * 2
def baseEnd_8295227 : Nat := 4259438589153721619913451

theorem tailTrace_8295227 : CollatzResearch.WordTrace tailWord_8295227 prefixEnd_8295227 4259438589153721619913451 := by
  unfold tailWord_8295227
  simp only [CollatzResearch.WordTrace]
  refine ⟨302551784318816765826507935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201701189545877843884338623 302551784318816765826507935)
  ·
    refine ⟨453827676478225148739761903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 302551784318816765826507935 453827676478225148739761903)
    ·
      refine ⟨680741514717337723109642855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 453827676478225148739761903 680741514717337723109642855)
      ·
        refine ⟨1021112272076006584664464283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 680741514717337723109642855 1021112272076006584664464283)
        ·
          refine ⟨1531668408114009876996696425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1021112272076006584664464283 1531668408114009876996696425)
          ·
            refine ⟨1148751306085507407747522319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1531668408114009876996696425 1148751306085507407747522319)
            ·
              refine ⟨1723126959128261111621283479, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1148751306085507407747522319 1723126959128261111621283479)
              ·
                refine ⟨2584690438692391667431925219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1723126959128261111621283479 2584690438692391667431925219)
                ·
                  refine ⟨3877035658038587501147887829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2584690438692391667431925219 3877035658038587501147887829)
                  ·
                    refine ⟨90868023235279394558153621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 3877035658038587501147887829 90868023235279394558153621)
                    ·
                      refine ⟨4259438589153721619913451, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 90868023235279394558153621 4259438589153721619913451)
                      ·
                        rfl

theorem cell23_8295227_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 7, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 7, 6].length) (baseStart_8295227 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8295227 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8295227 prefixEnd_8295227 := by exact prefixLift 8295227
  have htrace : WordTrace (prefixWord ++ tailWord_8295227) baseStart_8295227 baseEnd_8295227 := by
    simpa [prefixWord, tailWord_8295227, baseEnd_8295227] using wordTrace_append hprefix tailTrace_8295227
  have hstable : (prefixWord ++ tailWord_8295227).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8295227).length < 2 ^ (prefixWord ++ tailWord_8295227).sum := by decide
  have hdescent : baseEnd_8295227 < baseStart_8295227 := by decide
  rcases family_descends (prefixWord ++ tailWord_8295227) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8295236 : List Nat := [2, 3, 4, 2, 2, 1, 2, 2, 1, 4]
def baseStart_8295236 : Nat := 118140960795 + 8295236 * 2 ^ 59
def prefixEnd_8295236 : Nat := 4983230072969 + 3 ^ 40 * 8295236 * 2
def baseEnd_8295236 : Nat := 1419814403493204028233637

theorem tailTrace_8295236 : CollatzResearch.WordTrace tailWord_8295236 prefixEnd_8295236 1419814403493204028233637 := by
  unfold tailWord_8295236
  simp only [CollatzResearch.WordTrace]
  refine ⟨151276056287892080181792781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 201701408383856106909057041 151276056287892080181792781)
  ·
    refine ⟨56728521107959530068172293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 151276056287892080181792781 56728521107959530068172293)
    ·
      refine ⟨10636597707742411887782305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 56728521107959530068172293 10636597707742411887782305)
      ·
        refine ⟨7977448280806808915836729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10636597707742411887782305 7977448280806808915836729)
        ·
          refine ⟨5983086210605106686877547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7977448280806808915836729 5983086210605106686877547)
          ·
            refine ⟨8974629315907660030316321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5983086210605106686877547 8974629315907660030316321)
            ·
              refine ⟨6730971986930745022737241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8974629315907660030316321 6730971986930745022737241)
              ·
                refine ⟨5048228990198058767052931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6730971986930745022737241 5048228990198058767052931)
                ·
                  refine ⟨7572343485297088150579397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5048228990198058767052931 7572343485297088150579397)
                  ·
                    refine ⟨1419814403493204028233637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7572343485297088150579397 1419814403493204028233637)
                    ·
                      rfl

theorem cell23_8295236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 2, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 2, 1, 2, 2, 1, 4].length) (baseStart_8295236 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8295236 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8295236 prefixEnd_8295236 := by exact prefixLift 8295236
  have htrace : WordTrace (prefixWord ++ tailWord_8295236) baseStart_8295236 baseEnd_8295236 := by
    simpa [prefixWord, tailWord_8295236, baseEnd_8295236] using wordTrace_append hprefix tailTrace_8295236
  have hstable : (prefixWord ++ tailWord_8295236).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8295236).length < 2 ^ (prefixWord ++ tailWord_8295236).sum := by decide
  have hdescent : baseEnd_8295236 < baseStart_8295236 := by decide
  rcases family_descends (prefixWord ++ tailWord_8295236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8295241 : List Nat := [1, 2, 1, 1, 2, 5, 1, 4, 2, 4]
def baseStart_8295241 : Nat := 118140960795 + 8295241 * 2 ^ 59
def prefixEnd_8295241 : Nat := 4983230072969 + 3 ^ 40 * 8295241 * 2
def baseEnd_8295241 : Nat := 1419815259294294855046129

theorem tailTrace_8295241 : CollatzResearch.WordTrace tailWord_8295241 prefixEnd_8295241 1419815259294294855046129 := by
  unfold tailWord_8295241
  simp only [CollatzResearch.WordTrace]
  refine ⟨302552294940766046217517577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201701529960510697478345051 302552294940766046217517577)
  ·
    refine ⟨226914221205574534663138183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 302552294940766046217517577 226914221205574534663138183)
    ·
      refine ⟨340371331808361801994707275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 226914221205574534663138183 340371331808361801994707275)
      ·
        refine ⟨510556997712542702992060913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 340371331808361801994707275 510556997712542702992060913)
        ·
          refine ⟨382917748284407027244045685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 510556997712542702992060913 382917748284407027244045685)
          ·
            refine ⟨35898538901663158804129283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 382917748284407027244045685 35898538901663158804129283)
            ·
              refine ⟨53847808352494738206193925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35898538901663158804129283 53847808352494738206193925)
              ·
                refine ⟨10096464066092763413661361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 53847808352494738206193925 10096464066092763413661361)
                ·
                  refine ⟨7572348049569572560246021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10096464066092763413661361 7572348049569572560246021)
                  ·
                    refine ⟨1419815259294294855046129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7572348049569572560246021 1419815259294294855046129)
                    ·
                      rfl

theorem cell23_8295241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 5, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 5, 1, 4, 2, 4].length) (baseStart_8295241 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8295241 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8295241 prefixEnd_8295241 := by exact prefixLift 8295241
  have htrace : WordTrace (prefixWord ++ tailWord_8295241) baseStart_8295241 baseEnd_8295241 := by
    simpa [prefixWord, tailWord_8295241, baseEnd_8295241] using wordTrace_append hprefix tailTrace_8295241
  have hstable : (prefixWord ++ tailWord_8295241).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8295241).length < 2 ^ (prefixWord ++ tailWord_8295241).sum := by decide
  have hdescent : baseEnd_8295241 < baseStart_8295241 := by decide
  rcases family_descends (prefixWord ++ tailWord_8295241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8295271 : List Nat := [1, 1, 5, 1, 2, 3, 3, 7]
def baseStart_8295271 : Nat := 118140960795 + 8295271 * 2 ^ 59
def prefixEnd_8295271 : Nat := 4983230072969 + 3 ^ 40 * 8295271 * 2
def baseEnd_8295271 : Nat := 157757821566759979546787

theorem tailTrace_8295271 : CollatzResearch.WordTrace tailWord_8295271 prefixEnd_8295271 157757821566759979546787 := by
  unfold tailWord_8295271
  simp only [CollatzResearch.WordTrace]
  refine ⟨302553389130657361341109667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201702259420438240894073111 302553389130657361341109667)
  ·
    refine ⟨453830083695986042011664501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 302553389130657361341109667 453830083695986042011664501)
    ·
      refine ⟨42546570346498691438593547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 453830083695986042011664501 42546570346498691438593547)
      ·
        refine ⟨63819855519748037157890321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42546570346498691438593547 63819855519748037157890321)
        ·
          refine ⟨47864891639811027868417741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63819855519748037157890321 47864891639811027868417741)
          ·
            refine ⟨17949334364929135450656653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 47864891639811027868417741 17949334364929135450656653)
            ·
              refine ⟨6731000386848425793996245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17949334364929135450656653 6731000386848425793996245)
              ·
                refine ⟨157757821566759979546787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6731000386848425793996245 157757821566759979546787)
                ·
                  rfl

theorem cell23_8295271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 3, 3, 7].length) (baseStart_8295271 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8295271 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8295271 prefixEnd_8295271 := by exact prefixLift 8295271
  have htrace : WordTrace (prefixWord ++ tailWord_8295271) baseStart_8295271 baseEnd_8295271 := by
    simpa [prefixWord, tailWord_8295271, baseEnd_8295271] using wordTrace_append hprefix tailTrace_8295271
  have hstable : (prefixWord ++ tailWord_8295271).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8295271).length < 2 ^ (prefixWord ++ tailWord_8295271).sum := by decide
  have hdescent : baseEnd_8295271 < baseStart_8295271 := by decide
  rcases family_descends (prefixWord ++ tailWord_8295271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8295281 : List Nat := [1, 2, 2, 2, 1, 4, 2, 2, 1, 3, 3]
def baseStart_8295281 : Nat := 118140960795 + 8295281 * 2 ^ 59
def prefixEnd_8295281 : Nat := 4983230072969 + 3 ^ 40 * 8295281 * 2
def baseEnd_8295281 : Nat := 4259466317109064408638203

theorem tailTrace_8295281 : CollatzResearch.WordTrace tailWord_8295281 prefixEnd_8295281 4259466317109064408638203 := by
  unfold tailWord_8295281
  simp only [CollatzResearch.WordTrace]
  refine ⟨302553753860621133048973697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201702502573747422032649131 302553753860621133048973697)
  ·
    refine ⟨226915315395465849786730273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 302553753860621133048973697 226915315395465849786730273)
    ·
      refine ⟨170186486546599387340047705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 226915315395465849786730273 170186486546599387340047705)
      ·
        refine ⟨127639864909949540505035779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 170186486546599387340047705 127639864909949540505035779)
        ·
          refine ⟨191459797364924310757553669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 127639864909949540505035779 191459797364924310757553669)
          ·
            refine ⟨35898712005923308267041313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 191459797364924310757553669 35898712005923308267041313)
            ·
              refine ⟨26924034004442481200280985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35898712005923308267041313 26924034004442481200280985)
              ·
                refine ⟨20193025503331860900210739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26924034004442481200280985 20193025503331860900210739)
                ·
                  refine ⟨30289538254997791350316109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20193025503331860900210739 30289538254997791350316109)
                  ·
                    refine ⟨11358576845624171756368541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 30289538254997791350316109 11358576845624171756368541)
                    ·
                      refine ⟨4259466317109064408638203, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11358576845624171756368541 4259466317109064408638203)
                      ·
                        rfl

theorem cell23_8295281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 4, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 4, 2, 2, 1, 3, 3].length) (baseStart_8295281 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8295281 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8295281 prefixEnd_8295281 := by exact prefixLift 8295281
  have htrace : WordTrace (prefixWord ++ tailWord_8295281) baseStart_8295281 baseEnd_8295281 := by
    simpa [prefixWord, tailWord_8295281, baseEnd_8295281] using wordTrace_append hprefix tailTrace_8295281
  have hstable : (prefixWord ++ tailWord_8295281).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8295281).length < 2 ^ (prefixWord ++ tailWord_8295281).sum := by decide
  have hdescent : baseEnd_8295281 < baseStart_8295281 := by decide
  rcases family_descends (prefixWord ++ tailWord_8295281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8295285 : List Nat := [1, 3, 4, 1, 1, 2, 4, 1, 1, 2, 3]
def baseStart_8295285 : Nat := 118140960795 + 8295285 * 2 ^ 59
def prefixEnd_8295285 : Nat := 4983230072969 + 3 ^ 40 * 8295285 * 2
def baseEnd_8295285 : Nat := 4259468371031682392988185

theorem tailTrace_8295285 : CollatzResearch.WordTrace tailWord_8295285 prefixEnd_8295285 4259468371031682392988185 := by
  unfold tailWord_8295285
  simp only [CollatzResearch.WordTrace]
  refine ⟨302553899752606641732119309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201702599835071094488079539 302553899752606641732119309)
  ·
    refine ⟨113457712407227490649544741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 302553899752606641732119309 113457712407227490649544741)
    ·
      refine ⟨21273321076355154496789639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 113457712407227490649544741 21273321076355154496789639)
      ·
        refine ⟨31909981614532731745184459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21273321076355154496789639 31909981614532731745184459)
        ·
          refine ⟨47864972421799097617776689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31909981614532731745184459 47864972421799097617776689)
          ·
            refine ⟨35898729316349323213332517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47864972421799097617776689 35898729316349323213332517)
            ·
              refine ⟨6731011746815498102499847, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 35898729316349323213332517 6731011746815498102499847)
              ·
                refine ⟨10096517620223247153749771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6731011746815498102499847 10096517620223247153749771)
                ·
                  refine ⟨15144776430334870730624657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10096517620223247153749771 15144776430334870730624657)
                  ·
                    refine ⟨11358582322751153047968493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15144776430334870730624657 11358582322751153047968493)
                    ·
                      refine ⟨4259468371031682392988185, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11358582322751153047968493 4259468371031682392988185)
                      ·
                        rfl

theorem cell23_8295285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 2, 4, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 2, 4, 1, 1, 2, 3].length) (baseStart_8295285 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8295285 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8295285 prefixEnd_8295285 := by exact prefixLift 8295285
  have htrace : WordTrace (prefixWord ++ tailWord_8295285) baseStart_8295285 baseEnd_8295285 := by
    simpa [prefixWord, tailWord_8295285, baseEnd_8295285] using wordTrace_append hprefix tailTrace_8295285
  have hstable : (prefixWord ++ tailWord_8295285).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8295285).length < 2 ^ (prefixWord ++ tailWord_8295285).sum := by decide
  have hdescent : baseEnd_8295285 < baseStart_8295285 := by decide
  rcases family_descends (prefixWord ++ tailWord_8295285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8295325 : List Nat := [1, 4, 2, 1, 2, 1, 4, 2, 1, 3, 2]
def baseStart_8295325 : Nat := 118140960795 + 8295325 * 2 ^ 59
def prefixEnd_8295325 : Nat := 4983230072969 + 3 ^ 40 * 8295325 * 2
def baseEnd_8295325 : Nat := 4259488910257862236488001

theorem tailTrace_8295325 : CollatzResearch.WordTrace tailWord_8295325 prefixEnd_8295325 4259488910257862236488001 := by
  unfold tailWord_8295325
  simp only [CollatzResearch.WordTrace]
  refine ⟨302555358672461728563575429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201703572448307819042383619 302555358672461728563575429)
  ·
    refine ⟨56729129751086574105670393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 302555358672461728563575429 56729129751086574105670393)
    ·
      refine ⟨42546847313314930579252795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56729129751086574105670393 42546847313314930579252795)
      ·
        refine ⟨63820270969972395868879193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42546847313314930579252795 63820270969972395868879193)
        ·
          refine ⟨47865203227479296901659395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63820270969972395868879193 47865203227479296901659395)
          ·
            refine ⟨71797804841218945352489093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47865203227479296901659395 71797804841218945352489093)
            ·
              refine ⟨13462088407728552253591705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 71797804841218945352489093 13462088407728552253591705)
              ·
                refine ⟨10096566305796414190193779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13462088407728552253591705 10096566305796414190193779)
                ·
                  refine ⟨15144849458694621285290669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10096566305796414190193779 15144849458694621285290669)
                  ·
                    refine ⟨5679318547010482981984001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15144849458694621285290669 5679318547010482981984001)
                    ·
                      refine ⟨4259488910257862236488001, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5679318547010482981984001 4259488910257862236488001)
                      ·
                        rfl

theorem cell23_8295325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 4, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 4, 2, 1, 3, 2].length) (baseStart_8295325 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8295325 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8295325 prefixEnd_8295325 := by exact prefixLift 8295325
  have htrace : WordTrace (prefixWord ++ tailWord_8295325) baseStart_8295325 baseEnd_8295325 := by
    simpa [prefixWord, tailWord_8295325, baseEnd_8295325] using wordTrace_append hprefix tailTrace_8295325
  have hstable : (prefixWord ++ tailWord_8295325).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8295325).length < 2 ^ (prefixWord ++ tailWord_8295325).sum := by decide
  have hdescent : baseEnd_8295325 < baseStart_8295325 := by decide
  rcases family_descends (prefixWord ++ tailWord_8295325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8295350 : List Nat := [5, 1, 4, 1, 1, 1, 3, 2, 1, 2, 2]
def baseStart_8295350 : Nat := 118140960795 + 8295350 * 2 ^ 59
def prefixEnd_8295350 : Nat := 4983230072969 + 3 ^ 40 * 8295350 * 2
def baseEnd_8295350 : Nat := 4259501747274224638675387

theorem tailTrace_8295350 : CollatzResearch.WordTrace tailWord_8295350 prefixEnd_8295350 4259501747274224638675387 := by
  unfold tailWord_8295350
  simp only [CollatzResearch.WordTrace]
  refine ⟨18909766906085697364577219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 201704180331580771888823669 18909766906085697364577219)
  ·
    refine ⟨28364650359128546046865829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18909766906085697364577219 28364650359128546046865829)
    ·
      refine ⟨5318371942336602383787343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 28364650359128546046865829 5318371942336602383787343)
      ·
        refine ⟨7977557913504903575681015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5318371942336602383787343 7977557913504903575681015)
        ·
          refine ⟨11966336870257355363521523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7977557913504903575681015 11966336870257355363521523)
          ·
            refine ⟨17949505305386033045282285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11966336870257355363521523 17949505305386033045282285)
            ·
              refine ⟨6731064489519762391980857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17949505305386033045282285 6731064489519762391980857)
              ·
                refine ⟨5048298367139821793985643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6731064489519762391980857 5048298367139821793985643)
                ·
                  refine ⟨7572447550709732690978465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5048298367139821793985643 7572447550709732690978465)
                  ·
                    refine ⟨5679335663032299518233849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7572447550709732690978465 5679335663032299518233849)
                    ·
                      refine ⟨4259501747274224638675387, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5679335663032299518233849 4259501747274224638675387)
                      ·
                        rfl

theorem cell23_8295350_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 1, 1, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 1, 1, 3, 2, 1, 2, 2].length) (baseStart_8295350 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8295350 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8295350 prefixEnd_8295350 := by exact prefixLift 8295350
  have htrace : WordTrace (prefixWord ++ tailWord_8295350) baseStart_8295350 baseEnd_8295350 := by
    simpa [prefixWord, tailWord_8295350, baseEnd_8295350] using wordTrace_append hprefix tailTrace_8295350
  have hstable : (prefixWord ++ tailWord_8295350).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8295350).length < 2 ^ (prefixWord ++ tailWord_8295350).sum := by decide
  have hdescent : baseEnd_8295350 < baseStart_8295350 := by decide
  rcases family_descends (prefixWord ++ tailWord_8295350) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8295354 : List Nat := [3, 1, 1, 1, 2, 1, 3, 1, 1, 2, 7]
def baseStart_8295354 : Nat := 118140960795 + 8295354 * 2 ^ 59
def prefixEnd_8295354 : Nat := 4983230072969 + 3 ^ 40 * 8295354 * 2
def baseEnd_8295354 : Nat := 4259503801196842623025367

theorem tailTrace_8295354 : CollatzResearch.WordTrace tailWord_8295354 prefixEnd_8295354 4259503801196842623025367 := by
  unfold tailWord_8295354
  simp only [CollatzResearch.WordTrace]
  refine ⟨75639104097339166629095279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 201704277592904444344254077 75639104097339166629095279)
  ·
    refine ⟨113458656146008749943642919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75639104097339166629095279 113458656146008749943642919)
    ·
      refine ⟨170187984219013124915464379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113458656146008749943642919 170187984219013124915464379)
      ·
        refine ⟨255281976328519687373196569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 170187984219013124915464379 255281976328519687373196569)
        ·
          refine ⟨191461482246389765529897427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 255281976328519687373196569 191461482246389765529897427)
          ·
            refine ⟨287192223369584648294846141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 191461482246389765529897427 287192223369584648294846141)
            ·
              refine ⟨107697083763594243110567303, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 287192223369584648294846141 107697083763594243110567303)
              ·
                refine ⟨161545625645391364665850955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 107697083763594243110567303 161545625645391364665850955)
                ·
                  refine ⟨242318438468087046998776433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 161545625645391364665850955 242318438468087046998776433)
                  ·
                    refine ⟨181738828851065285249082325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 242318438468087046998776433 181738828851065285249082325)
                    ·
                      refine ⟨4259503801196842623025367, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 181738828851065285249082325 4259503801196842623025367)
                      ·
                        rfl

theorem cell23_8295354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 3, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 3, 1, 1, 2, 7].length) (baseStart_8295354 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8295354 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8295354 prefixEnd_8295354 := by exact prefixLift 8295354
  have htrace : WordTrace (prefixWord ++ tailWord_8295354) baseStart_8295354 baseEnd_8295354 := by
    simpa [prefixWord, tailWord_8295354, baseEnd_8295354] using wordTrace_append hprefix tailTrace_8295354
  have hstable : (prefixWord ++ tailWord_8295354).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8295354).length < 2 ^ (prefixWord ++ tailWord_8295354).sum := by decide
  have hdescent : baseEnd_8295354 < baseStart_8295354 := by decide
  rcases family_descends (prefixWord ++ tailWord_8295354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8295438 : List Nat := [4, 1, 1, 2, 2, 2, 1, 1, 5, 4]
def baseStart_8295438 : Nat := 118140960795 + 8295438 * 2 ^ 59
def prefixEnd_8295438 : Nat := 4983230072969 + 3 ^ 40 * 8295438 * 2
def baseEnd_8295438 : Nat := 1419848977857273431458327

theorem tailTrace_8295438 : CollatzResearch.WordTrace tailWord_8295438 prefixEnd_8295438 1419848977857273431458327 := by
  unfold tailWord_8295438
  simp only [CollatzResearch.WordTrace]
  refine ⟨37819935015131543607804871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 201706320080701565908292645 37819935015131543607804871)
  ·
    refine ⟨56729902522697315411707307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37819935015131543607804871 56729902522697315411707307)
    ·
      refine ⟨85094853784045973117560961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56729902522697315411707307 85094853784045973117560961)
      ·
        refine ⟨63821140338034479838170721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85094853784045973117560961 63821140338034479838170721)
        ·
          refine ⟨47865855253525859878628041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63821140338034479838170721 47865855253525859878628041)
          ·
            refine ⟨35899391440144394908971031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47865855253525859878628041 35899391440144394908971031)
            ·
              refine ⟨53849087160216592363456547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35899391440144394908971031 53849087160216592363456547)
              ·
                refine ⟨80773630740324888545184821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53849087160216592363456547 80773630740324888545184821)
                ·
                  refine ⟨7572527881905458301111077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 80773630740324888545184821 7572527881905458301111077)
                  ·
                    refine ⟨1419848977857273431458327, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7572527881905458301111077 1419848977857273431458327)
                    ·
                      rfl

theorem cell23_8295438_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 2, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 2, 1, 1, 5, 4].length) (baseStart_8295438 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8295438 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8295438 prefixEnd_8295438 := by exact prefixLift 8295438
  have htrace : WordTrace (prefixWord ++ tailWord_8295438) baseStart_8295438 baseEnd_8295438 := by
    simpa [prefixWord, tailWord_8295438, baseEnd_8295438] using wordTrace_append hprefix tailTrace_8295438
  have hstable : (prefixWord ++ tailWord_8295438).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8295438).length < 2 ^ (prefixWord ++ tailWord_8295438).sum := by decide
  have hdescent : baseEnd_8295438 < baseStart_8295438 := by decide
  rcases family_descends (prefixWord ++ tailWord_8295438) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8295442 : List Nat := [3, 2, 5, 1, 1, 1, 1, 1, 1, 7]
def baseStart_8295442 : Nat := 118140960795 + 8295442 * 2 ^ 59
def prefixEnd_8295442 : Nat := 4983230072969 + 3 ^ 40 * 8295442 * 2
def baseEnd_8295442 : Nat := 1419849662498146092908321

theorem tailTrace_8295442 : CollatzResearch.WordTrace tailWord_8295442 prefixEnd_8295442 1419849662498146092908321 := by
  unfold tailWord_8295442
  simp only [CollatzResearch.WordTrace]
  refine ⟨75639906503259464386396145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 201706417342025238363723053 75639906503259464386396145)
  ·
    refine ⟨56729929877444598289797109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75639906503259464386396145 56729929877444598289797109)
    ·
      refine ⟨5318430926010431089668479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 56729929877444598289797109 5318430926010431089668479)
      ·
        refine ⟨7977646389015646634502719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5318430926010431089668479 7977646389015646634502719)
        ·
          refine ⟨11966469583523469951754079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7977646389015646634502719 11966469583523469951754079)
          ·
            refine ⟨17949704375285204927631119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11966469583523469951754079 17949704375285204927631119)
            ·
              refine ⟨26924556562927807391446679, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17949704375285204927631119 26924556562927807391446679)
              ·
                refine ⟨40386834844391711087170019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26924556562927807391446679 40386834844391711087170019)
                ·
                  refine ⟨60580252266587566630755029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40386834844391711087170019 60580252266587566630755029)
                  ·
                    refine ⟨1419849662498146092908321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 60580252266587566630755029 1419849662498146092908321)
                    ·
                      rfl

theorem cell23_8295442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 1, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 1, 1, 1, 1, 1, 7].length) (baseStart_8295442 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8295442 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8295442 prefixEnd_8295442 := by exact prefixLift 8295442
  have htrace : WordTrace (prefixWord ++ tailWord_8295442) baseStart_8295442 baseEnd_8295442 := by
    simpa [prefixWord, tailWord_8295442, baseEnd_8295442] using wordTrace_append hprefix tailTrace_8295442
  have hstable : (prefixWord ++ tailWord_8295442).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8295442).length < 2 ^ (prefixWord ++ tailWord_8295442).sum := by decide
  have hdescent : baseEnd_8295442 < baseStart_8295442 := by decide
  rcases family_descends (prefixWord ++ tailWord_8295442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8295445 : List Nat := [1, 3, 2, 1, 4, 3, 1, 1, 2, 1, 4]
def baseStart_8295445 : Nat := 118140960795 + 8295445 * 2 ^ 59
def prefixEnd_8295445 : Nat := 4983230072969 + 3 ^ 40 * 8295445 * 2
def baseEnd_8295445 : Nat := 4259550527936401766987449

theorem tailTrace_8295445 : CollatzResearch.WordTrace tailWord_8295445 prefixEnd_8295445 4259550527936401766987449 := by
  unfold tailWord_8295445
  simp only [CollatzResearch.WordTrace]
  refine ⟨302559735432026989057943789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201706490288017992705295859 302559735432026989057943789)
  ·
    refine ⟨113459900787010120896728921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 302559735432026989057943789 113459900787010120896728921)
    ·
      refine ⟨85094925590257590672546691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 113459900787010120896728921 85094925590257590672546691)
      ·
        refine ⟨127642388385386386008820037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85094925590257590672546691 127642388385386386008820037)
        ·
          refine ⟨23932947822259947376653757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 127642388385386386008820037 23932947822259947376653757)
          ·
            refine ⟨8974855433347480266245159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23932947822259947376653757 8974855433347480266245159)
            ·
              refine ⟨13462283150021220399367739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8974855433347480266245159 13462283150021220399367739)
              ·
                refine ⟨20193424725031830599051609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13462283150021220399367739 20193424725031830599051609)
                ·
                  refine ⟨15145068543773872949288707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20193424725031830599051609 15145068543773872949288707)
                  ·
                    refine ⟨22717602815660809423933061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15145068543773872949288707 22717602815660809423933061)
                    ·
                      refine ⟨4259550527936401766987449, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22717602815660809423933061 4259550527936401766987449)
                      ·
                        rfl

theorem cell23_8295445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 3, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 3, 1, 1, 2, 1, 4].length) (baseStart_8295445 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8295445 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8295445 prefixEnd_8295445 := by exact prefixLift 8295445
  have htrace : WordTrace (prefixWord ++ tailWord_8295445) baseStart_8295445 baseEnd_8295445 := by
    simpa [prefixWord, tailWord_8295445, baseEnd_8295445] using wordTrace_append hprefix tailTrace_8295445
  have hstable : (prefixWord ++ tailWord_8295445).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8295445).length < 2 ^ (prefixWord ++ tailWord_8295445).sum := by decide
  have hdescent : baseEnd_8295445 < baseStart_8295445 := by decide
  rcases family_descends (prefixWord ++ tailWord_8295445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8295448 : List Nat := [2, 1, 2, 3, 2, 3, 1, 1, 1, 4, 3]
def baseStart_8295448 : Nat := 118140960795 + 8295448 * 2 ^ 59
def prefixEnd_8295448 : Nat := 4983230072969 + 3 ^ 40 * 8295448 * 2
def baseEnd_8295448 : Nat := 4259552068378365255249935

theorem tailTrace_8295448 : CollatzResearch.WordTrace tailWord_8295448 prefixEnd_8295448 4259552068378365255249935 := by
  unfold tailWord_8295448
  simp only [CollatzResearch.WordTrace]
  refine ⟨151279922425508060285151499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 201706563234010747046868665 151279922425508060285151499)
  ·
    refine ⟨226919883638262090427727249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151279922425508060285151499 226919883638262090427727249)
    ·
      refine ⟨170189912728696567820795437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 226919883638262090427727249 170189912728696567820795437)
      ·
        refine ⟨63821217273261212932798289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 170189912728696567820795437 63821217273261212932798289)
        ·
          refine ⟨47865912954945909699598717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63821217273261212932798289 47865912954945909699598717)
          ·
            refine ⟨17949717358104716137349519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 47865912954945909699598717 17949717358104716137349519)
            ·
              refine ⟨26924576037157074206024279, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17949717358104716137349519 26924576037157074206024279)
              ·
                refine ⟨40386864055735611309036419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26924576037157074206024279 40386864055735611309036419)
                ·
                  refine ⟨60580296083603416963554629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40386864055735611309036419 60580296083603416963554629)
                  ·
                    refine ⟨11358805515675640680666493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 60580296083603416963554629 11358805515675640680666493)
                    ·
                      refine ⟨4259552068378365255249935, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11358805515675640680666493 4259552068378365255249935)
                      ·
                        rfl

theorem cell23_8295448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 3, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 3, 1, 1, 1, 4, 3].length) (baseStart_8295448 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8295448 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8295448 prefixEnd_8295448 := by exact prefixLift 8295448
  have htrace : WordTrace (prefixWord ++ tailWord_8295448) baseStart_8295448 baseEnd_8295448 := by
    simpa [prefixWord, tailWord_8295448, baseEnd_8295448] using wordTrace_append hprefix tailTrace_8295448
  have hstable : (prefixWord ++ tailWord_8295448).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8295448).length < 2 ^ (prefixWord ++ tailWord_8295448).sum := by decide
  have hdescent : baseEnd_8295448 < baseStart_8295448 := by decide
  rcases family_descends (prefixWord ++ tailWord_8295448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8295455 : List Nat := [1, 1, 2, 4, 1, 3, 1, 5, 1, 4]
def baseStart_8295455 : Nat := 118140960795 + 8295455 * 2 ^ 59
def prefixEnd_8295455 : Nat := 4983230072969 + 3 ^ 40 * 8295455 * 2
def baseEnd_8295455 : Nat := 1419851887580982242620801

theorem tailTrace_8295455 : CollatzResearch.WordTrace tailWord_8295455 prefixEnd_8295455 1419851887580982242620801 := by
  unfold tailWord_8295455
  simp only [CollatzResearch.WordTrace]
  refine ⟨302560100161990760765807819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201706733441327173843871879 302560100161990760765807819)
  ·
    refine ⟨453840150242986141148711729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 302560100161990760765807819 453840150242986141148711729)
    ·
      refine ⟨340380112682239605861533797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 453840150242986141148711729 340380112682239605861533797)
      ·
        refine ⟨63821271127919926099037587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 340380112682239605861533797 63821271127919926099037587)
        ·
          refine ⟨95731906691879889148556381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63821271127919926099037587 95731906691879889148556381)
          ·
            refine ⟨35899465009454958430708643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 95731906691879889148556381 35899465009454958430708643)
            ·
              refine ⟨53849197514182437646062965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35899465009454958430708643 53849197514182437646062965)
              ·
                refine ⟨5048362266954603529318403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 53849197514182437646062965 5048362266954603529318403)
                ·
                  refine ⟨7572543400431905293977605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5048362266954603529318403 7572543400431905293977605)
                  ·
                    refine ⟨1419851887580982242620801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7572543400431905293977605 1419851887580982242620801)
                    ·
                      rfl

theorem cell23_8295455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 3, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 3, 1, 5, 1, 4].length) (baseStart_8295455 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8295455 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8295455 prefixEnd_8295455 := by exact prefixLift 8295455
  have htrace : WordTrace (prefixWord ++ tailWord_8295455) baseStart_8295455 baseEnd_8295455 := by
    simpa [prefixWord, tailWord_8295455, baseEnd_8295455] using wordTrace_append hprefix tailTrace_8295455
  have hstable : (prefixWord ++ tailWord_8295455).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8295455).length < 2 ^ (prefixWord ++ tailWord_8295455).sum := by decide
  have hdescent : baseEnd_8295455 < baseStart_8295455 := by decide
  rcases family_descends (prefixWord ++ tailWord_8295455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8295485 : List Nat := [1, 4, 1, 3, 1, 3, 3, 1, 6]
def baseStart_8295485 : Nat := 118140960795 + 8295485 * 2 ^ 59
def prefixEnd_8295485 : Nat := 4983230072969 + 3 ^ 40 * 8295485 * 2
def baseEnd_8295485 : Nat := 473285674129175734498585

theorem tailTrace_8295485 : CollatzResearch.WordTrace tailWord_8295485 prefixEnd_8295485 473285674129175734498585 := by
  unfold tailWord_8295485
  simp only [CollatzResearch.WordTrace]
  refine ⟨302561194351882075889399909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201707462901254717259599939 302561194351882075889399909)
  ·
    refine ⟨56730223940977889229262483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 302561194351882075889399909 56730223940977889229262483)
    ·
      refine ⟨85095335911466833843893725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56730223940977889229262483 85095335911466833843893725)
      ·
        refine ⟨31910750966800062691460147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 85095335911466833843893725 31910750966800062691460147)
        ·
          refine ⟨47866126450200094037190221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31910750966800062691460147 47866126450200094037190221)
          ·
            refine ⟨17949797418825035263946333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 47866126450200094037190221 17949797418825035263946333)
            ·
              refine ⟨6731174032059388223979875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17949797418825035263946333 6731174032059388223979875)
              ·
                refine ⟨10096761048089082335969813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6731174032059388223979875 10096761048089082335969813)
                ·
                  refine ⟨473285674129175734498585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 10096761048089082335969813 473285674129175734498585)
                  ·
                    rfl

theorem cell23_8295485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 3, 3, 1, 6].length) (baseStart_8295485 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8295485 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8295485 prefixEnd_8295485 := by exact prefixLift 8295485
  have htrace : WordTrace (prefixWord ++ tailWord_8295485) baseStart_8295485 baseEnd_8295485 := by
    simpa [prefixWord, tailWord_8295485, baseEnd_8295485] using wordTrace_append hprefix tailTrace_8295485
  have hstable : (prefixWord ++ tailWord_8295485).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8295485).length < 2 ^ (prefixWord ++ tailWord_8295485).sum := by decide
  have hdescent : baseEnd_8295485 < baseStart_8295485 := by decide
  rcases family_descends (prefixWord ++ tailWord_8295485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8295488 : List Nat := [2, 1, 1, 2, 2, 3, 1, 1, 3, 5, 2]
def baseStart_8295488 : Nat := 118140960795 + 8295488 * 2 ^ 59
def prefixEnd_8295488 : Nat := 4983230072969 + 3 ^ 40 * 8295488 * 2
def baseEnd_8295488 : Nat := 4259572607604545098749751

theorem tailTrace_8295488 : CollatzResearch.WordTrace tailWord_8295488 prefixEnd_8295488 4259572607604545098749751 := by
  unfold tailWord_8295488
  simp only [CollatzResearch.WordTrace]
  refine ⟨151280651885435603700879559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 201707535847247471601172745 151280651885435603700879559)
  ·
    refine ⟨226920977828153405551319339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151280651885435603700879559 226920977828153405551319339)
    ·
      refine ⟨340381466742230108326979009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 226920977828153405551319339 340381466742230108326979009)
      ·
        refine ⟨255286100056672581245234257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 340381466742230108326979009 255286100056672581245234257)
        ·
          refine ⟨191464575042504435933925693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 255286100056672581245234257 191464575042504435933925693)
          ·
            refine ⟨71799215640939163475222135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 191464575042504435933925693 71799215640939163475222135)
            ·
              refine ⟨107698823461408745212833203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71799215640939163475222135 107698823461408745212833203)
              ·
                refine ⟨161548235192113117819249805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 107698823461408745212833203 161548235192113117819249805)
                ·
                  refine ⟨60580588197042419182218677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 161548235192113117819249805 60580588197042419182218677)
                  ·
                    refine ⟨5679430143472726798333001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 60580588197042419182218677 5679430143472726798333001)
                    ·
                      refine ⟨4259572607604545098749751, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5679430143472726798333001 4259572607604545098749751)
                      ·
                        rfl

theorem cell23_8295488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 1, 1, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 1, 1, 3, 5, 2].length) (baseStart_8295488 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8295488 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8295488 prefixEnd_8295488 := by exact prefixLift 8295488
  have htrace : WordTrace (prefixWord ++ tailWord_8295488) baseStart_8295488 baseEnd_8295488 := by
    simpa [prefixWord, tailWord_8295488, baseEnd_8295488] using wordTrace_append hprefix tailTrace_8295488
  have hstable : (prefixWord ++ tailWord_8295488).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8295488).length < 2 ^ (prefixWord ++ tailWord_8295488).sum := by decide
  have hdescent : baseEnd_8295488 < baseStart_8295488 := by decide
  rcases family_descends (prefixWord ++ tailWord_8295488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8295495 : List Nat := [1, 1, 4, 1, 3, 2, 2, 2, 3, 1, 3]
def baseStart_8295495 : Nat := 118140960795 + 8295495 * 2 ^ 59
def prefixEnd_8295495 : Nat := 4983230072969 + 3 ^ 40 * 8295495 * 2
def baseEnd_8295495 : Nat := 4259576201969126571362219

theorem tailTrace_8295495 : CollatzResearch.WordTrace tailWord_8295495 prefixEnd_8295495 4259576201969126571362219 := by
  unfold tailWord_8295495
  simp only [CollatzResearch.WordTrace]
  refine ⟨302561559081845847597263939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201707706054563898398175959 302561559081845847597263939)
  ·
    refine ⟨453842338622768771395895909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 302561559081845847597263939 453842338622768771395895909)
    ·
      refine ⟨85095438491769144636730483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 453842338622768771395895909 85095438491769144636730483)
      ·
        refine ⟨127643157737653716955095725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85095438491769144636730483 127643157737653716955095725)
        ·
          refine ⟨47866184151620143858160897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 127643157737653716955095725 47866184151620143858160897)
          ·
            refine ⟨35899638113715107893620673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47866184151620143858160897 35899638113715107893620673)
            ·
              refine ⟨26924728585286330920215505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35899638113715107893620673 26924728585286330920215505)
              ·
                refine ⟨20193546438964748190161629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26924728585286330920215505 20193546438964748190161629)
                ·
                  refine ⟨7572579914611780571310611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20193546438964748190161629 7572579914611780571310611)
                  ·
                    refine ⟨11358869871917670856965917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7572579914611780571310611 11358869871917670856965917)
                    ·
                      refine ⟨4259576201969126571362219, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11358869871917670856965917 4259576201969126571362219)
                      ·
                        rfl

theorem cell23_8295495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 2, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 2, 2, 2, 3, 1, 3].length) (baseStart_8295495 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8295495 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8295495 prefixEnd_8295495 := by exact prefixLift 8295495
  have htrace : WordTrace (prefixWord ++ tailWord_8295495) baseStart_8295495 baseEnd_8295495 := by
    simpa [prefixWord, tailWord_8295495, baseEnd_8295495] using wordTrace_append hprefix tailTrace_8295495
  have hstable : (prefixWord ++ tailWord_8295495).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8295495).length < 2 ^ (prefixWord ++ tailWord_8295495).sum := by decide
  have hdescent : baseEnd_8295495 < baseStart_8295495 := by decide
  rcases family_descends (prefixWord ++ tailWord_8295495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8295498 : List Nat := [3, 1, 2, 1, 1, 2, 3, 4, 1, 5]
def baseStart_8295498 : Nat := 118140960795 + 8295498 * 2 ^ 59
def prefixEnd_8295498 : Nat := 4983230072969 + 3 ^ 40 * 8295498 * 2
def baseEnd_8295498 : Nat := 1419859247470363353208235

theorem tailTrace_8295498 : CollatzResearch.WordTrace tailWord_8295498 prefixEnd_8295498 1419859247470363353208235 := by
  unfold tailWord_8295498
  simp only [CollatzResearch.WordTrace]
  refine ⟨75640417125208744777405787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 201707779000556652739748765 75640417125208744777405787)
  ·
    refine ⟨113460625687813117166108681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75640417125208744777405787 113460625687813117166108681)
    ·
      refine ⟨85095469265859837874581511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 113460625687813117166108681 85095469265859837874581511)
      ·
        refine ⟨127643203898789756811872267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85095469265859837874581511 127643203898789756811872267)
        ·
          refine ⟨191464805848184635217808401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 127643203898789756811872267 191464805848184635217808401)
          ·
            refine ⟨143598604386138476413356301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 191464805848184635217808401 143598604386138476413356301)
            ·
              refine ⟨53849476644801928655008613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 143598604386138476413356301 53849476644801928655008613)
              ·
                refine ⟨10096776870900361622814115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 53849476644801928655008613 10096776870900361622814115)
                ·
                  refine ⟨15145165306350542434221173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10096776870900361622814115 15145165306350542434221173)
                  ·
                    refine ⟨1419859247470363353208235, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15145165306350542434221173 1419859247470363353208235)
                    ·
                      rfl

theorem cell23_8295498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 3, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 3, 4, 1, 5].length) (baseStart_8295498 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8295498 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8295498 prefixEnd_8295498 := by exact prefixLift 8295498
  have htrace : WordTrace (prefixWord ++ tailWord_8295498) baseStart_8295498 baseEnd_8295498 := by
    simpa [prefixWord, tailWord_8295498, baseEnd_8295498] using wordTrace_append hprefix tailTrace_8295498
  have hstable : (prefixWord ++ tailWord_8295498).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8295498).length < 2 ^ (prefixWord ++ tailWord_8295498).sum := by decide
  have hdescent : baseEnd_8295498 < baseStart_8295498 := by decide
  rcases family_descends (prefixWord ++ tailWord_8295498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8295511 : List Nat := [1, 1, 3, 2, 2, 1, 1, 3, 3, 6]
def baseStart_8295511 : Nat := 118140960795 + 8295511 * 2 ^ 59
def prefixEnd_8295511 : Nat := 4983230072969 + 3 ^ 40 * 8295511 * 2
def baseEnd_8295511 : Nat := 1419861472553199502920715

theorem tailTrace_8295511 : CollatzResearch.WordTrace tailWord_8295511 prefixEnd_8295511 1419861472553199502920715 := by
  unfold tailWord_8295511
  simp only [CollatzResearch.WordTrace]
  refine ⟨302562142649787882329846387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201708095099858588219897591 302562142649787882329846387)
  ·
    refine ⟨453843213974681823494769581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 302562142649787882329846387 453843213974681823494769581)
    ·
      refine ⟨170191205240505683810538593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 453843213974681823494769581 170191205240505683810538593)
      ·
        refine ⟨127643403930379262857903945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 170191205240505683810538593 127643403930379262857903945)
        ·
          refine ⟨95732552947784447143427959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 127643403930379262857903945 95732552947784447143427959)
          ·
            refine ⟨143598829421676670715141939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 95732552947784447143427959 143598829421676670715141939)
            ·
              refine ⟨215398244132515006072712909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 143598829421676670715141939 215398244132515006072712909)
              ·
                refine ⟨80774341549693127277267341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 215398244132515006072712909 80774341549693127277267341)
                ·
                  refine ⟨30290378081134922728975253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 80774341549693127277267341 30290378081134922728975253)
                  ·
                    refine ⟨1419861472553199502920715, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 30290378081134922728975253 1419861472553199502920715)
                    ·
                      rfl

theorem cell23_8295511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 1, 3, 3, 6].length) (baseStart_8295511 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8295511 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8295511 prefixEnd_8295511 := by exact prefixLift 8295511
  have htrace : WordTrace (prefixWord ++ tailWord_8295511) baseStart_8295511 baseEnd_8295511 := by
    simpa [prefixWord, tailWord_8295511, baseEnd_8295511] using wordTrace_append hprefix tailTrace_8295511
  have hstable : (prefixWord ++ tailWord_8295511).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8295511).length < 2 ^ (prefixWord ++ tailWord_8295511).sum := by decide
  have hdescent : baseEnd_8295511 < baseStart_8295511 := by decide
  rcases family_descends (prefixWord ++ tailWord_8295511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8295522 : List Nat := [3, 3, 2, 2, 1, 1, 1, 1, 4, 3, 2]
def baseStart_8295522 : Nat := 118140960795 + 8295522 * 2 ^ 59
def prefixEnd_8295522 : Nat := 4983230072969 + 3 ^ 40 * 8295522 * 2
def baseEnd_8295522 : Nat := 4259590065946797965724595

theorem tailTrace_8295522 : CollatzResearch.WordTrace tailWord_8295522 prefixEnd_8295522 4259590065946797965724595 := by
  unfold tailWord_8295522
  simp only [CollatzResearch.WordTrace]
  refine ⟨75640635963187007802124205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 201708362568498687472331213 75640635963187007802124205)
  ·
    refine ⟨28365238486195127925796577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 75640635963187007802124205 28365238486195127925796577)
    ·
      refine ⟨21273928864646345944347433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28365238486195127925796577 21273928864646345944347433)
      ·
        refine ⟨15955446648484759458260575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21273928864646345944347433 15955446648484759458260575)
        ·
          refine ⟨23933169972727139187390863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15955446648484759458260575 23933169972727139187390863)
          ·
            refine ⟨35899754959090708781086295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23933169972727139187390863 35899754959090708781086295)
            ·
              refine ⟨53849632438636063171629443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35899754959090708781086295 53849632438636063171629443)
              ·
                refine ⟨80774448657954094757444165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53849632438636063171629443 80774448657954094757444165)
                ·
                  refine ⟨15145209123366392767020781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 80774448657954094757444165 15145209123366392767020781)
                  ·
                    refine ⟨5679453421262397287632793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15145209123366392767020781 5679453421262397287632793)
                    ·
                      refine ⟨4259590065946797965724595, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5679453421262397287632793 4259590065946797965724595)
                      ·
                        rfl

theorem cell23_8295522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 1, 1, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 1, 1, 1, 4, 3, 2].length) (baseStart_8295522 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8295522 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8295522 prefixEnd_8295522 := by exact prefixLift 8295522
  have htrace : WordTrace (prefixWord ++ tailWord_8295522) baseStart_8295522 baseEnd_8295522 := by
    simpa [prefixWord, tailWord_8295522, baseEnd_8295522] using wordTrace_append hprefix tailTrace_8295522
  have hstable : (prefixWord ++ tailWord_8295522).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8295522).length < 2 ^ (prefixWord ++ tailWord_8295522).sum := by decide
  have hdescent : baseEnd_8295522 < baseStart_8295522 := by decide
  rcases family_descends (prefixWord ++ tailWord_8295522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8295529 : List Nat := [1, 2, 1, 1, 1, 7, 3, 2, 1, 1, 3]
def baseStart_8295529 : Nat := 118140960795 + 8295529 * 2 ^ 59
def prefixEnd_8295529 : Nat := 4983230072969 + 3 ^ 40 * 8295529 * 2
def baseEnd_8295529 : Nat := 4259593660311379438337063

theorem tailTrace_8295529 : CollatzResearch.WordTrace tailWord_8295529 prefixEnd_8295529 4259593660311379438337063 := by
  unfold tailWord_8295529
  simp only [CollatzResearch.WordTrace]
  refine ⟨302562799163722671404001641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201708532775815114269334427 302562799163722671404001641)
  ·
    refine ⟨226922099372792003553001231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 302562799163722671404001641 226922099372792003553001231)
    ·
      refine ⟨340383149059188005329501847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 226922099372792003553001231 340383149059188005329501847)
      ·
        refine ⟨510574723588782007994252771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 340383149059188005329501847 510574723588782007994252771)
        ·
          refine ⟨765862085383173011991379157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 510574723588782007994252771 765862085383173011991379157)
          ·
            refine ⟨17949892626168117468547949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 765862085383173011991379157 17949892626168117468547949)
            ·
              refine ⟨6731209734813044050705481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17949892626168117468547949 6731209734813044050705481)
              ·
                refine ⟨5048407301109783038029111, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6731209734813044050705481 5048407301109783038029111)
                ·
                  refine ⟨7572610951664674557043667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5048407301109783038029111 7572610951664674557043667)
                  ·
                    refine ⟨11358916427497011835565501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7572610951664674557043667 11358916427497011835565501)
                    ·
                      refine ⟨4259593660311379438337063, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11358916427497011835565501 4259593660311379438337063)
                      ·
                        rfl

theorem cell23_8295529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 7, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 7, 3, 2, 1, 1, 3].length) (baseStart_8295529 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8295529 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8295529 prefixEnd_8295529 := by exact prefixLift 8295529
  have htrace : WordTrace (prefixWord ++ tailWord_8295529) baseStart_8295529 baseEnd_8295529 := by
    simpa [prefixWord, tailWord_8295529, baseEnd_8295529] using wordTrace_append hprefix tailTrace_8295529
  have hstable : (prefixWord ++ tailWord_8295529).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8295529).length < 2 ^ (prefixWord ++ tailWord_8295529).sum := by decide
  have hdescent : baseEnd_8295529 < baseStart_8295529 := by decide
  rcases family_descends (prefixWord ++ tailWord_8295529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8295538 : List Nat := [3, 2, 1, 2, 2, 1, 1, 4, 1, 1, 5]
def baseStart_8295538 : Nat := 118140960795 + 8295538 * 2 ^ 59
def prefixEnd_8295538 : Nat := 4983230072969 + 3 ^ 40 * 8295538 * 2
def baseEnd_8295538 : Nat := 4259598281637269903124521

theorem tailTrace_8295538 : CollatzResearch.WordTrace tailWord_8295538 prefixEnd_8295538 4259598281637269903124521 := by
  unfold tailWord_8295538
  simp only [CollatzResearch.WordTrace]
  refine ⟨75640781855172516485269817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 201708751613793377294052845 75640781855172516485269817)
  ·
    refine ⟨56730586391379387363952363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75640781855172516485269817 56730586391379387363952363)
    ·
      refine ⟨85095879587069081045928545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56730586391379387363952363 85095879587069081045928545)
      ·
        refine ⟨63821909690301810784446409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85095879587069081045928545 63821909690301810784446409)
        ·
          refine ⟨47866432267726358088334807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63821909690301810784446409 47866432267726358088334807)
          ·
            refine ⟨71799648401589537132502211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47866432267726358088334807 71799648401589537132502211)
            ·
              refine ⟨107699472602384305698753317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71799648401589537132502211 107699472602384305698753317)
              ·
                refine ⟨20193651112947057318516247, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 107699472602384305698753317 20193651112947057318516247)
                ·
                  refine ⟨30290476669420585977774371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20193651112947057318516247 30290476669420585977774371)
                  ·
                    refine ⟨45435715004130878966661557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 30290476669420585977774371 45435715004130878966661557)
                    ·
                      refine ⟨4259598281637269903124521, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 45435715004130878966661557 4259598281637269903124521)
                      ·
                        rfl

theorem cell23_8295538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 1, 4, 1, 1, 5].length) (baseStart_8295538 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8295538 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8295538 prefixEnd_8295538 := by exact prefixLift 8295538
  have htrace : WordTrace (prefixWord ++ tailWord_8295538) baseStart_8295538 baseEnd_8295538 := by
    simpa [prefixWord, tailWord_8295538, baseEnd_8295538] using wordTrace_append hprefix tailTrace_8295538
  have hstable : (prefixWord ++ tailWord_8295538).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8295538).length < 2 ^ (prefixWord ++ tailWord_8295538).sum := by decide
  have hdescent : baseEnd_8295538 < baseStart_8295538 := by decide
  rcases family_descends (prefixWord ++ tailWord_8295538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8295548 : List Nat := [2, 2, 2, 1, 1, 3, 2, 3, 1, 2, 4]
def baseStart_8295548 : Nat := 118140960795 + 8295548 * 2 ^ 59
def prefixEnd_8295548 : Nat := 4983230072969 + 3 ^ 40 * 8295548 * 2
def baseEnd_8295548 : Nat := 4259603416443814863999475

theorem tailTrace_8295548 : CollatzResearch.WordTrace tailWord_8295548 prefixEnd_8295548 4259603416443814863999475 := by
  unfold tailWord_8295548
  simp only [CollatzResearch.WordTrace]
  refine ⟨151281746075326918824471649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 201708994767102558432628865 151281746075326918824471649)
  ·
    refine ⟨113461309556495189118353737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 151281746075326918824471649 113461309556495189118353737)
    ·
      refine ⟨85095982167371391838765303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 113461309556495189118353737 85095982167371391838765303)
      ·
        refine ⟨127643973251057087758147955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85095982167371391838765303 127643973251057087758147955)
        ·
          refine ⟨191465959876585631637221933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 127643973251057087758147955 191465959876585631637221933)
          ·
            refine ⟨71799734953719611863958225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 191465959876585631637221933 71799734953719611863958225)
            ·
              refine ⟨53849801215289708897968669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 71799734953719611863958225 53849801215289708897968669)
              ·
                refine ⟨20193675455733640836738251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 53849801215289708897968669 20193675455733640836738251)
                ·
                  refine ⟨30290513183600461255107377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20193675455733640836738251 30290513183600461255107377)
                  ·
                    refine ⟨22717884887700345941330533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 30290513183600461255107377 22717884887700345941330533)
                    ·
                      refine ⟨4259603416443814863999475, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22717884887700345941330533 4259603416443814863999475)
                      ·
                        rfl

theorem cell23_8295548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 2, 3, 1, 2, 4].length) (baseStart_8295548 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8295548 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8295548 prefixEnd_8295548 := by exact prefixLift 8295548
  have htrace : WordTrace (prefixWord ++ tailWord_8295548) baseStart_8295548 baseEnd_8295548 := by
    simpa [prefixWord, tailWord_8295548, baseEnd_8295548] using wordTrace_append hprefix tailTrace_8295548
  have hstable : (prefixWord ++ tailWord_8295548).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8295548).length < 2 ^ (prefixWord ++ tailWord_8295548).sum := by decide
  have hdescent : baseEnd_8295548 < baseStart_8295548 := by decide
  rcases family_descends (prefixWord ++ tailWord_8295548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8295588 : List Nat := [2, 3, 1, 2, 3, 1, 1, 1, 2, 7]
def baseStart_8295588 : Nat := 118140960795 + 8295588 * 2 ^ 59
def prefixEnd_8295588 : Nat := 4983230072969 + 3 ^ 40 * 8295588 * 2
def baseEnd_8295588 : Nat := 1419874651889998235833097

theorem tailTrace_8295588 : CollatzResearch.WordTrace tailWord_8295588 prefixEnd_8295588 1419874651889998235833097 := by
  unfold tailWord_8295588
  simp only [CollatzResearch.WordTrace]
  refine ⟨151282475535254462240199709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 201709967380339282986932945 151282475535254462240199709)
  ·
    refine ⟨56730928325720423340074891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 151282475535254462240199709 56730928325720423340074891)
    ·
      refine ⟨85096392488580635010112337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56730928325720423340074891 85096392488580635010112337)
      ·
        refine ⟨63822294366435476257584253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85096392488580635010112337 63822294366435476257584253)
        ·
          refine ⟨23933360387413303596594095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 63822294366435476257584253 23933360387413303596594095)
          ·
            refine ⟨35900040581119955394891143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23933360387413303596594095 35900040581119955394891143)
            ·
              refine ⟨53850060871679933092336715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35900040581119955394891143 53850060871679933092336715)
              ·
                refine ⟨80775091307519899638505073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53850060871679933092336715 80775091307519899638505073)
                ·
                  refine ⟨60581318480639924728878805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 80775091307519899638505073 60581318480639924728878805)
                  ·
                    refine ⟨1419874651889998235833097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 60581318480639924728878805 1419874651889998235833097)
                    ·
                      rfl

theorem cell23_8295588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 1, 1, 1, 2, 7].length) (baseStart_8295588 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8295588 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8295588 prefixEnd_8295588 := by exact prefixLift 8295588
  have htrace : WordTrace (prefixWord ++ tailWord_8295588) baseStart_8295588 baseEnd_8295588 := by
    simpa [prefixWord, tailWord_8295588, baseEnd_8295588] using wordTrace_append hprefix tailTrace_8295588
  have hstable : (prefixWord ++ tailWord_8295588).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8295588).length < 2 ^ (prefixWord ++ tailWord_8295588).sum := by decide
  have hdescent : baseEnd_8295588 < baseStart_8295588 := by decide
  rcases family_descends (prefixWord ++ tailWord_8295588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8295602 : List Nat := [3, 2, 1, 1, 1, 4, 2, 3, 2, 1, 3]
def baseStart_8295602 : Nat := 118140960795 + 8295602 * 2 ^ 59
def prefixEnd_8295602 : Nat := 4983230072969 + 3 ^ 40 * 8295602 * 2
def baseEnd_8295602 : Nat := 4259631144399157652724227

theorem tailTrace_8295602 : CollatzResearch.WordTrace tailWord_8295602 prefixEnd_8295602 4259631144399157652724227 := by
  unfold tailWord_8295602
  simp only [CollatzResearch.WordTrace]
  refine ⟨75641365423114551217852265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 201710307794972136580939373 75641365423114551217852265)
  ·
    refine ⟨56731024067335913413389199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75641365423114551217852265 56731024067335913413389199)
    ·
      refine ⟨85096536101003870120083799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56731024067335913413389199 85096536101003870120083799)
      ·
        refine ⟨127644804151505805180125699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85096536101003870120083799 127644804151505805180125699)
        ·
          refine ⟨191467206227258707770188549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 127644804151505805180125699 191467206227258707770188549)
          ·
            refine ⟨35900101167611007706910353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 191467206227258707770188549 35900101167611007706910353)
            ·
              refine ⟨26925075875708255780182765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35900101167611007706910353 26925075875708255780182765)
              ·
                refine ⟨10096903453390595917568537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26925075875708255780182765 10096903453390595917568537)
                ·
                  refine ⟨7572677590042946938176403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10096903453390595917568537 7572677590042946938176403)
                  ·
                    refine ⟨11359016385064420407264605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7572677590042946938176403 11359016385064420407264605)
                    ·
                      refine ⟨4259631144399157652724227, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11359016385064420407264605 4259631144399157652724227)
                      ·
                        rfl

theorem cell23_8295602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 4, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 4, 2, 3, 2, 1, 3].length) (baseStart_8295602 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8295602 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8295602 prefixEnd_8295602 := by exact prefixLift 8295602
  have htrace : WordTrace (prefixWord ++ tailWord_8295602) baseStart_8295602 baseEnd_8295602 := by
    simpa [prefixWord, tailWord_8295602, baseEnd_8295602] using wordTrace_append hprefix tailTrace_8295602
  have hstable : (prefixWord ++ tailWord_8295602).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8295602).length < 2 ^ (prefixWord ++ tailWord_8295602).sum := by decide
  have hdescent : baseEnd_8295602 < baseStart_8295602 := by decide
  rcases family_descends (prefixWord ++ tailWord_8295602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8295612 : List Nat := [2, 2, 2, 3, 2, 1, 2, 1, 3, 3, 2]
def baseStart_8295612 : Nat := 118140960795 + 8295612 * 2 ^ 59
def prefixEnd_8295612 : Nat := 4983230072969 + 3 ^ 40 * 8295612 * 2
def baseEnd_8295612 : Nat := 4259636279205702613599181

theorem tailTrace_8295612 : CollatzResearch.WordTrace tailWord_8295612 prefixEnd_8295612 4259636279205702613599181 := by
  unfold tailWord_8295612
  simp only [CollatzResearch.WordTrace]
  refine ⟨151282913211210988289636545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 201710550948281317719515393 151282913211210988289636545)
  ·
    refine ⟨113462184908408241217227409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 151282913211210988289636545 113462184908408241217227409)
    ·
      refine ⟨85096638681306180912920557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 113462184908408241217227409 85096638681306180912920557)
      ·
        refine ⟨31911239505489817842345209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 85096638681306180912920557 31911239505489817842345209)
        ·
          refine ⟨23933429629117363381758907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31911239505489817842345209 23933429629117363381758907)
          ·
            refine ⟨35900144443676045072638361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23933429629117363381758907 35900144443676045072638361)
            ·
              refine ⟨26925108332757033804478771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35900144443676045072638361 26925108332757033804478771)
              ·
                refine ⟨40387662499135550706718157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26925108332757033804478771 40387662499135550706718157)
                ·
                  refine ⟨15145373437175831515019309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 40387662499135550706718157 15145373437175831515019309)
                  ·
                    refine ⟨5679515038940936818132241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15145373437175831515019309 5679515038940936818132241)
                    ·
                      refine ⟨4259636279205702613599181, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5679515038940936818132241 4259636279205702613599181)
                      ·
                        rfl

theorem cell23_8295612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 1, 2, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 1, 2, 1, 3, 3, 2].length) (baseStart_8295612 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8295612 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8295612 prefixEnd_8295612 := by exact prefixLift 8295612
  have htrace : WordTrace (prefixWord ++ tailWord_8295612) baseStart_8295612 baseEnd_8295612 := by
    simpa [prefixWord, tailWord_8295612, baseEnd_8295612] using wordTrace_append hprefix tailTrace_8295612
  have hstable : (prefixWord ++ tailWord_8295612).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8295612).length < 2 ^ (prefixWord ++ tailWord_8295612).sum := by decide
  have hdescent : baseEnd_8295612 < baseStart_8295612 := by decide
  rcases family_descends (prefixWord ++ tailWord_8295612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8295648 : List Nat := [2, 1, 1, 3, 1, 4, 1, 3, 7]
def baseStart_8295648 : Nat := 118140960795 + 8295648 * 2 ^ 59
def prefixEnd_8295648 : Nat := 4983230072969 + 3 ^ 40 * 8295648 * 2
def baseEnd_8295648 : Nat := 473294973834362719194335

theorem tailTrace_8295648 : CollatzResearch.WordTrace tailWord_8295648 prefixEnd_8295648 473294973834362719194335 := by
  unfold tailWord_8295648
  simp only [CollatzResearch.WordTrace]
  refine ⟨151283569725145777363791799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 201711426300194369818389065 151283569725145777363791799)
  ·
    refine ⟨226925354587718666045687699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151283569725145777363791799 226925354587718666045687699)
    ·
      refine ⟨340388031881577999068531549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 226925354587718666045687699 340388031881577999068531549)
      ·
        refine ⟨127645511955591749650699331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 340388031881577999068531549 127645511955591749650699331)
        ·
          refine ⟨191468267933387624476048997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 127645511955591749650699331 191468267933387624476048997)
          ·
            refine ⟨35900300237510179589259187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 191468267933387624476048997 35900300237510179589259187)
            ·
              refine ⟨53850450356265269383888781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35900300237510179589259187 53850450356265269383888781)
              ·
                refine ⟨20193918883599476018958293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 53850450356265269383888781 20193918883599476018958293)
                ·
                  refine ⟨473294973834362719194335, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 20193918883599476018958293 473294973834362719194335)
                  ·
                    rfl

theorem cell23_8295648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 4, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 4, 1, 3, 7].length) (baseStart_8295648 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8295648 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8295648 prefixEnd_8295648 := by exact prefixLift 8295648
  have htrace : WordTrace (prefixWord ++ tailWord_8295648) baseStart_8295648 baseEnd_8295648 := by
    simpa [prefixWord, tailWord_8295648, baseEnd_8295648] using wordTrace_append hprefix tailTrace_8295648
  have hstable : (prefixWord ++ tailWord_8295648).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8295648).length < 2 ^ (prefixWord ++ tailWord_8295648).sum := by decide
  have hdescent : baseEnd_8295648 < baseStart_8295648 := by decide
  rcases family_descends (prefixWord ++ tailWord_8295648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8295750 : List Nat := [6, 1, 1, 3, 1, 2, 2, 2, 5]
def baseStart_8295750 : Nat := 118140960795 + 8295750 * 2 ^ 59
def prefixEnd_8295750 : Nat := 4983230072969 + 3 ^ 40 * 8295750 * 2
def baseEnd_8295750 : Nat := 473300793281780341519283

theorem tailTrace_8295750 : CollatzResearch.WordTrace tailWord_8295750 prefixEnd_8295750 473300793281780341519283 := by
  unfold tailWord_8295750
  simp only [CollatzResearch.WordTrace]
  refine ⟨9455339365497563317118647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 201713906463948017431864469 9455339365497563317118647)
  ·
    refine ⟨14183009048246344975677971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9455339365497563317118647 14183009048246344975677971)
    ·
      refine ⟨21274513572369517463516957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14183009048246344975677971 21274513572369517463516957)
      ·
        refine ⟨7977942589638569048818859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21274513572369517463516957 7977942589638569048818859)
        ·
          refine ⟨11966913884457853573228289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7977942589638569048818859 11966913884457853573228289)
          ·
            refine ⟨8975185413343390179921217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11966913884457853573228289 8975185413343390179921217)
            ·
              refine ⟨6731389060007542634940913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8975185413343390179921217 6731389060007542634940913)
              ·
                refine ⟨5048541795005656976205685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6731389060007542634940913 5048541795005656976205685)
                ·
                  refine ⟨473300793281780341519283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5048541795005656976205685 473300793281780341519283)
                  ·
                    rfl

theorem cell23_8295750_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 1, 2, 2, 2, 5].length) (baseStart_8295750 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8295750 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8295750 prefixEnd_8295750 := by exact prefixLift 8295750
  have htrace : WordTrace (prefixWord ++ tailWord_8295750) baseStart_8295750 baseEnd_8295750 := by
    simpa [prefixWord, tailWord_8295750, baseEnd_8295750] using wordTrace_append hprefix tailTrace_8295750
  have hstable : (prefixWord ++ tailWord_8295750).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8295750).length < 2 ^ (prefixWord ++ tailWord_8295750).sum := by decide
  have hdescent : baseEnd_8295750 < baseStart_8295750 := by decide
  rcases family_descends (prefixWord ++ tailWord_8295750) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8295786 : List Nat := [3, 1, 3, 3, 2, 2, 1, 1, 2, 2, 3]
def baseStart_8295786 : Nat := 118140960795 + 8295786 * 2 ^ 59
def prefixEnd_8295786 : Nat := 4983230072969 + 3 ^ 40 * 8295786 * 2
def baseEnd_8295786 : Nat := 4259725624839584932823381

theorem tailTrace_8295786 : CollatzResearch.WordTrace tailWord_8295786 prefixEnd_8295786 4259725624839584932823381 := by
  unfold tailWord_8295786
  simp only [CollatzResearch.WordTrace]
  refine ⟨75643043180947901074026803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 201714781815861069530738141 75643043180947901074026803)
  ·
    refine ⟨113464564771421851611040205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75643043180947901074026803 113464564771421851611040205)
    ·
      refine ⟨42549211789283194354140077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 113464564771421851611040205 42549211789283194354140077)
      ·
        refine ⟨15955954420981197882802529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42549211789283194354140077 15955954420981197882802529)
        ·
          refine ⟨11966965815735898412101897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15955954420981197882802529 11966965815735898412101897)
          ·
            refine ⟨8975224361801923809076423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11966965815735898412101897 8975224361801923809076423)
            ·
              refine ⟨13462836542702885713614635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8975224361801923809076423 13462836542702885713614635)
              ·
                refine ⟨20194254814054328570421953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13462836542702885713614635 20194254814054328570421953)
                ·
                  refine ⟨15145691110540746427816465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20194254814054328570421953 15145691110540746427816465)
                  ·
                    refine ⟨11359268332905559820862349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15145691110540746427816465 11359268332905559820862349)
                    ·
                      refine ⟨4259725624839584932823381, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11359268332905559820862349 4259725624839584932823381)
                      ·
                        rfl

theorem cell23_8295786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 2, 2, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 2, 2, 1, 1, 2, 2, 3].length) (baseStart_8295786 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8295786 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8295786 prefixEnd_8295786 := by exact prefixLift 8295786
  have htrace : WordTrace (prefixWord ++ tailWord_8295786) baseStart_8295786 baseEnd_8295786 := by
    simpa [prefixWord, tailWord_8295786, baseEnd_8295786] using wordTrace_append hprefix tailTrace_8295786
  have hstable : (prefixWord ++ tailWord_8295786).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8295786).length < 2 ^ (prefixWord ++ tailWord_8295786).sum := by decide
  have hdescent : baseEnd_8295786 < baseStart_8295786 := by decide
  rcases family_descends (prefixWord ++ tailWord_8295786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8295792 : List Nat := [2, 1, 1, 1, 4, 2, 3, 1, 1, 5, 2]
def baseStart_8295792 : Nat := 118140960795 + 8295792 * 2 ^ 59
def prefixEnd_8295792 : Nat := 4983230072969 + 3 ^ 40 * 8295792 * 2
def baseEnd_8295792 : Nat := 4259728705723511909348353

theorem tailTrace_8295792 : CollatzResearch.WordTrace tailWord_8295792 prefixEnd_8295792 4259728705723511909348353 := by
  unfold tailWord_8295792
  simp only [CollatzResearch.WordTrace]
  refine ⟨151286195780884933660412815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 201714927707846578213883753 151286195780884933660412815)
  ·
    refine ⟨226929293671327400490619223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151286195780884933660412815 226929293671327400490619223)
    ·
      refine ⟨340393940506991100735928835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 226929293671327400490619223 340393940506991100735928835)
      ·
        refine ⟨510590910760486651103893253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 340393940506991100735928835 510590910760486651103893253)
        ·
          refine ⟨95735795767591247081979985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 510590910760486651103893253 95735795767591247081979985)
          ·
            refine ⟨71801846825693435311484989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 95735795767591247081979985 71801846825693435311484989)
            ·
              refine ⟨26925692559635038241806871, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 71801846825693435311484989 26925692559635038241806871)
              ·
                refine ⟨40388538839452557362710307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26925692559635038241806871 40388538839452557362710307)
                ·
                  refine ⟨60582808259178836044065461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40388538839452557362710307 60582808259178836044065461)
                  ·
                    refine ⟨5679638274298015879131137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 60582808259178836044065461 5679638274298015879131137)
                    ·
                      refine ⟨4259728705723511909348353, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5679638274298015879131137 4259728705723511909348353)
                      ·
                        rfl

theorem cell23_8295792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 3, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 3, 1, 1, 5, 2].length) (baseStart_8295792 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8295792 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8295792 prefixEnd_8295792 := by exact prefixLift 8295792
  have htrace : WordTrace (prefixWord ++ tailWord_8295792) baseStart_8295792 baseEnd_8295792 := by
    simpa [prefixWord, tailWord_8295792, baseEnd_8295792] using wordTrace_append hprefix tailTrace_8295792
  have hstable : (prefixWord ++ tailWord_8295792).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8295792).length < 2 ^ (prefixWord ++ tailWord_8295792).sum := by decide
  have hdescent : baseEnd_8295792 < baseStart_8295792 := by decide
  rcases family_descends (prefixWord ++ tailWord_8295792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8295816 : List Nat := [2, 1, 3, 3, 1, 2, 2, 4, 1, 1, 3]
def baseStart_8295816 : Nat := 118140960795 + 8295816 * 2 ^ 59
def prefixEnd_8295816 : Nat := 4983230072969 + 3 ^ 40 * 8295816 * 2
def baseEnd_8295816 : Nat := 4259741029259219815448243

theorem tailTrace_8295816 : CollatzResearch.WordTrace tailWord_8295816 prefixEnd_8295816 4259741029259219815448243 := by
  unfold tailWord_8295816
  simp only [CollatzResearch.WordTrace]
  refine ⟨151286633456841459709849651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 201715511275788612946466201 151286633456841459709849651)
  ·
    refine ⟨226929950185262189564774477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151286633456841459709849651 226929950185262189564774477)
    ·
      refine ⟨85098731319473321086790429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 226929950185262189564774477 85098731319473321086790429)
      ·
        refine ⟨31912024244802495407546411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 85098731319473321086790429 31912024244802495407546411)
        ·
          refine ⟨47868036367203743111319617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31912024244802495407546411 47868036367203743111319617)
          ·
            refine ⟨35901027275402807333489713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47868036367203743111319617 35901027275402807333489713)
            ·
              refine ⟨26925770456552105500117285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35901027275402807333489713 26925770456552105500117285)
              ·
                refine ⟨5048581960603519781271991, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26925770456552105500117285 5048581960603519781271991)
                ·
                  refine ⟨7572872940905279671907987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5048581960603519781271991 7572872940905279671907987)
                  ·
                    refine ⟨11359309411357919507861981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7572872940905279671907987 11359309411357919507861981)
                    ·
                      refine ⟨4259741029259219815448243, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11359309411357919507861981 4259741029259219815448243)
                      ·
                        rfl

theorem cell23_8295816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 2, 2, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 2, 2, 4, 1, 1, 3].length) (baseStart_8295816 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8295816 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8295816 prefixEnd_8295816 := by exact prefixLift 8295816
  have htrace : WordTrace (prefixWord ++ tailWord_8295816) baseStart_8295816 baseEnd_8295816 := by
    simpa [prefixWord, tailWord_8295816, baseEnd_8295816] using wordTrace_append hprefix tailTrace_8295816
  have hstable : (prefixWord ++ tailWord_8295816).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8295816).length < 2 ^ (prefixWord ++ tailWord_8295816).sum := by decide
  have hdescent : baseEnd_8295816 < baseStart_8295816 := by decide
  rcases family_descends (prefixWord ++ tailWord_8295816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8295825 : List Nat := [1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 5]
def baseStart_8295825 : Nat := 118140960795 + 8295825 * 2 ^ 59
def prefixEnd_8295825 : Nat := 4983230072969 + 3 ^ 40 * 8295825 * 2
def baseEnd_8295825 : Nat := 4259745650585110280235701

theorem tailTrace_8295825 : CollatzResearch.WordTrace tailWord_8295825 prefixEnd_8295825 4259745650585110280235701 := by
  unfold tailWord_8295825
  simp only [CollatzResearch.WordTrace]
  refine ⟨302573595170650313956776929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201715730113766875971184619 302573595170650313956776929)
  ·
    refine ⟨226930196377987735467582697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 302573595170650313956776929 226930196377987735467582697)
    ·
      refine ⟨170197647283490801600687023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 226930196377987735467582697 170197647283490801600687023)
      ·
        refine ⟨255296470925236202401030535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 170197647283490801600687023 255296470925236202401030535)
        ·
          refine ⟨382944706387854303601545803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 255296470925236202401030535 382944706387854303601545803)
          ·
            refine ⟨574417059581781455402318705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 382944706387854303601545803 574417059581781455402318705)
            ·
              refine ⟨430812794686336091551739029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 574417059581781455402318705 430812794686336091551739029)
              ·
                refine ⟨20194349750922004291487767, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 430812794686336091551739029 20194349750922004291487767)
                ·
                  refine ⟨30291524626383006437231651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20194349750922004291487767 30291524626383006437231651)
                  ·
                    refine ⟨45437286939574509655847477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 30291524626383006437231651 45437286939574509655847477)
                    ·
                      refine ⟨4259745650585110280235701, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 45437286939574509655847477 4259745650585110280235701)
                      ·
                        rfl

theorem cell23_8295825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 5].length) (baseStart_8295825 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8295825 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8295825 prefixEnd_8295825 := by exact prefixLift 8295825
  have htrace : WordTrace (prefixWord ++ tailWord_8295825) baseStart_8295825 baseEnd_8295825 := by
    simpa [prefixWord, tailWord_8295825, baseEnd_8295825] using wordTrace_append hprefix tailTrace_8295825
  have hstable : (prefixWord ++ tailWord_8295825).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8295825).length < 2 ^ (prefixWord ++ tailWord_8295825).sum := by decide
  have hdescent : baseEnd_8295825 < baseStart_8295825 := by decide
  rcases family_descends (prefixWord ++ tailWord_8295825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8295836 : List Nat := [2, 2, 3, 4, 1, 1, 2, 2, 1, 5]
def baseStart_8295836 : Nat := 118140960795 + 8295836 * 2 ^ 59
def prefixEnd_8295836 : Nat := 4983230072969 + 3 ^ 40 * 8295836 * 2
def baseEnd_8295836 : Nat := 1419917099624103245732717

theorem tailTrace_8295836 : CollatzResearch.WordTrace tailWord_8295836 prefixEnd_8295836 1419917099624103245732717 := by
  unfold tailWord_8295836
  simp only [CollatzResearch.WordTrace]
  refine ⟨151286998186805231417713681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 201715997582406975223618241 151286998186805231417713681)
  ·
    refine ⟨113465248640103923563285261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 151286998186805231417713681 113465248640103923563285261)
    ·
      refine ⟨42549468240038971336231973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 113465248640103923563285261 42549468240038971336231973)
      ·
        refine ⟨7978025295007307125543495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 42549468240038971336231973 7978025295007307125543495)
        ·
          refine ⟨11967037942510960688315243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7978025295007307125543495 11967037942510960688315243)
          ·
            refine ⟨17950556913766441032472865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11967037942510960688315243 17950556913766441032472865)
            ·
              refine ⟨13462917685324830774354649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17950556913766441032472865 13462917685324830774354649)
              ·
                refine ⟨10097188263993623080765987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13462917685324830774354649 10097188263993623080765987)
                ·
                  refine ⟨15145782395990434621148981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10097188263993623080765987 15145782395990434621148981)
                  ·
                    refine ⟨1419917099624103245732717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15145782395990434621148981 1419917099624103245732717)
                    ·
                      rfl

theorem cell23_8295836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 1, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 1, 1, 2, 2, 1, 5].length) (baseStart_8295836 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8295836 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8295836 prefixEnd_8295836 := by exact prefixLift 8295836
  have htrace : WordTrace (prefixWord ++ tailWord_8295836) baseStart_8295836 baseEnd_8295836 := by
    simpa [prefixWord, tailWord_8295836, baseEnd_8295836] using wordTrace_append hprefix tailTrace_8295836
  have hstable : (prefixWord ++ tailWord_8295836).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8295836).length < 2 ^ (prefixWord ++ tailWord_8295836).sum := by decide
  have hdescent : baseEnd_8295836 < baseStart_8295836 := by decide
  rcases family_descends (prefixWord ++ tailWord_8295836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8295839 : List Nat := [1, 1, 2, 5, 1, 3, 2, 2, 1, 1, 4]
def baseStart_8295839 : Nat := 118140960795 + 8295839 * 2 ^ 59
def prefixEnd_8295839 : Nat := 4983230072969 + 3 ^ 40 * 8295839 * 2
def baseEnd_8295839 : Nat := 4259752839314273225460637

theorem tailTrace_8295839 : CollatzResearch.WordTrace tailWord_8295839 prefixEnd_8295839 4259752839314273225460637 := by
  unfold tailWord_8295839
  simp only [CollatzResearch.WordTrace]
  refine ⟨302574105792599594347786571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201716070528399729565191047 302574105792599594347786571)
  ·
    refine ⟨453861158688899391521679857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 302574105792599594347786571 453861158688899391521679857)
    ·
      refine ⟨340395869016674543641259893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 453861158688899391521679857 340395869016674543641259893)
      ·
        refine ⟨31912112720313238466368115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 340395869016674543641259893 31912112720313238466368115)
        ·
          refine ⟨47868169080469857699552173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31912112720313238466368115 47868169080469857699552173)
          ·
            refine ⟨17950563405176196637332065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 47868169080469857699552173 17950563405176196637332065)
            ·
              refine ⟨13462922553882147477999049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17950563405176196637332065 13462922553882147477999049)
              ·
                refine ⟨10097191915411610608499287, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13462922553882147477999049 10097191915411610608499287)
                ·
                  refine ⟨15145787873117415912748931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10097191915411610608499287 15145787873117415912748931)
                  ·
                    refine ⟨22718681809676123869123397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15145787873117415912748931 22718681809676123869123397)
                    ·
                      refine ⟨4259752839314273225460637, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22718681809676123869123397 4259752839314273225460637)
                      ·
                        rfl

theorem cell23_8295839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 3, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 3, 2, 2, 1, 1, 4].length) (baseStart_8295839 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8295839 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8295839 prefixEnd_8295839 := by exact prefixLift 8295839
  have htrace : WordTrace (prefixWord ++ tailWord_8295839) baseStart_8295839 baseEnd_8295839 := by
    simpa [prefixWord, tailWord_8295839, baseEnd_8295839] using wordTrace_append hprefix tailTrace_8295839
  have hstable : (prefixWord ++ tailWord_8295839).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8295839).length < 2 ^ (prefixWord ++ tailWord_8295839).sum := by decide
  have hdescent : baseEnd_8295839 < baseStart_8295839 := by decide
  rcases family_descends (prefixWord ++ tailWord_8295839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8295856 : List Nat := [2, 1, 1, 1, 2, 1, 1, 9, 1, 2, 2]
def baseStart_8295856 : Nat := 118140960795 + 8295856 * 2 ^ 59
def prefixEnd_8295856 : Nat := 4983230072969 + 3 ^ 40 * 8295856 * 2
def baseEnd_8295856 : Nat := 4259761568485399658948059

theorem tailTrace_8295856 : CollatzResearch.WordTrace tailWord_8295856 prefixEnd_8295856 4259761568485399658948059 := by
  unfold tailWord_8295856
  simp only [CollatzResearch.WordTrace]
  refine ⟨151287362916769003125577711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 201716483889025337500770281 151287362916769003125577711)
  ·
    refine ⟨226931044375153504688366567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151287362916769003125577711 226931044375153504688366567)
    ·
      refine ⟨340396566562730257032549851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 226931044375153504688366567 340396566562730257032549851)
      ·
        refine ⟨510594849844095385548824777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 340396566562730257032549851 510594849844095385548824777)
        ·
          refine ⟨382946137383071539161618583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 510594849844095385548824777 382946137383071539161618583)
          ·
            refine ⟨574419206074607308742427875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 382946137383071539161618583 574419206074607308742427875)
            ·
              refine ⟨861628809111910963113641813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 574419206074607308742427875 861628809111910963113641813)
              ·
                refine ⟨5048606303390103299493995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 861628809111910963113641813 5048606303390103299493995)
                ·
                  refine ⟨7572909455085154949240993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5048606303390103299493995 7572909455085154949240993)
                  ·
                    refine ⟨5679682091313866211930745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7572909455085154949240993 5679682091313866211930745)
                    ·
                      refine ⟨4259761568485399658948059, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5679682091313866211930745 4259761568485399658948059)
                      ·
                        rfl

theorem cell23_8295856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 9, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 9, 1, 2, 2].length) (baseStart_8295856 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8295856 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8295856 prefixEnd_8295856 := by exact prefixLift 8295856
  have htrace : WordTrace (prefixWord ++ tailWord_8295856) baseStart_8295856 baseEnd_8295856 := by
    simpa [prefixWord, tailWord_8295856, baseEnd_8295856] using wordTrace_append hprefix tailTrace_8295856
  have hstable : (prefixWord ++ tailWord_8295856).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8295856).length < 2 ^ (prefixWord ++ tailWord_8295856).sum := by decide
  have hdescent : baseEnd_8295856 < baseStart_8295856 := by decide
  rcases family_descends (prefixWord ++ tailWord_8295856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8295915 : List Nat := [1, 1, 1, 1, 2, 3, 2, 3, 1, 3, 5]
def baseStart_8295915 : Nat := 118140960795 + 8295915 * 2 ^ 59
def prefixEnd_8295915 : Nat := 4983230072969 + 3 ^ 40 * 8295915 * 2
def baseEnd_8295915 : Nat := 4259791863844014928110287

theorem tailTrace_8295915 : CollatzResearch.WordTrace tailWord_8295915 prefixEnd_8295915 4259791863844014928110287 := by
  unfold tailWord_8295915
  simp only [CollatzResearch.WordTrace]
  refine ⟨302576877740324259327553199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201717918493549506218368799 302576877740324259327553199)
  ·
    refine ⟨453865316610486388991329799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 302576877740324259327553199 453865316610486388991329799)
    ·
      refine ⟨680797974915729583486994699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 453865316610486388991329799 680797974915729583486994699)
      ·
        refine ⟨1021196962373594375230492049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 680797974915729583486994699 1021196962373594375230492049)
        ·
          refine ⟨765897721780195781422869037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1021196962373594375230492049 765897721780195781422869037)
          ·
            refine ⟨287211645667573418033575889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 765897721780195781422869037 287211645667573418033575889)
            ·
              refine ⟨215408734250680063525181917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 287211645667573418033575889 215408734250680063525181917)
              ·
                refine ⟨80778275344005023821943219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 215408734250680063525181917 80778275344005023821943219)
                ·
                  refine ⟨121167413016007535732914829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 80778275344005023821943219 121167413016007535732914829)
                  ·
                    refine ⟨45437779881002825899843061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 121167413016007535732914829 45437779881002825899843061)
                    ·
                      refine ⟨4259791863844014928110287, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 45437779881002825899843061 4259791863844014928110287)
                      ·
                        rfl

theorem cell23_8295915_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 2, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 2, 3, 1, 3, 5].length) (baseStart_8295915 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8295915 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8295915 prefixEnd_8295915 := by exact prefixLift 8295915
  have htrace : WordTrace (prefixWord ++ tailWord_8295915) baseStart_8295915 baseEnd_8295915 := by
    simpa [prefixWord, tailWord_8295915, baseEnd_8295915] using wordTrace_append hprefix tailTrace_8295915
  have hstable : (prefixWord ++ tailWord_8295915).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8295915).length < 2 ^ (prefixWord ++ tailWord_8295915).sum := by decide
  have hdescent : baseEnd_8295915 < baseStart_8295915 := by decide
  rcases family_descends (prefixWord ++ tailWord_8295915) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8295932 : List Nat := [2, 2, 2, 1, 2, 1, 3, 1, 2, 4, 3]
def baseStart_8295932 : Nat := 118140960795 + 8295932 * 2 ^ 59
def prefixEnd_8295932 : Nat := 4983230072969 + 3 ^ 40 * 8295932 * 2
def baseEnd_8295932 : Nat := 4259800593015141361597709

theorem tailTrace_8295932 : CollatzResearch.WordTrace tailWord_8295932 prefixEnd_8295932 4259800593015141361597709 := by
  unfold tailWord_8295932
  simp only [CollatzResearch.WordTrace]
  refine ⟨151288748890631335615461025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 201718331854175114153948033 151288748890631335615461025)
  ·
    refine ⟨113466561667973501711595769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 151288748890631335615461025 113466561667973501711595769)
    ·
      refine ⟨85099921250980126283696827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 113466561667973501711595769 85099921250980126283696827)
      ·
        refine ⟨127649881876470189425545241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85099921250980126283696827 127649881876470189425545241)
        ·
          refine ⟨95737411407352642069158931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 127649881876470189425545241 95737411407352642069158931)
          ·
            refine ⟨143606117111028963103738397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 95737411407352642069158931 143606117111028963103738397)
            ·
              refine ⟨53852293916635861163901899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 143606117111028963103738397 53852293916635861163901899)
              ·
                refine ⟨80778440874953791745852849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53852293916635861163901899 80778440874953791745852849)
                ·
                  refine ⟨60583830656215343809389637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 80778440874953791745852849 60583830656215343809389637)
                  ·
                    refine ⟨11359468248040376964260557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 60583830656215343809389637 11359468248040376964260557)
                    ·
                      refine ⟨4259800593015141361597709, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11359468248040376964260557 4259800593015141361597709)
                      ·
                        rfl

theorem cell23_8295932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 3, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 3, 1, 2, 4, 3].length) (baseStart_8295932 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8295932 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8295932 prefixEnd_8295932 := by exact prefixLift 8295932
  have htrace : WordTrace (prefixWord ++ tailWord_8295932) baseStart_8295932 baseEnd_8295932 := by
    simpa [prefixWord, tailWord_8295932, baseEnd_8295932] using wordTrace_append hprefix tailTrace_8295932
  have hstable : (prefixWord ++ tailWord_8295932).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8295932).length < 2 ^ (prefixWord ++ tailWord_8295932).sum := by decide
  have hdescent : baseEnd_8295932 < baseStart_8295932 := by decide
  rcases family_descends (prefixWord ++ tailWord_8295932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8295946 : List Nat := [3, 1, 2, 2, 2, 3, 2, 1, 1, 4, 2]
def baseStart_8295946 : Nat := 118140960795 + 8295946 * 2 ^ 59
def prefixEnd_8295946 : Nat := 4983230072969 + 3 ^ 40 * 8295946 * 2
def baseEnd_8295946 : Nat := 4259807781744304306822645

theorem tailTrace_8295946 : CollatzResearch.WordTrace tailWord_8295946 prefixEnd_8295946 4259807781744304306822645 := by
  unfold tailWord_8295946
  simp only [CollatzResearch.WordTrace]
  refine ⟨75644502100802987905482923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 201718672268807967747954461 75644502100802987905482923)
  ·
    refine ⟨113466753151204481858224385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75644502100802987905482923 113466753151204481858224385)
    ·
      refine ⟨85100064863403361393668289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 113466753151204481858224385 85100064863403361393668289)
      ·
        refine ⟨63825048647552521045251217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85100064863403361393668289 63825048647552521045251217)
        ·
          refine ⟨47868786485664390783938413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63825048647552521045251217 47868786485664390783938413)
          ·
            refine ⟨17950794932124146543976905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 47868786485664390783938413 17950794932124146543976905)
            ·
              refine ⟨13463096199093109907982679, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17950794932124146543976905 13463096199093109907982679)
              ·
                refine ⟨20194644298639664861974019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13463096199093109907982679 20194644298639664861974019)
                ·
                  refine ⟨30291966447959497292961029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20194644298639664861974019 30291966447959497292961029)
                  ·
                    refine ⟨5679743708992405742430193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 30291966447959497292961029 5679743708992405742430193)
                    ·
                      refine ⟨4259807781744304306822645, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5679743708992405742430193 4259807781744304306822645)
                      ·
                        rfl

theorem cell23_8295946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 3, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 3, 2, 1, 1, 4, 2].length) (baseStart_8295946 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8295946 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8295946 prefixEnd_8295946 := by exact prefixLift 8295946
  have htrace : WordTrace (prefixWord ++ tailWord_8295946) baseStart_8295946 baseEnd_8295946 := by
    simpa [prefixWord, tailWord_8295946, baseEnd_8295946] using wordTrace_append hprefix tailTrace_8295946
  have hstable : (prefixWord ++ tailWord_8295946).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8295946).length < 2 ^ (prefixWord ++ tailWord_8295946).sum := by decide
  have hdescent : baseEnd_8295946 < baseStart_8295946 := by decide
  rcases family_descends (prefixWord ++ tailWord_8295946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8295962 : List Nat := [3, 1, 1, 3, 1, 1, 1, 1, 3, 5, 3]
def baseStart_8295962 : Nat := 118140960795 + 8295962 * 2 ^ 59
def prefixEnd_8295962 : Nat := 4983230072969 + 3 ^ 40 * 8295962 * 2
def baseEnd_8295962 : Nat := 4259815997434776244222571

theorem tailTrace_8295962 : CollatzResearch.WordTrace tailWord_8295962 prefixEnd_8295962 4259815997434776244222571 := by
  unfold tailWord_8295962
  simp only [CollatzResearch.WordTrace]
  refine ⟨75644647992788496588628535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 201719061314102657569676093 75644647992788496588628535)
  ·
    refine ⟨113466971989182744882942803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75644647992788496588628535 113466971989182744882942803)
    ·
      refine ⟨170200457983774117324414205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113466971989182744882942803 170200457983774117324414205)
      ·
        refine ⟨63825171743915293996655327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 170200457983774117324414205 63825171743915293996655327)
        ·
          refine ⟨95737757615872940994982991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63825171743915293996655327 95737757615872940994982991)
          ·
            refine ⟨143606636423809411492474487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 95737757615872940994982991 143606636423809411492474487)
            ·
              refine ⟨215409954635714117238711731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 143606636423809411492474487 215409954635714117238711731)
              ·
                refine ⟨323114931953571175858067597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 215409954635714117238711731 323114931953571175858067597)
                ·
                  refine ⟨121168099482589190946775349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 323114931953571175858067597 121168099482589190946775349)
                  ·
                    refine ⟨11359509326492736651260189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 121168099482589190946775349 11359509326492736651260189)
                    ·
                      refine ⟨4259815997434776244222571, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11359509326492736651260189 4259815997434776244222571)
                      ·
                        rfl

theorem cell23_8295962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 1, 1, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 1, 1, 3, 5, 3].length) (baseStart_8295962 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8295962 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8295962 prefixEnd_8295962 := by exact prefixLift 8295962
  have htrace : WordTrace (prefixWord ++ tailWord_8295962) baseStart_8295962 baseEnd_8295962 := by
    simpa [prefixWord, tailWord_8295962, baseEnd_8295962] using wordTrace_append hprefix tailTrace_8295962
  have hstable : (prefixWord ++ tailWord_8295962).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8295962).length < 2 ^ (prefixWord ++ tailWord_8295962).sum := by decide
  have hdescent : baseEnd_8295962 < baseStart_8295962 := by decide
  rcases family_descends (prefixWord ++ tailWord_8295962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8295969 : List Nat := [1, 2, 3, 2, 2, 2, 1, 5, 5]
def baseStart_8295969 : Nat := 118140960795 + 8295969 * 2 ^ 59
def prefixEnd_8295969 : Nat := 4983230072969 + 3 ^ 40 * 8295969 * 2
def baseEnd_8295969 : Nat := 473313287977706412981671

theorem tailTrace_8295969 : CollatzResearch.WordTrace tailWord_8295969 prefixEnd_8295969 473313287977706412981671 := by
  unfold tailWord_8295969
  simp only [CollatzResearch.WordTrace]
  refine ⟨302578847282128626550018961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201719231521419084366679307 302578847282128626550018961)
  ·
    refine ⟨226934135461596469912514221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 302578847282128626550018961 226934135461596469912514221)
    ·
      refine ⟨85100300798098676217192833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 226934135461596469912514221 85100300798098676217192833)
      ·
        refine ⟨63825225598574007162894625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85100300798098676217192833 63825225598574007162894625)
        ·
          refine ⟨47868919198930505372170969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63825225598574007162894625 47868919198930505372170969)
          ·
            refine ⟨35901689399197879029128227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47868919198930505372170969 35901689399197879029128227)
            ·
              refine ⟨53852534098796818543692341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35901689399197879029128227 53852534098796818543692341)
              ·
                refine ⟨5048675071762201738471157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 53852534098796818543692341 5048675071762201738471157)
                ·
                  refine ⟨473313287977706412981671, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5048675071762201738471157 473313287977706412981671)
                  ·
                    rfl

theorem cell23_8295969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 2, 1, 5, 5].length) (baseStart_8295969 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8295969 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8295969 prefixEnd_8295969 := by exact prefixLift 8295969
  have htrace : WordTrace (prefixWord ++ tailWord_8295969) baseStart_8295969 baseEnd_8295969 := by
    simpa [prefixWord, tailWord_8295969, baseEnd_8295969] using wordTrace_append hprefix tailTrace_8295969
  have hstable : (prefixWord ++ tailWord_8295969).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8295969).length < 2 ^ (prefixWord ++ tailWord_8295969).sum := by decide
  have hdescent : baseEnd_8295969 < baseStart_8295969 := by decide
  rcases family_descends (prefixWord ++ tailWord_8295969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8296039 : List Nat := [1, 1, 5, 1, 1, 1, 3, 1, 4, 2, 3]
def baseStart_8296039 : Nat := 118140960795 + 8296039 * 2 ^ 59
def prefixEnd_8296039 : Nat := 4983230072969 + 3 ^ 40 * 8296039 * 2
def baseEnd_8296039 : Nat := 4259855535445172442959717

theorem tailTrace_8296039 : CollatzResearch.WordTrace tailWord_8296039 prefixEnd_8296039 4259855535445172442959717 := by
  unfold tailWord_8296039
  simp only [CollatzResearch.WordTrace]
  refine ⟨302581400391875028505067171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201720933594583352336711447 302581400391875028505067171)
  ·
    refine ⟨453872100587812542757600757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 302581400391875028505067171 453872100587812542757600757)
    ·
      refine ⟨42550509430107425883525071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 453872100587812542757600757 42550509430107425883525071)
      ·
        refine ⟨63825764145161138825287607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42550509430107425883525071 63825764145161138825287607)
        ·
          refine ⟨95738646217741708237931411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63825764145161138825287607 95738646217741708237931411)
          ·
            refine ⟨143607969326612562356897117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 95738646217741708237931411 143607969326612562356897117)
            ·
              refine ⟨53852988497479710883836419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 143607969326612562356897117 53852988497479710883836419)
              ·
                refine ⟨80779482746219566325754629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53852988497479710883836419 80779482746219566325754629)
                ·
                  refine ⟨15146153014916168686078993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 80779482746219566325754629 15146153014916168686078993)
                  ·
                    refine ⟨11359614761187126514559245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15146153014916168686078993 11359614761187126514559245)
                    ·
                      refine ⟨4259855535445172442959717, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11359614761187126514559245 4259855535445172442959717)
                      ·
                        rfl

theorem cell23_8296039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 3, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 3, 1, 4, 2, 3].length) (baseStart_8296039 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8296039 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8296039 prefixEnd_8296039 := by exact prefixLift 8296039
  have htrace : WordTrace (prefixWord ++ tailWord_8296039) baseStart_8296039 baseEnd_8296039 := by
    simpa [prefixWord, tailWord_8296039, baseEnd_8296039] using wordTrace_append hprefix tailTrace_8296039
  have hstable : (prefixWord ++ tailWord_8296039).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8296039).length < 2 ^ (prefixWord ++ tailWord_8296039).sum := by decide
  have hdescent : baseEnd_8296039 < baseStart_8296039 := by decide
  rcases family_descends (prefixWord ++ tailWord_8296039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8296119 : List Nat := [1, 1, 3, 1, 5, 1, 1, 3, 1, 6]
def baseStart_8296119 : Nat := 118140960795 + 8296119 * 2 ^ 59
def prefixEnd_8296119 : Nat := 4983230072969 + 3 ^ 40 * 8296119 * 2
def baseEnd_8296119 : Nat := 1419965537965844043319783

theorem tailTrace_8296119 : CollatzResearch.WordTrace tailWord_8296119 prefixEnd_8296119 1419965537965844043319783 := by
  unfold tailWord_8296119
  simp only [CollatzResearch.WordTrace]
  refine ⟨302584318231585202167979411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201722878821056801445319607 302584318231585202167979411)
  ·
    refine ⟨453876477347377803251969117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 302584318231585202167979411 453876477347377803251969117)
    ·
      refine ⟨170203679005266676219488419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 453876477347377803251969117 170203679005266676219488419)
      ·
        refine ⟨255305518507900014329232629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 170203679005266676219488419 255305518507900014329232629)
        ·
          refine ⟨23934892360115626343365559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 255305518507900014329232629 23934892360115626343365559)
          ·
            refine ⟨35902338540173439515048339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23934892360115626343365559 35902338540173439515048339)
            ·
              refine ⟨53853507810260159272572509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35902338540173439515048339 53853507810260159272572509)
              ·
                refine ⟨20195065428847559727214691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 53853507810260159272572509 20195065428847559727214691)
                ·
                  refine ⟨30292598143271339590822037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20195065428847559727214691 30292598143271339590822037)
                  ·
                    refine ⟨1419965537965844043319783, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 30292598143271339590822037 1419965537965844043319783)
                    ·
                      rfl

theorem cell23_8296119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 1, 1, 3, 1, 6].length) (baseStart_8296119 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8296119 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8296119 prefixEnd_8296119 := by exact prefixLift 8296119
  have htrace : WordTrace (prefixWord ++ tailWord_8296119) baseStart_8296119 baseEnd_8296119 := by
    simpa [prefixWord, tailWord_8296119, baseEnd_8296119] using wordTrace_append hprefix tailTrace_8296119
  have hstable : (prefixWord ++ tailWord_8296119).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8296119).length < 2 ^ (prefixWord ++ tailWord_8296119).sum := by decide
  have hdescent : baseEnd_8296119 < baseStart_8296119 := by decide
  rcases family_descends (prefixWord ++ tailWord_8296119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8296126 : List Nat := [4, 2, 1, 1, 2, 2, 2, 1, 3, 1, 4]
def baseStart_8296126 : Nat := 118140960795 + 8296126 * 2 ^ 59
def prefixEnd_8296126 : Nat := 4983230072969 + 3 ^ 40 * 8296126 * 2
def baseEnd_8296126 : Nat := 4259900208262113602571817

theorem tailTrace_8296126 : CollatzResearch.WordTrace tailWord_8296126 prefixEnd_8296126 4259900208262113602571817 := by
  unfold tailWord_8296126
  simp only [CollatzResearch.WordTrace]
  refine ⟨37823071692819980295435529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 201723049028373228242322821 37823071692819980295435529)
  ·
    refine ⟨28367303769614985221576647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37823071692819980295435529 28367303769614985221576647)
    ·
      refine ⟨42550955654422477832364971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28367303769614985221576647 42550955654422477832364971)
      ·
        refine ⟨63826433481633716748547457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42550955654422477832364971 63826433481633716748547457)
        ·
          refine ⟨47869825111225287561410593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63826433481633716748547457 47869825111225287561410593)
          ·
            refine ⟨35902368833418965671057945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47869825111225287561410593 35902368833418965671057945)
            ·
              refine ⟨26926776625064224253293459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35902368833418965671057945 26926776625064224253293459)
              ·
                refine ⟨40390164937596336379940189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26926776625064224253293459 40390164937596336379940189)
                ·
                  refine ⟨15146311851598626142477571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 40390164937596336379940189 15146311851598626142477571)
                  ·
                    refine ⟨22719467777397939213716357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15146311851598626142477571 22719467777397939213716357)
                    ·
                      refine ⟨4259900208262113602571817, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22719467777397939213716357 4259900208262113602571817)
                      ·
                        rfl

theorem cell23_8296126_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 2, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 2, 2, 1, 3, 1, 4].length) (baseStart_8296126 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8296126 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8296126 prefixEnd_8296126 := by exact prefixLift 8296126
  have htrace : WordTrace (prefixWord ++ tailWord_8296126) baseStart_8296126 baseEnd_8296126 := by
    simpa [prefixWord, tailWord_8296126, baseEnd_8296126] using wordTrace_append hprefix tailTrace_8296126
  have hstable : (prefixWord ++ tailWord_8296126).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8296126).length < 2 ^ (prefixWord ++ tailWord_8296126).sum := by decide
  have hdescent : baseEnd_8296126 < baseStart_8296126 := by decide
  rcases family_descends (prefixWord ++ tailWord_8296126) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8296140 : List Nat := [2, 2, 1, 5, 2, 2, 2, 1, 1, 5]
def baseStart_8296140 : Nat := 118140960795 + 8296140 * 2 ^ 59
def prefixEnd_8296140 : Nat := 4983230072969 + 3 ^ 40 * 8296140 * 2
def baseEnd_8296140 : Nat := 1419969132330425515932251

theorem tailTrace_8296140 : CollatzResearch.WordTrace tailWord_8296140 prefixEnd_8296140 1419969132330425515932251 := by
  unfold tailWord_8296140
  simp only [CollatzResearch.WordTrace]
  refine ⟨151292542082254561377246937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 201723389443006081836329249 151292542082254561377246937)
  ·
    refine ⟨113469406561690921032935203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 151292542082254561377246937 113469406561690921032935203)
    ·
      refine ⟨170204109842536381549402805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113469406561690921032935203 170204109842536381549402805)
      ·
        refine ⟨15956635297737785770256513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 170204109842536381549402805 15956635297737785770256513)
        ·
          refine ⟨11967476473303339327692385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15956635297737785770256513 11967476473303339327692385)
          ·
            refine ⟨8975607354977504495769289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11967476473303339327692385 8975607354977504495769289)
            ·
              refine ⟨6731705516233128371826967, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8975607354977504495769289 6731705516233128371826967)
              ·
                refine ⟨10097558274349692557740451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6731705516233128371826967 10097558274349692557740451)
                ·
                  refine ⟨15146337411524538836610677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10097558274349692557740451 15146337411524538836610677)
                  ·
                    refine ⟨1419969132330425515932251, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15146337411524538836610677 1419969132330425515932251)
                    ·
                      rfl

theorem cell23_8296140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 2, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 2, 2, 2, 1, 1, 5].length) (baseStart_8296140 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8296140 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8296140 prefixEnd_8296140 := by exact prefixLift 8296140
  have htrace : WordTrace (prefixWord ++ tailWord_8296140) baseStart_8296140 baseEnd_8296140 := by
    simpa [prefixWord, tailWord_8296140, baseEnd_8296140] using wordTrace_append hprefix tailTrace_8296140
  have hstable : (prefixWord ++ tailWord_8296140).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8296140).length < 2 ^ (prefixWord ++ tailWord_8296140).sum := by decide
  have hdescent : baseEnd_8296140 < baseStart_8296140 := by decide
  rcases family_descends (prefixWord ++ tailWord_8296140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8296153 : List Nat := [1, 2, 1, 2, 3, 5, 1, 2, 2, 4]
def baseStart_8296153 : Nat := 118140960795 + 8296153 * 2 ^ 59
def prefixEnd_8296153 : Nat := 4983230072969 + 3 ^ 40 * 8296153 * 2
def baseEnd_8296153 : Nat := 1419971357413261665644731

theorem tailTrace_8296153 : CollatzResearch.WordTrace tailWord_8296153 prefixEnd_8296153 1419971357413261665644731 := by
  unfold tailWord_8296153
  simp only [CollatzResearch.WordTrace]
  refine ⟨302585558313462025974717113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201723705542308017316478075 302585558313462025974717113)
  ·
    refine ⟨226939168735096519481037835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 302585558313462025974717113 226939168735096519481037835)
    ·
      refine ⟨340408753102644779221556753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 226939168735096519481037835 340408753102644779221556753)
      ·
        refine ⟨255306564826983584416167565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 340408753102644779221556753 255306564826983584416167565)
        ·
          refine ⟨95739961810118844156062837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 255306564826983584416167565 95739961810118844156062837)
          ·
            refine ⟨8975621419698641639630891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 95739961810118844156062837 8975621419698641639630891)
            ·
              refine ⟨13463432129547962459446337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8975621419698641639630891 13463432129547962459446337)
              ·
                refine ⟨10097574097160971844584753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13463432129547962459446337 10097574097160971844584753)
                ·
                  refine ⟨7573180572870728883438565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10097574097160971844584753 7573180572870728883438565)
                  ·
                    refine ⟨1419971357413261665644731, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7573180572870728883438565 1419971357413261665644731)
                    ·
                      rfl

theorem cell23_8296153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 5, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 5, 1, 2, 2, 4].length) (baseStart_8296153 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8296153 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8296153 prefixEnd_8296153 := by exact prefixLift 8296153
  have htrace : WordTrace (prefixWord ++ tailWord_8296153) baseStart_8296153 baseEnd_8296153 := by
    simpa [prefixWord, tailWord_8296153, baseEnd_8296153] using wordTrace_append hprefix tailTrace_8296153
  have hstable : (prefixWord ++ tailWord_8296153).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8296153).length < 2 ^ (prefixWord ++ tailWord_8296153).sum := by decide
  have hdescent : baseEnd_8296153 < baseStart_8296153 := by decide
  rcases family_descends (prefixWord ++ tailWord_8296153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8296160 : List Nat := [2, 1, 1, 3, 1, 2, 4, 4, 1, 2, 2]
def baseStart_8296160 : Nat := 118140960795 + 8296160 * 2 ^ 59
def prefixEnd_8296160 : Nat := 4983230072969 + 3 ^ 40 * 8296160 * 2
def baseEnd_8296160 : Nat := 4259917666604366469546661

theorem tailTrace_8296160 : CollatzResearch.WordTrace tailWord_8296160 prefixEnd_8296160 4259917666604366469546661 := by
  unfold tailWord_8296160
  simp only [CollatzResearch.WordTrace]
  refine ⟨151292906812218333085110967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 201723875749624444113481289 151292906812218333085110967)
  ·
    refine ⟨226939360218327499627666451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151292906812218333085110967 226939360218327499627666451)
    ·
      refine ⟨340409040327491249441499677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 226939360218327499627666451 340409040327491249441499677)
      ·
        refine ⟨127653390122809218540562379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 340409040327491249441499677 127653390122809218540562379)
        ·
          refine ⟨191480085184213827810843569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 127653390122809218540562379 191480085184213827810843569)
          ·
            refine ⟨143610063888160370858132677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 191480085184213827810843569 143610063888160370858132677)
            ·
              refine ⟨26926886979030069535899877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 143610063888160370858132677 26926886979030069535899877)
              ·
                refine ⟨5048791308568138037981227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26926886979030069535899877 5048791308568138037981227)
                ·
                  refine ⟨7573186962852207056971841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5048791308568138037981227 7573186962852207056971841)
                  ·
                    refine ⟨5679890222139155292728881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7573186962852207056971841 5679890222139155292728881)
                    ·
                      refine ⟨4259917666604366469546661, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5679890222139155292728881 4259917666604366469546661)
                      ·
                        rfl

theorem cell23_8296160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 4, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 4, 4, 1, 2, 2].length) (baseStart_8296160 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8296160 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8296160 prefixEnd_8296160 := by exact prefixLift 8296160
  have htrace : WordTrace (prefixWord ++ tailWord_8296160) baseStart_8296160 baseEnd_8296160 := by
    simpa [prefixWord, tailWord_8296160, baseEnd_8296160] using wordTrace_append hprefix tailTrace_8296160
  have hstable : (prefixWord ++ tailWord_8296160).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8296160).length < 2 ^ (prefixWord ++ tailWord_8296160).sum := by decide
  have hdescent : baseEnd_8296160 < baseStart_8296160 := by decide
  rcases family_descends (prefixWord ++ tailWord_8296160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8296173 : List Nat := [1, 5, 1, 2, 1, 4, 1, 1, 1, 2, 4]
def baseStart_8296173 : Nat := 118140960795 + 8296173 * 2 ^ 59
def prefixEnd_8296173 : Nat := 4983230072969 + 3 ^ 40 * 8296173 * 2
def baseEnd_8296173 : Nat := 4259924341852874918684101

theorem tailTrace_8296173 : CollatzResearch.WordTrace tailWord_8296173 prefixEnd_8296173 4259924341852874918684101 := by
  unfold tailWord_8296173
  simp only [CollatzResearch.WordTrace]
  refine ⟨302586287773389569390445173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201724191848926379593630115 302586287773389569390445173)
  ·
    refine ⟨28367464478755272130354235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 302586287773389569390445173 28367464478755272130354235)
    ·
      refine ⟨42551196718132908195531353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28367464478755272130354235 42551196718132908195531353)
      ·
        refine ⟨31913397538599681146648515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42551196718132908195531353 31913397538599681146648515)
        ·
          refine ⟨47870096307899521719972773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31913397538599681146648515 47870096307899521719972773)
          ·
            refine ⟨8975643057731160322494895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 47870096307899521719972773 8975643057731160322494895)
            ·
              refine ⟨13463464586596740483742343, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8975643057731160322494895 13463464586596740483742343)
              ·
                refine ⟨20195196879895110725613515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13463464586596740483742343 20195196879895110725613515)
                ·
                  refine ⟨30292795319842666088420273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20195196879895110725613515 30292795319842666088420273)
                  ·
                    refine ⟨22719596489881999566315205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 30292795319842666088420273 22719596489881999566315205)
                    ·
                      refine ⟨4259924341852874918684101, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22719596489881999566315205 4259924341852874918684101)
                      ·
                        rfl

theorem cell23_8296173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 4, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 4, 1, 1, 1, 2, 4].length) (baseStart_8296173 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8296173 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8296173 prefixEnd_8296173 := by exact prefixLift 8296173
  have htrace : WordTrace (prefixWord ++ tailWord_8296173) baseStart_8296173 baseEnd_8296173 := by
    simpa [prefixWord, tailWord_8296173, baseEnd_8296173] using wordTrace_append hprefix tailTrace_8296173
  have hstable : (prefixWord ++ tailWord_8296173).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8296173).length < 2 ^ (prefixWord ++ tailWord_8296173).sum := by decide
  have hdescent : baseEnd_8296173 < baseStart_8296173 := by decide
  rcases family_descends (prefixWord ++ tailWord_8296173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8296203 : List Nat := [1, 1, 1, 1, 5, 1, 4, 3, 1, 3, 2]
def baseStart_8296203 : Nat := 118140960795 + 8296203 * 2 ^ 59
def prefixEnd_8296203 : Nat := 4983230072969 + 3 ^ 40 * 8296203 * 2
def baseEnd_8296203 : Nat := 4259939746272509801308963

theorem tailTrace_8296203 : CollatzResearch.WordTrace tailWord_8296203 prefixEnd_8296203 4259939746272509801308963 := by
  unfold tailWord_8296203
  simp only [CollatzResearch.WordTrace]
  refine ⟨302587381963280884514037263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201724921308853923009358175 302587381963280884514037263)
  ·
    refine ⟨453881072944921326771055895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 302587381963280884514037263 453881072944921326771055895)
    ·
      refine ⟨680821609417381990156583843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 453881072944921326771055895 680821609417381990156583843)
      ·
        refine ⟨1021232414126072985234875765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 680821609417381990156583843 1021232414126072985234875765)
        ·
          refine ⟨95740538824319342365769603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 1021232414126072985234875765 95740538824319342365769603)
          ·
            refine ⟨143610808236479013548654405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 95740538824319342365769603 143610808236479013548654405)
            ·
              refine ⟨26927026544339815040372701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 143610808236479013548654405 26927026544339815040372701)
              ·
                refine ⟨10097634954127430640139763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26927026544339815040372701 10097634954127430640139763)
                ·
                  refine ⟨15146452431191145960209645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10097634954127430640139763 15146452431191145960209645)
                  ·
                    refine ⟨5679919661696679735078617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15146452431191145960209645 5679919661696679735078617)
                    ·
                      refine ⟨4259939746272509801308963, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5679919661696679735078617 4259939746272509801308963)
                      ·
                        rfl

theorem cell23_8296203_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 4, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 4, 3, 1, 3, 2].length) (baseStart_8296203 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8296203 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8296203 prefixEnd_8296203 := by exact prefixLift 8296203
  have htrace : WordTrace (prefixWord ++ tailWord_8296203) baseStart_8296203 baseEnd_8296203 := by
    simpa [prefixWord, tailWord_8296203, baseEnd_8296203] using wordTrace_append hprefix tailTrace_8296203
  have hstable : (prefixWord ++ tailWord_8296203).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8296203).length < 2 ^ (prefixWord ++ tailWord_8296203).sum := by decide
  have hdescent : baseEnd_8296203 < baseStart_8296203 := by decide
  rcases family_descends (prefixWord ++ tailWord_8296203) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8296210 : List Nat := [3, 2, 4, 1, 1, 1, 2, 1, 4, 1, 3]
def baseStart_8296210 : Nat := 118140960795 + 8296210 * 2 ^ 59
def prefixEnd_8296210 : Nat := 4983230072969 + 3 ^ 40 * 8296210 * 2
def baseEnd_8296210 : Nat := 4259943340637091273921431

theorem tailTrace_8296210 : CollatzResearch.WordTrace tailWord_8296210 prefixEnd_8296210 4259943340637091273921431 := by
  unfold tailWord_8296210
  simp only [CollatzResearch.WordTrace]
  refine ⟨75646909318563881177385521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 201725091516170349806361389 75646909318563881177385521)
  ·
    refine ⟨56735181988922910883039141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75646909318563881177385521 56735181988922910883039141)
    ·
      refine ⟨10637846622923045790569839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 56735181988922910883039141 10637846622923045790569839)
      ·
        refine ⟨15956769934384568685854759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10637846622923045790569839 15956769934384568685854759)
        ·
          refine ⟨23935154901576853028782139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15956769934384568685854759 23935154901576853028782139)
          ·
            refine ⟨35902732352365279543173209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23935154901576853028782139 35902732352365279543173209)
            ·
              refine ⟨26927049264273959657379907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35902732352365279543173209 26927049264273959657379907)
              ·
                refine ⟨40390573896410939486069861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26927049264273959657379907 40390573896410939486069861)
                ·
                  refine ⟨7573232605577051153638099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 40390573896410939486069861 7573232605577051153638099)
                  ·
                    refine ⟨11359848908365576730457149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7573232605577051153638099 11359848908365576730457149)
                    ·
                      refine ⟨4259943340637091273921431, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11359848908365576730457149 4259943340637091273921431)
                      ·
                        rfl

theorem cell23_8296210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 1, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 1, 2, 1, 4, 1, 3].length) (baseStart_8296210 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8296210 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8296210 prefixEnd_8296210 := by exact prefixLift 8296210
  have htrace : WordTrace (prefixWord ++ tailWord_8296210) baseStart_8296210 baseEnd_8296210 := by
    simpa [prefixWord, tailWord_8296210, baseEnd_8296210] using wordTrace_append hprefix tailTrace_8296210
  have hstable : (prefixWord ++ tailWord_8296210).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8296210).length < 2 ^ (prefixWord ++ tailWord_8296210).sum := by decide
  have hdescent : baseEnd_8296210 < baseStart_8296210 := by decide
  rcases family_descends (prefixWord ++ tailWord_8296210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8296219 : List Nat := [1, 1, 1, 1, 1, 1, 4, 3, 1, 6, 3]
def baseStart_8296219 : Nat := 118140960795 + 8296219 * 2 ^ 59
def prefixEnd_8296219 : Nat := 4983230072969 + 3 ^ 40 * 8296219 * 2
def baseEnd_8296219 : Nat := 4259947961962981738708889

theorem tailTrace_8296219 : CollatzResearch.WordTrace tailWord_8296219 prefixEnd_8296219 4259947961962981738708889 := by
  unfold tailWord_8296219
  simp only [CollatzResearch.WordTrace]
  refine ⟨302587965531222919246619711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201725310354148612831079807 302587965531222919246619711)
  ·
    refine ⟨453881948296834378869929567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 302587965531222919246619711 453881948296834378869929567)
    ·
      refine ⟨680822922445251568304894351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 453881948296834378869929567 680822922445251568304894351)
      ·
        refine ⟨1021234383667877352457341527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 680822922445251568304894351 1021234383667877352457341527)
        ·
          refine ⟨1531851575501816028686012291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1021234383667877352457341527 1531851575501816028686012291)
          ·
            refine ⟨2297777363252724043029018437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1531851575501816028686012291 2297777363252724043029018437)
            ·
              refine ⟨430833255609885758067940957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2297777363252724043029018437 430833255609885758067940957)
              ·
                refine ⟨161562470853707159275477859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 430833255609885758067940957 161562470853707159275477859)
                ·
                  refine ⟨242343706280560738913216789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 161562470853707159275477859 242343706280560738913216789)
                  ·
                    refine ⟨11359861231901284636557037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 242343706280560738913216789 11359861231901284636557037)
                    ·
                      refine ⟨4259947961962981738708889, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11359861231901284636557037 4259947961962981738708889)
                      ·
                        rfl

theorem cell23_8296219_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 4, 3, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 4, 3, 1, 6, 3].length) (baseStart_8296219 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8296219 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8296219 prefixEnd_8296219 := by exact prefixLift 8296219
  have htrace : WordTrace (prefixWord ++ tailWord_8296219) baseStart_8296219 baseEnd_8296219 := by
    simpa [prefixWord, tailWord_8296219, baseEnd_8296219] using wordTrace_append hprefix tailTrace_8296219
  have hstable : (prefixWord ++ tailWord_8296219).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8296219).length < 2 ^ (prefixWord ++ tailWord_8296219).sum := by decide
  have hdescent : baseEnd_8296219 < baseStart_8296219 := by decide
  rcases family_descends (prefixWord ++ tailWord_8296219) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8296266 : List Nat := [3, 1, 2, 1, 1, 1, 4, 2, 2, 3, 3]
def baseStart_8296266 : Nat := 118140960795 + 8296266 * 2 ^ 59
def prefixEnd_8296266 : Nat := 4983230072969 + 3 ^ 40 * 8296266 * 2
def baseEnd_8296266 : Nat := 4259972095553743054821173

theorem tailTrace_8296266 : CollatzResearch.WordTrace tailWord_8296266 prefixEnd_8296266 4259972095553743054821173 := by
  unfold tailWord_8296266
  simp only [CollatzResearch.WordTrace]
  refine ⟨75647419940513161568395163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 201726453174701764182387101 75647419940513161568395163)
  ·
    refine ⟨113471129910769742352592745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75647419940513161568395163 113471129910769742352592745)
    ·
      refine ⟨85103347433077306764444559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 113471129910769742352592745 85103347433077306764444559)
      ·
        refine ⟨127655021149615960146666839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85103347433077306764444559 127655021149615960146666839)
        ·
          refine ⟨191482531724423940220000259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 127655021149615960146666839 191482531724423940220000259)
          ·
            refine ⟨287223797586635910330000389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 191482531724423940220000259 287223797586635910330000389)
            ·
              refine ⟨53854462047494233186875073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 287223797586635910330000389 53854462047494233186875073)
              ·
                refine ⟨40390846535620674890156305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53854462047494233186875073 40390846535620674890156305)
                ·
                  refine ⟨30293134901715506167617229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40390846535620674890156305 30293134901715506167617229)
                  ·
                    refine ⟨11359925588143314812856461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 30293134901715506167617229 11359925588143314812856461)
                    ·
                      refine ⟨4259972095553743054821173, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11359925588143314812856461 4259972095553743054821173)
                      ·
                        rfl

theorem cell23_8296266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 4, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 4, 2, 2, 3, 3].length) (baseStart_8296266 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8296266 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8296266 prefixEnd_8296266 := by exact prefixLift 8296266
  have htrace : WordTrace (prefixWord ++ tailWord_8296266) baseStart_8296266 baseEnd_8296266 := by
    simpa [prefixWord, tailWord_8296266, baseEnd_8296266] using wordTrace_append hprefix tailTrace_8296266
  have hstable : (prefixWord ++ tailWord_8296266).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8296266).length < 2 ^ (prefixWord ++ tailWord_8296266).sum := by decide
  have hdescent : baseEnd_8296266 < baseStart_8296266 := by decide
  rcases family_descends (prefixWord ++ tailWord_8296266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8296273 : List Nat := [1, 2, 2, 1, 5, 2, 1, 4, 5]
def baseStart_8296273 : Nat := 118140960795 + 8296273 * 2 ^ 59
def prefixEnd_8296273 : Nat := 4983230072969 + 3 ^ 40 * 8296273 * 2
def baseEnd_8296273 : Nat := 473330632213147169714849

theorem tailTrace_8296273 : CollatzResearch.WordTrace tailWord_8296273 prefixEnd_8296273 473330632213147169714849 := by
  unfold tailWord_8296273
  simp only [CollatzResearch.WordTrace]
  refine ⟨302589935073027286469085473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201726623382018190979390315 302589935073027286469085473)
  ·
    refine ⟨226942451304770464851814105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 302589935073027286469085473 226942451304770464851814105)
    ·
      refine ⟨170206838478577848638860579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 226942451304770464851814105 170206838478577848638860579)
      ·
        refine ⟨255310257717866772958290869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 170206838478577848638860579 255310257717866772958290869)
        ·
          refine ⟨23935336661050009964839769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 255310257717866772958290869 23935336661050009964839769)
          ·
            refine ⟨17951502495787507473629827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23935336661050009964839769 17951502495787507473629827)
            ·
              refine ⟨26927253743681261210444741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17951502495787507473629827 26927253743681261210444741)
              ·
                refine ⟨5048860076940236476958389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26927253743681261210444741 5048860076940236476958389)
                ·
                  refine ⟨473330632213147169714849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5048860076940236476958389 473330632213147169714849)
                  ·
                    rfl

theorem cell23_8296273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 2, 1, 4, 5].length) (baseStart_8296273 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8296273 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8296273 prefixEnd_8296273 := by exact prefixLift 8296273
  have htrace : WordTrace (prefixWord ++ tailWord_8296273) baseStart_8296273 baseEnd_8296273 := by
    simpa [prefixWord, tailWord_8296273, baseEnd_8296273] using wordTrace_append hprefix tailTrace_8296273
  have hstable : (prefixWord ++ tailWord_8296273).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8296273).length < 2 ^ (prefixWord ++ tailWord_8296273).sum := by decide
  have hdescent : baseEnd_8296273 < baseStart_8296273 := by decide
  rcases family_descends (prefixWord ++ tailWord_8296273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8296323 : List Nat := [1, 1, 1, 3, 4, 2, 1, 2, 2, 4, 2]
def baseStart_8296323 : Nat := 118140960795 + 8296323 * 2 ^ 59
def prefixEnd_8296323 : Nat := 4983230072969 + 3 ^ 40 * 8296323 * 2
def baseEnd_8296323 : Nat := 4260001363951049331808411

theorem tailTrace_8296323 : CollatzResearch.WordTrace tailWord_8296323 prefixEnd_8296323 4260001363951049331808411 := by
  unfold tailWord_8296323
  simp only [CollatzResearch.WordTrace]
  refine ⟨302591758722846145008405623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201727839148564096672270415 302591758722846145008405623)
  ·
    refine ⟨453887638084269217512608435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 302591758722846145008405623 453887638084269217512608435)
    ·
      refine ⟨680831457126403826268912653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 453887638084269217512608435 680831457126403826268912653)
      ·
        refine ⟨255311796422401434850842245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 680831457126403826268912653 255311796422401434850842245)
        ·
          refine ⟨47870961829200269034532921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 255311796422401434850842245 47870961829200269034532921)
          ·
            refine ⟨35903221371900201775899691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47870961829200269034532921 35903221371900201775899691)
            ·
              refine ⟨53854832057850302663849537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35903221371900201775899691 53854832057850302663849537)
              ·
                refine ⟨40391124043387726997887153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53854832057850302663849537 40391124043387726997887153)
                ·
                  refine ⟨30293343032540795248415365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40391124043387726997887153 30293343032540795248415365)
                  ·
                    refine ⟨5680001818601399109077881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 30293343032540795248415365 5680001818601399109077881)
                    ·
                      refine ⟨4260001363951049331808411, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5680001818601399109077881 4260001363951049331808411)
                      ·
                        rfl

theorem cell23_8296323_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 2, 1, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 2, 1, 2, 2, 4, 2].length) (baseStart_8296323 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8296323 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8296323 prefixEnd_8296323 := by exact prefixLift 8296323
  have htrace : WordTrace (prefixWord ++ tailWord_8296323) baseStart_8296323 baseEnd_8296323 := by
    simpa [prefixWord, tailWord_8296323, baseEnd_8296323] using wordTrace_append hprefix tailTrace_8296323
  have hstable : (prefixWord ++ tailWord_8296323).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8296323).length < 2 ^ (prefixWord ++ tailWord_8296323).sum := by decide
  have hdescent : baseEnd_8296323 < baseStart_8296323 := by decide
  rcases family_descends (prefixWord ++ tailWord_8296323) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8296339 : List Nat := [1, 1, 1, 2, 1, 2, 1, 2, 2, 1, 9]
def baseStart_8296339 : Nat := 118140960795 + 8296339 * 2 ^ 59
def prefixEnd_8296339 : Nat := 4983230072969 + 3 ^ 40 * 8296339 * 2
def baseEnd_8296339 : Nat := 4260009579641521269208337

theorem tailTrace_8296339 : CollatzResearch.WordTrace tailWord_8296339 prefixEnd_8296339 4260009579641521269208337 := by
  unfold tailWord_8296339
  simp only [CollatzResearch.WordTrace]
  refine ⟨302592342290788179740988071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201728228193858786493992047 302592342290788179740988071)
  ·
    refine ⟨453888513436182269611482107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 302592342290788179740988071 453888513436182269611482107)
    ·
      refine ⟨680832770154273404417223161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 453888513436182269611482107 680832770154273404417223161)
      ·
        refine ⟨510624577615705053312917371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 680832770154273404417223161 510624577615705053312917371)
        ·
          refine ⟨765936866423557579969376057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 510624577615705053312917371 765936866423557579969376057)
          ·
            refine ⟨574452649817668184977032043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 765936866423557579969376057 574452649817668184977032043)
            ·
              refine ⟨861678974726502277465548065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 574452649817668184977032043 861678974726502277465548065)
              ·
                refine ⟨646259231044876708099161049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 861678974726502277465548065 646259231044876708099161049)
                ·
                  refine ⟨484694423283657531074370787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 646259231044876708099161049 484694423283657531074370787)
                  ·
                    refine ⟨727041634925486296611556181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 484694423283657531074370787 727041634925486296611556181)
                    ·
                      refine ⟨4260009579641521269208337, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 727041634925486296611556181 4260009579641521269208337)
                      ·
                        rfl

theorem cell23_8296339_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 2, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 2, 2, 1, 9].length) (baseStart_8296339 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8296339 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8296339 prefixEnd_8296339 := by exact prefixLift 8296339
  have htrace : WordTrace (prefixWord ++ tailWord_8296339) baseStart_8296339 baseEnd_8296339 := by
    simpa [prefixWord, tailWord_8296339, baseEnd_8296339] using wordTrace_append hprefix tailTrace_8296339
  have hstable : (prefixWord ++ tailWord_8296339).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8296339).length < 2 ^ (prefixWord ++ tailWord_8296339).sum := by decide
  have hdescent : baseEnd_8296339 < baseStart_8296339 := by decide
  rcases family_descends (prefixWord ++ tailWord_8296339) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8296340 : List Nat := [2, 4, 2, 1, 1, 2, 2, 1, 2, 4, 2]
def baseStart_8296340 : Nat := 118140960795 + 8296340 * 2 ^ 59
def prefixEnd_8296340 : Nat := 4983230072969 + 3 ^ 40 * 8296340 * 2
def baseEnd_8296340 : Nat := 4260010093122175765295833

theorem tailTrace_8296340 : CollatzResearch.WordTrace tailWord_8296340 prefixEnd_8296340 4260010093122175765295833 := by
  unfold tailWord_8296340
  simp only [CollatzResearch.WordTrace]
  refine ⟨151296189381892278455887237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 201728252509189704607849649 151296189381892278455887237)
  ·
    refine ⟨28368035509104802210478857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 151296189381892278455887237 28368035509104802210478857)
    ·
      refine ⟨21276026631828601657859143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28368035509104802210478857 21276026631828601657859143)
      ·
        refine ⟨31914039947742902486788715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21276026631828601657859143 31914039947742902486788715)
        ·
          refine ⟨47871059921614353730183073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31914039947742902486788715 47871059921614353730183073)
          ·
            refine ⟨35903294941210765297637305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47871059921614353730183073 35903294941210765297637305)
            ·
              refine ⟨26927471205908073973227979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35903294941210765297637305 26927471205908073973227979)
              ·
                refine ⟨40391206808862110959841969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26927471205908073973227979 40391206808862110959841969)
                ·
                  refine ⟨30293405106646583219881477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40391206808862110959841969 30293405106646583219881477)
                  ·
                    refine ⟨5680013457496234353727777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 30293405106646583219881477 5680013457496234353727777)
                    ·
                      refine ⟨4260010093122175765295833, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5680013457496234353727777 4260010093122175765295833)
                      ·
                        rfl

theorem cell23_8296340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 2, 2, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 2, 2, 1, 2, 4, 2].length) (baseStart_8296340 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8296340 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8296340 prefixEnd_8296340 := by exact prefixLift 8296340
  have htrace : WordTrace (prefixWord ++ tailWord_8296340) baseStart_8296340 baseEnd_8296340 := by
    simpa [prefixWord, tailWord_8296340, baseEnd_8296340] using wordTrace_append hprefix tailTrace_8296340
  have hstable : (prefixWord ++ tailWord_8296340).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8296340).length < 2 ^ (prefixWord ++ tailWord_8296340).sum := by decide
  have hdescent : baseEnd_8296340 < baseStart_8296340 := by decide
  rcases family_descends (prefixWord ++ tailWord_8296340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8296416 : List Nat := [2, 1, 1, 3, 1, 1, 1, 4, 3, 1, 5]
def baseStart_8296416 : Nat := 118140960795 + 8296416 * 2 ^ 59
def prefixEnd_8296416 : Nat := 4983230072969 + 3 ^ 40 * 8296416 * 2
def baseEnd_8296416 : Nat := 4260049117651917467945483

theorem tailTrace_8296416 : CollatzResearch.WordTrace tailWord_8296416 prefixEnd_8296416 4260049117651917467945483 := by
  unfold tailWord_8296416
  simp only [CollatzResearch.WordTrace]
  refine ⟨151297575355754610945770551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 201730100474339481261027401 151297575355754610945770551)
  ·
    refine ⟨226946363033631916418655827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151297575355754610945770551 226946363033631916418655827)
    ·
      refine ⟨340419544550447874627983741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 226946363033631916418655827 340419544550447874627983741)
      ·
        refine ⟨127657329206417952985493903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 340419544550447874627983741 127657329206417952985493903)
        ·
          refine ⟨191485993809626929478240855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 127657329206417952985493903 191485993809626929478240855)
          ·
            refine ⟨287228990714440394217361283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 191485993809626929478240855 287228990714440394217361283)
            ·
              refine ⟨430843486071660591326041925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 287228990714440394217361283 430843486071660591326041925)
              ·
                refine ⟨80783153638436360873632861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 430843486071660591326041925 80783153638436360873632861)
                ·
                  refine ⟨30293682614413635327612323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 80783153638436360873632861 30293682614413635327612323)
                  ·
                    refine ⟨45440523921620452991418485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 30293682614413635327612323 45440523921620452991418485)
                    ·
                      refine ⟨4260049117651917467945483, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 45440523921620452991418485 4260049117651917467945483)
                      ·
                        rfl

theorem cell23_8296416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 1, 4, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 1, 4, 3, 1, 5].length) (baseStart_8296416 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8296416 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8296416 prefixEnd_8296416 := by exact prefixLift 8296416
  have htrace : WordTrace (prefixWord ++ tailWord_8296416) baseStart_8296416 baseEnd_8296416 := by
    simpa [prefixWord, tailWord_8296416, baseEnd_8296416] using wordTrace_append hprefix tailTrace_8296416
  have hstable : (prefixWord ++ tailWord_8296416).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8296416).length < 2 ^ (prefixWord ++ tailWord_8296416).sum := by decide
  have hdescent : baseEnd_8296416 < baseStart_8296416 := by decide
  rcases family_descends (prefixWord ++ tailWord_8296416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8296453 : List Nat := [1, 3, 1, 1, 2, 6, 1, 8]
def baseStart_8296453 : Nat := 118140960795 + 8296453 * 2 ^ 59
def prefixEnd_8296453 : Nat := 4983230072969 + 3 ^ 40 * 8296453 * 2
def baseEnd_8296453 : Nat := 157780300608745697154919

theorem tailTrace_8296453 : CollatzResearch.WordTrace tailWord_8296453 prefixEnd_8296453 157780300608745697154919 := by
  unfold tailWord_8296453
  simp only [CollatzResearch.WordTrace]
  refine ⟨302596500212375177210638013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201731000141583451473758675 302596500212375177210638013)
  ·
    refine ⟨113473687579640691453989255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 302596500212375177210638013 113473687579640691453989255)
    ·
      refine ⟨170210531369461037180983883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113473687579640691453989255 170210531369461037180983883)
      ·
        refine ⟨255315797054191555771475825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 170210531369461037180983883 255315797054191555771475825)
        ·
          refine ⟨191486847790643666828606869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 255315797054191555771475825 191486847790643666828606869)
          ·
            refine ⟨8975945990186421882590947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 191486847790643666828606869 8975945990186421882590947)
            ·
              refine ⟨13463918985279632823886421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8975945990186421882590947 13463918985279632823886421)
              ·
                refine ⟨157780300608745697154919, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 13463918985279632823886421 157780300608745697154919)
                ·
                  rfl

theorem cell23_8296453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 6, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 6, 1, 8].length) (baseStart_8296453 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8296453 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8296453 prefixEnd_8296453 := by exact prefixLift 8296453
  have htrace : WordTrace (prefixWord ++ tailWord_8296453) baseStart_8296453 baseEnd_8296453 := by
    simpa [prefixWord, tailWord_8296453, baseEnd_8296453] using wordTrace_append hprefix tailTrace_8296453
  have hstable : (prefixWord ++ tailWord_8296453).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8296453).length < 2 ^ (prefixWord ++ tailWord_8296453).sum := by decide
  have hdescent : baseEnd_8296453 < baseStart_8296453 := by decide
  rcases family_descends (prefixWord ++ tailWord_8296453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8296468 : List Nat := [2, 4, 3, 2, 2, 1, 1, 1, 2, 3, 2]
def baseStart_8296468 : Nat := 118140960795 + 8296468 * 2 ^ 59
def prefixEnd_8296468 : Nat := 4983230072969 + 3 ^ 40 * 8296468 * 2
def baseEnd_8296468 : Nat := 4260075818645951264495245

theorem tailTrace_8296468 : CollatzResearch.WordTrace tailWord_8296468 prefixEnd_8296468 4260075818645951264495245 := by
  unfold tailWord_8296468
  simp only [CollatzResearch.WordTrace]
  refine ⟨151298523653660417386217029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 201731364871547223181622705 151298523653660417386217029)
  ·
    refine ⟨28368473185061328259915693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 151298523653660417386217029 28368473185061328259915693)
    ·
      refine ⟨10638177444397998097468385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28368473185061328259915693 10638177444397998097468385)
      ·
        refine ⟨7978633083298498573101289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10638177444397998097468385 7978633083298498573101289)
        ·
          refine ⟨5983974812473873929825967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7978633083298498573101289 5983974812473873929825967)
          ·
            refine ⟨8975962218710810894738951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5983974812473873929825967 8975962218710810894738951)
            ·
              refine ⟨13463943328066216342108427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8975962218710810894738951 13463943328066216342108427)
              ·
                refine ⟨20195914992099324513162641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13463943328066216342108427 20195914992099324513162641)
                ·
                  refine ⟨15146936244074493384871981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20195914992099324513162641 15146936244074493384871981)
                  ·
                    refine ⟨5680101091527935019326993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15146936244074493384871981 5680101091527935019326993)
                    ·
                      refine ⟨4260075818645951264495245, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5680101091527935019326993 4260075818645951264495245)
                      ·
                        rfl

theorem cell23_8296468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 2, 1, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 2, 1, 1, 1, 2, 3, 2].length) (baseStart_8296468 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8296468 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8296468 prefixEnd_8296468 := by exact prefixLift 8296468
  have htrace : WordTrace (prefixWord ++ tailWord_8296468) baseStart_8296468 baseEnd_8296468 := by
    simpa [prefixWord, tailWord_8296468, baseEnd_8296468] using wordTrace_append hprefix tailTrace_8296468
  have hstable : (prefixWord ++ tailWord_8296468).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8296468).length < 2 ^ (prefixWord ++ tailWord_8296468).sum := by decide
  have hdescent : baseEnd_8296468 < baseStart_8296468 := by decide
  rcases family_descends (prefixWord ++ tailWord_8296468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8296481 : List Nat := [1, 2, 3, 2, 4, 1, 2, 3, 1, 2, 2]
def baseStart_8296481 : Nat := 118140960795 + 8296481 * 2 ^ 59
def prefixEnd_8296481 : Nat := 4983230072969 + 3 ^ 40 * 8296481 * 2
def baseEnd_8296481 : Nat := 4260082493894459713632685

theorem tailTrace_8296481 : CollatzResearch.WordTrace tailWord_8296481 prefixEnd_8296481 4260082493894459713632685 := by
  unfold tailWord_8296481
  simp only [CollatzResearch.WordTrace]
  refine ⟨302597521456273737992657297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201731680970849158661771531 302597521456273737992657297)
  ·
    refine ⟨226948141092205303494492973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 302597521456273737992657297 226948141092205303494492973)
    ·
      refine ⟨85105552909576988810434865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 226948141092205303494492973 85105552909576988810434865)
      ·
        refine ⟨63829164682182741607826149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85105552909576988810434865 63829164682182741607826149)
        ·
          refine ⟨11967968377909264051467403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 63829164682182741607826149 11967968377909264051467403)
          ·
            refine ⟨17951952566863896077201105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11967968377909264051467403 17951952566863896077201105)
            ·
              refine ⟨13463964425147922057900829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17951952566863896077201105 13463964425147922057900829)
              ·
                refine ⟨5048986659430470771712811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13463964425147922057900829 5048986659430470771712811)
                ·
                  refine ⟨7573479989145706157569217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5048986659430470771712811 7573479989145706157569217)
                  ·
                    refine ⟨5680109991859279618176913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7573479989145706157569217 5680109991859279618176913)
                    ·
                      refine ⟨4260082493894459713632685, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5680109991859279618176913 4260082493894459713632685)
                      ·
                        rfl

theorem cell23_8296481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 4, 1, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 4, 1, 2, 3, 1, 2, 2].length) (baseStart_8296481 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8296481 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8296481 prefixEnd_8296481 := by exact prefixLift 8296481
  have htrace : WordTrace (prefixWord ++ tailWord_8296481) baseStart_8296481 baseEnd_8296481 := by
    simpa [prefixWord, tailWord_8296481, baseEnd_8296481] using wordTrace_append hprefix tailTrace_8296481
  have hstable : (prefixWord ++ tailWord_8296481).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8296481).length < 2 ^ (prefixWord ++ tailWord_8296481).sum := by decide
  have hdescent : baseEnd_8296481 < baseStart_8296481 := by decide
  rcases family_descends (prefixWord ++ tailWord_8296481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8296497 : List Nat := [1, 2, 2, 3, 1, 3, 3, 2, 2, 1, 3]
def baseStart_8296497 : Nat := 118140960795 + 8296497 * 2 ^ 59
def prefixEnd_8296497 : Nat := 4983230072969 + 3 ^ 40 * 8296497 * 2
def baseEnd_8296497 : Nat := 4260090709584931651032611

theorem tailTrace_8296497 : CollatzResearch.WordTrace tailWord_8296497 prefixEnd_8296497 4260090709584931651032611 := by
  unfold tailWord_8296497
  simp only [CollatzResearch.WordTrace]
  refine ⟨302598105024215772725239745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201732070016143848483493163 302598105024215772725239745)
  ·
    refine ⟨226948578768161829543929809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 302598105024215772725239745 226948578768161829543929809)
    ·
      refine ⟨170211434076121372157947357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 226948578768161829543929809 170211434076121372157947357)
      ·
        refine ⟨63829287778545514559230259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 170211434076121372157947357 63829287778545514559230259)
        ·
          refine ⟨95743931667818271838845389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63829287778545514559230259 95743931667818271838845389)
          ·
            refine ⟨35903974375431851939567021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 95743931667818271838845389 35903974375431851939567021)
            ·
              refine ⟨13463990390786944477337633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35903974375431851939567021 13463990390786944477337633)
              ·
                refine ⟨10097992793090208358003225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13463990390786944477337633 10097992793090208358003225)
                ·
                  refine ⟨7573494594817656268502419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10097992793090208358003225 7573494594817656268502419)
                  ·
                    refine ⟨11360241892226484402753629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7573494594817656268502419 11360241892226484402753629)
                    ·
                      refine ⟨4260090709584931651032611, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11360241892226484402753629 4260090709584931651032611)
                      ·
                        rfl

theorem cell23_8296497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 3, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 3, 3, 2, 2, 1, 3].length) (baseStart_8296497 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8296497 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8296497 prefixEnd_8296497 := by exact prefixLift 8296497
  have htrace : WordTrace (prefixWord ++ tailWord_8296497) baseStart_8296497 baseEnd_8296497 := by
    simpa [prefixWord, tailWord_8296497, baseEnd_8296497] using wordTrace_append hprefix tailTrace_8296497
  have hstable : (prefixWord ++ tailWord_8296497).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8296497).length < 2 ^ (prefixWord ++ tailWord_8296497).sum := by decide
  have hdescent : baseEnd_8296497 < baseStart_8296497 := by decide
  rcases family_descends (prefixWord ++ tailWord_8296497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8296520 : List Nat := [2, 1, 3, 1, 1, 1, 2, 5, 1, 4, 2]
def baseStart_8296520 : Nat := 118140960795 + 8296520 * 2 ^ 59
def prefixEnd_8296520 : Nat := 4983230072969 + 3 ^ 40 * 8296520 * 2
def baseEnd_8296520 : Nat := 4260102519639985061045005

theorem tailTrace_8296520 : CollatzResearch.WordTrace tailWord_8296520 prefixEnd_8296520 4260102519639985061045005 := by
  unfold tailWord_8296520
  simp only [CollatzResearch.WordTrace]
  refine ⟨151299471951566223826663507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 201732629268754965102218009 151299471951566223826663507)
  ·
    refine ⟨226949207927349335739995261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151299471951566223826663507 226949207927349335739995261)
    ·
      refine ⟨85105952972756000902498223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 226949207927349335739995261 85105952972756000902498223)
      ·
        refine ⟨127658929459134001353747335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85105952972756000902498223 127658929459134001353747335)
        ·
          refine ⟨191488394188701002030621003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 127658929459134001353747335 191488394188701002030621003)
          ·
            refine ⟨287232591283051503045931505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 191488394188701002030621003 287232591283051503045931505)
            ·
              refine ⟨215424443462288627284448629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 287232591283051503045931505 215424443462288627284448629)
              ·
                refine ⟨20196041574589558807917059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 215424443462288627284448629 20196041574589558807917059)
                ·
                  refine ⟨30294062361884338211875589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20196041574589558807917059 30294062361884338211875589)
                  ·
                    refine ⟨5680136692853313414726673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 30294062361884338211875589 5680136692853313414726673)
                    ·
                      refine ⟨4260102519639985061045005, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5680136692853313414726673 4260102519639985061045005)
                      ·
                        rfl

theorem cell23_8296520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 2, 5, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 2, 5, 1, 4, 2].length) (baseStart_8296520 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8296520 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8296520 prefixEnd_8296520 := by exact prefixLift 8296520
  have htrace : WordTrace (prefixWord ++ tailWord_8296520) baseStart_8296520 baseEnd_8296520 := by
    simpa [prefixWord, tailWord_8296520, baseEnd_8296520] using wordTrace_append hprefix tailTrace_8296520
  have hstable : (prefixWord ++ tailWord_8296520).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8296520).length < 2 ^ (prefixWord ++ tailWord_8296520).sum := by decide
  have hdescent : baseEnd_8296520 < baseStart_8296520 := by decide
  rcases family_descends (prefixWord ++ tailWord_8296520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8296540 : List Nat := [2, 2, 4, 1, 1, 3, 1, 1, 2, 1, 5]
def baseStart_8296540 : Nat := 118140960795 + 8296540 * 2 ^ 59
def prefixEnd_8296540 : Nat := 4983230072969 + 3 ^ 40 * 8296540 * 2
def baseEnd_8296540 : Nat := 4260112789253074982794913

theorem tailTrace_8296540 : CollatzResearch.WordTrace tailWord_8296540 prefixEnd_8296540 4260112789253074982794913 := by
  unfold tailWord_8296540
  simp only [CollatzResearch.WordTrace]
  refine ⟨151299836681529995534527537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 201733115575373327379370049 151299836681529995534527537)
  ·
    refine ⟨113474877511147496650895653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 151299836681529995534527537 113474877511147496650895653)
    ·
      refine ⟨21276539533340155622042935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 113474877511147496650895653 21276539533340155622042935)
      ·
        refine ⟨31914809300010233433064403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21276539533340155622042935 31914809300010233433064403)
        ·
          refine ⟨47872213950015350149596605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31914809300010233433064403 47872213950015350149596605)
          ·
            refine ⟨17952080231255756306098727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 47872213950015350149596605 17952080231255756306098727)
            ·
              refine ⟨26928120346883634459148091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17952080231255756306098727 26928120346883634459148091)
              ·
                refine ⟨40392180520325451688722137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26928120346883634459148091 40392180520325451688722137)
                ·
                  refine ⟨30294135390244088766541603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40392180520325451688722137 30294135390244088766541603)
                  ·
                    refine ⟨45441203085366133149812405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 30294135390244088766541603 45441203085366133149812405)
                    ·
                      refine ⟨4260112789253074982794913, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 45441203085366133149812405 4260112789253074982794913)
                      ·
                        rfl

theorem cell23_8296540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 3, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 3, 1, 1, 2, 1, 5].length) (baseStart_8296540 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8296540 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8296540 prefixEnd_8296540 := by exact prefixLift 8296540
  have htrace : WordTrace (prefixWord ++ tailWord_8296540) baseStart_8296540 baseEnd_8296540 := by
    simpa [prefixWord, tailWord_8296540, baseEnd_8296540] using wordTrace_append hprefix tailTrace_8296540
  have hstable : (prefixWord ++ tailWord_8296540).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8296540).length < 2 ^ (prefixWord ++ tailWord_8296540).sum := by decide
  have hdescent : baseEnd_8296540 < baseStart_8296540 := by decide
  rcases family_descends (prefixWord ++ tailWord_8296540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8296560 : List Nat := [2, 1, 1, 1, 5, 4, 1, 1, 7]
def baseStart_8296560 : Nat := 118140960795 + 8296560 * 2 ^ 59
def prefixEnd_8296560 : Nat := 4983230072969 + 3 ^ 40 * 8296560 * 2
def baseEnd_8296560 : Nat := 473347006540684989393869

theorem tailTrace_8296560 : CollatzResearch.WordTrace tailWord_8296560 prefixEnd_8296560 473347006540684989393869 := by
  unfold tailWord_8296560
  simp only [CollatzResearch.WordTrace]
  refine ⟨151300201411493767242391567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 201733601881991689656522089 151300201411493767242391567)
  ·
    refine ⟨226950302117240650863587351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151300201411493767242391567 226950302117240650863587351)
    ·
      refine ⟨340425453175860976295381027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 226950302117240650863587351 340425453175860976295381027)
      ·
        refine ⟨510638179763791464443071541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 340425453175860976295381027 510638179763791464443071541)
        ·
          refine ⟨47872329352855449791537957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 510638179763791464443071541 47872329352855449791537957)
          ·
            refine ⟨8976061753660396835913367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 47872329352855449791537957 8976061753660396835913367)
            ·
              refine ⟨13464092630490595253870051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8976061753660396835913367 13464092630490595253870051)
              ·
                refine ⟨20196138945735892880805077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13464092630490595253870051 20196138945735892880805077)
                ·
                  refine ⟨473347006540684989393869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 20196138945735892880805077 473347006540684989393869)
                  ·
                    rfl

theorem cell23_8296560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 4, 1, 1, 7].length) (baseStart_8296560 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8296560 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8296560 prefixEnd_8296560 := by exact prefixLift 8296560
  have htrace : WordTrace (prefixWord ++ tailWord_8296560) baseStart_8296560 baseEnd_8296560 := by
    simpa [prefixWord, tailWord_8296560, baseEnd_8296560] using wordTrace_append hprefix tailTrace_8296560
  have hstable : (prefixWord ++ tailWord_8296560).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8296560).length < 2 ^ (prefixWord ++ tailWord_8296560).sum := by decide
  have hdescent : baseEnd_8296560 < baseStart_8296560 := by decide
  rcases family_descends (prefixWord ++ tailWord_8296560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8296613 : List Nat := [1, 3, 1, 2, 1, 3, 1, 1, 2, 3, 5]
def baseStart_8296613 : Nat := 118140960795 + 8296613 * 2 ^ 59
def prefixEnd_8296613 : Nat := 4983230072969 + 3 ^ 40 * 8296613 * 2
def baseEnd_8296613 : Nat := 4260150273340853197182077

theorem tailTrace_8296613 : CollatzResearch.WordTrace tailWord_8296613 prefixEnd_8296613 4260150273340853197182077 := by
  unfold tailWord_8296613
  simp only [CollatzResearch.WordTrace]
  refine ⟨302602335891795524536462493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201734890594530349690974995 302602335891795524536462493)
  ·
    refine ⟨113475875959423321701173435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 302602335891795524536462493 113475875959423321701173435)
    ·
      refine ⟨170213813939134982551760153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113475875959423321701173435 170213813939134982551760153)
      ·
        refine ⟨127660360454351236913820115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 170213813939134982551760153 127660360454351236913820115)
        ·
          refine ⟨191490540681526855370730173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 127660360454351236913820115 191490540681526855370730173)
          ·
            refine ⟨71808952755572570764023815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 191490540681526855370730173 71808952755572570764023815)
            ·
              refine ⟨107713429133358856146035723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71808952755572570764023815 107713429133358856146035723)
              ·
                refine ⟨161570143700038284219053585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 107713429133358856146035723 161570143700038284219053585)
                ·
                  refine ⟨121177607775028713164290189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 161570143700038284219053585 121177607775028713164290189)
                  ·
                    refine ⟨45441602915635767436608821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 121177607775028713164290189 45441602915635767436608821)
                    ·
                      refine ⟨4260150273340853197182077, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 45441602915635767436608821 4260150273340853197182077)
                      ·
                        rfl

theorem cell23_8296613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 1, 1, 2, 3, 5].length) (baseStart_8296613 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8296613 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8296613 prefixEnd_8296613 := by exact prefixLift 8296613
  have htrace : WordTrace (prefixWord ++ tailWord_8296613) baseStart_8296613 baseEnd_8296613 := by
    simpa [prefixWord, tailWord_8296613, baseEnd_8296613] using wordTrace_append hprefix tailTrace_8296613
  have hstable : (prefixWord ++ tailWord_8296613).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8296613).length < 2 ^ (prefixWord ++ tailWord_8296613).sum := by decide
  have hdescent : baseEnd_8296613 < baseStart_8296613 := by decide
  rcases family_descends (prefixWord ++ tailWord_8296613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8296623 : List Nat := [1, 1, 2, 1, 2, 3, 1, 2, 2, 4, 4]
def baseStart_8296623 : Nat := 118140960795 + 8296623 * 2 ^ 59
def prefixEnd_8296623 : Nat := 4983230072969 + 3 ^ 40 * 8296623 * 2
def baseEnd_8296623 : Nat := 4260155408147398158057031

theorem tailTrace_8296623 : CollatzResearch.WordTrace tailWord_8296623 prefixEnd_8296623 4260155408147398158057031 := by
  unfold tailWord_8296623
  simp only [CollatzResearch.WordTrace]
  refine ⟨302602700621759296244326523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201735133747839530829551015 302602700621759296244326523)
  ·
    refine ⟨453904050932638944366489785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 302602700621759296244326523 453904050932638944366489785)
    ·
      refine ⟨340428038199479208274867339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 453904050932638944366489785 340428038199479208274867339)
      ·
        refine ⟨510642057299218812412301009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 340428038199479208274867339 510642057299218812412301009)
        ·
          refine ⟨382981542974414109309225757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 510642057299218812412301009 382981542974414109309225757)
          ·
            refine ⟨143618078615405290990959659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 382981542974414109309225757 143618078615405290990959659)
            ·
              refine ⟨215427117923107936486439489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 143618078615405290990959659 215427117923107936486439489)
              ·
                refine ⟨161570338442330952364829617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 215427117923107936486439489 161570338442330952364829617)
                ·
                  refine ⟨121177753831748214273622213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 161570338442330952364829617 121177753831748214273622213)
                  ·
                    refine ⟨22720828843452790176304165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 121177753831748214273622213 22720828843452790176304165)
                    ·
                      refine ⟨4260155408147398158057031, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22720828843452790176304165 4260155408147398158057031)
                      ·
                        rfl

theorem cell23_8296623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 1, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 1, 2, 2, 4, 4].length) (baseStart_8296623 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8296623 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8296623 prefixEnd_8296623 := by exact prefixLift 8296623
  have htrace : WordTrace (prefixWord ++ tailWord_8296623) baseStart_8296623 baseEnd_8296623 := by
    simpa [prefixWord, tailWord_8296623, baseEnd_8296623] using wordTrace_append hprefix tailTrace_8296623
  have hstable : (prefixWord ++ tailWord_8296623).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8296623).length < 2 ^ (prefixWord ++ tailWord_8296623).sum := by decide
  have hdescent : baseEnd_8296623 < baseStart_8296623 := by decide
  rcases family_descends (prefixWord ++ tailWord_8296623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8296641 : List Nat := [1, 2, 6, 1, 3, 1, 1, 1, 2, 5]
def baseStart_8296641 : Nat := 118140960795 + 8296641 * 2 ^ 59
def prefixEnd_8296641 : Nat := 4983230072969 + 3 ^ 40 * 8296641 * 2
def baseEnd_8296641 : Nat := 1420054883599726362543983

theorem tailTrace_8296641 : CollatzResearch.WordTrace tailWord_8296641 prefixEnd_8296641 1420054883599726362543983 := by
  unfold tailWord_8296641
  simp only [CollatzResearch.WordTrace]
  refine ⟨302603357135694085318481777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201735571423796056878987851 302603357135694085318481777)
  ·
    refine ⟨226952517851770563988861333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 302603357135694085318481777 226952517851770563988861333)
    ·
      refine ⟨10638399274301745186977875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 226952517851770563988861333 10638399274301745186977875)
      ·
        refine ⟨15957598911452617780466813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10638399274301745186977875 15957598911452617780466813)
        ·
          refine ⟨5984099591794731667675055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15957598911452617780466813 5984099591794731667675055)
          ·
            refine ⟨8976149387692097501512583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5984099591794731667675055 8976149387692097501512583)
            ·
              refine ⟨13464224081538146252268875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8976149387692097501512583 13464224081538146252268875)
              ·
                refine ⟨20196336122307219378403313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13464224081538146252268875 20196336122307219378403313)
                ·
                  refine ⟨15147252091730414533802485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20196336122307219378403313 15147252091730414533802485)
                  ·
                    refine ⟨1420054883599726362543983, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15147252091730414533802485 1420054883599726362543983)
                    ·
                      rfl

theorem cell23_8296641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 3, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 3, 1, 1, 1, 2, 5].length) (baseStart_8296641 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8296641 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8296641 prefixEnd_8296641 := by exact prefixLift 8296641
  have htrace : WordTrace (prefixWord ++ tailWord_8296641) baseStart_8296641 baseEnd_8296641 := by
    simpa [prefixWord, tailWord_8296641, baseEnd_8296641] using wordTrace_append hprefix tailTrace_8296641
  have hstable : (prefixWord ++ tailWord_8296641).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8296641).length < 2 ^ (prefixWord ++ tailWord_8296641).sum := by decide
  have hdescent : baseEnd_8296641 < baseStart_8296641 := by decide
  rcases family_descends (prefixWord ++ tailWord_8296641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8296644 : List Nat := [2, 3, 3, 1, 2, 3, 1, 1, 2, 1, 4]
def baseStart_8296644 : Nat := 118140960795 + 8296644 * 2 ^ 59
def prefixEnd_8296644 : Nat := 4983230072969 + 3 ^ 40 * 8296644 * 2
def baseEnd_8296644 : Nat := 4260166191241142575894435

theorem tailTrace_8296644 : CollatzResearch.WordTrace tailWord_8296644 prefixEnd_8296644 4260166191241142575894435 := by
  unfold tailWord_8296644
  simp only [CollatzResearch.WordTrace]
  refine ⟨151301733277341608415420493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 201735644369788811220560657 151301733277341608415420493)
  ·
    refine ⟨56738149979003103155782685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 151301733277341608415420493 56738149979003103155782685)
    ·
      refine ⟨21276806242126163683418507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 56738149979003103155782685 21276806242126163683418507)
      ·
        refine ⟨31915209363189245525127761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21276806242126163683418507 31915209363189245525127761)
        ·
          refine ⟨23936407022391934143845821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31915209363189245525127761 23936407022391934143845821)
          ·
            refine ⟨8976152633396975303942183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23936407022391934143845821 8976152633396975303942183)
            ·
              refine ⟨13464228950095462955913275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8976152633396975303942183 13464228950095462955913275)
              ·
                refine ⟨20196343425143194433869913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13464228950095462955913275 20196343425143194433869913)
                ·
                  refine ⟨15147257568857395825402435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20196343425143194433869913 15147257568857395825402435)
                  ·
                    refine ⟨22720886353286093738103653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15147257568857395825402435 22720886353286093738103653)
                    ·
                      refine ⟨4260166191241142575894435, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22720886353286093738103653 4260166191241142575894435)
                      ·
                        rfl

theorem cell23_8296644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 3, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 3, 1, 1, 2, 1, 4].length) (baseStart_8296644 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8296644 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8296644 prefixEnd_8296644 := by exact prefixLift 8296644
  have htrace : WordTrace (prefixWord ++ tailWord_8296644) baseStart_8296644 baseEnd_8296644 := by
    simpa [prefixWord, tailWord_8296644, baseEnd_8296644] using wordTrace_append hprefix tailTrace_8296644
  have hstable : (prefixWord ++ tailWord_8296644).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8296644).length < 2 ^ (prefixWord ++ tailWord_8296644).sum := by decide
  have hdescent : baseEnd_8296644 < baseStart_8296644 := by decide
  rcases family_descends (prefixWord ++ tailWord_8296644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8296654 : List Nat := [4, 1, 1, 1, 4, 1, 1, 5, 1, 4]
def baseStart_8296654 : Nat := 118140960795 + 8296654 * 2 ^ 59
def prefixEnd_8296654 : Nat := 4983230072969 + 3 ^ 40 * 8296654 * 2
def baseEnd_8296654 : Nat := 1420057108682562512256463

theorem tailTrace_8296654 : CollatzResearch.WordTrace tailWord_8296654 prefixEnd_8296654 1420057108682562512256463 := by
  unfold tailWord_8296654
  simp only [CollatzResearch.WordTrace]
  refine ⟨37825478910580873567338127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 201735887523097992359136677 37825478910580873567338127)
  ·
    refine ⟨56738218365871310351007191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37825478910580873567338127 56738218365871310351007191)
    ·
      refine ⟨85107327548806965526510787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56738218365871310351007191 85107327548806965526510787)
      ·
        refine ⟨127660991323210448289766181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85107327548806965526510787 127660991323210448289766181)
        ·
          refine ⟨23936435873101959054331159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 127660991323210448289766181 23936435873101959054331159)
          ·
            refine ⟨35904653809652938581496739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23936435873101959054331159 35904653809652938581496739)
            ·
              refine ⟨53856980714479407872245109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35904653809652938581496739 53856980714479407872245109)
              ·
                refine ⟨5049091941982444488022979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 53856980714479407872245109 5049091941982444488022979)
                ·
                  refine ⟨7573637912973666732034469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5049091941982444488022979 7573637912973666732034469)
                  ·
                    refine ⟨1420057108682562512256463, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7573637912973666732034469 1420057108682562512256463)
                    ·
                      rfl

theorem cell23_8296654_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 1, 1, 5, 1, 4].length) (baseStart_8296654 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8296654 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8296654 prefixEnd_8296654 := by exact prefixLift 8296654
  have htrace : WordTrace (prefixWord ++ tailWord_8296654) baseStart_8296654 baseEnd_8296654 := by
    simpa [prefixWord, tailWord_8296654, baseEnd_8296654] using wordTrace_append hprefix tailTrace_8296654
  have hstable : (prefixWord ++ tailWord_8296654).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8296654).length < 2 ^ (prefixWord ++ tailWord_8296654).sum := by decide
  have hdescent : baseEnd_8296654 < baseStart_8296654 := by decide
  rcases family_descends (prefixWord ++ tailWord_8296654) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8296687 : List Nat := [1, 1, 2, 1, 6, 1, 1, 2, 1, 5, 2]
def baseStart_8296687 : Nat := 118140960795 + 8296687 * 2 ^ 59
def prefixEnd_8296687 : Nat := 4983230072969 + 3 ^ 40 * 8296687 * 2
def baseEnd_8296687 : Nat := 4260188270909285907656737

theorem tailTrace_8296687 : CollatzResearch.WordTrace tailWord_8296687 prefixEnd_8296687 4260188270909285907656737 := by
  unfold tailWord_8296687
  simp only [CollatzResearch.WordTrace]
  refine ⟨302605034893527435174656315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201736689929018290116437543 302605034893527435174656315)
  ·
    refine ⟨453907552340291152761984473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 302605034893527435174656315 453907552340291152761984473)
    ·
      refine ⟨340430664255218364571488355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 453907552340291152761984473 340430664255218364571488355)
      ·
        refine ⟨510645996382827546857232533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 340430664255218364571488355 510645996382827546857232533)
        ·
          refine ⟨23936531080445041258932775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 510645996382827546857232533 23936531080445041258932775)
          ·
            refine ⟨35904796620667561888399163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23936531080445041258932775 35904796620667561888399163)
            ·
              refine ⟨53857194931001342832598745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35904796620667561888399163 53857194931001342832598745)
              ·
                refine ⟨40392896198251007124449059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53857194931001342832598745 40392896198251007124449059)
                ·
                  refine ⟨60589344297376510686673589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40392896198251007124449059 60589344297376510686673589)
                  ·
                    refine ⟨5680251027879047876875649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 60589344297376510686673589 5680251027879047876875649)
                    ·
                      refine ⟨4260188270909285907656737, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5680251027879047876875649 4260188270909285907656737)
                      ·
                        rfl

theorem cell23_8296687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 1, 1, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 1, 1, 2, 1, 5, 2].length) (baseStart_8296687 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8296687 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8296687 prefixEnd_8296687 := by exact prefixLift 8296687
  have htrace : WordTrace (prefixWord ++ tailWord_8296687) baseStart_8296687 baseEnd_8296687 := by
    simpa [prefixWord, tailWord_8296687, baseEnd_8296687] using wordTrace_append hprefix tailTrace_8296687
  have hstable : (prefixWord ++ tailWord_8296687).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8296687).length < 2 ^ (prefixWord ++ tailWord_8296687).sum := by decide
  have hdescent : baseEnd_8296687 < baseStart_8296687 := by decide
  rcases family_descends (prefixWord ++ tailWord_8296687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8296694 : List Nat := [5, 1, 1, 1, 1, 1, 4, 2, 3, 1, 3]
def baseStart_8296694 : Nat := 118140960795 + 8296694 * 2 ^ 59
def prefixEnd_8296694 : Nat := 4983230072969 + 3 ^ 40 * 8296694 * 2
def baseEnd_8296694 : Nat := 4260191865273867380269205

theorem tailTrace_8296694 : CollatzResearch.WordTrace tailWord_8296694 prefixEnd_8296694 4260191865273867380269205 := by
  unfold tailWord_8296694
  simp only [CollatzResearch.WordTrace]
  refine ⟨18912830637781379710635071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 201736860136334716913440757 18912830637781379710635071)
  ·
    refine ⟨28369245956672069565952607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18912830637781379710635071 28369245956672069565952607)
    ·
      refine ⟨42553868935008104348928911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28369245956672069565952607 42553868935008104348928911)
      ·
        refine ⟨63830803402512156523393367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42553868935008104348928911 63830803402512156523393367)
        ·
          refine ⟨95746205103768234785090051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63830803402512156523393367 95746205103768234785090051)
          ·
            refine ⟨143619307655652352177635077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 95746205103768234785090051 143619307655652352177635077)
            ·
              refine ⟨26928620185434816033306577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 143619307655652352177635077 26928620185434816033306577)
              ·
                refine ⟨20196465139076112024979933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26928620185434816033306577 20196465139076112024979933)
                ·
                  refine ⟨7573674427153542009367475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20196465139076112024979933 7573674427153542009367475)
                  ·
                    refine ⟨11360511640730313014051213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7573674427153542009367475 11360511640730313014051213)
                    ·
                      refine ⟨4260191865273867380269205, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11360511640730313014051213 4260191865273867380269205)
                      ·
                        rfl

theorem cell23_8296694_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 4, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 4, 2, 3, 1, 3].length) (baseStart_8296694 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8296694 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8296694 prefixEnd_8296694 := by exact prefixLift 8296694
  have htrace : WordTrace (prefixWord ++ tailWord_8296694) baseStart_8296694 baseEnd_8296694 := by
    simpa [prefixWord, tailWord_8296694, baseEnd_8296694] using wordTrace_append hprefix tailTrace_8296694
  have hstable : (prefixWord ++ tailWord_8296694).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8296694).length < 2 ^ (prefixWord ++ tailWord_8296694).sum := by decide
  have hdescent : baseEnd_8296694 < baseStart_8296694 := by decide
  rcases family_descends (prefixWord ++ tailWord_8296694) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8296727 : List Nat := [1, 1, 3, 4, 1, 2, 2, 1, 4, 4]
def baseStart_8296727 : Nat := 118140960795 + 8296727 * 2 ^ 59
def prefixEnd_8296727 : Nat := 4983230072969 + 3 ^ 40 * 8296727 * 2
def baseEnd_8296727 : Nat := 1420069603378488583718851

theorem tailTrace_8296727 : CollatzResearch.WordTrace tailWord_8296727 prefixEnd_8296727 1420069603378488583718851 := by
  unfold tailWord_8296727
  simp only [CollatzResearch.WordTrace]
  refine ⟨302606493813382522006112435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201737662542255014670741623 302606493813382522006112435)
  ·
    refine ⟨453909740720073783009168653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 302606493813382522006112435 453909740720073783009168653)
    ·
      refine ⟨170216152770027668628438245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 453909740720073783009168653 170216152770027668628438245)
      ·
        refine ⟨31915528644380187867832171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 170216152770027668628438245 31915528644380187867832171)
        ·
          refine ⟨47873292966570281801748257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31915528644380187867832171 47873292966570281801748257)
          ·
            refine ⟨35904969724927711351311193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47873292966570281801748257 35904969724927711351311193)
            ·
              refine ⟨26928727293695783513483395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35904969724927711351311193 26928727293695783513483395)
              ·
                refine ⟨40393090940543675270225093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26928727293695783513483395 40393090940543675270225093)
                ·
                  refine ⟨7573704551351939113167205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 40393090940543675270225093 7573704551351939113167205)
                  ·
                    refine ⟨1420069603378488583718851, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7573704551351939113167205 1420069603378488583718851)
                    ·
                      rfl

theorem cell23_8296727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 2, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 2, 2, 1, 4, 4].length) (baseStart_8296727 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8296727 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8296727 prefixEnd_8296727 := by exact prefixLift 8296727
  have htrace : WordTrace (prefixWord ++ tailWord_8296727) baseStart_8296727 baseEnd_8296727 := by
    simpa [prefixWord, tailWord_8296727, baseEnd_8296727] using wordTrace_append hprefix tailTrace_8296727
  have hstable : (prefixWord ++ tailWord_8296727).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8296727).length < 2 ^ (prefixWord ++ tailWord_8296727).sum := by decide
  have hdescent : baseEnd_8296727 < baseStart_8296727 := by decide
  rcases family_descends (prefixWord ++ tailWord_8296727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8296740 : List Nat := [2, 3, 1, 3, 1, 2, 1, 10]
def baseStart_8296740 : Nat := 118140960795 + 8296740 * 2 ^ 59
def prefixEnd_8296740 : Nat := 4983230072969 + 3 ^ 40 * 8296740 * 2
def baseEnd_8296740 : Nat := 157785758717924970381259

theorem tailTrace_8296740 : CollatzResearch.WordTrace tailWord_8296740 prefixEnd_8296740 157785758717924970381259 := by
  unfold tailWord_8296740
  simp only [CollatzResearch.WordTrace]
  refine ⟨151303483981167712613167837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 201737978641556950150890449 151303483981167712613167837)
  ·
    refine ⟨56738806492937892229937939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 151303483981167712613167837 56738806492937892229937939)
    ·
      refine ⟨85108209739406838344906909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56738806492937892229937939 85108209739406838344906909)
      ·
        refine ⟨31915578652277564379340091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 85108209739406838344906909 31915578652277564379340091)
        ·
          refine ⟨47873367978416346569010137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31915578652277564379340091 47873367978416346569010137)
          ·
            refine ⟨35905025983812259926757603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47873367978416346569010137 35905025983812259926757603)
            ·
              refine ⟨53857538975718389890136405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35905025983812259926757603 53857538975718389890136405)
              ·
                refine ⟨157785758717924970381259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 53857538975718389890136405 157785758717924970381259)
                ·
                  rfl

theorem cell23_8296740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 2, 1, 10].length) (baseStart_8296740 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8296740 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8296740 prefixEnd_8296740 := by exact prefixLift 8296740
  have htrace : WordTrace (prefixWord ++ tailWord_8296740) baseStart_8296740 baseEnd_8296740 := by
    simpa [prefixWord, tailWord_8296740, baseEnd_8296740] using wordTrace_append hprefix tailTrace_8296740
  have hstable : (prefixWord ++ tailWord_8296740).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8296740).length < 2 ^ (prefixWord ++ tailWord_8296740).sum := by decide
  have hdescent : baseEnd_8296740 < baseStart_8296740 := by decide
  rcases family_descends (prefixWord ++ tailWord_8296740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8296754 : List Nat := [3, 2, 1, 1, 5, 1, 1, 1, 3, 2, 3]
def baseStart_8296754 : Nat := 118140960795 + 8296754 * 2 ^ 59
def prefixEnd_8296754 : Nat := 4983230072969 + 3 ^ 40 * 8296754 * 2
def baseEnd_8296754 : Nat := 4260222674113137145518929

theorem tailTrace_8296754 : CollatzResearch.WordTrace tailWord_8296754 prefixEnd_8296754 4260222674113137145518929 := by
  unfold tailWord_8296754
  simp only [CollatzResearch.WordTrace]
  refine ⟨75651869646071176404336329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 201738319056189803744896877 75651869646071176404336329)
  ·
    refine ⟨56738902234553382303252247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75651869646071176404336329 56738902234553382303252247)
    ·
      refine ⟨85108353351830073454878371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56738902234553382303252247 85108353351830073454878371)
      ·
        refine ⟨127662530027745110182317557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85108353351830073454878371 127662530027745110182317557)
        ·
          refine ⟨11968362190101104079592271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 127662530027745110182317557 11968362190101104079592271)
          ·
            refine ⟨17952543285151656119388407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11968362190101104079592271 17952543285151656119388407)
            ·
              refine ⟨26928814927727484179082611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17952543285151656119388407 26928814927727484179082611)
              ·
                refine ⟨40393222391591226268623917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26928814927727484179082611 40393222391591226268623917)
                ·
                  refine ⟨15147458396846709850733969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 40393222391591226268623917 15147458396846709850733969)
                  ·
                    refine ⟨11360593797635032388050477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15147458396846709850733969 11360593797635032388050477)
                    ·
                      refine ⟨4260222674113137145518929, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11360593797635032388050477 4260222674113137145518929)
                      ·
                        rfl

theorem cell23_8296754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 5, 1, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 5, 1, 1, 1, 3, 2, 3].length) (baseStart_8296754 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8296754 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8296754 prefixEnd_8296754 := by exact prefixLift 8296754
  have htrace : WordTrace (prefixWord ++ tailWord_8296754) baseStart_8296754 baseEnd_8296754 := by
    simpa [prefixWord, tailWord_8296754, baseEnd_8296754] using wordTrace_append hprefix tailTrace_8296754
  have hstable : (prefixWord ++ tailWord_8296754).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8296754).length < 2 ^ (prefixWord ++ tailWord_8296754).sum := by decide
  have hdescent : baseEnd_8296754 < baseStart_8296754 := by decide
  rcases family_descends (prefixWord ++ tailWord_8296754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8296767 : List Nat := [1, 1, 2, 2, 4, 1, 3, 2, 1, 3, 3]
def baseStart_8296767 : Nat := 118140960795 + 8296767 * 2 ^ 59
def prefixEnd_8296767 : Nat := 4983230072969 + 3 ^ 40 * 8296767 * 2
def baseEnd_8296767 : Nat := 4260229349361645594656369

theorem tailTrace_8296767 : CollatzResearch.WordTrace tailWord_8296767 prefixEnd_8296767 4260229349361645594656369 := by
  unfold tailWord_8296767
  simp only [CollatzResearch.WordTrace]
  refine ⟨302607952733237608837568555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201738635155491739225045703 302607952733237608837568555)
  ·
    refine ⟨453911929099856413256352833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 302607952733237608837568555 453911929099856413256352833)
    ·
      refine ⟨340433946824892309942264625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 453911929099856413256352833 340433946824892309942264625)
      ·
        refine ⟨255325460118669232456698469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 340433946824892309942264625 255325460118669232456698469)
        ·
          refine ⟨47873523772250481085630963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 255325460118669232456698469 47873523772250481085630963)
          ·
            refine ⟨71810285658375721628446445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47873523772250481085630963 71810285658375721628446445)
            ·
              refine ⟨26928857121890895610667417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 71810285658375721628446445 26928857121890895610667417)
              ·
                refine ⟨20196642841418171708000563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26928857121890895610667417 20196642841418171708000563)
                ·
                  refine ⟨30294964262127257562000845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20196642841418171708000563 30294964262127257562000845)
                  ·
                    refine ⟨11360611598297721585750317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 30294964262127257562000845 11360611598297721585750317)
                    ·
                      refine ⟨4260229349361645594656369, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11360611598297721585750317 4260229349361645594656369)
                      ·
                        rfl

theorem cell23_8296767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 3, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 3, 2, 1, 3, 3].length) (baseStart_8296767 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8296767 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8296767 prefixEnd_8296767 := by exact prefixLift 8296767
  have htrace : WordTrace (prefixWord ++ tailWord_8296767) baseStart_8296767 baseEnd_8296767 := by
    simpa [prefixWord, tailWord_8296767, baseEnd_8296767] using wordTrace_append hprefix tailTrace_8296767
  have hstable : (prefixWord ++ tailWord_8296767).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8296767).length < 2 ^ (prefixWord ++ tailWord_8296767).sum := by decide
  have hdescent : baseEnd_8296767 < baseStart_8296767 := by decide
  rcases family_descends (prefixWord ++ tailWord_8296767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8296784 : List Nat := [2, 1, 1, 1, 1, 6, 1, 4, 2, 1, 3]
def baseStart_8296784 : Nat := 118140960795 + 8296784 * 2 ^ 59
def prefixEnd_8296784 : Nat := 4983230072969 + 3 ^ 40 * 8296784 * 2
def baseEnd_8296784 : Nat := 4260238078532772028143791

theorem tailTrace_8296784 : CollatzResearch.WordTrace tailWord_8296784 prefixEnd_8296784 4260238078532772028143791 := by
  unfold tailWord_8296784
  simp only [CollatzResearch.WordTrace]
  refine ⟨151304286387088010370468703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 201739048516117347160624937 151304286387088010370468703)
  ·
    refine ⟨226956429580632015555703055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151304286387088010370468703 226956429580632015555703055)
    ·
      refine ⟨340434644370948023333554583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 226956429580632015555703055 340434644370948023333554583)
      ·
        refine ⟨510651966556422035000331875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 340434644370948023333554583 510651966556422035000331875)
        ·
          refine ⟨765977949834633052500497813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 510651966556422035000331875 765977949834633052500497813)
          ·
            refine ⟨35905216398498424335960835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 765977949834633052500497813 35905216398498424335960835)
            ·
              refine ⟨53857824597747636503941253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35905216398498424335960835 53857824597747636503941253)
              ·
                refine ⟨10098342112077681844488985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 53857824597747636503941253 10098342112077681844488985)
                ·
                  refine ⟨7573756584058261383366739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10098342112077681844488985 7573756584058261383366739)
                  ·
                    refine ⟨11360634876087392075050109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7573756584058261383366739 11360634876087392075050109)
                    ·
                      refine ⟨4260238078532772028143791, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11360634876087392075050109 4260238078532772028143791)
                      ·
                        rfl

theorem cell23_8296784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 6, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 6, 1, 4, 2, 1, 3].length) (baseStart_8296784 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8296784 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8296784 prefixEnd_8296784 := by exact prefixLift 8296784
  have htrace : WordTrace (prefixWord ++ tailWord_8296784) baseStart_8296784 baseEnd_8296784 := by
    simpa [prefixWord, tailWord_8296784, baseEnd_8296784] using wordTrace_append hprefix tailTrace_8296784
  have hstable : (prefixWord ++ tailWord_8296784).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8296784).length < 2 ^ (prefixWord ++ tailWord_8296784).sum := by decide
  have hdescent : baseEnd_8296784 < baseStart_8296784 := by decide
  rcases family_descends (prefixWord ++ tailWord_8296784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8296785 : List Nat := [1, 2, 2, 1, 4, 4, 2, 2, 1, 2, 2]
def baseStart_8296785 : Nat := 118140960795 + 8296785 * 2 ^ 59
def prefixEnd_8296785 : Nat := 4983230072969 + 3 ^ 40 * 8296785 * 2
def baseEnd_8296785 : Nat := 4260238592013426524231287

theorem tailTrace_8296785 : CollatzResearch.WordTrace tailWord_8296785 prefixEnd_8296785 4260238592013426524231287 := by
  unfold tailWord_8296785
  simp only [CollatzResearch.WordTrace]
  refine ⟨302608609247172397911723809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201739072831448265274482539 302608609247172397911723809)
  ·
    refine ⟨226956456935379298433792857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 302608609247172397911723809 226956456935379298433792857)
    ·
      refine ⟨170217342701534473825344643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 226956456935379298433792857 170217342701534473825344643)
      ·
        refine ⟨255326014052301710738016965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 170217342701534473825344643 255326014052301710738016965)
        ·
          refine ⟨47873627634806570763378181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 255326014052301710738016965 47873627634806570763378181)
          ·
            refine ⟨8976305181526232018133409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 47873627634806570763378181 8976305181526232018133409)
            ·
              refine ⟨6732228886144674013600057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8976305181526232018133409 6732228886144674013600057)
              ·
                refine ⟨5049171664608505510200043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6732228886144674013600057 5049171664608505510200043)
                ·
                  refine ⟨7573757496912758265300065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5049171664608505510200043 7573757496912758265300065)
                  ·
                    refine ⟨5680318122684568698975049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7573757496912758265300065 5680318122684568698975049)
                    ·
                      refine ⟨4260238592013426524231287, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5680318122684568698975049 4260238592013426524231287)
                      ·
                        rfl

theorem cell23_8296785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 4, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 4, 2, 2, 1, 2, 2].length) (baseStart_8296785 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8296785 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8296785 prefixEnd_8296785 := by exact prefixLift 8296785
  have htrace : WordTrace (prefixWord ++ tailWord_8296785) baseStart_8296785 baseEnd_8296785 := by
    simpa [prefixWord, tailWord_8296785, baseEnd_8296785] using wordTrace_append hprefix tailTrace_8296785
  have hstable : (prefixWord ++ tailWord_8296785).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8296785).length < 2 ^ (prefixWord ++ tailWord_8296785).sum := by decide
  have hdescent : baseEnd_8296785 < baseStart_8296785 := by decide
  rcases family_descends (prefixWord ++ tailWord_8296785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8296822 : List Nat := [5, 1, 1, 4, 2, 1, 2, 1, 1, 2, 3]
def baseStart_8296822 : Nat := 118140960795 + 8296822 * 2 ^ 59
def prefixEnd_8296822 : Nat := 4983230072969 + 3 ^ 40 * 8296822 * 2
def baseEnd_8296822 : Nat := 4260257590797642879468617

theorem tailTrace_8296822 : CollatzResearch.WordTrace tailWord_8296822 prefixEnd_8296822 4260257590797642879468617 := by
  unfold tailWord_8296822
  simp only [CollatzResearch.WordTrace]
  refine ⟨18913122421752397076926295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 201739972498692235487213813 18913122421752397076926295)
  ·
    refine ⟨28369683632628595615389443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18913122421752397076926295 28369683632628595615389443)
    ·
      refine ⟨42554525448942893423084165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28369683632628595615389443 42554525448942893423084165)
      ·
        refine ⟨7978973521676792516828281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 42554525448942893423084165 7978973521676792516828281)
        ·
          refine ⟨5984230141257594387621211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7978973521676792516828281 5984230141257594387621211)
          ·
            refine ⟨8976345211886391581431817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5984230141257594387621211 8976345211886391581431817)
            ·
              refine ⟨6732258908914793686073863, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8976345211886391581431817 6732258908914793686073863)
              ·
                refine ⟨10098388363372190529110795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6732258908914793686073863 10098388363372190529110795)
                ·
                  refine ⟨15147582545058285793666193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10098388363372190529110795 15147582545058285793666193)
                  ·
                    refine ⟨11360686908793714345249645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15147582545058285793666193 11360686908793714345249645)
                    ·
                      refine ⟨4260257590797642879468617, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11360686908793714345249645 4260257590797642879468617)
                      ·
                        rfl

theorem cell23_8296822_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 2, 1, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 2, 1, 2, 1, 1, 2, 3].length) (baseStart_8296822 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8296822 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8296822 prefixEnd_8296822 := by exact prefixLift 8296822
  have htrace : WordTrace (prefixWord ++ tailWord_8296822) baseStart_8296822 baseEnd_8296822 := by
    simpa [prefixWord, tailWord_8296822, baseEnd_8296822] using wordTrace_append hprefix tailTrace_8296822
  have hstable : (prefixWord ++ tailWord_8296822).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8296822).length < 2 ^ (prefixWord ++ tailWord_8296822).sum := by decide
  have hdescent : baseEnd_8296822 < baseStart_8296822 := by decide
  rcases family_descends (prefixWord ++ tailWord_8296822) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8296841 : List Nat := [1, 2, 1, 1, 6, 2, 1, 1, 4, 2, 2]
def baseStart_8296841 : Nat := 118140960795 + 8296841 * 2 ^ 59
def prefixEnd_8296841 : Nat := 4983230072969 + 3 ^ 40 * 8296841 * 2
def baseEnd_8296841 : Nat := 4260267346930078305131029

theorem tailTrace_8296841 : CollatzResearch.WordTrace tailWord_8296841 prefixEnd_8296841 4260267346930078305131029 := by
  unfold tailWord_8296841
  simp only [CollatzResearch.WordTrace]
  refine ⟨302610651734969519475762377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201740434489979679650508251 302610651734969519475762377)
  ·
    refine ⟨226957988801227139606821783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 302610651734969519475762377 226957988801227139606821783)
    ·
      refine ⟨340436983201840709410232675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 226957988801227139606821783 340436983201840709410232675)
      ·
        refine ⟨510655474802761064115349013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 340436983201840709410232675 510655474802761064115349013)
        ·
          refine ⟨23936975381379424880406985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 510655474802761064115349013 23936975381379424880406985)
          ·
            refine ⟨17952731536034568660305239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23936975381379424880406985 17952731536034568660305239)
            ·
              refine ⟨26929097304051852990457859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17952731536034568660305239 26929097304051852990457859)
              ·
                refine ⟨40393645956077779485686789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26929097304051852990457859 40393645956077779485686789)
                ·
                  refine ⟨7573808616764583653566273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 40393645956077779485686789 7573808616764583653566273)
                  ·
                    refine ⟨5680356462573437740174705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7573808616764583653566273 5680356462573437740174705)
                    ·
                      refine ⟨4260267346930078305131029, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5680356462573437740174705 4260267346930078305131029)
                      ·
                        rfl

theorem cell23_8296841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 2, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 2, 1, 1, 4, 2, 2].length) (baseStart_8296841 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8296841 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8296841 prefixEnd_8296841 := by exact prefixLift 8296841
  have htrace : WordTrace (prefixWord ++ tailWord_8296841) baseStart_8296841 baseEnd_8296841 := by
    simpa [prefixWord, tailWord_8296841, baseEnd_8296841] using wordTrace_append hprefix tailTrace_8296841
  have hstable : (prefixWord ++ tailWord_8296841).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8296841).length < 2 ^ (prefixWord ++ tailWord_8296841).sum := by decide
  have hdescent : baseEnd_8296841 < baseStart_8296841 := by decide
  rcases family_descends (prefixWord ++ tailWord_8296841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8296857 : List Nat := [1, 2, 1, 2, 1, 4, 1, 3, 2, 3, 3]
def baseStart_8296857 : Nat := 118140960795 + 8296857 * 2 ^ 59
def prefixEnd_8296857 : Nat := 4983230072969 + 3 ^ 40 * 8296857 * 2
def baseEnd_8296857 : Nat := 4260275562620550242530955

theorem tailTrace_8296857 : CollatzResearch.WordTrace tailWord_8296857 prefixEnd_8296857 4260275562620550242530955 := by
  unfold tailWord_8296857
  simp only [CollatzResearch.WordTrace]
  refine ⟨302611235302911554208344825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201740823535274369472229883 302611235302911554208344825)
  ·
    refine ⟨226958426477183665656258619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 302611235302911554208344825 226958426477183665656258619)
    ·
      refine ⟨340437639715775498484387929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 226958426477183665656258619 340437639715775498484387929)
      ·
        refine ⟨255328229786831623863290947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 340437639715775498484387929 255328229786831623863290947)
        ·
          refine ⟨382992344680247435794936421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 255328229786831623863290947 382992344680247435794936421)
          ·
            refine ⟨71811064627546394211550579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 382992344680247435794936421 71811064627546394211550579)
            ·
              refine ⟨107716596941319591317325869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71811064627546394211550579 107716596941319591317325869)
              ·
                refine ⟨40393723852994846743997201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 107716596941319591317325869 40393723852994846743997201)
                ·
                  refine ⟨30295292889746135057997901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40393723852994846743997201 30295292889746135057997901)
                  ·
                    refine ⟨11360734833654800646749213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 30295292889746135057997901 11360734833654800646749213)
                    ·
                      refine ⟨4260275562620550242530955, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11360734833654800646749213 4260275562620550242530955)
                      ·
                        rfl

theorem cell23_8296857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 1, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 1, 3, 2, 3, 3].length) (baseStart_8296857 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8296857 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8296857 prefixEnd_8296857 := by exact prefixLift 8296857
  have htrace : WordTrace (prefixWord ++ tailWord_8296857) baseStart_8296857 baseEnd_8296857 := by
    simpa [prefixWord, tailWord_8296857, baseEnd_8296857] using wordTrace_append hprefix tailTrace_8296857
  have hstable : (prefixWord ++ tailWord_8296857).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8296857).length < 2 ^ (prefixWord ++ tailWord_8296857).sum := by decide
  have hdescent : baseEnd_8296857 < baseStart_8296857 := by decide
  rcases family_descends (prefixWord ++ tailWord_8296857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8296880 : List Nat := [2, 1, 1, 1, 2, 1, 1, 2, 2, 2, 8]
def baseStart_8296880 : Nat := 118140960795 + 8296880 * 2 ^ 59
def prefixEnd_8296880 : Nat := 4983230072969 + 3 ^ 40 * 8296880 * 2
def baseEnd_8296880 : Nat := 4260287372675603652543349

theorem tailTrace_8296880 : CollatzResearch.WordTrace tailWord_8296880 prefixEnd_8296880 4260287372675603652543349 := by
  unfold tailWord_8296880
  simp only [CollatzResearch.WordTrace]
  refine ⟨151306037090914114568216047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 201741382787885486090954729 151306037090914114568216047)
  ·
    refine ⟨226959055636371171852324071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151306037090914114568216047 226959055636371171852324071)
    ·
      refine ⟨340438583454556757778486107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 226959055636371171852324071 340438583454556757778486107)
      ·
        refine ⟨510657875181835136667729161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 340438583454556757778486107 510657875181835136667729161)
        ·
          refine ⟨382993406386376352500796871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 510657875181835136667729161 382993406386376352500796871)
          ·
            refine ⟨574490109579564528751195307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 382993406386376352500796871 574490109579564528751195307)
            ·
              refine ⟨861735164369346793126792961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 574490109579564528751195307 861735164369346793126792961)
              ·
                refine ⟨646301373277010094845094721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 861735164369346793126792961 646301373277010094845094721)
                ·
                  refine ⟨484726029957757571133821041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 646301373277010094845094721 484726029957757571133821041)
                  ·
                    refine ⟨363544522468318178350365781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 484726029957757571133821041 363544522468318178350365781)
                    ·
                      refine ⟨4260287372675603652543349, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 363544522468318178350365781 4260287372675603652543349)
                      ·
                        rfl

theorem cell23_8296880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 2, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 2, 2, 2, 8].length) (baseStart_8296880 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8296880 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8296880 prefixEnd_8296880 := by exact prefixLift 8296880
  have htrace : WordTrace (prefixWord ++ tailWord_8296880) baseStart_8296880 baseEnd_8296880 := by
    simpa [prefixWord, tailWord_8296880, baseEnd_8296880] using wordTrace_append hprefix tailTrace_8296880
  have hstable : (prefixWord ++ tailWord_8296880).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8296880).length < 2 ^ (prefixWord ++ tailWord_8296880).sum := by decide
  have hdescent : baseEnd_8296880 < baseStart_8296880 := by decide
  rcases family_descends (prefixWord ++ tailWord_8296880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8296881 : List Nat := [1, 2, 2, 4, 1, 4, 1, 3, 5]
def baseStart_8296881 : Nat := 118140960795 + 8296881 * 2 ^ 59
def prefixEnd_8296881 : Nat := 4983230072969 + 3 ^ 40 * 8296881 * 2
def baseEnd_8296881 : Nat := 473365320684028683181205

theorem tailTrace_8296881 : CollatzResearch.WordTrace tailWord_8296881 prefixEnd_8296881 473365320684028683181205 := by
  unfold tailWord_8296881
  simp only [CollatzResearch.WordTrace]
  refine ⟨302612110654824606307218497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201741407103216404204812331 302612110654824606307218497)
  ·
    refine ⟨226959082991118454730413873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 302612110654824606307218497 226959082991118454730413873)
    ·
      refine ⟨170219312243338841047810405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 226959082991118454730413873 170219312243338841047810405)
      ·
        refine ⟨31916121045626032696464451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 170219312243338841047810405 31916121045626032696464451)
        ·
          refine ⟨47874181568439049044696677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31916121045626032696464451 47874181568439049044696677)
          ·
            refine ⟨8976409044082321695880627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 47874181568439049044696677 8976409044082321695880627)
            ·
              refine ⟨13464613566123482543820941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8976409044082321695880627 13464613566123482543820941)
              ·
                refine ⟨5049230087296305953932853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13464613566123482543820941 5049230087296305953932853)
                ·
                  refine ⟨473365320684028683181205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5049230087296305953932853 473365320684028683181205)
                  ·
                    rfl

theorem cell23_8296881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 4, 1, 3, 5].length) (baseStart_8296881 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8296881 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8296881 prefixEnd_8296881 := by exact prefixLift 8296881
  have htrace : WordTrace (prefixWord ++ tailWord_8296881) baseStart_8296881 baseEnd_8296881 := by
    simpa [prefixWord, tailWord_8296881, baseEnd_8296881] using wordTrace_append hprefix tailTrace_8296881
  have hstable : (prefixWord ++ tailWord_8296881).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8296881).length < 2 ^ (prefixWord ++ tailWord_8296881).sum := by decide
  have hdescent : baseEnd_8296881 < baseStart_8296881 := by decide
  rcases family_descends (prefixWord ++ tailWord_8296881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8296931 : List Nat := [1, 1, 1, 6, 3, 1, 2, 1, 2, 1, 4]
def baseStart_8296931 : Nat := 118140960795 + 8296931 * 2 ^ 59
def prefixEnd_8296931 : Nat := 4983230072969 + 3 ^ 40 * 8296931 * 2
def baseEnd_8296931 : Nat := 4260313560188982953005615

theorem tailTrace_8296931 : CollatzResearch.WordTrace tailWord_8296931 prefixEnd_8296931 4260313560188982953005615 := by
  unfold tailWord_8296931
  simp only [CollatzResearch.WordTrace]
  refine ⟨302613934304643464846538647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201742622869762309897692431 302613934304643464846538647)
  ·
    refine ⟨453920901456965197269807971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 302613934304643464846538647 453920901456965197269807971)
    ·
      refine ⟨680881352185447795904711957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 453920901456965197269807971 680881352185447795904711957)
      ·
        refine ⟨31916313383692865433033373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 680881352185447795904711957 31916313383692865433033373)
        ·
          refine ⟨11968617518884824537387515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31916313383692865433033373 11968617518884824537387515)
          ·
            refine ⟨17952926278327236806081273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11968617518884824537387515 17952926278327236806081273)
            ·
              refine ⟨13464694708745427604560955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17952926278327236806081273 13464694708745427604560955)
              ·
                refine ⟨20197042063118141406841433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13464694708745427604560955 20197042063118141406841433)
                ·
                  refine ⟨15147781547338606055131075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20197042063118141406841433 15147781547338606055131075)
                  ·
                    refine ⟨22721672321007909082696613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15147781547338606055131075 22721672321007909082696613)
                    ·
                      refine ⟨4260313560188982953005615, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22721672321007909082696613 4260313560188982953005615)
                      ·
                        rfl

theorem cell23_8296931_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 3, 1, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 3, 1, 2, 1, 2, 1, 4].length) (baseStart_8296931 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8296931 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8296931 prefixEnd_8296931 := by exact prefixLift 8296931
  have htrace : WordTrace (prefixWord ++ tailWord_8296931) baseStart_8296931 baseEnd_8296931 := by
    simpa [prefixWord, tailWord_8296931, baseEnd_8296931] using wordTrace_append hprefix tailTrace_8296931
  have hstable : (prefixWord ++ tailWord_8296931).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8296931).length < 2 ^ (prefixWord ++ tailWord_8296931).sum := by decide
  have hdescent : baseEnd_8296931 < baseStart_8296931 := by decide
  rcases family_descends (prefixWord ++ tailWord_8296931) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8296957 : List Nat := [1, 4, 1, 1, 1, 3, 2, 1, 1, 2, 6]
def baseStart_8296957 : Nat := 118140960795 + 8296957 * 2 ^ 59
def prefixEnd_8296957 : Nat := 4983230072969 + 3 ^ 40 * 8296957 * 2
def baseEnd_8296957 : Nat := 4260326910685999851280495

theorem tailTrace_8296957 : CollatzResearch.WordTrace tailWord_8296957 prefixEnd_8296957 4260326910685999851280495 := by
  unfold tailWord_8296957
  simp only [CollatzResearch.WordTrace]
  refine ⟨302614882602549271286985125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201743255068366180857990083 302614882602549271286985125)
  ·
    refine ⟨56740290487977988366309711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 302614882602549271286985125 56740290487977988366309711)
    ·
      refine ⟨85110435731966982549464567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56740290487977988366309711 85110435731966982549464567)
      ·
        refine ⟨127665653597950473824196851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85110435731966982549464567 127665653597950473824196851)
        ·
          refine ⟨191498480396925710736295277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 127665653597950473824196851 191498480396925710736295277)
          ·
            refine ⟨71811930148847141526110729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 191498480396925710736295277 71811930148847141526110729)
            ·
              refine ⟨53858947611635356144583047, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 71811930148847141526110729 53858947611635356144583047)
              ·
                refine ⟨80788421417453034216874571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53858947611635356144583047 80788421417453034216874571)
                ·
                  refine ⟨121182632126179551325311857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 80788421417453034216874571 121182632126179551325311857)
                  ·
                    refine ⟨90886974094634663493983893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 121182632126179551325311857 90886974094634663493983893)
                    ·
                      refine ⟨4260326910685999851280495, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 90886974094634663493983893 4260326910685999851280495)
                      ·
                        rfl

theorem cell23_8296957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 2, 1, 1, 2, 6].length) (baseStart_8296957 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8296957 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8296957 prefixEnd_8296957 := by exact prefixLift 8296957
  have htrace : WordTrace (prefixWord ++ tailWord_8296957) baseStart_8296957 baseEnd_8296957 := by
    simpa [prefixWord, tailWord_8296957, baseEnd_8296957] using wordTrace_append hprefix tailTrace_8296957
  have hstable : (prefixWord ++ tailWord_8296957).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8296957).length < 2 ^ (prefixWord ++ tailWord_8296957).sum := by decide
  have hdescent : baseEnd_8296957 < baseStart_8296957 := by decide
  rcases family_descends (prefixWord ++ tailWord_8296957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8296981 : List Nat := [1, 3, 2, 1, 3, 1, 3, 2, 3, 1, 3]
def baseStart_8296981 : Nat := 118140960795 + 8296981 * 2 ^ 59
def prefixEnd_8296981 : Nat := 4983230072969 + 3 ^ 40 * 8296981 * 2
def baseEnd_8296981 : Nat := 4260339234221707757380385

theorem tailTrace_8296981 : CollatzResearch.WordTrace tailWord_8296981 prefixEnd_8296981 4260339234221707757380385 := by
  unfold tailWord_8296981
  simp only [CollatzResearch.WordTrace]
  refine ⟨302615757954462323385858797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201743838636308215590572531 302615757954462323385858797)
  ·
    refine ⟨113480909232923371269697049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 302615757954462323385858797 113480909232923371269697049)
    ·
      refine ⟨85110681924692528452272787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 113480909232923371269697049 85110681924692528452272787)
      ·
        refine ⟨127666022887038792678409181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85110681924692528452272787 127666022887038792678409181)
        ·
          refine ⟨47874758582639547254403443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 127666022887038792678409181 47874758582639547254403443)
          ·
            refine ⟨71812137873959320881605165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47874758582639547254403443 71812137873959320881605165)
            ·
              refine ⟨26929551702734745330601937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 71812137873959320881605165 26929551702734745330601937)
              ·
                refine ⟨20197163777051058997951453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26929551702734745330601937 20197163777051058997951453)
                ·
                  refine ⟨7573936416394147124231795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20197163777051058997951453 7573936416394147124231795)
                  ·
                    refine ⟨11360904624591220686347693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7573936416394147124231795 11360904624591220686347693)
                    ·
                      refine ⟨4260339234221707757380385, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11360904624591220686347693 4260339234221707757380385)
                      ·
                        rfl

theorem cell23_8296981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 3, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 3, 2, 3, 1, 3].length) (baseStart_8296981 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8296981 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8296981 prefixEnd_8296981 := by exact prefixLift 8296981
  have htrace : WordTrace (prefixWord ++ tailWord_8296981) baseStart_8296981 baseEnd_8296981 := by
    simpa [prefixWord, tailWord_8296981, baseEnd_8296981] using wordTrace_append hprefix tailTrace_8296981
  have hstable : (prefixWord ++ tailWord_8296981).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8296981).length < 2 ^ (prefixWord ++ tailWord_8296981).sum := by decide
  have hdescent : baseEnd_8296981 < baseStart_8296981 := by decide
  rcases family_descends (prefixWord ++ tailWord_8296981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8296984 : List Nat := [2, 1, 2, 3, 3, 1, 2, 1, 3, 5]
def baseStart_8296984 : Nat := 118140960795 + 8296984 * 2 ^ 59
def prefixEnd_8296984 : Nat := 4983230072969 + 3 ^ 40 * 8296984 * 2
def baseEnd_8296984 : Nat := 1420113591554557081880957

theorem tailTrace_8296984 : CollatzResearch.WordTrace tailWord_8296984 prefixEnd_8296984 1420113591554557081880957 := by
  unfold tailWord_8296984
  simp only [CollatzResearch.WordTrace]
  refine ⟨151307933686725727449109003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 201743911582300969932145337 151307933686725727449109003)
  ·
    refine ⟨226961900530088591173663505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151307933686725727449109003 226961900530088591173663505)
    ·
      refine ⟨170221425397566443380247629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 226961900530088591173663505 170221425397566443380247629)
      ·
        refine ⟨63833034524087416267592861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 170221425397566443380247629 63833034524087416267592861)
        ·
          refine ⟨23937387946532781100347323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 63833034524087416267592861 23937387946532781100347323)
          ·
            refine ⟨35906081919799171650520985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23937387946532781100347323 35906081919799171650520985)
            ·
              refine ⟨26929561439849378737890739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35906081919799171650520985 26929561439849378737890739)
              ·
                refine ⟨40394342159774068106836109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26929561439849378737890739 40394342159774068106836109)
                ·
                  refine ⟨15147878309915275540063541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 40394342159774068106836109 15147878309915275540063541)
                  ·
                    refine ⟨1420113591554557081880957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15147878309915275540063541 1420113591554557081880957)
                    ·
                      rfl

theorem cell23_8296984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 1, 2, 1, 3, 5].length) (baseStart_8296984 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8296984 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8296984 prefixEnd_8296984 := by exact prefixLift 8296984
  have htrace : WordTrace (prefixWord ++ tailWord_8296984) baseStart_8296984 baseEnd_8296984 := by
    simpa [prefixWord, tailWord_8296984, baseEnd_8296984] using wordTrace_append hprefix tailTrace_8296984
  have hstable : (prefixWord ++ tailWord_8296984).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8296984).length < 2 ^ (prefixWord ++ tailWord_8296984).sum := by decide
  have hdescent : baseEnd_8296984 < baseStart_8296984 := by decide
  rcases family_descends (prefixWord ++ tailWord_8296984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8297004 : List Nat := [2, 2, 1, 1, 1, 2, 1, 2, 1, 8, 2]
def baseStart_8297004 : Nat := 118140960795 + 8297004 * 2 ^ 59
def prefixEnd_8297004 : Nat := 4983230072969 + 3 ^ 40 * 8297004 * 2
def baseEnd_8297004 : Nat := 4260351044276761167392779

theorem tailTrace_8297004 : CollatzResearch.WordTrace tailWord_8297004 prefixEnd_8297004 4260351044276761167392779 := by
  unfold tailWord_8297004
  simp only [CollatzResearch.WordTrace]
  refine ⟨151308298416689499156973033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 201744397888919332209297377 151308298416689499156973033)
  ·
    refine ⟨113481223812517124367729775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 151308298416689499156973033 113481223812517124367729775)
    ·
      refine ⟨170221835718775686551594663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113481223812517124367729775 170221835718775686551594663)
      ·
        refine ⟨255332753578163529827391995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 170221835718775686551594663 255332753578163529827391995)
        ·
          refine ⟨382999130367245294741087993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 255332753578163529827391995 382999130367245294741087993)
          ·
            refine ⟨287249347775433971055815995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 382999130367245294741087993 287249347775433971055815995)
            ·
              refine ⟨430874021663150956583723993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 287249347775433971055815995 430874021663150956583723993)
              ·
                refine ⟨323155516247363217437792995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 430874021663150956583723993 323155516247363217437792995)
                ·
                  refine ⟨484733274371044826156689493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 323155516247363217437792995 484733274371044826156689493)
                  ·
                    refine ⟨5680468059035681556523705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 484733274371044826156689493 5680468059035681556523705)
                    ·
                      refine ⟨4260351044276761167392779, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5680468059035681556523705 4260351044276761167392779)
                      ·
                        rfl

theorem cell23_8297004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 8, 2].length) (baseStart_8297004 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8297004 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8297004 prefixEnd_8297004 := by exact prefixLift 8297004
  have htrace : WordTrace (prefixWord ++ tailWord_8297004) baseStart_8297004 baseEnd_8297004 := by
    simpa [prefixWord, tailWord_8297004, baseEnd_8297004] using wordTrace_append hprefix tailTrace_8297004
  have hstable : (prefixWord ++ tailWord_8297004).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8297004).length < 2 ^ (prefixWord ++ tailWord_8297004).sum := by decide
  have hdescent : baseEnd_8297004 < baseStart_8297004 := by decide
  rcases family_descends (prefixWord ++ tailWord_8297004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8297007 : List Nat := [1, 1, 2, 1, 2, 1, 1, 1, 7, 1, 5]
def baseStart_8297007 : Nat := 118140960795 + 8297007 * 2 ^ 59
def prefixEnd_8297007 : Nat := 4983230072969 + 3 ^ 40 * 8297007 * 2
def baseEnd_8297007 : Nat := 4260352584718724655655265

theorem tailTrace_8297007 : CollatzResearch.WordTrace tailWord_8297007 prefixEnd_8297007 4260352584718724655655265 := by
  unfold tailWord_8297007
  simp only [CollatzResearch.WordTrace]
  refine ⟨302616706252368129826305275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201744470834912086550870183 302616706252368129826305275)
  ·
    refine ⟨453925059378552194739457913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 302616706252368129826305275 453925059378552194739457913)
    ·
      refine ⟨340443794533914146054593435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 453925059378552194739457913 340443794533914146054593435)
      ·
        refine ⟨510665691800871219081890153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 340443794533914146054593435 510665691800871219081890153)
        ·
          refine ⟨382999268850653414311417615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 510665691800871219081890153 382999268850653414311417615)
          ·
            refine ⟨574498903275980121467126423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 382999268850653414311417615 574498903275980121467126423)
            ·
              refine ⟨861748354913970182200689635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 574498903275980121467126423 861748354913970182200689635)
              ·
                refine ⟨1292622532370955273301034453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 861748354913970182200689635 1292622532370955273301034453)
                ·
                  refine ⟨30295840602444264217992995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1292622532370955273301034453 30295840602444264217992995)
                  ·
                    refine ⟨45443760903666396326989493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 30295840602444264217992995 45443760903666396326989493)
                    ·
                      refine ⟨4260352584718724655655265, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 45443760903666396326989493 4260352584718724655655265)
                      ·
                        rfl

theorem cell23_8297007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 1, 7, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 1, 7, 1, 5].length) (baseStart_8297007 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8297007 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8297007 prefixEnd_8297007 := by exact prefixLift 8297007
  have htrace : WordTrace (prefixWord ++ tailWord_8297007) baseStart_8297007 baseEnd_8297007 := by
    simpa [prefixWord, tailWord_8297007, baseEnd_8297007] using wordTrace_append hprefix tailTrace_8297007
  have hstable : (prefixWord ++ tailWord_8297007).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8297007).length < 2 ^ (prefixWord ++ tailWord_8297007).sum := by decide
  have hdescent : baseEnd_8297007 < baseStart_8297007 := by decide
  rcases family_descends (prefixWord ++ tailWord_8297007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8297024 : List Nat := [2, 1, 1, 2, 2, 2, 2, 1, 5, 2, 3]
def baseStart_8297024 : Nat := 118140960795 + 8297024 * 2 ^ 59
def prefixEnd_8297024 : Nat := 4983230072969 + 3 ^ 40 * 8297024 * 2
def baseEnd_8297024 : Nat := 4260361313889851089142687

theorem tailTrace_8297024 : CollatzResearch.WordTrace tailWord_8297024 prefixEnd_8297024 4260361313889851089142687 := by
  unfold tailWord_8297024
  simp only [CollatzResearch.WordTrace]
  refine ⟨151308663146653270864837063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 201744884195537694486449417 151308663146653270864837063)
  ·
    refine ⟨226962994719979906297255595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151308663146653270864837063 226962994719979906297255595)
    ·
      refine ⟨340444492079969859445883393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 226962994719979906297255595 340444492079969859445883393)
      ·
        refine ⟨255333369059977394584412545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 340444492079969859445883393 255333369059977394584412545)
        ·
          refine ⟨191500026794983045938309409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 255333369059977394584412545 191500026794983045938309409)
          ·
            refine ⟨143625020096237284453732057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 191500026794983045938309409 143625020096237284453732057)
            ·
              refine ⟨107718765072177963340299043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 143625020096237284453732057 107718765072177963340299043)
              ·
                refine ⟨161578147608266945010448565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 107718765072177963340299043 161578147608266945010448565)
                ·
                  refine ⟨15147951338275026094729553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 161578147608266945010448565 15147951338275026094729553)
                  ·
                    refine ⟨11360963503706269571047165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15147951338275026094729553 11360963503706269571047165)
                    ·
                      refine ⟨4260361313889851089142687, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11360963503706269571047165 4260361313889851089142687)
                      ·
                        rfl

theorem cell23_8297024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 2, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 2, 1, 5, 2, 3].length) (baseStart_8297024 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8297024 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8297024 prefixEnd_8297024 := by exact prefixLift 8297024
  have htrace : WordTrace (prefixWord ++ tailWord_8297024) baseStart_8297024 baseEnd_8297024 := by
    simpa [prefixWord, tailWord_8297024, baseEnd_8297024] using wordTrace_append hprefix tailTrace_8297024
  have hstable : (prefixWord ++ tailWord_8297024).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8297024).length < 2 ^ (prefixWord ++ tailWord_8297024).sum := by decide
  have hdescent : baseEnd_8297024 < baseStart_8297024 := by decide
  rcases family_descends (prefixWord ++ tailWord_8297024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8297031 : List Nat := [1, 1, 4, 1, 4, 3, 1, 1, 1, 6]
def baseStart_8297031 : Nat := 118140960795 + 8297031 * 2 ^ 59
def prefixEnd_8297031 : Nat := 4983230072969 + 3 ^ 40 * 8297031 * 2
def baseEnd_8297031 : Nat := 1420121636084810853918385

theorem tailTrace_8297031 : CollatzResearch.WordTrace tailWord_8297031 prefixEnd_8297031 1420121636084810853918385 := by
  unfold tailWord_8297031
  simp only [CollatzResearch.WordTrace]
  refine ⟨302617581604281181925178947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201745054402854121283452631 302617581604281181925178947)
  ·
    refine ⟨453926372406421772887768421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 302617581604281181925178947 453926372406421772887768421)
    ·
      refine ⟨85111194826204082416456579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 453926372406421772887768421 85111194826204082416456579)
      ·
        refine ⟨127666792239306123624684869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85111194826204082416456579 127666792239306123624684869)
        ·
          refine ⟨23937523544869898179628413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 127666792239306123624684869 23937523544869898179628413)
          ·
            refine ⟨8976571329326211817360655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23937523544869898179628413 8976571329326211817360655)
            ·
              refine ⟨13464856993989317726040983, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8976571329326211817360655 13464856993989317726040983)
              ·
                refine ⟨20197285490983976589061475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13464856993989317726040983 20197285490983976589061475)
                ·
                  refine ⟨30295928236475964883592213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20197285490983976589061475 30295928236475964883592213)
                  ·
                    refine ⟨1420121636084810853918385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 30295928236475964883592213 1420121636084810853918385)
                    ·
                      rfl

theorem cell23_8297031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 3, 1, 1, 1, 6].length) (baseStart_8297031 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8297031 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8297031 prefixEnd_8297031 := by exact prefixLift 8297031
  have htrace : WordTrace (prefixWord ++ tailWord_8297031) baseStart_8297031 baseEnd_8297031 := by
    simpa [prefixWord, tailWord_8297031, baseEnd_8297031] using wordTrace_append hprefix tailTrace_8297031
  have hstable : (prefixWord ++ tailWord_8297031).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8297031).length < 2 ^ (prefixWord ++ tailWord_8297031).sum := by decide
  have hdescent : baseEnd_8297031 < baseStart_8297031 := by decide
  rcases family_descends (prefixWord ++ tailWord_8297031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8297034 : List Nat := [3, 1, 2, 1, 1, 5, 1, 1, 1, 1, 6]
def baseStart_8297034 : Nat := 118140960795 + 8297034 * 2 ^ 59
def prefixEnd_8297034 : Nat := 4983230072969 + 3 ^ 40 * 8297034 * 2
def baseEnd_8297034 : Nat := 4260366448696396050017641

theorem tailTrace_8297034 : CollatzResearch.WordTrace tailWord_8297034 prefixEnd_8297034 4260366448696396050017641 := by
  unfold tailWord_8297034
  simp only [CollatzResearch.WordTrace]
  refine ⟨75654422755817578359384539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 201745127348846875625025437 75654422755817578359384539)
  ·
    refine ⟨113481634133726367539076809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75654422755817578359384539 113481634133726367539076809)
    ·
      refine ⟨85111225600294775654307607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 113481634133726367539076809 85111225600294775654307607)
      ·
        refine ⟨127666838400442163481461411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85111225600294775654307607 127666838400442163481461411)
        ·
          refine ⟨191500257600663245222192117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 127666838400442163481461411 191500257600663245222192117)
          ·
            refine ⟨17953149150062179239580511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 191500257600663245222192117 17953149150062179239580511)
            ·
              refine ⟨26929723725093268859370767, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17953149150062179239580511 26929723725093268859370767)
              ·
                refine ⟨40394585587639903289056151, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26929723725093268859370767 40394585587639903289056151)
                ·
                  refine ⟨60591878381459854933584227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40394585587639903289056151 60591878381459854933584227)
                  ·
                    refine ⟨90887817572189782400376341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 60591878381459854933584227 90887817572189782400376341)
                    ·
                      refine ⟨4260366448696396050017641, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 90887817572189782400376341 4260366448696396050017641)
                      ·
                        rfl

theorem cell23_8297034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 5, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 5, 1, 1, 1, 1, 6].length) (baseStart_8297034 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8297034 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8297034 prefixEnd_8297034 := by exact prefixLift 8297034
  have htrace : WordTrace (prefixWord ++ tailWord_8297034) baseStart_8297034 baseEnd_8297034 := by
    simpa [prefixWord, tailWord_8297034, baseEnd_8297034] using wordTrace_append hprefix tailTrace_8297034
  have hstable : (prefixWord ++ tailWord_8297034).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8297034).length < 2 ^ (prefixWord ++ tailWord_8297034).sum := by decide
  have hdescent : baseEnd_8297034 < baseStart_8297034 := by decide
  rcases family_descends (prefixWord ++ tailWord_8297034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8297038 : List Nat := [4, 1, 1, 1, 1, 2, 4, 2, 3, 2, 2]
def baseStart_8297038 : Nat := 118140960795 + 8297038 * 2 ^ 59
def prefixEnd_8297038 : Nat := 4983230072969 + 3 ^ 40 * 8297038 * 2
def baseEnd_8297038 : Nat := 4260368502619014034367623

theorem tailTrace_8297038 : CollatzResearch.WordTrace tailWord_8297038 prefixEnd_8297038 4260368502619014034367623 := by
  unfold tailWord_8297038
  simp only [CollatzResearch.WordTrace]
  refine ⟨37827229614406977765085471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 201745224610170548080455845 37827229614406977765085471)
  ·
    refine ⟨56740844421610466647628207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37827229614406977765085471 56740844421610466647628207)
    ·
      refine ⟨85111266632415699971442311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56740844421610466647628207 85111266632415699971442311)
      ·
        refine ⟨127666899948623549957163467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85111266632415699971442311 127666899948623549957163467)
        ·
          refine ⟨191500349922935324935745201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 127666899948623549957163467 191500349922935324935745201)
          ·
            refine ⟨143625262442201493701808901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 191500349922935324935745201 143625262442201493701808901)
            ·
              refine ⟨26929736707912780069089169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 143625262442201493701808901 26929736707912780069089169)
              ·
                refine ⟨20197302530934585051816877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26929736707912780069089169 20197302530934585051816877)
                ·
                  refine ⟨7573988449100469394431329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20197302530934585051816877 7573988449100469394431329)
                  ·
                    refine ⟨5680491336825352045823497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7573988449100469394431329 5680491336825352045823497)
                    ·
                      refine ⟨4260368502619014034367623, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5680491336825352045823497 4260368502619014034367623)
                      ·
                        rfl

theorem cell23_8297038_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 4, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 4, 2, 3, 2, 2].length) (baseStart_8297038 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8297038 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8297038 prefixEnd_8297038 := by exact prefixLift 8297038
  have htrace : WordTrace (prefixWord ++ tailWord_8297038) baseStart_8297038 baseEnd_8297038 := by
    simpa [prefixWord, tailWord_8297038, baseEnd_8297038] using wordTrace_append hprefix tailTrace_8297038
  have hstable : (prefixWord ++ tailWord_8297038).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8297038).length < 2 ^ (prefixWord ++ tailWord_8297038).sum := by decide
  have hdescent : baseEnd_8297038 < baseStart_8297038 := by decide
  rcases family_descends (prefixWord ++ tailWord_8297038) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8297041 : List Nat := [1, 2, 2, 1, 3, 3, 1, 4, 1, 2, 3]
def baseStart_8297041 : Nat := 118140960795 + 8297041 * 2 ^ 59
def prefixEnd_8297041 : Nat := 4983230072969 + 3 ^ 40 * 8297041 * 2
def baseEnd_8297041 : Nat := 4260370043060977522630109

theorem tailTrace_8297041 : CollatzResearch.WordTrace tailWord_8297041 prefixEnd_8297041 4260370043060977522630109 := by
  unfold tailWord_8297041
  simp only [CollatzResearch.WordTrace]
  refine ⟨302617946334244953633042977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201745297556163302422028651 302617946334244953633042977)
  ·
    refine ⟨226963459750683715224782233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 302617946334244953633042977 226963459750683715224782233)
    ·
      refine ⟨170222594813012786418586675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 226963459750683715224782233 170222594813012786418586675)
      ·
        refine ⟨255333892219519179627880013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 170222594813012786418586675 255333892219519179627880013)
        ·
          refine ⟨95750209582319692360455005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 255333892219519179627880013 95750209582319692360455005)
          ·
            refine ⟨35906328593369884635170627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 95750209582319692360455005 35906328593369884635170627)
            ·
              refine ⟨53859492890054826952755941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35906328593369884635170627 53859492890054826952755941)
              ·
                refine ⟨10098654916885280053641739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 53859492890054826952755941 10098654916885280053641739)
                ·
                  refine ⟨15147982375327920080462609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10098654916885280053641739 15147982375327920080462609)
                  ·
                    refine ⟨11360986781495940060346957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15147982375327920080462609 11360986781495940060346957)
                    ·
                      refine ⟨4260370043060977522630109, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11360986781495940060346957 4260370043060977522630109)
                      ·
                        rfl

theorem cell23_8297041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 3, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 3, 1, 4, 1, 2, 3].length) (baseStart_8297041 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8297041 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8297041 prefixEnd_8297041 := by exact prefixLift 8297041
  have htrace : WordTrace (prefixWord ++ tailWord_8297041) baseStart_8297041 baseEnd_8297041 := by
    simpa [prefixWord, tailWord_8297041, baseEnd_8297041] using wordTrace_append hprefix tailTrace_8297041
  have hstable : (prefixWord ++ tailWord_8297041).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8297041).length < 2 ^ (prefixWord ++ tailWord_8297041).sum := by decide
  have hdescent : baseEnd_8297041 < baseStart_8297041 := by decide
  rcases family_descends (prefixWord ++ tailWord_8297041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8297044 : List Nat := [2, 4, 1, 1, 1, 4, 1, 9]
def baseStart_8297044 : Nat := 118140960795 + 8297044 * 2 ^ 59
def prefixEnd_8297044 : Nat := 4983230072969 + 3 ^ 40 * 8297044 * 2
def baseEnd_8297044 : Nat := 157791540129738555958985

theorem tailTrace_8297044 : CollatzResearch.WordTrace tailWord_8297044 prefixEnd_8297044 157791540129738555958985 := by
  unfold tailWord_8297044
  simp only [CollatzResearch.WordTrace]
  refine ⟨151309027876617042572701093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 201745370502156056763601457 151309027876617042572701093)
  ·
    refine ⟨28370442726865695482381455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 151309027876617042572701093 28370442726865695482381455)
    ·
      refine ⟨42555664090298543223572183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28370442726865695482381455 42555664090298543223572183)
      ·
        refine ⟨63833496135447814835358275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42555664090298543223572183 63833496135447814835358275)
        ·
          refine ⟨95750244203171722253037413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63833496135447814835358275 95750244203171722253037413)
          ·
            refine ⟨17953170788094697922444515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 95750244203171722253037413 17953170788094697922444515)
            ·
              refine ⟨26929756182142046883666773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17953170788094697922444515 26929756182142046883666773)
              ·
                refine ⟨157791540129738555958985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 26929756182142046883666773 157791540129738555958985)
                ·
                  rfl

theorem cell23_8297044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 4, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 4, 1, 9].length) (baseStart_8297044 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8297044 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8297044 prefixEnd_8297044 := by exact prefixLift 8297044
  have htrace : WordTrace (prefixWord ++ tailWord_8297044) baseStart_8297044 baseEnd_8297044 := by
    simpa [prefixWord, tailWord_8297044, baseEnd_8297044] using wordTrace_append hprefix tailTrace_8297044
  have hstable : (prefixWord ++ tailWord_8297044).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8297044).length < 2 ^ (prefixWord ++ tailWord_8297044).sum := by decide
  have hdescent : baseEnd_8297044 < baseStart_8297044 := by decide
  rcases family_descends (prefixWord ++ tailWord_8297044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8297061 : List Nat := [1, 3, 1, 3, 5, 1, 9]
def baseStart_8297061 : Nat := 118140960795 + 8297061 * 2 ^ 59
def prefixEnd_8297061 : Nat := 4983230072969 + 3 ^ 40 * 8297061 * 2
def baseEnd_8297061 : Nat := 52597287810790956103457

theorem tailTrace_8297061 : CollatzResearch.WordTrace tailWord_8297061 prefixEnd_8297061 52597287810790956103457 := by
  unfold tailWord_8297061
  simp only [CollatzResearch.WordTrace]
  refine ⟨302618675794172497048771037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201745783862781664699180691 302618675794172497048771037)
  ·
    refine ⟨113482003422814686393289139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 302618675794172497048771037 113482003422814686393289139)
    ·
      refine ⟨170223005134222029589933709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113482003422814686393289139 170223005134222029589933709)
      ·
        refine ⟨63833626925333261096225141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 170223005134222029589933709 63833626925333261096225141)
        ·
          refine ⟨5984402524249993227771107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 63833626925333261096225141 5984402524249993227771107)
          ·
            refine ⟨8976603786374989841656661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5984402524249993227771107 8976603786374989841656661)
            ·
              refine ⟨52597287810790956103457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 8976603786374989841656661 52597287810790956103457)
              ·
                rfl

theorem cell23_8297061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 5, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 5, 1, 9].length) (baseStart_8297061 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8297061 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8297061 prefixEnd_8297061 := by exact prefixLift 8297061
  have htrace : WordTrace (prefixWord ++ tailWord_8297061) baseStart_8297061 baseEnd_8297061 := by
    simpa [prefixWord, tailWord_8297061, baseEnd_8297061] using wordTrace_append hprefix tailTrace_8297061
  have hstable : (prefixWord ++ tailWord_8297061).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8297061).length < 2 ^ (prefixWord ++ tailWord_8297061).sum := by decide
  have hdescent : baseEnd_8297061 < baseStart_8297061 := by decide
  rcases family_descends (prefixWord ++ tailWord_8297061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8297071 : List Nat := [1, 1, 2, 1, 3, 2, 4, 1, 4, 1, 3]
def baseStart_8297071 : Nat := 118140960795 + 8297071 * 2 ^ 59
def prefixEnd_8297071 : Nat := 4983230072969 + 3 ^ 40 * 8297071 * 2
def baseEnd_8297071 : Nat := 4260385447480612405254971

theorem tailTrace_8297071 : CollatzResearch.WordTrace tailWord_8297071 prefixEnd_8297071 4260385447480612405254971 := by
  unfold tailWord_8297071
  simp only [CollatzResearch.WordTrace]
  refine ⟨302619040524136268756635067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201746027016090845837756711 302619040524136268756635067)
  ·
    refine ⟨453928560786204403134952601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 302619040524136268756635067 453928560786204403134952601)
    ·
      refine ⟨340446420589653302351214451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 453928560786204403134952601 340446420589653302351214451)
      ·
        refine ⟨510669630884479953526821677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 340446420589653302351214451 510669630884479953526821677)
        ·
          refine ⟨191501111581679982572558129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 510669630884479953526821677 191501111581679982572558129)
          ·
            refine ⟨143625833686259986929418597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 191501111581679982572558129 143625833686259986929418597)
            ·
              refine ⟨26929843816173747549265987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 143625833686259986929418597 26929843816173747549265987)
              ·
                refine ⟨40394765724260621323898981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26929843816173747549265987 40394765724260621323898981)
                ·
                  refine ⟨7574018573298866498231059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 40394765724260621323898981 7574018573298866498231059)
                  ·
                    refine ⟨11361027859948299747346589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7574018573298866498231059 11361027859948299747346589)
                    ·
                      refine ⟨4260385447480612405254971, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11361027859948299747346589 4260385447480612405254971)
                      ·
                        rfl

theorem cell23_8297071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 4, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 4, 1, 4, 1, 3].length) (baseStart_8297071 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8297071 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8297071 prefixEnd_8297071 := by exact prefixLift 8297071
  have htrace : WordTrace (prefixWord ++ tailWord_8297071) baseStart_8297071 baseEnd_8297071 := by
    simpa [prefixWord, tailWord_8297071, baseEnd_8297071] using wordTrace_append hprefix tailTrace_8297071
  have hstable : (prefixWord ++ tailWord_8297071).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8297071).length < 2 ^ (prefixWord ++ tailWord_8297071).sum := by decide
  have hdescent : baseEnd_8297071 < baseStart_8297071 := by decide
  rcases family_descends (prefixWord ++ tailWord_8297071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8297072 : List Nat := [2, 1, 1, 1, 8, 1, 1, 1, 3, 2, 2]
def baseStart_8297072 : Nat := 118140960795 + 8297072 * 2 ^ 59
def prefixEnd_8297072 : Nat := 4983230072969 + 3 ^ 40 * 8297072 * 2
def baseEnd_8297072 : Nat := 4260385960961266901342467

theorem tailTrace_8297072 : CollatzResearch.WordTrace tailWord_8297072 prefixEnd_8297072 4260385960961266901342467 := by
  unfold tailWord_8297072
  simp only [CollatzResearch.WordTrace]
  refine ⟨151309538498566322963710735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 201746051331421763951614313 151309538498566322963710735)
  ·
    refine ⟨226964307747849484445566103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151309538498566322963710735 226964307747849484445566103)
    ·
      refine ⟨340446461621774226668349155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 226964307747849484445566103 340446461621774226668349155)
      ·
        refine ⟨510669692432661340002523733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 340446461621774226668349155 510669692432661340002523733)
        ·
          refine ⟨5984410458195250078154575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 510669692432661340002523733 5984410458195250078154575)
          ·
            refine ⟨8976615687292875117231863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5984410458195250078154575 8976615687292875117231863)
            ·
              refine ⟨13464923530939312675847795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8976615687292875117231863 13464923530939312675847795)
              ·
                refine ⟨20197385296408969013771693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13464923530939312675847795 20197385296408969013771693)
                ·
                  refine ⟨7574019486153363380164385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20197385296408969013771693 7574019486153363380164385)
                  ·
                    refine ⟨5680514614615022535123289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7574019486153363380164385 5680514614615022535123289)
                    ·
                      refine ⟨4260385960961266901342467, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5680514614615022535123289 4260385960961266901342467)
                      ·
                        rfl

theorem cell23_8297072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 8, 1, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 8, 1, 1, 1, 3, 2, 2].length) (baseStart_8297072 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8297072 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8297072 prefixEnd_8297072 := by exact prefixLift 8297072
  have htrace : WordTrace (prefixWord ++ tailWord_8297072) baseStart_8297072 baseEnd_8297072 := by
    simpa [prefixWord, tailWord_8297072, baseEnd_8297072] using wordTrace_append hprefix tailTrace_8297072
  have hstable : (prefixWord ++ tailWord_8297072).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8297072).length < 2 ^ (prefixWord ++ tailWord_8297072).sum := by decide
  have hdescent : baseEnd_8297072 < baseStart_8297072 := by decide
  rcases family_descends (prefixWord ++ tailWord_8297072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8297088 : List Nat := [2, 1, 1, 2, 1, 6, 1, 3, 2, 1, 3]
def baseStart_8297088 : Nat := 118140960795 + 8297088 * 2 ^ 59
def prefixEnd_8297088 : Nat := 4983230072969 + 3 ^ 40 * 8297088 * 2
def baseEnd_8297088 : Nat := 4260394176651738838742393

theorem tailTrace_8297088 : CollatzResearch.WordTrace tailWord_8297088 prefixEnd_8297088 4260394176651738838742393 := by
  unfold tailWord_8297088
  simp only [CollatzResearch.WordTrace]
  refine ⟨151309830282537340330001959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 201746440376716453773335945 151309830282537340330001959)
  ·
    refine ⟨226964745423806010495002939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151309830282537340330001959 226964745423806010495002939)
    ·
      refine ⟨340447118135709015742504409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 226964745423806010495002939 340447118135709015742504409)
      ·
        refine ⟨255335338601781761806878307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 340447118135709015742504409 255335338601781761806878307)
        ·
          refine ⟨383003007902672642710317461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 255335338601781761806878307 383003007902672642710317461)
          ·
            refine ⟨17953265995437780127046131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 383003007902672642710317461 17953265995437780127046131)
            ·
              refine ⟨26929898993156670190569197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17953265995437780127046131 26929898993156670190569197)
              ·
                refine ⟨10098712122433751321463449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26929898993156670190569197 10098712122433751321463449)
                ·
                  refine ⟨7574034091825313491097587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10098712122433751321463449 7574034091825313491097587)
                  ·
                    refine ⟨11361051137737970236646381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7574034091825313491097587 11361051137737970236646381)
                    ·
                      refine ⟨4260394176651738838742393, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11361051137737970236646381 4260394176651738838742393)
                      ·
                        rfl

theorem cell23_8297088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 6, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 6, 1, 3, 2, 1, 3].length) (baseStart_8297088 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8297088 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8297088 prefixEnd_8297088 := by exact prefixLift 8297088
  have htrace : WordTrace (prefixWord ++ tailWord_8297088) baseStart_8297088 baseEnd_8297088 := by
    simpa [prefixWord, tailWord_8297088, baseEnd_8297088] using wordTrace_append hprefix tailTrace_8297088
  have hstable : (prefixWord ++ tailWord_8297088).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8297088).length < 2 ^ (prefixWord ++ tailWord_8297088).sum := by decide
  have hdescent : baseEnd_8297088 < baseStart_8297088 := by decide
  rcases family_descends (prefixWord ++ tailWord_8297088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8297141 : List Nat := [1, 3, 3, 3, 1, 1, 1, 1, 1, 4, 4]
def baseStart_8297141 : Nat := 118140960795 + 8297141 * 2 ^ 59
def prefixEnd_8297141 : Nat := 4983230072969 + 3 ^ 40 * 8297141 * 2
def baseEnd_8297141 : Nat := 4260421391126427131379649

theorem tailTrace_8297141 : CollatzResearch.WordTrace tailWord_8297141 prefixEnd_8297141 4260421391126427131379649 := by
  unfold tailWord_8297141
  simp only [CollatzResearch.WordTrace]
  refine ⟨302621593633882670711683277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201747729089255113807788851 302621593633882670711683277)
  ·
    refine ⟨113483097612706001516881229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 302621593633882670711683277 113483097612706001516881229)
    ·
      refine ⟨42556161604764750568830461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 113483097612706001516881229 42556161604764750568830461)
      ·
        refine ⟨15958560601786781463311423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42556161604764750568830461 15958560601786781463311423)
        ·
          refine ⟨23937840902680172194967135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15958560601786781463311423 23937840902680172194967135)
          ·
            refine ⟨35906761354020258292450703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23937840902680172194967135 35906761354020258292450703)
            ·
              refine ⟨53860142031030387438676055, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35906761354020258292450703 53860142031030387438676055)
              ·
                refine ⟨80790213046545581158014083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53860142031030387438676055 80790213046545581158014083)
                ·
                  refine ⟨121185319569818371737021125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 80790213046545581158014083 121185319569818371737021125)
                  ·
                    refine ⟨22722247419340944700691461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 121185319569818371737021125 22722247419340944700691461)
                    ·
                      refine ⟨4260421391126427131379649, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22722247419340944700691461 4260421391126427131379649)
                      ·
                        rfl

theorem cell23_8297141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 1, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 1, 1, 1, 1, 4, 4].length) (baseStart_8297141 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8297141 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8297141 prefixEnd_8297141 := by exact prefixLift 8297141
  have htrace : WordTrace (prefixWord ++ tailWord_8297141) baseStart_8297141 baseEnd_8297141 := by
    simpa [prefixWord, tailWord_8297141, baseEnd_8297141] using wordTrace_append hprefix tailTrace_8297141
  have hstable : (prefixWord ++ tailWord_8297141).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8297141).length < 2 ^ (prefixWord ++ tailWord_8297141).sum := by decide
  have hdescent : baseEnd_8297141 < baseStart_8297141 := by decide
  rcases family_descends (prefixWord ++ tailWord_8297141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8297218 : List Nat := [3, 4, 1, 1, 1, 2, 2, 1, 1, 3, 4]
def baseStart_8297218 : Nat := 118140960795 + 8297218 * 2 ^ 59
def prefixEnd_8297218 : Nat := 4983230072969 + 3 ^ 40 * 8297218 * 2
def baseEnd_8297218 : Nat := 4260460929136823330116795

theorem tailTrace_8297218 : CollatzResearch.WordTrace tailWord_8297218 prefixEnd_8297218 4260460929136823330116795 := by
  unfold tailWord_8297218
  simp only [CollatzResearch.WordTrace]
  refine ⟨75656100513650928215559077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 201749601369735808574824205 75656100513650928215559077)
  ·
    refine ⟨14185518846309549040417327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 75656100513650928215559077 14185518846309549040417327)
    ·
      refine ⟨21278278269464323560625991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14185518846309549040417327 21278278269464323560625991)
      ·
        refine ⟨31917417404196485340938987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21278278269464323560625991 31917417404196485340938987)
        ·
          refine ⟨47876126106294728011408481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31917417404196485340938987 47876126106294728011408481)
          ·
            refine ⟨35907094579721046008556361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47876126106294728011408481 35907094579721046008556361)
            ·
              refine ⟨26930320934790784506417271, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35907094579721046008556361 26930320934790784506417271)
              ·
                refine ⟨40395481402186176759625907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26930320934790784506417271 40395481402186176759625907)
                ·
                  refine ⟨60593222103279265139438861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40395481402186176759625907 60593222103279265139438861)
                  ·
                    refine ⟨22722458288729724427289573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 60593222103279265139438861 22722458288729724427289573)
                    ·
                      refine ⟨4260460929136823330116795, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22722458288729724427289573 4260460929136823330116795)
                      ·
                        rfl

theorem cell23_8297218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 2, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 2, 2, 1, 1, 3, 4].length) (baseStart_8297218 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8297218 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8297218 prefixEnd_8297218 := by exact prefixLift 8297218
  have htrace : WordTrace (prefixWord ++ tailWord_8297218) baseStart_8297218 baseEnd_8297218 := by
    simpa [prefixWord, tailWord_8297218, baseEnd_8297218] using wordTrace_append hprefix tailTrace_8297218
  have hstable : (prefixWord ++ tailWord_8297218).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8297218).length < 2 ^ (prefixWord ++ tailWord_8297218).sum := by decide
  have hdescent : baseEnd_8297218 < baseStart_8297218 := by decide
  rcases family_descends (prefixWord ++ tailWord_8297218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8297221 : List Nat := [1, 3, 1, 1, 2, 1, 1, 2, 6, 2, 3]
def baseStart_8297221 : Nat := 118140960795 + 8297221 * 2 ^ 59
def prefixEnd_8297221 : Nat := 4983230072969 + 3 ^ 40 * 8297221 * 2
def baseEnd_8297221 : Nat := 4260462469578786818379281

theorem tailTrace_8297221 : CollatzResearch.WordTrace tailWord_8297221 prefixEnd_8297221 4260462469578786818379281 := by
  unfold tailWord_8297221
  simp only [CollatzResearch.WordTrace]
  refine ⟨302624511473592844374595517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201749674315728562916397011 302624511473592844374595517)
  ·
    refine ⟨113484191802597316640473319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 302624511473592844374595517 113484191802597316640473319)
    ·
      refine ⟨170226287703895974960709979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113484191802597316640473319 170226287703895974960709979)
      ·
        refine ⟨255339431555843962441064969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 170226287703895974960709979 255339431555843962441064969)
        ·
          refine ⟨191504573666882971830798727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 255339431555843962441064969 191504573666882971830798727)
          ·
            refine ⟨287256860500324457746198091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 191504573666882971830798727 287256860500324457746198091)
            ·
              refine ⟨430885290750486686619297137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 287256860500324457746198091 430885290750486686619297137)
              ·
                refine ⟨323163968062865014964472853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 430885290750486686619297137 323163968062865014964472853)
                ·
                  refine ⟨15148311002946797576459665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 323163968062865014964472853 15148311002946797576459665)
                  ·
                    refine ⟨11361233252210098182344749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15148311002946797576459665 11361233252210098182344749)
                    ·
                      refine ⟨4260462469578786818379281, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11361233252210098182344749 4260462469578786818379281)
                      ·
                        rfl

theorem cell23_8297221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 1, 2, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 1, 2, 6, 2, 3].length) (baseStart_8297221 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8297221 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8297221 prefixEnd_8297221 := by exact prefixLift 8297221
  have htrace : WordTrace (prefixWord ++ tailWord_8297221) baseStart_8297221 baseEnd_8297221 := by
    simpa [prefixWord, tailWord_8297221, baseEnd_8297221] using wordTrace_append hprefix tailTrace_8297221
  have hstable : (prefixWord ++ tailWord_8297221).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8297221).length < 2 ^ (prefixWord ++ tailWord_8297221).sum := by decide
  have hdescent : baseEnd_8297221 < baseStart_8297221 := by decide
  rcases family_descends (prefixWord ++ tailWord_8297221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8297271 : List Nat := [1, 1, 3, 1, 2, 1, 5, 1, 3, 5]
def baseStart_8297271 : Nat := 118140960795 + 8297271 * 2 ^ 59
def prefixEnd_8297271 : Nat := 4983230072969 + 3 ^ 40 * 8297271 * 2
def baseEnd_8297271 : Nat := 1420162714537170540918017

theorem tailTrace_8297271 : CollatzResearch.WordTrace tailWord_8297271 prefixEnd_8297271 1420162714537170540918017 := by
  unfold tailWord_8297271
  simp only [CollatzResearch.WordTrace]
  refine ⟨302626335123411702913915667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201750890082274468609277111 302626335123411702913915667)
  ·
    refine ⟨453939502685117554370873501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 302626335123411702913915667 453939502685117554370873501)
    ·
      refine ⟨170227313506919082889077563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 453939502685117554370873501 170227313506919082889077563)
      ·
        refine ⟨255340970260378624333616345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 170227313506919082889077563 255340970260378624333616345)
        ·
          refine ⟨191505727695283968250212259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 255340970260378624333616345 191505727695283968250212259)
          ·
            refine ⟨287258591542925952375318389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 191505727695283968250212259 287258591542925952375318389)
            ·
              refine ⟨26930492957149308035186099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 287258591542925952375318389 26930492957149308035186099)
              ·
                refine ⟨40395739435723962052779149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26930492957149308035186099 40395739435723962052779149)
                ·
                  refine ⟨15148402288396485769792181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 40395739435723962052779149 15148402288396485769792181)
                  ·
                    refine ⟨1420162714537170540918017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15148402288396485769792181 1420162714537170540918017)
                    ·
                      rfl

theorem cell23_8297271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 5, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 5, 1, 3, 5].length) (baseStart_8297271 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8297271 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8297271 prefixEnd_8297271 := by exact prefixLift 8297271
  have htrace : WordTrace (prefixWord ++ tailWord_8297271) baseStart_8297271 baseEnd_8297271 := by
    simpa [prefixWord, tailWord_8297271, baseEnd_8297271] using wordTrace_append hprefix tailTrace_8297271
  have hstable : (prefixWord ++ tailWord_8297271).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8297271).length < 2 ^ (prefixWord ++ tailWord_8297271).sum := by decide
  have hdescent : baseEnd_8297271 < baseStart_8297271 := by decide
  rcases family_descends (prefixWord ++ tailWord_8297271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8297301 : List Nat := [1, 3, 2, 2, 2, 1, 1, 2, 3, 6]
def baseStart_8297301 : Nat := 118140960795 + 8297301 * 2 ^ 59
def prefixEnd_8297301 : Nat := 4983230072969 + 3 ^ 40 * 8297301 * 2
def baseEnd_8297301 : Nat := 1420167849343715501792971

theorem tailTrace_8297301 : CollatzResearch.WordTrace tailWord_8297301 prefixEnd_8297301 1420167849343715501792971 := by
  unfold tailWord_8297301
  simp only [CollatzResearch.WordTrace]
  refine ⟨302627429313303018037507757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201751619542202012025005171 302627429313303018037507757)
  ·
    refine ⟨113485285992488631764065409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 302627429313303018037507757 113485285992488631764065409)
    ·
      refine ⟨85113964494366473823049057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 113485285992488631764065409 85113964494366473823049057)
      ·
        refine ⟨63835473370774855367286793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85113964494366473823049057 63835473370774855367286793)
        ·
          refine ⟨47876605028081141525465095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63835473370774855367286793 47876605028081141525465095)
          ·
            refine ⟨71814907542121712288197643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47876605028081141525465095 71814907542121712288197643)
            ·
              refine ⟨107722361313182568432296465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71814907542121712288197643 107722361313182568432296465)
              ·
                refine ⟨80791770984886926324222349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 107722361313182568432296465 80791770984886926324222349)
                ·
                  refine ⟨30296914119332597371583381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 80791770984886926324222349 30296914119332597371583381)
                  ·
                    refine ⟨1420167849343715501792971, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 30296914119332597371583381 1420167849343715501792971)
                    ·
                      rfl

theorem cell23_8297301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 1, 2, 3, 6].length) (baseStart_8297301 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8297301 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8297301 prefixEnd_8297301 := by exact prefixLift 8297301
  have htrace : WordTrace (prefixWord ++ tailWord_8297301) baseStart_8297301 baseEnd_8297301 := by
    simpa [prefixWord, tailWord_8297301, baseEnd_8297301] using wordTrace_append hprefix tailTrace_8297301
  have hstable : (prefixWord ++ tailWord_8297301).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8297301).length < 2 ^ (prefixWord ++ tailWord_8297301).sum := by decide
  have hdescent : baseEnd_8297301 < baseStart_8297301 := by decide
  rcases family_descends (prefixWord ++ tailWord_8297301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8297311 : List Nat := [1, 1, 2, 3, 1, 3, 2, 1, 3, 1, 5]
def baseStart_8297311 : Nat := 118140960795 + 8297311 * 2 ^ 59
def prefixEnd_8297311 : Nat := 4983230072969 + 3 ^ 40 * 8297311 * 2
def baseEnd_8297311 : Nat := 4260508682837691466253867

theorem tailTrace_8297311 : CollatzResearch.WordTrace tailWord_8297311 prefixEnd_8297311 4260508682837691466253867 := by
  unfold tailWord_8297311
  simp only [CollatzResearch.WordTrace]
  refine ⟨302627794043266789745371787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201751862695511193163581191 302627794043266789745371787)
  ·
    refine ⟨453941691064900184618057681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 302627794043266789745371787 453941691064900184618057681)
    ·
      refine ⟨340456268298675138463543261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 453941691064900184618057681 340456268298675138463543261)
      ·
        refine ⟨127671100612003176923828723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 340456268298675138463543261 127671100612003176923828723)
        ·
          refine ⟨191506650918004765385743085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 127671100612003176923828723 191506650918004765385743085)
          ·
            refine ⟨71814994094251787019653657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 191506650918004765385743085 71814994094251787019653657)
            ·
              refine ⟨53861245570688840264740243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 71814994094251787019653657 53861245570688840264740243)
              ·
                refine ⟨80791868356033260397110365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53861245570688840264740243 80791868356033260397110365)
                ·
                  refine ⟨30296950633512472648916387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 80791868356033260397110365 30296950633512472648916387)
                  ·
                    refine ⟨45445425950268708973374581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 30296950633512472648916387 45445425950268708973374581)
                    ·
                      refine ⟨4260508682837691466253867, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 45445425950268708973374581 4260508682837691466253867)
                      ·
                        rfl

theorem cell23_8297311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 2, 1, 3, 1, 5].length) (baseStart_8297311 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8297311 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8297311 prefixEnd_8297311 := by exact prefixLift 8297311
  have htrace : WordTrace (prefixWord ++ tailWord_8297311) baseStart_8297311 baseEnd_8297311 := by
    simpa [prefixWord, tailWord_8297311, baseEnd_8297311] using wordTrace_append hprefix tailTrace_8297311
  have hstable : (prefixWord ++ tailWord_8297311).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8297311).length < 2 ^ (prefixWord ++ tailWord_8297311).sum := by decide
  have hdescent : baseEnd_8297311 < baseStart_8297311 := by decide
  rcases family_descends (prefixWord ++ tailWord_8297311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8297328 : List Nat := [2, 1, 1, 1, 4, 1, 4, 1, 3, 2, 3]
def baseStart_8297328 : Nat := 118140960795 + 8297328 * 2 ^ 59
def prefixEnd_8297328 : Nat := 4983230072969 + 3 ^ 40 * 8297328 * 2
def baseEnd_8297328 : Nat := 4260517412008817899741289

theorem tailTrace_8297328 : CollatzResearch.WordTrace tailWord_8297328 prefixEnd_8297328 4260517412008817899741289 := by
  unfold tailWord_8297328
  simp only [CollatzResearch.WordTrace]
  refine ⟨151314207042102600824370319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 201752276056136801099160425 151314207042102600824370319)
  ·
    refine ⟨226971310563153901236555479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151314207042102600824370319 226971310563153901236555479)
    ·
      refine ⟨340456965844730851854833219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 226971310563153901236555479 340456965844730851854833219)
      ·
        refine ⟨510685448767096277782249829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 340456965844730851854833219 510685448767096277782249829)
        ·
          refine ⟨95753521643830552084171843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 510685448767096277782249829 95753521643830552084171843)
          ·
            refine ⟨143630282465745828126257765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 95753521643830552084171843 143630282465745828126257765)
            ·
              refine ⟨26930677962327342773673331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 143630282465745828126257765 26930677962327342773673331)
              ·
                refine ⟨40396016943491014160509997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26930677962327342773673331 40396016943491014160509997)
                ·
                  refine ⟨15148506353809130310191249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 40396016943491014160509997 15148506353809130310191249)
                  ·
                    refine ⟨11361379765356847732643437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15148506353809130310191249 11361379765356847732643437)
                    ·
                      refine ⟨4260517412008817899741289, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11361379765356847732643437 4260517412008817899741289)
                      ·
                        rfl

theorem cell23_8297328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 4, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 4, 1, 3, 2, 3].length) (baseStart_8297328 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8297328 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8297328 prefixEnd_8297328 := by exact prefixLift 8297328
  have htrace : WordTrace (prefixWord ++ tailWord_8297328) baseStart_8297328 baseEnd_8297328 := by
    simpa [prefixWord, tailWord_8297328, baseEnd_8297328] using wordTrace_append hprefix tailTrace_8297328
  have hstable : (prefixWord ++ tailWord_8297328).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8297328).length < 2 ^ (prefixWord ++ tailWord_8297328).sum := by decide
  have hdescent : baseEnd_8297328 < baseStart_8297328 := by decide
  rcases family_descends (prefixWord ++ tailWord_8297328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8297352 : List Nat := [2, 1, 3, 3, 2, 3, 1, 2, 2, 4]
def baseStart_8297352 : Nat := 118140960795 + 8297352 * 2 ^ 59
def prefixEnd_8297352 : Nat := 4983230072969 + 3 ^ 40 * 8297352 * 2
def baseEnd_8297352 : Nat := 1420176578514841935280393

theorem tailTrace_8297352 : CollatzResearch.WordTrace tailWord_8297352 prefixEnd_8297352 1420176578514841935280393 := by
  unfold tailWord_8297352
  simp only [CollatzResearch.WordTrace]
  refine ⟨151314644718059126873807155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 201752859624078835831742873 151314644718059126873807155)
  ·
    refine ⟨226971967077088690310710733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151314644718059126873807155 226971967077088690310710733)
    ·
      refine ⟨85114487653908258866516525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 226971967077088690310710733 85114487653908258866516525)
      ·
        refine ⟨31917932870215597074943697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 85114487653908258866516525 31917932870215597074943697)
        ·
          refine ⟨23938449652661697806207773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31917932870215597074943697 23938449652661697806207773)
          ·
            refine ⟨8976918619748136677327915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23938449652661697806207773 8976918619748136677327915)
            ·
              refine ⟨13465377929622205015991873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8976918619748136677327915 13465377929622205015991873)
              ·
                refine ⟨10099033447216653761993905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13465377929622205015991873 10099033447216653761993905)
                ·
                  refine ⟨7574275085412490321495429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10099033447216653761993905 7574275085412490321495429)
                  ·
                    refine ⟨1420176578514841935280393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7574275085412490321495429 1420176578514841935280393)
                    ·
                      rfl

theorem cell23_8297352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 3, 1, 2, 2, 4].length) (baseStart_8297352 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8297352 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8297352 prefixEnd_8297352 := by exact prefixLift 8297352
  have htrace : WordTrace (prefixWord ++ tailWord_8297352) baseStart_8297352 baseEnd_8297352 := by
    simpa [prefixWord, tailWord_8297352, baseEnd_8297352] using wordTrace_append hprefix tailTrace_8297352
  have hstable : (prefixWord ++ tailWord_8297352).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8297352).length < 2 ^ (prefixWord ++ tailWord_8297352).sum := by decide
  have hdescent : baseEnd_8297352 < baseStart_8297352 := by decide
  rcases family_descends (prefixWord ++ tailWord_8297352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8297372 : List Nat := [2, 2, 3, 3, 2, 2, 1, 1, 1, 2, 4]
def baseStart_8297372 : Nat := 118140960795 + 8297372 * 2 ^ 59
def prefixEnd_8297372 : Nat := 4983230072969 + 3 ^ 40 * 8297372 * 2
def baseEnd_8297372 : Nat := 4260540005157615727591087

theorem tailTrace_8297372 : CollatzResearch.WordTrace tailWord_8297372 prefixEnd_8297372 4260540005157615727591087 := by
  unfold tailWord_8297372
  simp only [CollatzResearch.WordTrace]
  refine ⟨151315009448022898581671185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 201753345930697198108894913 151315009448022898581671185)
  ·
    refine ⟨113486257086017173936253389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 151315009448022898581671185 113486257086017173936253389)
    ·
      refine ⟨42557346407256440226095021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 113486257086017173936253389 42557346407256440226095021)
      ·
        refine ⟨15959004902721165084785633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42557346407256440226095021 15959004902721165084785633)
        ·
          refine ⟨11969253677040873813589225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15959004902721165084785633 11969253677040873813589225)
          ·
            refine ⟨8976940257780655360191919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11969253677040873813589225 8976940257780655360191919)
            ·
              refine ⟨13465410386670983040287879, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8976940257780655360191919 13465410386670983040287879)
              ·
                refine ⟨20198115580006474560431819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13465410386670983040287879 20198115580006474560431819)
                ·
                  refine ⟨30297173370009711840647729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20198115580006474560431819 30297173370009711840647729)
                  ·
                    refine ⟨22722880027507283880485797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 30297173370009711840647729 22722880027507283880485797)
                    ·
                      refine ⟨4260540005157615727591087, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22722880027507283880485797 4260540005157615727591087)
                      ·
                        rfl

theorem cell23_8297372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 2, 2, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 2, 2, 1, 1, 1, 2, 4].length) (baseStart_8297372 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8297372 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8297372 prefixEnd_8297372 := by exact prefixLift 8297372
  have htrace : WordTrace (prefixWord ++ tailWord_8297372) baseStart_8297372 baseEnd_8297372 := by
    simpa [prefixWord, tailWord_8297372, baseEnd_8297372] using wordTrace_append hprefix tailTrace_8297372
  have hstable : (prefixWord ++ tailWord_8297372).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8297372).length < 2 ^ (prefixWord ++ tailWord_8297372).sum := by decide
  have hdescent : baseEnd_8297372 < baseStart_8297372 := by decide
  rcases family_descends (prefixWord ++ tailWord_8297372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8297375 : List Nat := [1, 1, 2, 5, 2, 1, 3, 1, 1, 3, 3]
def baseStart_8297375 : Nat := 118140960795 + 8297375 * 2 ^ 59
def prefixEnd_8297375 : Nat := 4983230072969 + 3 ^ 40 * 8297375 * 2
def baseEnd_8297375 : Nat := 4260541545599579215853573

theorem tailTrace_8297375 : CollatzResearch.WordTrace tailWord_8297375 prefixEnd_8297375 4260541545599579215853573 := by
  unfold tailWord_8297375
  simp only [CollatzResearch.WordTrace]
  refine ⟨302630128315034928675701579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201753418876689952450467719 302630128315034928675701579)
  ·
    refine ⟨453945192472552393013552369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 302630128315034928675701579 453945192472552393013552369)
    ·
      refine ⟨340458894354414294760164277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 453945192472552393013552369 340458894354414294760164277)
      ·
        refine ⟨31918021345726340133765401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 340458894354414294760164277 31918021345726340133765401)
        ·
          refine ⟨23938516009294755100324051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31918021345726340133765401 23938516009294755100324051)
          ·
            refine ⟨35907774013942132650486077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23938516009294755100324051 35907774013942132650486077)
            ·
              refine ⟨13465415255228299743932279, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35907774013942132650486077 13465415255228299743932279)
              ·
                refine ⟨20198122882842449615898419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13465415255228299743932279 20198122882842449615898419)
                ·
                  refine ⟨30297184324263674423847629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20198122882842449615898419 30297184324263674423847629)
                  ·
                    refine ⟨11361444121598877908942861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 30297184324263674423847629 11361444121598877908942861)
                    ·
                      refine ⟨4260541545599579215853573, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11361444121598877908942861 4260541545599579215853573)
                      ·
                        rfl

theorem cell23_8297375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 1, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 1, 3, 1, 1, 3, 3].length) (baseStart_8297375 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8297375 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8297375 prefixEnd_8297375 := by exact prefixLift 8297375
  have htrace : WordTrace (prefixWord ++ tailWord_8297375) baseStart_8297375 baseEnd_8297375 := by
    simpa [prefixWord, tailWord_8297375, baseEnd_8297375] using wordTrace_append hprefix tailTrace_8297375
  have hstable : (prefixWord ++ tailWord_8297375).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8297375).length < 2 ^ (prefixWord ++ tailWord_8297375).sum := by decide
  have hdescent : baseEnd_8297375 < baseStart_8297375 := by decide
  rcases family_descends (prefixWord ++ tailWord_8297375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8297391 : List Nat := [1, 1, 2, 1, 2, 2, 2, 2, 4, 6]
def baseStart_8297391 : Nat := 118140960795 + 8297391 * 2 ^ 59
def prefixEnd_8297391 : Nat := 4983230072969 + 3 ^ 40 * 8297391 * 2
def baseEnd_8297391 : Nat := 1420183253763350384417833

theorem tailTrace_8297391 : CollatzResearch.WordTrace tailWord_8297391 prefixEnd_8297391 1420183253763350384417833 := by
  unfold tailWord_8297391
  simp only [CollatzResearch.WordTrace]
  refine ⟨302630711882976963408284027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201753807921984642272189351 302630711882976963408284027)
  ·
    refine ⟨453946067824465445112426041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 302630711882976963408284027 453946067824465445112426041)
    ·
      refine ⟨340459550868349083834319531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 453946067824465445112426041 340459550868349083834319531)
      ·
        refine ⟨510689326302523625751479297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 340459550868349083834319531 510689326302523625751479297)
        ·
          refine ⟨383016994726892719313609473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 510689326302523625751479297 383016994726892719313609473)
          ·
            refine ⟨287262746045169539485207105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 383016994726892719313609473 287262746045169539485207105)
            ·
              refine ⟨215447059533877154613905329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 287262746045169539485207105 215447059533877154613905329)
              ·
                refine ⟨161585294650407865960428997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 215447059533877154613905329 161585294650407865960428997)
                ·
                  refine ⟨30297242746951474867580437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 161585294650407865960428997 30297242746951474867580437)
                  ·
                    refine ⟨1420183253763350384417833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 30297242746951474867580437 1420183253763350384417833)
                    ·
                      rfl

theorem cell23_8297391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 2, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 2, 2, 4, 6].length) (baseStart_8297391 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8297391 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8297391 prefixEnd_8297391 := by exact prefixLift 8297391
  have htrace : WordTrace (prefixWord ++ tailWord_8297391) baseStart_8297391 baseEnd_8297391 := by
    simpa [prefixWord, tailWord_8297391, baseEnd_8297391] using wordTrace_append hprefix tailTrace_8297391
  have hstable : (prefixWord ++ tailWord_8297391).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8297391).length < 2 ^ (prefixWord ++ tailWord_8297391).sum := by decide
  have hdescent : baseEnd_8297391 < baseStart_8297391 := by decide
  rcases family_descends (prefixWord ++ tailWord_8297391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8297393 : List Nat := [1, 2, 2, 4, 4, 1, 1, 3, 1, 2, 2]
def baseStart_8297393 : Nat := 118140960795 + 8297393 * 2 ^ 59
def prefixEnd_8297393 : Nat := 4983230072969 + 3 ^ 40 * 8297393 * 2
def baseEnd_8297393 : Nat := 4260550788251360145428491

theorem tailTrace_8297393 : CollatzResearch.WordTrace tailWord_8297393 prefixEnd_8297393 4260550788251360145428491 := by
  unfold tailWord_8297393
  simp only [CollatzResearch.WordTrace]
  refine ⟨302630784828969717749856833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201753856552646478499904555 302630784828969717749856833)
  ·
    refine ⟨226973088621727288312392625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 302630784828969717749856833 226973088621727288312392625)
    ·
      refine ⟨170229816466295466234294469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 226973088621727288312392625 170229816466295466234294469)
      ·
        refine ⟨31918090587430399918930213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 170229816466295466234294469 31918090587430399918930213)
        ·
          refine ⟨5984641985143199984799415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 31918090587430399918930213 5984641985143199984799415)
          ·
            refine ⟨8976962977714799977199123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5984641985143199984799415 8976962977714799977199123)
            ·
              refine ⟨13465444466572199965798685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8976962977714799977199123 13465444466572199965798685)
              ·
                refine ⟨5049541674964574987174507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13465444466572199965798685 5049541674964574987174507)
                ·
                  refine ⟨7574312512446862480761761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5049541674964574987174507 7574312512446862480761761)
                  ·
                    refine ⟨5680734384335146860571321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7574312512446862480761761 5680734384335146860571321)
                    ·
                      refine ⟨4260550788251360145428491, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5680734384335146860571321 4260550788251360145428491)
                      ·
                        rfl

theorem cell23_8297393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 4, 1, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 4, 1, 1, 3, 1, 2, 2].length) (baseStart_8297393 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8297393 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8297393 prefixEnd_8297393 := by exact prefixLift 8297393
  have htrace : WordTrace (prefixWord ++ tailWord_8297393) baseStart_8297393 baseEnd_8297393 := by
    simpa [prefixWord, tailWord_8297393, baseEnd_8297393] using wordTrace_append hprefix tailTrace_8297393
  have hstable : (prefixWord ++ tailWord_8297393).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8297393).length < 2 ^ (prefixWord ++ tailWord_8297393).sum := by decide
  have hdescent : baseEnd_8297393 < baseStart_8297393 := by decide
  rcases family_descends (prefixWord ++ tailWord_8297393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8297418 : List Nat := [3, 1, 2, 1, 2, 1, 1, 3, 2, 4, 3]
def baseStart_8297418 : Nat := 118140960795 + 8297418 * 2 ^ 59
def prefixEnd_8297418 : Nat := 4983230072969 + 3 ^ 40 * 8297418 * 2
def baseEnd_8297418 : Nat := 4260563625267722547615875

theorem tailTrace_8297418 : CollatzResearch.WordTrace tailWord_8297418 prefixEnd_8297418 4260563625267722547615875 := by
  unfold tailWord_8297418
  simp only [CollatzResearch.WordTrace]
  refine ⟨75657924163469786754879227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 201754464435919431346344605 75657924163469786754879227)
  ·
    refine ⟨113486886245204680132318841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75657924163469786754879227 113486886245204680132318841)
    ·
      refine ⟨85115164683903510099239131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 113486886245204680132318841 85115164683903510099239131)
      ·
        refine ⟨127672747025855265148858697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85115164683903510099239131 127672747025855265148858697)
        ·
          refine ⟨95754560269391448861644023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 127672747025855265148858697 95754560269391448861644023)
          ·
            refine ⟨143631840404087173292466035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 95754560269391448861644023 143631840404087173292466035)
            ·
              refine ⟨215447760606130759938699053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 143631840404087173292466035 215447760606130759938699053)
              ·
                refine ⟨80792910227299034977012145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 215447760606130759938699053 80792910227299034977012145)
                ·
                  refine ⟨60594682670474276232759109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 80792910227299034977012145 60594682670474276232759109)
                  ·
                    refine ⟨11361503000713926793642333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 60594682670474276232759109 11361503000713926793642333)
                    ·
                      refine ⟨4260563625267722547615875, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11361503000713926793642333 4260563625267722547615875)
                      ·
                        rfl

theorem cell23_8297418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 1, 3, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 1, 3, 2, 4, 3].length) (baseStart_8297418 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8297418 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8297418 prefixEnd_8297418 := by exact prefixLift 8297418
  have htrace : WordTrace (prefixWord ++ tailWord_8297418) baseStart_8297418 baseEnd_8297418 := by
    simpa [prefixWord, tailWord_8297418, baseEnd_8297418] using wordTrace_append hprefix tailTrace_8297418
  have hstable : (prefixWord ++ tailWord_8297418).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8297418).length < 2 ^ (prefixWord ++ tailWord_8297418).sum := by decide
  have hdescent : baseEnd_8297418 < baseStart_8297418 := by decide
  rcases family_descends (prefixWord ++ tailWord_8297418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8297426 : List Nat := [3, 2, 2, 3, 1, 3, 2, 1, 2, 1, 3]
def baseStart_8297426 : Nat := 118140960795 + 8297426 * 2 ^ 59
def prefixEnd_8297426 : Nat := 4983230072969 + 3 ^ 40 * 8297426 * 2
def baseEnd_8297426 : Nat := 4260567733112958516315839

theorem tailTrace_8297426 : CollatzResearch.WordTrace tailWord_8297426 prefixEnd_8297426 4260567733112958516315839 := by
  unfold tailWord_8297426
  simp only [CollatzResearch.WordTrace]
  refine ⟨75657997109462541096452033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 201754658958566776257205421 75657997109462541096452033)
  ·
    refine ⟨56743497832096905822339025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75657997109462541096452033 56743497832096905822339025)
    ·
      refine ⟨42557623374072679366754269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56743497832096905822339025 42557623374072679366754269)
      ·
        refine ⟨15959108765277254762532851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42557623374072679366754269 15959108765277254762532851)
        ·
          refine ⟨23938663147915882143799277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15959108765277254762532851 23938663147915882143799277)
          ·
            refine ⟨8976998680468455803924729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23938663147915882143799277 8976998680468455803924729)
            ·
              refine ⟨6732749010351341852943547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8976998680468455803924729 6732749010351341852943547)
              ·
                refine ⟨10099123515527012779415321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6732749010351341852943547 10099123515527012779415321)
                ·
                  refine ⟨7574342636645259584561491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10099123515527012779415321 7574342636645259584561491)
                  ·
                    refine ⟨11361513954967889376842237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7574342636645259584561491 11361513954967889376842237)
                    ·
                      refine ⟨4260567733112958516315839, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11361513954967889376842237 4260567733112958516315839)
                      ·
                        rfl

theorem cell23_8297426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 3, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 3, 2, 1, 2, 1, 3].length) (baseStart_8297426 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8297426 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8297426 prefixEnd_8297426 := by exact prefixLift 8297426
  have htrace : WordTrace (prefixWord ++ tailWord_8297426) baseStart_8297426 baseEnd_8297426 := by
    simpa [prefixWord, tailWord_8297426, baseEnd_8297426] using wordTrace_append hprefix tailTrace_8297426
  have hstable : (prefixWord ++ tailWord_8297426).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8297426).length < 2 ^ (prefixWord ++ tailWord_8297426).sum := by decide
  have hdescent : baseEnd_8297426 < baseStart_8297426 := by decide
  rcases family_descends (prefixWord ++ tailWord_8297426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8297460 : List Nat := [2, 6, 2, 1, 1, 1, 2, 2, 2, 1, 3]
def baseStart_8297460 : Nat := 118140960795 + 8297460 * 2 ^ 59
def prefixEnd_8297460 : Nat := 4983230072969 + 3 ^ 40 * 8297460 * 2
def baseEnd_8297460 : Nat := 4260585191455211383290683

theorem tailTrace_8297460 : CollatzResearch.WordTrace tailWord_8297460 prefixEnd_8297460 4260585191455211383290683 := by
  unfold tailWord_8297460
  simp only [CollatzResearch.WordTrace]
  refine ⟨151316614259863494096272917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 201755485679817992128363889 151316614259863494096272917)
  ·
    refine ⟨7092966293431101285762793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 151316614259863494096272917 7092966293431101285762793)
    ·
      refine ⟨5319724720073325964322095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7092966293431101285762793 5319724720073325964322095)
      ·
        refine ⟨7979587080109988946483143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5319724720073325964322095 7979587080109988946483143)
        ·
          refine ⟨11969380620164983419724715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7979587080109988946483143 11969380620164983419724715)
          ·
            refine ⟨17954070930247475129587073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11969380620164983419724715 17954070930247475129587073)
            ·
              refine ⟨13465553197685606347190305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17954070930247475129587073 13465553197685606347190305)
              ·
                refine ⟨10099164898264204760392729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13465553197685606347190305 10099164898264204760392729)
                ·
                  refine ⟨7574373673698153570294547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10099164898264204760392729 7574373673698153570294547)
                  ·
                    refine ⟨11361560510547230355441821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7574373673698153570294547 11361560510547230355441821)
                    ·
                      refine ⟨4260585191455211383290683, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11361560510547230355441821 4260585191455211383290683)
                      ·
                        rfl

theorem cell23_8297460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 1, 1, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 1, 1, 2, 2, 2, 1, 3].length) (baseStart_8297460 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8297460 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8297460 prefixEnd_8297460 := by exact prefixLift 8297460
  have htrace : WordTrace (prefixWord ++ tailWord_8297460) baseStart_8297460 baseEnd_8297460 := by
    simpa [prefixWord, tailWord_8297460, baseEnd_8297460] using wordTrace_append hprefix tailTrace_8297460
  have hstable : (prefixWord ++ tailWord_8297460).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8297460).length < 2 ^ (prefixWord ++ tailWord_8297460).sum := by decide
  have hdescent : baseEnd_8297460 < baseStart_8297460 := by decide
  rcases family_descends (prefixWord ++ tailWord_8297460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8297505 : List Nat := [1, 2, 3, 2, 3, 2, 1, 1, 1, 3, 4]
def baseStart_8297505 : Nat := 118140960795 + 8297505 * 2 ^ 59
def prefixEnd_8297505 : Nat := 4983230072969 + 3 ^ 40 * 8297505 * 2
def baseEnd_8297505 : Nat := 4260608298084663707227975

theorem tailTrace_8297505 : CollatzResearch.WordTrace tailWord_8297505 prefixEnd_8297505 4260608298084663707227975 := by
  unfold tailWord_8297505
  simp only [CollatzResearch.WordTrace]
  refine ⟨302634869804563960877933969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201756579869709307251955979 302634869804563960877933969)
  ·
    refine ⟨226976152353422970658450477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 302634869804563960877933969 226976152353422970658450477)
    ·
      refine ⟨85116057132533613996918929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 226976152353422970658450477 85116057132533613996918929)
      ·
        refine ⟨63837042849400210497689197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85116057132533613996918929 63837042849400210497689197)
        ·
          refine ⟨23938891068525078936633449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 63837042849400210497689197 23938891068525078936633449)
          ·
            refine ⟨17954168301393809202475087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23938891068525078936633449 17954168301393809202475087)
            ·
              refine ⟨26931252452090713803712631, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17954168301393809202475087 26931252452090713803712631)
              ·
                refine ⟨40396878678136070705568947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26931252452090713803712631 40396878678136070705568947)
                ·
                  refine ⟨60595318017204106058353421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40396878678136070705568947 60595318017204106058353421)
                  ·
                    refine ⟨22723244256451539771882533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 60595318017204106058353421 22723244256451539771882533)
                    ·
                      refine ⟨4260608298084663707227975, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22723244256451539771882533 4260608298084663707227975)
                      ·
                        rfl

theorem cell23_8297505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 2, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 2, 1, 1, 1, 3, 4].length) (baseStart_8297505 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8297505 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8297505 prefixEnd_8297505 := by exact prefixLift 8297505
  have htrace : WordTrace (prefixWord ++ tailWord_8297505) baseStart_8297505 baseEnd_8297505 := by
    simpa [prefixWord, tailWord_8297505, baseEnd_8297505] using wordTrace_append hprefix tailTrace_8297505
  have hstable : (prefixWord ++ tailWord_8297505).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8297505).length < 2 ^ (prefixWord ++ tailWord_8297505).sum := by decide
  have hdescent : baseEnd_8297505 < baseStart_8297505 := by decide
  rcases family_descends (prefixWord ++ tailWord_8297505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8297525 : List Nat := [1, 3, 3, 1, 1, 1, 1, 3, 4, 2, 3]
def baseStart_8297525 : Nat := 118140960795 + 8297525 * 2 ^ 59
def prefixEnd_8297525 : Nat := 4983230072969 + 3 ^ 40 * 8297525 * 2
def baseEnd_8297525 : Nat := 4260618567697753628977883

theorem tailTrace_8297525 : CollatzResearch.WordTrace tailWord_8297525 prefixEnd_8297525 4260618567697753628977883 := by
  unfold tailWord_8297525
  simp only [CollatzResearch.WordTrace]
  refine ⟨302635599264491504293662029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201757066176327669529108019 302635599264491504293662029)
  ·
    refine ⟨113488349724184314110123261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 302635599264491504293662029 113488349724184314110123261)
    ·
      refine ⟨42558131146569117791296223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 113488349724184314110123261 42558131146569117791296223)
      ·
        refine ⟨63837196719853676686944335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42558131146569117791296223 63837196719853676686944335)
        ·
          refine ⟨95755795079780515030416503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63837196719853676686944335 95755795079780515030416503)
          ·
            refine ⟨143633692619670772545624755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 95755795079780515030416503 143633692619670772545624755)
            ·
              refine ⟨215450538929506158818437133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 143633692619670772545624755 215450538929506158818437133)
              ·
                refine ⟨80793952098564809556913925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 215450538929506158818437133 80793952098564809556913925)
                ·
                  refine ⟨15148866018480901791921361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 80793952098564809556913925 15148866018480901791921361)
                  ·
                    refine ⟨11361649513860676343941021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15148866018480901791921361 11361649513860676343941021)
                    ·
                      refine ⟨4260618567697753628977883, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11361649513860676343941021 4260618567697753628977883)
                      ·
                        rfl

theorem cell23_8297525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 1, 3, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 1, 3, 4, 2, 3].length) (baseStart_8297525 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8297525 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8297525 prefixEnd_8297525 := by exact prefixLift 8297525
  have htrace : WordTrace (prefixWord ++ tailWord_8297525) baseStart_8297525 baseEnd_8297525 := by
    simpa [prefixWord, tailWord_8297525, baseEnd_8297525] using wordTrace_append hprefix tailTrace_8297525
  have hstable : (prefixWord ++ tailWord_8297525).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8297525).length < 2 ^ (prefixWord ++ tailWord_8297525).sum := by decide
  have hdescent : baseEnd_8297525 < baseStart_8297525 := by decide
  rcases family_descends (prefixWord ++ tailWord_8297525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8297532 : List Nat := [2, 2, 2, 2, 2, 3, 2, 1, 3, 4]
def baseStart_8297532 : Nat := 118140960795 + 8297532 * 2 ^ 59
def prefixEnd_8297532 : Nat := 4983230072969 + 3 ^ 40 * 8297532 * 2
def baseEnd_8297532 : Nat := 1420207387354111700530117

theorem tailTrace_8297532 : CollatzResearch.WordTrace tailWord_8297532 prefixEnd_8297532 1420207387354111700530117 := by
  unfold tailWord_8297532
  simp only [CollatzResearch.WordTrace]
  refine ⟨151317927287733072244583425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 201757236383644096326111233 151317927287733072244583425)
  ·
    refine ⟨113488445465799804183437569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 151317927287733072244583425 113488445465799804183437569)
    ·
      refine ⟨85116334099349853137578177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 113488445465799804183437569 85116334099349853137578177)
      ·
        refine ⟨63837250574512389853183633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85116334099349853137578177 63837250574512389853183633)
        ·
          refine ⟨47877937930884292389887725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63837250574512389853183633 47877937930884292389887725)
          ·
            refine ⟨17954226724081609646207897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 47877937930884292389887725 17954226724081609646207897)
            ·
              refine ⟨13465670043061207234655923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17954226724081609646207897 13465670043061207234655923)
              ·
                refine ⟨20198505064591810851983885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13465670043061207234655923 20198505064591810851983885)
                ·
                  refine ⟨7574439399221929069493957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20198505064591810851983885 7574439399221929069493957)
                  ·
                    refine ⟨1420207387354111700530117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7574439399221929069493957 1420207387354111700530117)
                    ·
                      rfl

theorem cell23_8297532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 3, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 3, 2, 1, 3, 4].length) (baseStart_8297532 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8297532 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8297532 prefixEnd_8297532 := by exact prefixLift 8297532
  have htrace : WordTrace (prefixWord ++ tailWord_8297532) baseStart_8297532 baseEnd_8297532 := by
    simpa [prefixWord, tailWord_8297532, baseEnd_8297532] using wordTrace_append hprefix tailTrace_8297532
  have hstable : (prefixWord ++ tailWord_8297532).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8297532).length < 2 ^ (prefixWord ++ tailWord_8297532).sum := by decide
  have hdescent : baseEnd_8297532 < baseStart_8297532 := by decide
  rcases family_descends (prefixWord ++ tailWord_8297532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8297548 : List Nat := [2, 2, 1, 3, 1, 1, 1, 1, 3, 2, 6]
def baseStart_8297548 : Nat := 118140960795 + 8297548 * 2 ^ 59
def prefixEnd_8297548 : Nat := 4983230072969 + 3 ^ 40 * 8297548 * 2
def baseEnd_8297548 : Nat := 4260630377752807038990277

theorem tailTrace_8297548 : CollatzResearch.WordTrace tailWord_8297548 prefixEnd_8297548 4260630377752807038990277 := by
  unfold tailWord_8297548
  simp only [CollatzResearch.WordTrace]
  refine ⟨151318219071704089610874649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 201757625428938786147832865 151318219071704089610874649)
  ·
    refine ⟨113488664303778067208155987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 151318219071704089610874649 113488664303778067208155987)
    ·
      refine ⟨170232996455667100812233981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113488664303778067208155987 170232996455667100812233981)
      ·
        refine ⟨63837373670875162804587743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 170232996455667100812233981 63837373670875162804587743)
        ·
          refine ⟨95756060506312744206881615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63837373670875162804587743 95756060506312744206881615)
          ·
            refine ⟨143634090759469116310322423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 95756060506312744206881615 143634090759469116310322423)
            ·
              refine ⟨215451136139203674465483635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 143634090759469116310322423 215451136139203674465483635)
              ·
                refine ⟨323176704208805511698225453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 215451136139203674465483635 323176704208805511698225453)
                ·
                  refine ⟨121191264078302066886834545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 323176704208805511698225453 121191264078302066886834545)
                  ·
                    refine ⟨90893448058726550165125909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 121191264078302066886834545 90893448058726550165125909)
                    ·
                      refine ⟨4260630377752807038990277, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 90893448058726550165125909 4260630377752807038990277)
                      ·
                        rfl

theorem cell23_8297548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 1, 1, 3, 2, 6].length) (baseStart_8297548 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8297548 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8297548 prefixEnd_8297548 := by exact prefixLift 8297548
  have htrace : WordTrace (prefixWord ++ tailWord_8297548) baseStart_8297548 baseEnd_8297548 := by
    simpa [prefixWord, tailWord_8297548, baseEnd_8297548] using wordTrace_append hprefix tailTrace_8297548
  have hstable : (prefixWord ++ tailWord_8297548).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8297548).length < 2 ^ (prefixWord ++ tailWord_8297548).sum := by decide
  have hdescent : baseEnd_8297548 < baseStart_8297548 := by decide
  rcases family_descends (prefixWord ++ tailWord_8297548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8297629 : List Nat := [1, 4, 2, 1, 1, 2, 5, 1, 1, 1, 4]
def baseStart_8297629 : Nat := 118140960795 + 8297629 * 2 ^ 59
def prefixEnd_8297629 : Nat := 4983230072969 + 3 ^ 40 * 8297629 * 2
def baseEnd_8297629 : Nat := 4260671969685821222077405

theorem tailTrace_8297629 : CollatzResearch.WordTrace tailWord_8297629 prefixEnd_8297629 4260671969685821222077405 := by
  unfold tailWord_8297629
  simp only [CollatzResearch.WordTrace]
  refine ⟨302639392456114730055447941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201759594970743153370298627 302639392456114730055447941)
  ·
    refine ⟨56744886085521511885396489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 302639392456114730055447941 56744886085521511885396489)
    ·
      refine ⟨42558664564141133914047367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56744886085521511885396489 42558664564141133914047367)
      ·
        refine ⟨63837996846211700871071051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42558664564141133914047367 63837996846211700871071051)
        ·
          refine ⟨95756995269317551306606577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63837996846211700871071051 95756995269317551306606577)
          ·
            refine ⟨71817746451988163479954933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 95756995269317551306606577 71817746451988163479954933)
            ·
              refine ⟨6732913729873890326245775, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 71817746451988163479954933 6732913729873890326245775)
              ·
                refine ⟨10099370594810835489368663, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6732913729873890326245775 10099370594810835489368663)
                ·
                  refine ⟨15149055892216253234052995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10099370594810835489368663 15149055892216253234052995)
                  ·
                    refine ⟨22723583838324379851079493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15149055892216253234052995 22723583838324379851079493)
                    ·
                      refine ⟨4260671969685821222077405, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22723583838324379851079493 4260671969685821222077405)
                      ·
                        rfl

theorem cell23_8297629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 5, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 5, 1, 1, 1, 4].length) (baseStart_8297629 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8297629 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8297629 prefixEnd_8297629 := by exact prefixLift 8297629
  have htrace : WordTrace (prefixWord ++ tailWord_8297629) baseStart_8297629 baseEnd_8297629 := by
    simpa [prefixWord, tailWord_8297629, baseEnd_8297629] using wordTrace_append hprefix tailTrace_8297629
  have hstable : (prefixWord ++ tailWord_8297629).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8297629).length < 2 ^ (prefixWord ++ tailWord_8297629).sum := by decide
  have hdescent : baseEnd_8297629 < baseStart_8297629 := by decide
  rcases family_descends (prefixWord ++ tailWord_8297629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8297639 : List Nat := [1, 1, 6, 2, 1, 1, 1, 4, 2, 4]
def baseStart_8297639 : Nat := 118140960795 + 8297639 * 2 ^ 59
def prefixEnd_8297639 : Nat := 4983230072969 + 3 ^ 40 * 8297639 * 2
def baseEnd_8297639 : Nat := 1420225701497455394317453

theorem tailTrace_8297639 : CollatzResearch.WordTrace tailWord_8297639 prefixEnd_8297639 1420225701497455394317453 := by
  unfold tailWord_8297639
  simp only [CollatzResearch.WordTrace]
  refine ⟨302639757186078501763311971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201759838124052334508874647 302639757186078501763311971)
  ·
    refine ⟨453959635779117752644967957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 302639757186078501763311971 453959635779117752644967957)
    ·
      refine ⟨21279357927146144655232873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 453959635779117752644967957 21279357927146144655232873)
      ·
        refine ⟨15959518445359608491424655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21279357927146144655232873 15959518445359608491424655)
        ·
          refine ⟨23939277668039412737136983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15959518445359608491424655 23939277668039412737136983)
          ·
            refine ⟨35908916502059119105705475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23939277668039412737136983 35908916502059119105705475)
            ·
              refine ⟨53863374753088678658558213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35908916502059119105705475 53863374753088678658558213)
              ·
                refine ⟨10099382766204127248479665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 53863374753088678658558213 10099382766204127248479665)
                ·
                  refine ⟨7574537074653095436359749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10099382766204127248479665 7574537074653095436359749)
                  ·
                    refine ⟨1420225701497455394317453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7574537074653095436359749 1420225701497455394317453)
                    ·
                      rfl

theorem cell23_8297639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 1, 1, 4, 2, 4].length) (baseStart_8297639 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8297639 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8297639 prefixEnd_8297639 := by exact prefixLift 8297639
  have htrace : WordTrace (prefixWord ++ tailWord_8297639) baseStart_8297639 baseEnd_8297639 := by
    simpa [prefixWord, tailWord_8297639, baseEnd_8297639] using wordTrace_append hprefix tailTrace_8297639
  have hstable : (prefixWord ++ tailWord_8297639).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8297639).length < 2 ^ (prefixWord ++ tailWord_8297639).sum := by decide
  have hdescent : baseEnd_8297639 < baseStart_8297639 := by decide
  rcases family_descends (prefixWord ++ tailWord_8297639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8297695 : List Nat := [1, 1, 2, 3, 2, 1, 3, 2, 2, 6]
def baseStart_8297695 : Nat := 118140960795 + 8297695 * 2 ^ 59
def prefixEnd_8297695 : Nat := 4983230072969 + 3 ^ 40 * 8297695 * 2
def baseEnd_8297695 : Nat := 1420235286469672654617367

theorem tailTrace_8297695 : CollatzResearch.WordTrace tailWord_8297695 prefixEnd_8297695 1420235286469672654617367 := by
  unfold tailWord_8297695
  simp only [CollatzResearch.WordTrace]
  refine ⟨302641799673875623327350539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201761199782583748884900359 302641799673875623327350539)
  ·
    refine ⟨453962699510813434991025809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 302641799673875623327350539 453962699510813434991025809)
    ·
      refine ⟨340472024633110076243269357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 453962699510813434991025809 340472024633110076243269357)
      ·
        refine ⟨127677009237416278591226009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 340472024633110076243269357 127677009237416278591226009)
        ·
          refine ⟨95757756928062208943419507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 127677009237416278591226009 95757756928062208943419507)
          ·
            refine ⟨143636635392093313415129261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 95757756928062208943419507 143636635392093313415129261)
            ·
              refine ⟨53863738272034992530673473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 143636635392093313415129261 53863738272034992530673473)
              ·
                refine ⟨40397803704026244398005105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53863738272034992530673473 40397803704026244398005105)
                ·
                  refine ⟨30298352778019683298503829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40397803704026244398005105 30298352778019683298503829)
                  ·
                    refine ⟨1420235286469672654617367, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 30298352778019683298503829 1420235286469672654617367)
                    ·
                      rfl

theorem cell23_8297695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 3, 2, 2, 6].length) (baseStart_8297695 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8297695 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8297695 prefixEnd_8297695 := by exact prefixLift 8297695
  have htrace : WordTrace (prefixWord ++ tailWord_8297695) baseStart_8297695 baseEnd_8297695 := by
    simpa [prefixWord, tailWord_8297695, baseEnd_8297695] using wordTrace_append hprefix tailTrace_8297695
  have hstable : (prefixWord ++ tailWord_8297695).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8297695).length < 2 ^ (prefixWord ++ tailWord_8297695).sum := by decide
  have hdescent : baseEnd_8297695 < baseStart_8297695 := by decide
  rcases family_descends (prefixWord ++ tailWord_8297695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8297696 : List Nat := [2, 1, 1, 3, 1, 6, 1, 2, 2, 1, 3]
def baseStart_8297696 : Nat := 118140960795 + 8297696 * 2 ^ 59
def prefixEnd_8297696 : Nat := 4983230072969 + 3 ^ 40 * 8297696 * 2
def baseEnd_8297696 : Nat := 4260706372889672459939597

theorem tailTrace_8297696 : CollatzResearch.WordTrace tailWord_8297696 prefixEnd_8297696 4260706372889672459939597 := by
  unfold tailWord_8297696
  simp only [CollatzResearch.WordTrace]
  refine ⟨151320918073436000249068471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 201761224097914666998757961 151320918073436000249068471)
  ·
    refine ⟨226981377110154000373602707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151320918073436000249068471 226981377110154000373602707)
    ·
      refine ⟨340472065665231000560404061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 226981377110154000373602707 340472065665231000560404061)
      ·
        refine ⟨127677024624461625210151523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 340472065665231000560404061 127677024624461625210151523)
        ·
          refine ⟨191515536936692437815227285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 127677024624461625210151523 191515536936692437815227285)
          ·
            refine ⟨8977290793907458022588779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 191515536936692437815227285 8977290793907458022588779)
            ·
              refine ⟨13465936190861187033883169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8977290793907458022588779 13465936190861187033883169)
              ·
                refine ⟨10099452143145890275412377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13465936190861187033883169 10099452143145890275412377)
                ·
                  refine ⟨7574589107359417706559283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10099452143145890275412377 7574589107359417706559283)
                  ·
                    refine ⟨11361883661039126559838925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7574589107359417706559283 11361883661039126559838925)
                    ·
                      refine ⟨4260706372889672459939597, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11361883661039126559838925 4260706372889672459939597)
                      ·
                        rfl

theorem cell23_8297696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 6, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 6, 1, 2, 2, 1, 3].length) (baseStart_8297696 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8297696 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8297696 prefixEnd_8297696 := by exact prefixLift 8297696
  have htrace : WordTrace (prefixWord ++ tailWord_8297696) baseStart_8297696 baseEnd_8297696 := by
    simpa [prefixWord, tailWord_8297696, baseEnd_8297696] using wordTrace_append hprefix tailTrace_8297696
  have hstable : (prefixWord ++ tailWord_8297696).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8297696).length < 2 ^ (prefixWord ++ tailWord_8297696).sum := by decide
  have hdescent : baseEnd_8297696 < baseStart_8297696 := by decide
  rcases family_descends (prefixWord ++ tailWord_8297696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8297759 : List Nat := [1, 1, 2, 4, 4, 2, 1, 1, 7]
def baseStart_8297759 : Nat := 118140960795 + 8297759 * 2 ^ 59
def prefixEnd_8297759 : Nat := 4983230072969 + 3 ^ 40 * 8297759 * 2
def baseEnd_8297759 : Nat := 473415413574545079272423

theorem tailTrace_8297759 : CollatzResearch.WordTrace tailWord_8297759 prefixEnd_8297759 473415413574545079272423 := by
  unfold tailWord_8297759
  simp only [CollatzResearch.WordTrace]
  refine ⟨302644133945643762257680331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201762755963762508171786887 302644133945643762257680331)
  ·
    refine ⟨453966200918465643386520497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 302644133945643762257680331 453966200918465643386520497)
    ·
      refine ⟨340474650688849232539890373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 453966200918465643386520497 340474650688849232539890373)
      ·
        refine ⟨63838997004159231101229445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 340474650688849232539890373 63838997004159231101229445)
        ·
          refine ⟨11969811938279855831480521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 63838997004159231101229445 11969811938279855831480521)
          ·
            refine ⟨8977358953709891873610391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11969811938279855831480521 8977358953709891873610391)
            ·
              refine ⟨13466038430564837810415587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8977358953709891873610391 13466038430564837810415587)
              ·
                refine ⟨20199057645847256715623381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13466038430564837810415587 20199057645847256715623381)
                ·
                  refine ⟨473415413574545079272423, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 20199057645847256715623381 473415413574545079272423)
                  ·
                    rfl

theorem cell23_8297759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 4, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 4, 2, 1, 1, 7].length) (baseStart_8297759 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8297759 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8297759 prefixEnd_8297759 := by exact prefixLift 8297759
  have htrace : WordTrace (prefixWord ++ tailWord_8297759) baseStart_8297759 baseEnd_8297759 := by
    simpa [prefixWord, tailWord_8297759, baseEnd_8297759] using wordTrace_append hprefix tailTrace_8297759
  have hstable : (prefixWord ++ tailWord_8297759).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8297759).length < 2 ^ (prefixWord ++ tailWord_8297759).sum := by decide
  have hdescent : baseEnd_8297759 < baseStart_8297759 := by decide
  rcases family_descends (prefixWord ++ tailWord_8297759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8297770 : List Nat := [3, 1, 4, 2, 1, 1, 4, 1, 2, 2, 2]
def baseStart_8297770 : Nat := 118140960795 + 8297770 * 2 ^ 59
def prefixEnd_8297770 : Nat := 4983230072969 + 3 ^ 40 * 8297770 * 2
def baseEnd_8297770 : Nat := 4260744370458105170414257

theorem tailTrace_8297770 : CollatzResearch.WordTrace tailWord_8297770 prefixEnd_8297770 4260744370458105170414257 := by
  unfold tailWord_8297770
  simp only [CollatzResearch.WordTrace]
  refine ⟨75661133787150977784082691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 201763023432402607424220509 75661133787150977784082691)
  ·
    refine ⟨113491700680726466676124037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75661133787150977784082691 113491700680726466676124037)
    ·
      refine ⟨21279693877636212501773257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 113491700680726466676124037 21279693877636212501773257)
      ·
        refine ⟨15959770408227159376329943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21279693877636212501773257 15959770408227159376329943)
        ·
          refine ⟨23939655612340739064494915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15959770408227159376329943 23939655612340739064494915)
          ·
            refine ⟨35909483418511108596742373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23939655612340739064494915 35909483418511108596742373)
            ·
              refine ⟨6733028140970832861889195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 35909483418511108596742373 6733028140970832861889195)
              ·
                refine ⟨10099542211456249292833793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6733028140970832861889195 10099542211456249292833793)
                ·
                  refine ⟨7574656658592186969625345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10099542211456249292833793 7574656658592186969625345)
                  ·
                    refine ⟨5680992493944140227219009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7574656658592186969625345 5680992493944140227219009)
                    ·
                      refine ⟨4260744370458105170414257, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5680992493944140227219009 4260744370458105170414257)
                      ·
                        rfl

theorem cell23_8297770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 1, 4, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 1, 4, 1, 2, 2, 2].length) (baseStart_8297770 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8297770 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8297770 prefixEnd_8297770 := by exact prefixLift 8297770
  have htrace : WordTrace (prefixWord ++ tailWord_8297770) baseStart_8297770 baseEnd_8297770 := by
    simpa [prefixWord, tailWord_8297770, baseEnd_8297770] using wordTrace_append hprefix tailTrace_8297770
  have hstable : (prefixWord ++ tailWord_8297770).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8297770).length < 2 ^ (prefixWord ++ tailWord_8297770).sum := by decide
  have hdescent : baseEnd_8297770 < baseStart_8297770 := by decide
  rcases family_descends (prefixWord ++ tailWord_8297770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8297809 : List Nat := [1, 2, 2, 1, 4, 1, 2, 2, 2, 4, 2]
def baseStart_8297809 : Nat := 118140960795 + 8297809 * 2 ^ 59
def prefixEnd_8297809 : Nat := 4983230072969 + 3 ^ 40 * 8297809 * 2
def baseEnd_8297809 : Nat := 4260764396203630517826577

theorem tailTrace_8297809 : CollatzResearch.WordTrace tailWord_8297809 prefixEnd_8297809 4260764396203630517826577 := by
  unfold tailWord_8297809
  simp only [CollatzResearch.WordTrace]
  refine ⟨302645957595462620797000481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201763971730308413864666987 302645957595462620797000481)
  ·
    refine ⟨226984468196596965597750361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 302645957595462620797000481 226984468196596965597750361)
    ·
      refine ⟨170238351147447724198312771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 226984468196596965597750361 170238351147447724198312771)
      ·
        refine ⟨255357526721171586297469157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 170238351147447724198312771 255357526721171586297469157)
        ·
          refine ⟨47879536260219672430775467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 255357526721171586297469157 47879536260219672430775467)
          ·
            refine ⟨71819304390329508646163201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47879536260219672430775467 71819304390329508646163201)
            ·
              refine ⟨53864478292747131484622401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 71819304390329508646163201 53864478292747131484622401)
              ·
                refine ⟨40398358719560348613466801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53864478292747131484622401 40398358719560348613466801)
                ·
                  refine ⟨30298769039670261460100101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40398358719560348613466801 30298769039670261460100101)
                  ·
                    refine ⟨5681019194938174023768769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 30298769039670261460100101 5681019194938174023768769)
                    ·
                      refine ⟨4260764396203630517826577, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5681019194938174023768769 4260764396203630517826577)
                      ·
                        rfl

theorem cell23_8297809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 2, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 2, 2, 2, 4, 2].length) (baseStart_8297809 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8297809 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8297809 prefixEnd_8297809 := by exact prefixLift 8297809
  have htrace : WordTrace (prefixWord ++ tailWord_8297809) baseStart_8297809 baseEnd_8297809 := by
    simpa [prefixWord, tailWord_8297809, baseEnd_8297809] using wordTrace_append hprefix tailTrace_8297809
  have hstable : (prefixWord ++ tailWord_8297809).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8297809).length < 2 ^ (prefixWord ++ tailWord_8297809).sum := by decide
  have hdescent : baseEnd_8297809 < baseStart_8297809 := by decide
  rcases family_descends (prefixWord ++ tailWord_8297809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8297812 : List Nat := [2, 4, 1, 1, 2, 1, 1, 1, 2, 3, 5]
def baseStart_8297812 : Nat := 118140960795 + 8297812 * 2 ^ 59
def prefixEnd_8297812 : Nat := 4983230072969 + 3 ^ 40 * 8297812 * 2
def baseEnd_8297812 : Nat := 4260765936645594006089063

theorem tailTrace_8297812 : CollatzResearch.WordTrace tailWord_8297812 prefixEnd_8297812 4260765936645594006089063 := by
  unfold tailWord_8297812
  simp only [CollatzResearch.WordTrace]
  refine ⟨151323033507225876154679845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 201764044676301168206239793 151323033507225876154679845)
  ·
    refine ⟨28373068782604851779002471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 151323033507225876154679845 28373068782604851779002471)
    ·
      refine ⟨42559603173907277668503707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28373068782604851779002471 42559603173907277668503707)
      ·
        refine ⟨63839404760860916502755561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42559603173907277668503707 63839404760860916502755561)
        ·
          refine ⟨47879553570645687377066671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63839404760860916502755561 47879553570645687377066671)
          ·
            refine ⟨71819330355968531065600007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47879553570645687377066671 71819330355968531065600007)
            ·
              refine ⟨107728995533952796598400011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71819330355968531065600007 107728995533952796598400011)
              ·
                refine ⟨161593493300929194897600017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 107728995533952796598400011 161593493300929194897600017)
                ·
                  refine ⟨121195119975696896173200013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 161593493300929194897600017 121195119975696896173200013)
                  ·
                    refine ⟨45448169990886336064950005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 121195119975696896173200013 45448169990886336064950005)
                    ·
                      refine ⟨4260765936645594006089063, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 45448169990886336064950005 4260765936645594006089063)
                      ·
                        rfl

theorem cell23_8297812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 1, 1, 2, 3, 5].length) (baseStart_8297812 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8297812 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8297812 prefixEnd_8297812 := by exact prefixLift 8297812
  have htrace : WordTrace (prefixWord ++ tailWord_8297812) baseStart_8297812 baseEnd_8297812 := by
    simpa [prefixWord, tailWord_8297812, baseEnd_8297812] using wordTrace_append hprefix tailTrace_8297812
  have hstable : (prefixWord ++ tailWord_8297812).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8297812).length < 2 ^ (prefixWord ++ tailWord_8297812).sum := by decide
  have hdescent : baseEnd_8297812 < baseStart_8297812 := by decide
  rcases family_descends (prefixWord ++ tailWord_8297812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8297826 : List Nat := [3, 3, 2, 1, 1, 1, 3, 1, 2, 4, 2]
def baseStart_8297826 : Nat := 118140960795 + 8297826 * 2 ^ 59
def prefixEnd_8297826 : Nat := 4983230072969 + 3 ^ 40 * 8297826 * 2
def baseEnd_8297826 : Nat := 4260773125374756951313999

theorem tailTrace_8297826 : CollatzResearch.WordTrace tailWord_8297826 prefixEnd_8297826 4260773125374756951313999 := by
  unfold tailWord_8297826
  simp only [CollatzResearch.WordTrace]
  refine ⟨75661644409100258175092333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 201764385090934021800246221 75661644409100258175092333)
  ·
    refine ⟨28373116653412596815659625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 75661644409100258175092333 28373116653412596815659625)
    ·
      refine ⟨21279837490059447611744719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28373116653412596815659625 21279837490059447611744719)
      ·
        refine ⟨31919756235089171417617079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21279837490059447611744719 31919756235089171417617079)
        ·
          refine ⟨47879634352633757126425619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31919756235089171417617079 47879634352633757126425619)
          ·
            refine ⟨71819451528950635689638429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47879634352633757126425619 71819451528950635689638429)
            ·
              refine ⟨26932294323356488383614411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 71819451528950635689638429 26932294323356488383614411)
              ·
                refine ⟨40398441485034732575421617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26932294323356488383614411 40398441485034732575421617)
                ·
                  refine ⟨30298831113776049431566213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40398441485034732575421617 30298831113776049431566213)
                  ·
                    refine ⟨5681030833833009268418665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 30298831113776049431566213 5681030833833009268418665)
                    ·
                      refine ⟨4260773125374756951313999, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5681030833833009268418665 4260773125374756951313999)
                      ·
                        rfl

theorem cell23_8297826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 3, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 3, 1, 2, 4, 2].length) (baseStart_8297826 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8297826 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8297826 prefixEnd_8297826 := by exact prefixLift 8297826
  have htrace : WordTrace (prefixWord ++ tailWord_8297826) baseStart_8297826 baseEnd_8297826 := by
    simpa [prefixWord, tailWord_8297826, baseEnd_8297826] using wordTrace_append hprefix tailTrace_8297826
  have hstable : (prefixWord ++ tailWord_8297826).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8297826).length < 2 ^ (prefixWord ++ tailWord_8297826).sum := by decide
  have hdescent : baseEnd_8297826 < baseStart_8297826 := by decide
  rcases family_descends (prefixWord ++ tailWord_8297826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8297952 : List Nat := [2, 1, 1, 3, 1, 1, 2, 1, 4, 7]
def baseStart_8297952 : Nat := 118140960795 + 8297952 * 2 ^ 59
def prefixEnd_8297952 : Nat := 4983230072969 + 3 ^ 40 * 8297952 * 2
def baseEnd_8297952 : Nat := 1420279274645741152779473

theorem tailTrace_8297952 : CollatzResearch.WordTrace tailWord_8297952 prefixEnd_8297952 1420279274645741152779473 := by
  unfold tailWord_8297952
  simp only [CollatzResearch.WordTrace]
  refine ⟨151325586616972278109728055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 201767448822629704146304073 151325586616972278109728055)
  ·
    refine ⟨226988379925458417164592083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151325586616972278109728055 226988379925458417164592083)
    ·
      refine ⟨340482569888187625746888125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 226988379925458417164592083 340482569888187625746888125)
      ·
        refine ⟨127680963708070359655083047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 340482569888187625746888125 127680963708070359655083047)
        ·
          refine ⟨191521445562105539482624571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 127680963708070359655083047 191521445562105539482624571)
          ·
            refine ⟨287282168343158309223936857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 191521445562105539482624571 287282168343158309223936857)
            ·
              refine ⟨215461626257368731917952643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 287282168343158309223936857 215461626257368731917952643)
              ·
                refine ⟨323192439386053097876928965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 215461626257368731917952643 323192439386053097876928965)
                ·
                  refine ⟨60598582384884955851924181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 323192439386053097876928965 60598582384884955851924181)
                  ·
                    refine ⟨1420279274645741152779473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 60598582384884955851924181 1420279274645741152779473)
                    ·
                      rfl

theorem cell23_8297952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 2, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 2, 1, 4, 7].length) (baseStart_8297952 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8297952 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8297952 prefixEnd_8297952 := by exact prefixLift 8297952
  have htrace : WordTrace (prefixWord ++ tailWord_8297952) baseStart_8297952 baseEnd_8297952 := by
    simpa [prefixWord, tailWord_8297952, baseEnd_8297952] using wordTrace_append hprefix tailTrace_8297952
  have hstable : (prefixWord ++ tailWord_8297952).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8297952).length < 2 ^ (prefixWord ++ tailWord_8297952).sum := by decide
  have hdescent : baseEnd_8297952 < baseStart_8297952 := by decide
  rcases family_descends (prefixWord ++ tailWord_8297952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8297953 : List Nat := [1, 2, 3, 1, 2, 5, 1, 2, 1, 2, 3]
def baseStart_8297953 : Nat := 118140960795 + 8297953 * 2 ^ 59
def prefixEnd_8297953 : Nat := 4983230072969 + 3 ^ 40 * 8297953 * 2
def baseEnd_8297953 : Nat := 4260838337417877954425915

theorem tailTrace_8297953 : CollatzResearch.WordTrace tailWord_8297953 prefixEnd_8297953 4260838337417877954425915 := by
  unfold tailWord_8297953
  simp only [CollatzResearch.WordTrace]
  refine ⟨302651209706940933390242513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201767473137960622260161675 302651209706940933390242513)
  ·
    refine ⟨226988407280205700042681885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 302651209706940933390242513 226988407280205700042681885)
    ·
      refine ⟨85120652730077137516005707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 226988407280205700042681885 85120652730077137516005707)
      ·
        refine ⟨127680979095115706274008561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85120652730077137516005707 127680979095115706274008561)
        ·
          refine ⟨95760734321336779705506421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 127680979095115706274008561 95760734321336779705506421)
          ·
            refine ⟨8977568842625323097391227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 95760734321336779705506421 8977568842625323097391227)
            ·
              refine ⟨13466353263937984646086841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8977568842625323097391227 13466353263937984646086841)
              ·
                refine ⟨10099764947953488484565131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13466353263937984646086841 10099764947953488484565131)
                ·
                  refine ⟨15149647421930232726847697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10099764947953488484565131 15149647421930232726847697)
                  ·
                    refine ⟨11362235566447674545135773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15149647421930232726847697 11362235566447674545135773)
                    ·
                      refine ⟨4260838337417877954425915, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11362235566447674545135773 4260838337417877954425915)
                      ·
                        rfl

theorem cell23_8297953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 5, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 5, 1, 2, 1, 2, 3].length) (baseStart_8297953 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8297953 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8297953 prefixEnd_8297953 := by exact prefixLift 8297953
  have htrace : WordTrace (prefixWord ++ tailWord_8297953) baseStart_8297953 baseEnd_8297953 := by
    simpa [prefixWord, tailWord_8297953, baseEnd_8297953] using wordTrace_append hprefix tailTrace_8297953
  have hstable : (prefixWord ++ tailWord_8297953).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8297953).length < 2 ^ (prefixWord ++ tailWord_8297953).sum := by decide
  have hdescent : baseEnd_8297953 < baseStart_8297953 := by decide
  rcases family_descends (prefixWord ++ tailWord_8297953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8297966 : List Nat := [4, 1, 2, 1, 2, 1, 3, 2, 1, 3, 3]
def baseStart_8297966 : Nat := 118140960795 + 8297966 * 2 ^ 59
def prefixEnd_8297966 : Nat := 4983230072969 + 3 ^ 40 * 8297966 * 2
def baseEnd_8297966 : Nat := 4260845012666386403563355

theorem tailTrace_8297966 : CollatzResearch.WordTrace tailWord_8297966 prefixEnd_8297966 4260845012666386403563355 := by
  unfold tailWord_8297966
  simp only [CollatzResearch.WordTrace]
  refine ⟨37831460481986729576308219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 201767789237262557740310501 37831460481986729576308219)
  ·
    refine ⟨56747190722980094364462329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37831460481986729576308219 56747190722980094364462329)
    ·
      refine ⟨42560393042235070773346747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56747190722980094364462329 42560393042235070773346747)
      ·
        refine ⟨63840589563352606160020121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42560393042235070773346747 63840589563352606160020121)
        ·
          refine ⟨47880442172514454620015091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63840589563352606160020121 47880442172514454620015091)
          ·
            refine ⟨71820663258771681930022637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47880442172514454620015091 71820663258771681930022637)
            ·
              refine ⟨26932748722039380723758489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 71820663258771681930022637 26932748722039380723758489)
              ·
                refine ⟨20199561541529535542818867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26932748722039380723758489 20199561541529535542818867)
                ·
                  refine ⟨30299342312294303314228301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20199561541529535542818867 30299342312294303314228301)
                  ·
                    refine ⟨11362253367110363742835613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 30299342312294303314228301 11362253367110363742835613)
                    ·
                      refine ⟨4260845012666386403563355, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11362253367110363742835613 4260845012666386403563355)
                      ·
                        rfl

theorem cell23_8297966_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 3, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 3, 2, 1, 3, 3].length) (baseStart_8297966 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8297966 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8297966 prefixEnd_8297966 := by exact prefixLift 8297966
  have htrace : WordTrace (prefixWord ++ tailWord_8297966) baseStart_8297966 baseEnd_8297966 := by
    simpa [prefixWord, tailWord_8297966, baseEnd_8297966] using wordTrace_append hprefix tailTrace_8297966
  have hstable : (prefixWord ++ tailWord_8297966).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8297966).length < 2 ^ (prefixWord ++ tailWord_8297966).sum := by decide
  have hdescent : baseEnd_8297966 < baseStart_8297966 := by decide
  rcases family_descends (prefixWord ++ tailWord_8297966) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8297970 : List Nat := [3, 2, 1, 4, 1, 2, 3, 1, 1, 2, 3]
def baseStart_8297970 : Nat := 118140960795 + 8297970 * 2 ^ 59
def prefixEnd_8297970 : Nat := 4983230072969 + 3 ^ 40 * 8297970 * 2
def baseEnd_8297970 : Nat := 4260847066589004387913337

theorem tailTrace_8297970 : CollatzResearch.WordTrace tailWord_8297970 prefixEnd_8297970 4260847066589004387913337 := by
  unfold tailWord_8297970
  simp only [CollatzResearch.WordTrace]
  refine ⟨75662957436969836323402841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 201767886498586230195740909 75662957436969836323402841)
  ·
    refine ⟨56747218077727377242552131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75662957436969836323402841 56747218077727377242552131)
    ·
      refine ⟨85120827116591065863828197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56747218077727377242552131 85120827116591065863828197)
      ·
        refine ⟨15960155084360824849467787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 85120827116591065863828197 15960155084360824849467787)
        ·
          refine ⟨23940232626541237274201681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15960155084360824849467787 23940232626541237274201681)
          ·
            refine ⟨17955174469905927955651261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23940232626541237274201681 17955174469905927955651261)
            ·
              refine ⟨6733190426214722983369223, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17955174469905927955651261 6733190426214722983369223)
              ·
                refine ⟨10099785639322084475053835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6733190426214722983369223 10099785639322084475053835)
                ·
                  refine ⟨15149678458983126712580753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10099785639322084475053835 15149678458983126712580753)
                  ·
                    refine ⟨11362258844237345034435565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15149678458983126712580753 11362258844237345034435565)
                    ·
                      refine ⟨4260847066589004387913337, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11362258844237345034435565 4260847066589004387913337)
                      ·
                        rfl

theorem cell23_8297970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 2, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 2, 3, 1, 1, 2, 3].length) (baseStart_8297970 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8297970 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8297970 prefixEnd_8297970 := by exact prefixLift 8297970
  have htrace : WordTrace (prefixWord ++ tailWord_8297970) baseStart_8297970 baseEnd_8297970 := by
    simpa [prefixWord, tailWord_8297970, baseEnd_8297970] using wordTrace_append hprefix tailTrace_8297970
  have hstable : (prefixWord ++ tailWord_8297970).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8297970).length < 2 ^ (prefixWord ++ tailWord_8297970).sum := by decide
  have hdescent : baseEnd_8297970 < baseStart_8297970 := by decide
  rcases family_descends (prefixWord ++ tailWord_8297970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8297986 : List Nat := [3, 4, 1, 2, 1, 1, 1, 1, 2, 7]
def baseStart_8297986 : Nat := 118140960795 + 8297986 * 2 ^ 59
def prefixEnd_8297986 : Nat := 4983230072969 + 3 ^ 40 * 8297986 * 2
def baseEnd_8297986 : Nat := 1420285094093158775104421

theorem tailTrace_8297986 : CollatzResearch.WordTrace tailWord_8297986 prefixEnd_8297986 1420285094093158775104421 := by
  unfold tailWord_8297986
  simp only [CollatzResearch.WordTrace]
  refine ⟨75663103328955345006548453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 201768275543880920017462541 75663103328955345006548453)
  ·
    refine ⟨14186831874179127188727835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 75663103328955345006548453 14186831874179127188727835)
    ·
      refine ⟨21280247811268690783091753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14186831874179127188727835 21280247811268690783091753)
      ·
        refine ⟨15960185858451518087318815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21280247811268690783091753 15960185858451518087318815)
        ·
          refine ⟨23940278787677277130978223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15960185858451518087318815 23940278787677277130978223)
          ·
            refine ⟨35910418181515915696467335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23940278787677277130978223 35910418181515915696467335)
            ·
              refine ⟨53865627272273873544701003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35910418181515915696467335 53865627272273873544701003)
              ·
                refine ⟨80798440908410810317051505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53865627272273873544701003 80798440908410810317051505)
                ·
                  refine ⟨60598830681308107737788629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 80798440908410810317051505 60598830681308107737788629)
                  ·
                    refine ⟨1420285094093158775104421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 60598830681308107737788629 1420285094093158775104421)
                    ·
                      rfl

theorem cell23_8297986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 1, 1, 1, 2, 7].length) (baseStart_8297986 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8297986 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8297986 prefixEnd_8297986 := by exact prefixLift 8297986
  have htrace : WordTrace (prefixWord ++ tailWord_8297986) baseStart_8297986 baseEnd_8297986 := by
    simpa [prefixWord, tailWord_8297986, baseEnd_8297986] using wordTrace_append hprefix tailTrace_8297986
  have hstable : (prefixWord ++ tailWord_8297986).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8297986).length < 2 ^ (prefixWord ++ tailWord_8297986).sum := by decide
  have hdescent : baseEnd_8297986 < baseStart_8297986 := by decide
  rcases family_descends (prefixWord ++ tailWord_8297986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8298040 : List Nat := [2, 1, 2, 1, 4, 2, 3, 2, 2, 2, 2]
def baseStart_8298040 : Nat := 118140960795 + 8298040 * 2 ^ 59
def prefixEnd_8298040 : Nat := 4983230072969 + 3 ^ 40 * 8298040 * 2
def baseEnd_8298040 : Nat := 4260883010234819114038015

theorem tailTrace_8298040 : CollatzResearch.WordTrace tailWord_8298040 prefixEnd_8298040 4260883010234819114038015 := by
  unfold tailWord_8298040
  simp only [CollatzResearch.WordTrace]
  refine ⟨151327191428812873624329787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 201769588571750498165773049 151327191428812873624329787)
  ·
    refine ⟨226990787143219310436494681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151327191428812873624329787 226990787143219310436494681)
    ·
      refine ⟨170243090357414482827371011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 226990787143219310436494681 170243090357414482827371011)
      ·
        refine ⟨255364635536121724241056517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 170243090357414482827371011 255364635536121724241056517)
        ·
          refine ⟨47880869163022823295198097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 255364635536121724241056517 47880869163022823295198097)
          ·
            refine ⟨35910651872267117471398573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47880869163022823295198097 35910651872267117471398573)
            ·
              refine ⟨13466494452100169051774465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35910651872267117471398573 13466494452100169051774465)
              ·
                refine ⟨10099870839075126788830849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13466494452100169051774465 10099870839075126788830849)
                ·
                  refine ⟨7574903129306345091623137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10099870839075126788830849 7574903129306345091623137)
                  ·
                    refine ⟨5681177346979758818717353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7574903129306345091623137 5681177346979758818717353)
                    ·
                      refine ⟨4260883010234819114038015, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5681177346979758818717353 4260883010234819114038015)
                      ·
                        rfl

theorem cell23_8298040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 2, 3, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 2, 3, 2, 2, 2, 2].length) (baseStart_8298040 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8298040 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8298040 prefixEnd_8298040 := by exact prefixLift 8298040
  have htrace : WordTrace (prefixWord ++ tailWord_8298040) baseStart_8298040 baseEnd_8298040 := by
    simpa [prefixWord, tailWord_8298040, baseEnd_8298040] using wordTrace_append hprefix tailTrace_8298040
  have hstable : (prefixWord ++ tailWord_8298040).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8298040).length < 2 ^ (prefixWord ++ tailWord_8298040).sum := by decide
  have hdescent : baseEnd_8298040 < baseStart_8298040 := by decide
  rcases family_descends (prefixWord ++ tailWord_8298040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8298069 : List Nat := [1, 3, 2, 2, 1, 1, 1, 2, 3, 2, 5]
def baseStart_8298069 : Nat := 118140960795 + 8298069 * 2 ^ 59
def prefixEnd_8298069 : Nat := 4983230072969 + 3 ^ 40 * 8298069 * 2
def baseEnd_8298069 : Nat := 4260897901173799500575381

theorem tailTrace_8298069 : CollatzResearch.WordTrace tailWord_8298069 prefixEnd_8298069 4260897901173799500575381 := by
  unfold tailWord_8298069
  simp only [CollatzResearch.WordTrace]
  refine ⟨302655440574520685201465261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201770293716347123467643507 302655440574520685201465261)
  ·
    refine ⟨113495790215445256950549473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 302655440574520685201465261 113495790215445256950549473)
    ·
      refine ⟨85121842661583942712912105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 113495790215445256950549473 85121842661583942712912105)
      ·
        refine ⟨63841381996187957034684079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85121842661583942712912105 63841381996187957034684079)
        ·
          refine ⟨95762072994281935552026119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63841381996187957034684079 95762072994281935552026119)
          ·
            refine ⟨143643109491422903328039179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 95762072994281935552026119 143643109491422903328039179)
            ·
              refine ⟨215464664237134354992058769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 143643109491422903328039179 215464664237134354992058769)
              ·
                refine ⟨161598498177850766244044077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 215464664237134354992058769 161598498177850766244044077)
                ·
                  refine ⟨60599436816694037341516529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 161598498177850766244044077 60599436816694037341516529)
                  ·
                    refine ⟨45449577612520528006137397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 60599436816694037341516529 45449577612520528006137397)
                    ·
                      refine ⟨4260897901173799500575381, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 45449577612520528006137397 4260897901173799500575381)
                      ·
                        rfl

theorem cell23_8298069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 1, 2, 3, 2, 5].length) (baseStart_8298069 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8298069 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8298069 prefixEnd_8298069 := by exact prefixLift 8298069
  have htrace : WordTrace (prefixWord ++ tailWord_8298069) baseStart_8298069 baseEnd_8298069 := by
    simpa [prefixWord, tailWord_8298069, baseEnd_8298069] using wordTrace_append hprefix tailTrace_8298069
  have hstable : (prefixWord ++ tailWord_8298069).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8298069).length < 2 ^ (prefixWord ++ tailWord_8298069).sum := by decide
  have hdescent : baseEnd_8298069 < baseStart_8298069 := by decide
  rcases family_descends (prefixWord ++ tailWord_8298069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8298076 : List Nat := [2, 2, 4, 1, 2, 1, 2, 1, 1, 7]
def baseStart_8298076 : Nat := 118140960795 + 8298076 * 2 ^ 59
def prefixEnd_8298076 : Nat := 4983230072969 + 3 ^ 40 * 8298076 * 2
def baseEnd_8298076 : Nat := 1420300498512793657729283

theorem tailTrace_8298076 : CollatzResearch.WordTrace tailWord_8298076 prefixEnd_8298076 1420300498512793657729283 := by
  unfold tailWord_8298076
  simp only [CollatzResearch.WordTrace]
  refine ⟨151327847942747662698485041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 201770463923663550264646721 151327847942747662698485041)
  ·
    refine ⟨113495885957060747023863781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 151327847942747662698485041 113495885957060747023863781)
    ·
      refine ⟨21280478616948890066974459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 113495885957060747023863781 21280478616948890066974459)
      ·
        refine ⟨31920717925423335100461689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21280478616948890066974459 31920717925423335100461689)
        ·
          refine ⟨23940538444067501325346267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31920717925423335100461689 23940538444067501325346267)
          ·
            refine ⟨35910807666101251988019401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23940538444067501325346267 35910807666101251988019401)
            ·
              refine ⟨26933105749575938991014551, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35910807666101251988019401 26933105749575938991014551)
              ·
                refine ⟨40399658624363908486521827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26933105749575938991014551 40399658624363908486521827)
                ·
                  refine ⟨60599487936545862729782741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40399658624363908486521827 60599487936545862729782741)
                  ·
                    refine ⟨1420300498512793657729283, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 60599487936545862729782741 1420300498512793657729283)
                    ·
                      rfl

theorem cell23_8298076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 1, 2, 1, 1, 7].length) (baseStart_8298076 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8298076 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8298076 prefixEnd_8298076 := by exact prefixLift 8298076
  have htrace : WordTrace (prefixWord ++ tailWord_8298076) baseStart_8298076 baseEnd_8298076 := by
    simpa [prefixWord, tailWord_8298076, baseEnd_8298076] using wordTrace_append hprefix tailTrace_8298076
  have hstable : (prefixWord ++ tailWord_8298076).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8298076).length < 2 ^ (prefixWord ++ tailWord_8298076).sum := by decide
  have hdescent : baseEnd_8298076 < baseStart_8298076 := by decide
  rcases family_descends (prefixWord ++ tailWord_8298076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8298093 : List Nat := [1, 5, 1, 1, 4, 1, 1, 2, 2, 5]
def baseStart_8298093 : Nat := 118140960795 + 8298093 * 2 ^ 59
def prefixEnd_8298093 : Nat := 4983230072969 + 3 ^ 40 * 8298093 * 2
def baseEnd_8298093 : Nat := 1420303408236502468891757

theorem tailTrace_8298093 : CollatzResearch.WordTrace tailWord_8298093 prefixEnd_8298093 1420303408236502468891757 := by
  unfold tailWord_8298093
  simp only [CollatzResearch.WordTrace]
  refine ⟨302656315926433737300338933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201770877284289158200225955 302656315926433737300338933)
  ·
    refine ⟨28374029618103162871906775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 302656315926433737300338933 28374029618103162871906775)
    ·
      refine ⟨42561044427154744307860163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28374029618103162871906775 42561044427154744307860163)
      ·
        refine ⟨63841566640732116461790245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42561044427154744307860163 63841566640732116461790245)
        ·
          refine ⟨11970293745137271836585671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 63841566640732116461790245 11970293745137271836585671)
          ·
            refine ⟨17955440617705907754878507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11970293745137271836585671 17955440617705907754878507)
            ·
              refine ⟨26933160926558861632317761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17955440617705907754878507 26933160926558861632317761)
              ·
                refine ⟨20199870694919146224238321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26933160926558861632317761 20199870694919146224238321)
                ·
                  refine ⟨15149903021189359668178741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20199870694919146224238321 15149903021189359668178741)
                  ·
                    refine ⟨1420303408236502468891757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15149903021189359668178741 1420303408236502468891757)
                    ·
                      rfl

theorem cell23_8298093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 4, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 4, 1, 1, 2, 2, 5].length) (baseStart_8298093 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8298093 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8298093 prefixEnd_8298093 := by exact prefixLift 8298093
  have htrace : WordTrace (prefixWord ++ tailWord_8298093) baseStart_8298093 baseEnd_8298093 := by
    simpa [prefixWord, tailWord_8298093, baseEnd_8298093] using wordTrace_append hprefix tailTrace_8298093
  have hstable : (prefixWord ++ tailWord_8298093).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8298093).length < 2 ^ (prefixWord ++ tailWord_8298093).sum := by decide
  have hdescent : baseEnd_8298093 < baseStart_8298093 := by decide
  rcases family_descends (prefixWord ++ tailWord_8298093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8298096 : List Nat := [2, 1, 1, 1, 6, 1, 1, 1, 4, 1, 4]
def baseStart_8298096 : Nat := 118140960795 + 8298096 * 2 ^ 59
def prefixEnd_8298096 : Nat := 4983230072969 + 3 ^ 40 * 8298096 * 2
def baseEnd_8298096 : Nat := 4260911765151470894937757

theorem tailTrace_8298096 : CollatzResearch.WordTrace tailWord_8298096 prefixEnd_8298096 4260911765151470894937757 := by
  unfold tailWord_8298096
  simp only [CollatzResearch.WordTrace]
  refine ⟨151328212672711434406349071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 201770950230281912541798761 151328212672711434406349071)
  ·
    refine ⟨226992319009067151609523607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151328212672711434406349071 226992319009067151609523607)
    ·
      refine ⟨340488478513600727414285411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 226992319009067151609523607 340488478513600727414285411)
      ·
        refine ⟨510732717770401091121428117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 340488478513600727414285411 510732717770401091121428117)
        ·
          refine ⟨23940596145487551146316943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 510732717770401091121428117 23940596145487551146316943)
          ·
            refine ⟨35910894218231326719475415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23940596145487551146316943 35910894218231326719475415)
            ·
              refine ⟨53866341327346990079213123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35910894218231326719475415 53866341327346990079213123)
              ·
                refine ⟨80799511991020485118819685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53866341327346990079213123 80799511991020485118819685)
                ·
                  refine ⟨15149908498316340959778691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 80799511991020485118819685 15149908498316340959778691)
                  ·
                    refine ⟨22724862747474511439668037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15149908498316340959778691 22724862747474511439668037)
                    ·
                      refine ⟨4260911765151470894937757, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22724862747474511439668037 4260911765151470894937757)
                      ·
                        rfl

theorem cell23_8298096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 1, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 1, 1, 1, 4, 1, 4].length) (baseStart_8298096 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8298096 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8298096 prefixEnd_8298096 := by exact prefixLift 8298096
  have htrace : WordTrace (prefixWord ++ tailWord_8298096) baseStart_8298096 baseEnd_8298096 := by
    simpa [prefixWord, tailWord_8298096, baseEnd_8298096] using wordTrace_append hprefix tailTrace_8298096
  have hstable : (prefixWord ++ tailWord_8298096).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8298096).length < 2 ^ (prefixWord ++ tailWord_8298096).sum := by decide
  have hdescent : baseEnd_8298096 < baseStart_8298096 := by decide
  rcases family_descends (prefixWord ++ tailWord_8298096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8298106 : List Nat := [3, 1, 1, 1, 1, 1, 1, 7, 3, 4]
def baseStart_8298106 : Nat := 118140960795 + 8298106 * 2 ^ 59
def prefixEnd_8298106 : Nat := 4983230072969 + 3 ^ 40 * 8298106 * 2
def baseEnd_8298106 : Nat := 1420305633319338618604237

theorem tailTrace_8298106 : CollatzResearch.WordTrace tailWord_8298106 prefixEnd_8298106 1420305633319338618604237 := by
  unfold tailWord_8298106
  simp only [CollatzResearch.WordTrace]
  refine ⟨75664197518846660130140543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 201771193383591093680374781 75664197518846660130140543)
  ·
    refine ⟨113496296278269990195210815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75664197518846660130140543 113496296278269990195210815)
    ·
      refine ⟨170244444417404985292816223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113496296278269990195210815 170244444417404985292816223)
      ·
        refine ⟨255366666626107477939224335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 170244444417404985292816223 255366666626107477939224335)
        ·
          refine ⟨383049999939161216908836503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 255366666626107477939224335 383049999939161216908836503)
          ·
            refine ⟨574574999908741825363254755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 383049999939161216908836503 574574999908741825363254755)
            ·
              refine ⟨861862499863112738044882133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 574574999908741825363254755 861862499863112738044882133)
              ·
                refine ⟨20199902340541704797926925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 861862499863112738044882133 20199902340541704797926925)
                ·
                  refine ⟨7574963377703139299222597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20199902340541704797926925 7574963377703139299222597)
                  ·
                    refine ⟨1420305633319338618604237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7574963377703139299222597 1420305633319338618604237)
                    ·
                      rfl

theorem cell23_8298106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 7, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 7, 3, 4].length) (baseStart_8298106 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8298106 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8298106 prefixEnd_8298106 := by exact prefixLift 8298106
  have htrace : WordTrace (prefixWord ++ tailWord_8298106) baseStart_8298106 baseEnd_8298106 := by
    simpa [prefixWord, tailWord_8298106, baseEnd_8298106] using wordTrace_append hprefix tailTrace_8298106
  have hstable : (prefixWord ++ tailWord_8298106).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8298106).length < 2 ^ (prefixWord ++ tailWord_8298106).sum := by decide
  have hdescent : baseEnd_8298106 < baseStart_8298106 := by decide
  rcases family_descends (prefixWord ++ tailWord_8298106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8298130 : List Nat := [3, 2, 3, 1, 3, 1, 2, 1, 2, 1, 4]
def baseStart_8298130 : Nat := 118140960795 + 8298130 * 2 ^ 59
def prefixEnd_8298130 : Nat := 4983230072969 + 3 ^ 40 * 8298130 * 2
def baseEnd_8298130 : Nat := 4260929223493723761912601

theorem tailTrace_8298130 : CollatzResearch.WordTrace tailWord_8298130 prefixEnd_8298130 4260929223493723761912601 := by
  unfold tailWord_8298130
  simp only [CollatzResearch.WordTrace]
  refine ⟨75664416356824923154858961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 201771776951533128412957229 75664416356824923154858961)
  ·
    refine ⟨56748312267618692366144221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75664416356824923154858961 56748312267618692366144221)
    ·
      refine ⟨21280617100357009637304083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 56748312267618692366144221 21280617100357009637304083)
      ·
        refine ⟨31920925650535514455956125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21280617100357009637304083 31920925650535514455956125)
        ·
          refine ⟨11970347118950817920983547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31920925650535514455956125 11970347118950817920983547)
          ·
            refine ⟨17955520678426226881475321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11970347118950817920983547 17955520678426226881475321)
            ·
              refine ⟨13466640508819670161106491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17955520678426226881475321 13466640508819670161106491)
              ·
                refine ⟨20199960763229505241659737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13466640508819670161106491 20199960763229505241659737)
                ·
                  refine ⟨15149970572422128931244803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20199960763229505241659737 15149970572422128931244803)
                  ·
                    refine ⟨22724955858633193396867205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15149970572422128931244803 22724955858633193396867205)
                    ·
                      refine ⟨4260929223493723761912601, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22724955858633193396867205 4260929223493723761912601)
                      ·
                        rfl

theorem cell23_8298130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 3, 1, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 3, 1, 2, 1, 2, 1, 4].length) (baseStart_8298130 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8298130 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8298130 prefixEnd_8298130 := by exact prefixLift 8298130
  have htrace : WordTrace (prefixWord ++ tailWord_8298130) baseStart_8298130 baseEnd_8298130 := by
    simpa [prefixWord, tailWord_8298130, baseEnd_8298130] using wordTrace_append hprefix tailTrace_8298130
  have hstable : (prefixWord ++ tailWord_8298130).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8298130).length < 2 ^ (prefixWord ++ tailWord_8298130).sum := by decide
  have hdescent : baseEnd_8298130 < baseStart_8298130 := by decide
  rcases family_descends (prefixWord ++ tailWord_8298130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8298163 : List Nat := [1, 1, 1, 2, 3, 3, 2, 3, 3, 1, 3]
def baseStart_8298163 : Nat := 118140960795 + 8298163 * 2 ^ 59
def prefixEnd_8298163 : Nat := 4983230072969 + 3 ^ 40 * 8298163 * 2
def baseEnd_8298163 : Nat := 4260946168355322132799949

theorem tailTrace_8298163 : CollatzResearch.WordTrace tailWord_8298163 prefixEnd_8298163 4260946168355322132799949 := by
  unfold tailWord_8298163
  simp only [CollatzResearch.WordTrace]
  refine ⟨302658869036180139255387143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201772579357453426170258095 302658869036180139255387143)
  ·
    refine ⟨453988303554270208883080715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 302658869036180139255387143 453988303554270208883080715)
    ·
      refine ⟨680982455331405313324621073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 453988303554270208883080715 680982455331405313324621073)
      ·
        refine ⟨510736841498553984993465805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 680982455331405313324621073 510736841498553984993465805)
        ·
          refine ⟨191526315561957744372549677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 510736841498553984993465805 191526315561957744372549677)
          ·
            refine ⟨71822368335734154139706129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 191526315561957744372549677 71822368335734154139706129)
            ·
              refine ⟨53866776251800615604779597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 71822368335734154139706129 53866776251800615604779597)
              ·
                refine ⟨20200041094425230851792349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 53866776251800615604779597 20200041094425230851792349)
                ·
                  refine ⟨7575015410409461569422131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20200041094425230851792349 7575015410409461569422131)
                  ·
                    refine ⟨11362523115614192354133197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7575015410409461569422131 11362523115614192354133197)
                    ·
                      refine ⟨4260946168355322132799949, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11362523115614192354133197 4260946168355322132799949)
                      ·
                        rfl

theorem cell23_8298163_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 2, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 2, 3, 3, 1, 3].length) (baseStart_8298163 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8298163 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8298163 prefixEnd_8298163 := by exact prefixLift 8298163
  have htrace : WordTrace (prefixWord ++ tailWord_8298163) baseStart_8298163 baseEnd_8298163 := by
    simpa [prefixWord, tailWord_8298163, baseEnd_8298163] using wordTrace_append hprefix tailTrace_8298163
  have hstable : (prefixWord ++ tailWord_8298163).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8298163).length < 2 ^ (prefixWord ++ tailWord_8298163).sum := by decide
  have hdescent : baseEnd_8298163 < baseStart_8298163 := by decide
  rcases family_descends (prefixWord ++ tailWord_8298163) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8298173 : List Nat := [1, 4, 1, 2, 1, 2, 2, 2, 1, 5, 2]
def baseStart_8298173 : Nat := 118140960795 + 8298173 * 2 ^ 59
def prefixEnd_8298173 : Nat := 4983230072969 + 3 ^ 40 * 8298173 * 2
def baseEnd_8298173 : Nat := 4260951303161867093674903

theorem tailTrace_8298173 : CollatzResearch.WordTrace tailWord_8298173 prefixEnd_8298173 4260951303161867093674903 := by
  unfold tailWord_8298173
  simp only [CollatzResearch.WordTrace]
  refine ⟨302659233766143910963251173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201772822510762607308834115 302659233766143910963251173)
  ·
    refine ⟨56748606331151983305609595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 302659233766143910963251173 56748606331151983305609595)
    ·
      refine ⟨85122909496727974958414393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56748606331151983305609595 85122909496727974958414393)
      ·
        refine ⟨63842182122545981218810795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85122909496727974958414393 63842182122545981218810795)
        ·
          refine ⟨95763273183818971828216193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63842182122545981218810795 95763273183818971828216193)
          ·
            refine ⟨71822454887864228871162145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 95763273183818971828216193 71822454887864228871162145)
            ·
              refine ⟨53866841165898171653371609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 71822454887864228871162145 53866841165898171653371609)
              ·
                refine ⟨40400130874423628740028707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53866841165898171653371609 40400130874423628740028707)
                ·
                  refine ⟨60600196311635443110043061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40400130874423628740028707 60600196311635443110043061)
                  ·
                    refine ⟨5681268404215822791566537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 60600196311635443110043061 5681268404215822791566537)
                    ·
                      refine ⟨4260951303161867093674903, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5681268404215822791566537 4260951303161867093674903)
                      ·
                        rfl

theorem cell23_8298173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 2, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 2, 2, 1, 5, 2].length) (baseStart_8298173 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8298173 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8298173 prefixEnd_8298173 := by exact prefixLift 8298173
  have htrace : WordTrace (prefixWord ++ tailWord_8298173) baseStart_8298173 baseEnd_8298173 := by
    simpa [prefixWord, tailWord_8298173, baseEnd_8298173] using wordTrace_append hprefix tailTrace_8298173
  have hstable : (prefixWord ++ tailWord_8298173).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8298173).length < 2 ^ (prefixWord ++ tailWord_8298173).sum := by decide
  have hdescent : baseEnd_8298173 < baseStart_8298173 := by decide
  rcases family_descends (prefixWord ++ tailWord_8298173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8298180 : List Nat := [2, 3, 3, 1, 1, 1, 3, 2, 3, 1, 3]
def baseStart_8298180 : Nat := 118140960795 + 8298180 * 2 ^ 59
def prefixEnd_8298180 : Nat := 4983230072969 + 3 ^ 40 * 8298180 * 2
def baseEnd_8298180 : Nat := 4260954897526448566287371

theorem tailTrace_8298180 : CollatzResearch.WordTrace tailWord_8298180 prefixEnd_8298180 4260954897526448566287371 := by
  unfold tailWord_8298180
  simp only [CollatzResearch.WordTrace]
  refine ⟨151329744538559275579377997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 201772992718079034105837329 151329744538559275579377997)
  ·
    refine ⟨56748654201959728342266749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 151329744538559275579377997 56748654201959728342266749)
    ·
      refine ⟨21280745325734898128350031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 56748654201959728342266749 21280745325734898128350031)
      ·
        refine ⟨31921117988602347192525047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21280745325734898128350031 31921117988602347192525047)
        ·
          refine ⟨47881676982903520788787571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31921117988602347192525047 47881676982903520788787571)
          ·
            refine ⟨71822515474355281183181357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47881676982903520788787571 71822515474355281183181357)
            ·
              refine ⟨26933443302883230443693009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 71822515474355281183181357 26933443302883230443693009)
              ·
                refine ⟨20200082477162422832769757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26933443302883230443693009 20200082477162422832769757)
                ·
                  refine ⟨7575030928935908562288659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20200082477162422832769757 7575030928935908562288659)
                  ·
                    refine ⟨11362546393403862843432989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7575030928935908562288659 11362546393403862843432989)
                    ·
                      refine ⟨4260954897526448566287371, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11362546393403862843432989 4260954897526448566287371)
                      ·
                        rfl

theorem cell23_8298180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 3, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 3, 2, 3, 1, 3].length) (baseStart_8298180 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8298180 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8298180 prefixEnd_8298180 := by exact prefixLift 8298180
  have htrace : WordTrace (prefixWord ++ tailWord_8298180) baseStart_8298180 baseEnd_8298180 := by
    simpa [prefixWord, tailWord_8298180, baseEnd_8298180] using wordTrace_append hprefix tailTrace_8298180
  have hstable : (prefixWord ++ tailWord_8298180).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8298180).length < 2 ^ (prefixWord ++ tailWord_8298180).sum := by decide
  have hdescent : baseEnd_8298180 < baseStart_8298180 := by decide
  rcases family_descends (prefixWord ++ tailWord_8298180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8298213 : List Nat := [1, 3, 1, 4, 1, 1, 3, 1, 4, 4]
def baseStart_8298213 : Nat := 118140960795 + 8298213 * 2 ^ 59
def prefixEnd_8298213 : Nat := 4983230072969 + 3 ^ 40 * 8298213 * 2
def baseEnd_8298213 : Nat := 1420323947462682312391573

theorem tailTrace_8298213 : CollatzResearch.WordTrace tailWord_8298213 prefixEnd_8298213 1420323947462682312391573 := by
  unfold tailWord_8298213
  simp only [CollatzResearch.WordTrace]
  refine ⟨302660692685998997794707293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201773795123999331863138195 302660692685998997794707293)
  ·
    refine ⟨113497759757249624173015235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 302660692685998997794707293 113497759757249624173015235)
    ·
      refine ⟨170246639635874436259522853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113497759757249624173015235 170246639635874436259522853)
      ·
        refine ⟨31921244931726456798660535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 170246639635874436259522853 31921244931726456798660535)
        ·
          refine ⟨47881867397589685197990803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31921244931726456798660535 47881867397589685197990803)
          ·
            refine ⟨71822801096384527796986205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47881867397589685197990803 71822801096384527796986205)
            ·
              refine ⟨26933550411144197923869827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 71822801096384527796986205 26933550411144197923869827)
              ·
                refine ⟨40400325616716296885804741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26933550411144197923869827 40400325616716296885804741)
                ·
                  refine ⟨7575061053134305666088389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 40400325616716296885804741 7575061053134305666088389)
                  ·
                    refine ⟨1420323947462682312391573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7575061053134305666088389 1420323947462682312391573)
                    ·
                      rfl

theorem cell23_8298213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 3, 1, 4, 4].length) (baseStart_8298213 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8298213 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8298213 prefixEnd_8298213 := by exact prefixLift 8298213
  have htrace : WordTrace (prefixWord ++ tailWord_8298213) baseStart_8298213 baseEnd_8298213 := by
    simpa [prefixWord, tailWord_8298213, baseEnd_8298213] using wordTrace_append hprefix tailTrace_8298213
  have hstable : (prefixWord ++ tailWord_8298213).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8298213).length < 2 ^ (prefixWord ++ tailWord_8298213).sum := by decide
  have hdescent : baseEnd_8298213 < baseStart_8298213 := by decide
  rcases family_descends (prefixWord ++ tailWord_8298213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8298220 : List Nat := [2, 2, 1, 1, 2, 2, 3, 3, 3, 2, 2]
def baseStart_8298220 : Nat := 118140960795 + 8298220 * 2 ^ 59
def prefixEnd_8298220 : Nat := 4983230072969 + 3 ^ 40 * 8298220 * 2
def baseEnd_8298220 : Nat := 4260975436752628409787187

theorem tailTrace_8298220 : CollatzResearch.WordTrace tailWord_8298220 prefixEnd_8298220 4260975436752628409787187 := by
  unfold tailWord_8298220
  simp only [CollatzResearch.WordTrace]
  refine ⟨151330473998486818995106057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 201773965331315758660141409 151330473998486818995106057)
  ·
    refine ⟨113497855498865114246329543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 151330473998486818995106057 113497855498865114246329543)
    ·
      refine ⟨170246783248297671369494315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113497855498865114246329543 170246783248297671369494315)
      ·
        refine ⟨255370174872446507054241473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 170246783248297671369494315 255370174872446507054241473)
        ·
          refine ⟨191527631154334880290681105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 255370174872446507054241473 191527631154334880290681105)
          ·
            refine ⟨143645723365751160218010829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 191527631154334880290681105 143645723365751160218010829)
            ·
              refine ⟨53867146262156685081754061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 143645723365751160218010829 53867146262156685081754061)
              ·
                refine ⟨20200179848308756905657773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 53867146262156685081754061 20200179848308756905657773)
                ·
                  refine ⟨7575067443115783839621665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20200179848308756905657773 7575067443115783839621665)
                  ·
                    refine ⟨5681300582336837879716249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7575067443115783839621665 5681300582336837879716249)
                    ·
                      refine ⟨4260975436752628409787187, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5681300582336837879716249 4260975436752628409787187)
                      ·
                        rfl

theorem cell23_8298220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 3, 2, 2].length) (baseStart_8298220 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8298220 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8298220 prefixEnd_8298220 := by exact prefixLift 8298220
  have htrace : WordTrace (prefixWord ++ tailWord_8298220) baseStart_8298220 baseEnd_8298220 := by
    simpa [prefixWord, tailWord_8298220, baseEnd_8298220] using wordTrace_append hprefix tailTrace_8298220
  have hstable : (prefixWord ++ tailWord_8298220).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8298220).length < 2 ^ (prefixWord ++ tailWord_8298220).sum := by decide
  have hdescent : baseEnd_8298220 < baseStart_8298220 := by decide
  rcases family_descends (prefixWord ++ tailWord_8298220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8298226 : List Nat := [3, 2, 1, 3, 1, 1, 2, 10]
def baseStart_8298226 : Nat := 118140960795 + 8298226 * 2 ^ 59
def prefixEnd_8298226 : Nat := 4983230072969 + 3 ^ 40 * 8298226 * 2
def baseEnd_8298226 : Nat := 157814019171724273567117

theorem tailTrace_8298226 : CollatzResearch.WordTrace tailWord_8298226 prefixEnd_8298226 157814019171724273567117 := by
  unfold tailWord_8298226
  simp only [CollatzResearch.WordTrace]
  refine ⟨75665291708737975253732633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 201774111223301267343287021 75665291708737975253732633)
  ·
    refine ⟨56748968781553481440299475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75665291708737975253732633 56748968781553481440299475)
    ·
      refine ⟨85123453172330222160449213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56748968781553481440299475 85123453172330222160449213)
      ·
        refine ⟨31921294939623833310168455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 85123453172330222160449213 31921294939623833310168455)
        ·
          refine ⟨47881942409435749965252683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31921294939623833310168455 47881942409435749965252683)
          ·
            refine ⟨71822913614153624947879025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47881942409435749965252683 71822913614153624947879025)
            ·
              refine ⟨53867185210615218710909269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 71822913614153624947879025 53867185210615218710909269)
              ·
                refine ⟨157814019171724273567117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 53867185210615218710909269 157814019171724273567117)
                ·
                  rfl

theorem cell23_8298226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 2, 10].length) (baseStart_8298226 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8298226 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8298226 prefixEnd_8298226 := by exact prefixLift 8298226
  have htrace : WordTrace (prefixWord ++ tailWord_8298226) baseStart_8298226 baseEnd_8298226 := by
    simpa [prefixWord, tailWord_8298226, baseEnd_8298226] using wordTrace_append hprefix tailTrace_8298226
  have hstable : (prefixWord ++ tailWord_8298226).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8298226).length < 2 ^ (prefixWord ++ tailWord_8298226).sum := by decide
  have hdescent : baseEnd_8298226 < baseStart_8298226 := by decide
  rcases family_descends (prefixWord ++ tailWord_8298226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8298230 : List Nat := [5, 1, 1, 1, 1, 5, 1, 1, 1, 6]
def baseStart_8298230 : Nat := 118140960795 + 8298230 * 2 ^ 59
def prefixEnd_8298230 : Nat := 4983230072969 + 3 ^ 40 * 8298230 * 2
def baseEnd_8298230 : Nat := 1420326857186391123554047

theorem tailTrace_8298230 : CollatzResearch.WordTrace tailWord_8298230 prefixEnd_8298230 1420326857186391123554047 := by
  unfold tailWord_8298230
  simp only [CollatzResearch.WordTrace]
  refine ⟨18916332045433588106129759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 201774208484624939798717429 18916332045433588106129759)
  ·
    refine ⟨28374498068150382159194639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18916332045433588106129759 28374498068150382159194639)
    ·
      refine ⟨42561747102225573238791959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28374498068150382159194639 42561747102225573238791959)
      ·
        refine ⟨63842620653338359858187939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42561747102225573238791959 63842620653338359858187939)
        ·
          refine ⟨95763930980007539787281909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63842620653338359858187939 95763930980007539787281909)
          ·
            refine ⟨8977868529375706855057679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 95763930980007539787281909 8977868529375706855057679)
            ·
              refine ⟨13466802794063560282586519, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8977868529375706855057679 13466802794063560282586519)
              ·
                refine ⟨20200204191095340423879779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13466802794063560282586519 20200204191095340423879779)
                ·
                  refine ⟨30300306286643010635819669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20200204191095340423879779 30300306286643010635819669)
                  ·
                    refine ⟨1420326857186391123554047, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 30300306286643010635819669 1420326857186391123554047)
                    ·
                      rfl

theorem cell23_8298230_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 5, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 5, 1, 1, 1, 6].length) (baseStart_8298230 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8298230 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8298230 prefixEnd_8298230 := by exact prefixLift 8298230
  have htrace : WordTrace (prefixWord ++ tailWord_8298230) baseStart_8298230 baseEnd_8298230 := by
    simpa [prefixWord, tailWord_8298230, baseEnd_8298230] using wordTrace_append hprefix tailTrace_8298230
  have hstable : (prefixWord ++ tailWord_8298230).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8298230).length < 2 ^ (prefixWord ++ tailWord_8298230).sum := by decide
  have hdescent : baseEnd_8298230 < baseStart_8298230 := by decide
  rcases family_descends (prefixWord ++ tailWord_8298230) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8298254 : List Nat := [4, 1, 1, 2, 1, 1, 5, 3, 1, 2, 2]
def baseStart_8298254 : Nat := 118140960795 + 8298254 * 2 ^ 59
def prefixEnd_8298254 : Nat := 4983230072969 + 3 ^ 40 * 8298254 * 2
def baseEnd_8298254 : Nat := 4260992895094881276762031

theorem tailTrace_8298254 : CollatzResearch.WordTrace tailWord_8298254 prefixEnd_8298254 4260992895094881276762031 := by
  unfold tailWord_8298254
  simp only [CollatzResearch.WordTrace]
  refine ⟨37832773509856307724618727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 201774792052566974531299877 37832773509856307724618727)
  ·
    refine ⟨56749160264784461586928091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37832773509856307724618727 56749160264784461586928091)
    ·
      refine ⟨85123740397176692380392137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56749160264784461586928091 85123740397176692380392137)
      ·
        refine ⟨63842805297882519285294103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85123740397176692380392137 63842805297882519285294103)
        ·
          refine ⟨95764207946823778927941155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63842805297882519285294103 95764207946823778927941155)
          ·
            refine ⟨143646311920235668391911733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 95764207946823778927941155 143646311920235668391911733)
            ·
              refine ⟨13466841742522093911741725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 143646311920235668391911733 13466841742522093911741725)
              ·
                refine ⟨5050065653445785216903147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13466841742522093911741725 5050065653445785216903147)
                ·
                  refine ⟨7575098480168677825354721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5050065653445785216903147 7575098480168677825354721)
                  ·
                    refine ⟨5681323860126508369016041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7575098480168677825354721 5681323860126508369016041)
                    ·
                      refine ⟨4260992895094881276762031, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5681323860126508369016041 4260992895094881276762031)
                      ·
                        rfl

theorem cell23_8298254_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 5, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 5, 3, 1, 2, 2].length) (baseStart_8298254 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8298254 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8298254 prefixEnd_8298254 := by exact prefixLift 8298254
  have htrace : WordTrace (prefixWord ++ tailWord_8298254) baseStart_8298254 baseEnd_8298254 := by
    simpa [prefixWord, tailWord_8298254, baseEnd_8298254] using wordTrace_append hprefix tailTrace_8298254
  have hstable : (prefixWord ++ tailWord_8298254).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8298254).length < 2 ^ (prefixWord ++ tailWord_8298254).sum := by decide
  have hdescent : baseEnd_8298254 < baseStart_8298254 := by decide
  rcases family_descends (prefixWord ++ tailWord_8298254) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8298340 : List Nat := [2, 3, 1, 1, 5, 1, 1, 1, 2, 2, 4]
def baseStart_8298340 : Nat := 118140960795 + 8298340 * 2 ^ 59
def prefixEnd_8298340 : Nat := 4983230072969 + 3 ^ 40 * 8298340 * 2
def baseEnd_8298340 : Nat := 4261037054431167940286635

theorem tailTrace_8298340 : CollatzResearch.WordTrace tailWord_8298340 prefixEnd_8298340 4261037054431167940286635 := by
  unfold tailWord_8298340
  simp only [CollatzResearch.WordTrace]
  refine ⟨151332662378269449242290237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 201776883171025932323053649 151332662378269449242290237)
  ·
    refine ⟨56749748391851043465858839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 151332662378269449242290237 56749748391851043465858839)
    ·
      refine ⟨85124622587776565198788259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56749748391851043465858839 85124622587776565198788259)
      ·
        refine ⟨127686933881664847798182389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85124622587776565198788259 127686933881664847798182389)
        ·
          refine ⟨11970650051406079481079599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 127686933881664847798182389 11970650051406079481079599)
          ·
            refine ⟨17955975077109119221619399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11970650051406079481079599 17955975077109119221619399)
            ·
              refine ⟨26933962615663678832429099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17955975077109119221619399 26933962615663678832429099)
              ·
                refine ⟨40400943923495518248643649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26933962615663678832429099 40400943923495518248643649)
                ·
                  refine ⟨30300707942621638686482737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40400943923495518248643649 30300707942621638686482737)
                  ·
                    refine ⟨22725530956966229014862053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 30300707942621638686482737 22725530956966229014862053)
                    ·
                      refine ⟨4261037054431167940286635, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22725530956966229014862053 4261037054431167940286635)
                      ·
                        rfl

theorem cell23_8298340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 5, 1, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 5, 1, 1, 1, 2, 2, 4].length) (baseStart_8298340 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8298340 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8298340 prefixEnd_8298340 := by exact prefixLift 8298340
  have htrace : WordTrace (prefixWord ++ tailWord_8298340) baseStart_8298340 baseEnd_8298340 := by
    simpa [prefixWord, tailWord_8298340, baseEnd_8298340] using wordTrace_append hprefix tailTrace_8298340
  have hstable : (prefixWord ++ tailWord_8298340).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8298340).length < 2 ^ (prefixWord ++ tailWord_8298340).sum := by decide
  have hdescent : baseEnd_8298340 < baseStart_8298340 := by decide
  rcases family_descends (prefixWord ++ tailWord_8298340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8298350 : List Nat := [4, 1, 2, 3, 1, 2, 1, 2, 7]
def baseStart_8298350 : Nat := 118140960795 + 8298350 * 2 ^ 59
def prefixEnd_8298350 : Nat := 4983230072969 + 3 ^ 40 * 8298350 * 2
def baseEnd_8298350 : Nat := 473449132137523655684621

theorem tailTrace_8298350 : CollatzResearch.WordTrace tailWord_8298350 prefixEnd_8298350 473449132137523655684621 := by
  unfold tailWord_8298350
  simp only [CollatzResearch.WordTrace]
  refine ⟨37833211185812833774055563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 201777126324335113461629669 37833211185812833774055563)
  ·
    refine ⟨56749816778719250661083345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37833211185812833774055563 56749816778719250661083345)
    ·
      refine ⟨42562362584039437995812509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56749816778719250661083345 42562362584039437995812509)
      ·
        refine ⟨15960885969014789248429691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42562362584039437995812509 15960885969014789248429691)
        ·
          refine ⟨23941328953522183872644537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15960885969014789248429691 23941328953522183872644537)
          ·
            refine ⟨17955996715141637904483403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23941328953522183872644537 17955996715141637904483403)
            ·
              refine ⟨26933995072712456856725105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17955996715141637904483403 26933995072712456856725105)
              ·
                refine ⟨20200496304534342642543829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26933995072712456856725105 20200496304534342642543829)
                ·
                  refine ⟨473449132137523655684621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 20200496304534342642543829 473449132137523655684621)
                  ·
                    rfl

theorem cell23_8298350_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 2, 1, 2, 7].length) (baseStart_8298350 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8298350 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8298350 prefixEnd_8298350 := by exact prefixLift 8298350
  have htrace : WordTrace (prefixWord ++ tailWord_8298350) baseStart_8298350 baseEnd_8298350 := by
    simpa [prefixWord, tailWord_8298350, baseEnd_8298350] using wordTrace_append hprefix tailTrace_8298350
  have hstable : (prefixWord ++ tailWord_8298350).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8298350).length < 2 ^ (prefixWord ++ tailWord_8298350).sum := by decide
  have hdescent : baseEnd_8298350 < baseStart_8298350 := by decide
  rcases family_descends (prefixWord ++ tailWord_8298350) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8298378 : List Nat := [3, 1, 2, 4, 3, 1, 1, 2, 2, 2, 2]
def baseStart_8298378 : Nat := 118140960795 + 8298378 * 2 ^ 59
def prefixEnd_8298378 : Nat := 4983230072969 + 3 ^ 40 * 8298378 * 2
def baseEnd_8298378 : Nat := 4261056566696038791611461

theorem tailTrace_8298378 : CollatzResearch.WordTrace tailWord_8298378 prefixEnd_8298378 4261056566696038791611461 := by
  unfold tailWord_8298378
  simp only [CollatzResearch.WordTrace]
  refine ⟨75666677682600307743615947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 201777807153600820649642525 75666677682600307743615947)
  ·
    refine ⟨113500016523900461615423921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75666677682600307743615947 113500016523900461615423921)
    ·
      refine ⟨85125012392925346211567941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 113500016523900461615423921 85125012392925346211567941)
      ·
        refine ⟨15960939823673502414668989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 85125012392925346211567941 15960939823673502414668989)
        ·
          refine ⟨5985352433877563405500871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15960939823673502414668989 5985352433877563405500871)
          ·
            refine ⟨8978028650816345108251307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5985352433877563405500871 8978028650816345108251307)
            ·
              refine ⟨13467042976224517662376961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8978028650816345108251307 13467042976224517662376961)
              ·
                refine ⟨10100282232168388246782721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13467042976224517662376961 10100282232168388246782721)
                ·
                  refine ⟨7575211674126291185087041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10100282232168388246782721 7575211674126291185087041)
                  ·
                    refine ⟨5681408755594718388815281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7575211674126291185087041 5681408755594718388815281)
                    ·
                      refine ⟨4261056566696038791611461, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5681408755594718388815281 4261056566696038791611461)
                      ·
                        rfl

theorem cell23_8298378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 3, 1, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 3, 1, 1, 2, 2, 2, 2].length) (baseStart_8298378 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8298378 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8298378 prefixEnd_8298378 := by exact prefixLift 8298378
  have htrace : WordTrace (prefixWord ++ tailWord_8298378) baseStart_8298378 baseEnd_8298378 := by
    simpa [prefixWord, tailWord_8298378, baseEnd_8298378] using wordTrace_append hprefix tailTrace_8298378
  have hstable : (prefixWord ++ tailWord_8298378).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8298378).length < 2 ^ (prefixWord ++ tailWord_8298378).sum := by decide
  have hdescent : baseEnd_8298378 < baseStart_8298378 := by decide
  rcases family_descends (prefixWord ++ tailWord_8298378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8298501 : List Nat := [1, 3, 1, 1, 2, 4, 4, 2, 1, 1, 3]
def baseStart_8298501 : Nat := 118140960795 + 8298501 * 2 ^ 59
def prefixEnd_8298501 : Nat := 4983230072969 + 3 ^ 40 * 8298501 * 2
def baseEnd_8298501 : Nat := 4261119724816541810373395

theorem tailTrace_8298501 : CollatzResearch.WordTrace tailWord_8298501 prefixEnd_8298501 4261119724816541810373395 := by
  unfold tailWord_8298501
  simp only [CollatzResearch.WordTrace]
  refine ⟨302671196908955622981191357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201780797939303748654127571 302671196908955622981191357)
  ·
    refine ⟨113501698840858358617946759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 302671196908955622981191357 113501698840858358617946759)
    ·
      refine ⟨170252548261287537926920139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113501698840858358617946759 170252548261287537926920139)
      ·
        refine ⟨255378822391931306890380209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 170252548261287537926920139 255378822391931306890380209)
        ·
          refine ⟨191534116793948480167785157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 255378822391931306890380209 191534116793948480167785157)
          ·
            refine ⟨35912646898865340031459717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 191534116793948480167785157 35912646898865340031459717)
            ·
              refine ⟨6733621293537251255898697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 35912646898865340031459717 6733621293537251255898697)
              ·
                refine ⟨5050215970152938441924023, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6733621293537251255898697 5050215970152938441924023)
                ·
                  refine ⟨7575323955229407662886035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5050215970152938441924023 7575323955229407662886035)
                  ·
                    refine ⟨11362985932844111494329053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7575323955229407662886035 11362985932844111494329053)
                    ·
                      refine ⟨4261119724816541810373395, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11362985932844111494329053 4261119724816541810373395)
                      ·
                        rfl

theorem cell23_8298501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 4, 4, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 4, 4, 2, 1, 1, 3].length) (baseStart_8298501 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8298501 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8298501 prefixEnd_8298501 := by exact prefixLift 8298501
  have htrace : WordTrace (prefixWord ++ tailWord_8298501) baseStart_8298501 baseEnd_8298501 := by
    simpa [prefixWord, tailWord_8298501, baseEnd_8298501] using wordTrace_append hprefix tailTrace_8298501
  have hstable : (prefixWord ++ tailWord_8298501).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8298501).length < 2 ^ (prefixWord ++ tailWord_8298501).sum := by decide
  have hdescent : baseEnd_8298501 < baseStart_8298501 := by decide
  rcases family_descends (prefixWord ++ tailWord_8298501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8298510 : List Nat := [4, 1, 1, 2, 2, 1, 2, 1, 3, 1, 5]
def baseStart_8298510 : Nat := 118140960795 + 8298510 * 2 ^ 59
def prefixEnd_8298510 : Nat := 4983230072969 + 3 ^ 40 * 8298510 * 2
def baseEnd_8298510 : Nat := 4261124346142432275160853

theorem tailTrace_8298510 : CollatzResearch.WordTrace tailWord_8298510 prefixEnd_8298510 4261124346142432275160853 := by
  unfold tailWord_8298510
  simp only [CollatzResearch.WordTrace]
  refine ⟨37833940645740377189783623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 201781016777282011678845989 37833940645740377189783623)
  ·
    refine ⟨56750910968610565784675435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37833940645740377189783623 56750910968610565784675435)
    ·
      refine ⟨85126366452915848677013153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56750910968610565784675435 85126366452915848677013153)
      ·
        refine ⟨63844774839686886507759865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85126366452915848677013153 63844774839686886507759865)
        ·
          refine ⟨47883581129765164880819899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63844774839686886507759865 47883581129765164880819899)
          ·
            refine ⟨71825371694647747321229849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47883581129765164880819899 71825371694647747321229849)
            ·
              refine ⟨53869028770985810490922387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 71825371694647747321229849 53869028770985810490922387)
              ·
                refine ⟨80803543156478715736383581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53869028770985810490922387 80803543156478715736383581)
                ·
                  refine ⟨30301328683679518401143843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 80803543156478715736383581 30301328683679518401143843)
                  ·
                    refine ⟨45451993025519277601715765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 30301328683679518401143843 45451993025519277601715765)
                    ·
                      refine ⟨4261124346142432275160853, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 45451993025519277601715765 4261124346142432275160853)
                      ·
                        rfl

theorem cell23_8298510_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 2, 1, 3, 1, 5].length) (baseStart_8298510 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8298510 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8298510 prefixEnd_8298510 := by exact prefixLift 8298510
  have htrace : WordTrace (prefixWord ++ tailWord_8298510) baseStart_8298510 baseEnd_8298510 := by
    simpa [prefixWord, tailWord_8298510, baseEnd_8298510] using wordTrace_append hprefix tailTrace_8298510
  have hstable : (prefixWord ++ tailWord_8298510).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8298510).length < 2 ^ (prefixWord ++ tailWord_8298510).sum := by decide
  have hdescent : baseEnd_8298510 < baseStart_8298510 := by decide
  rcases family_descends (prefixWord ++ tailWord_8298510) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8298517 : List Nat := [1, 3, 2, 1, 5, 1, 2, 1, 1, 6]
def baseStart_8298517 : Nat := 118140960795 + 8298517 * 2 ^ 59
def prefixEnd_8298517 : Nat := 4983230072969 + 3 ^ 40 * 8298517 * 2
def baseEnd_8298517 : Nat := 1420375980169004582591107

theorem tailTrace_8298517 : CollatzResearch.WordTrace tailWord_8298517 prefixEnd_8298517 1420375980169004582591107 := by
  unfold tailWord_8298517
  simp only [CollatzResearch.WordTrace]
  refine ⟨302671780476897657713773805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201781186984598438475849203 302671780476897657713773805)
  ·
    refine ⟨113501917678836621642665177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 302671780476897657713773805 113501917678836621642665177)
    ·
      refine ⟨85126438259127466231998883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 113501917678836621642665177 85126438259127466231998883)
      ·
        refine ⟨127689657388691199347998325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85126438259127466231998883 127689657388691199347998325)
        ·
          refine ⟨11970905380189799938874843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 127689657388691199347998325 11970905380189799938874843)
          ·
            refine ⟨17956358070284699908312265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11970905380189799938874843 17956358070284699908312265)
            ·
              refine ⟨13467268552713524931234199, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17956358070284699908312265 13467268552713524931234199)
              ·
                refine ⟨20200902829070287396851299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13467268552713524931234199 20200902829070287396851299)
                ·
                  refine ⟨30301354243605431095276949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20200902829070287396851299 30301354243605431095276949)
                  ·
                    refine ⟨1420375980169004582591107, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 30301354243605431095276949 1420375980169004582591107)
                    ·
                      rfl

theorem cell23_8298517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 5, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 5, 1, 2, 1, 1, 6].length) (baseStart_8298517 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8298517 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8298517 prefixEnd_8298517 := by exact prefixLift 8298517
  have htrace : WordTrace (prefixWord ++ tailWord_8298517) baseStart_8298517 baseEnd_8298517 := by
    simpa [prefixWord, tailWord_8298517, baseEnd_8298517] using wordTrace_append hprefix tailTrace_8298517
  have hstable : (prefixWord ++ tailWord_8298517).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8298517).length < 2 ^ (prefixWord ++ tailWord_8298517).sum := by decide
  have hdescent : baseEnd_8298517 < baseStart_8298517 := by decide
  rcases family_descends (prefixWord ++ tailWord_8298517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8298524 : List Nat := [2, 2, 3, 1, 3, 1, 1, 1, 5, 2, 2]
def baseStart_8298524 : Nat := 118140960795 + 8298524 * 2 ^ 59
def prefixEnd_8298524 : Nat := 4983230072969 + 3 ^ 40 * 8298524 * 2
def baseEnd_8298524 : Nat := 4261131534871595220385789

theorem tailTrace_8298524 : CollatzResearch.WordTrace tailWord_8298524 prefixEnd_8298524 4261131534871595220385789 := by
  unfold tailWord_8298524
  simp only [CollatzResearch.WordTrace]
  refine ⟨151336017893936148954639313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 201781357191914865272852417 151336017893936148954639313)
  ·
    refine ⟨113502013420452111715979485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 151336017893936148954639313 113502013420452111715979485)
    ·
      refine ⟨42563255032669541893492307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 113502013420452111715979485 42563255032669541893492307)
      ·
        refine ⟨63844882549004312840238461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42563255032669541893492307 63844882549004312840238461)
        ·
          refine ⟨23941830955876617315089423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 63844882549004312840238461 23941830955876617315089423)
          ·
            refine ⟨35912746433814925972634135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23941830955876617315089423 35912746433814925972634135)
            ·
              refine ⟨53869119650722388958951203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35912746433814925972634135 53869119650722388958951203)
              ·
                refine ⟨80803679476083583438426805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53869119650722388958951203 80803679476083583438426805)
                ·
                  refine ⟨7575344950882835947352513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 80803679476083583438426805 7575344950882835947352513)
                  ·
                    refine ⟨5681508713162126960514385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7575344950882835947352513 5681508713162126960514385)
                    ·
                      refine ⟨4261131534871595220385789, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5681508713162126960514385 4261131534871595220385789)
                      ·
                        rfl

theorem cell23_8298524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 1, 1, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 1, 1, 1, 5, 2, 2].length) (baseStart_8298524 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8298524 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8298524 prefixEnd_8298524 := by exact prefixLift 8298524
  have htrace : WordTrace (prefixWord ++ tailWord_8298524) baseStart_8298524 baseEnd_8298524 := by
    simpa [prefixWord, tailWord_8298524, baseEnd_8298524] using wordTrace_append hprefix tailTrace_8298524
  have hstable : (prefixWord ++ tailWord_8298524).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8298524).length < 2 ^ (prefixWord ++ tailWord_8298524).sum := by decide
  have hdescent : baseEnd_8298524 < baseStart_8298524 := by decide
  rcases family_descends (prefixWord ++ tailWord_8298524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8298527 : List Nat := [1, 1, 2, 4, 1, 2, 2, 4, 1, 2, 3]
def baseStart_8298527 : Nat := 118140960795 + 8298527 * 2 ^ 59
def prefixEnd_8298527 : Nat := 4983230072969 + 3 ^ 40 * 8298527 * 2
def baseEnd_8298527 : Nat := 4261133075313558708648275

theorem tailTrace_8298527 : CollatzResearch.WordTrace tailWord_8298527 prefixEnd_8298527 4261133075313558708648275 := by
  unfold tailWord_8298527
  simp only [CollatzResearch.WordTrace]
  refine ⟨302672145206861429421637835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201781430137907619614425223 302672145206861429421637835)
  ·
    refine ⟨454008217810292144132456753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 302672145206861429421637835 454008217810292144132456753)
    ·
      refine ⟨340506163357719108099342565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 454008217810292144132456753 340506163357719108099342565)
      ·
        refine ⟨63844905629572332768626731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 340506163357719108099342565 63844905629572332768626731)
        ·
          refine ⟨95767358444358499152940097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63844905629572332768626731 95767358444358499152940097)
          ·
            refine ⟨71825518833268874364705073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 95767358444358499152940097 71825518833268874364705073)
            ·
              refine ⟨53869139124951655773528805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 71825518833268874364705073 53869139124951655773528805)
              ·
                refine ⟨10100463585928435457536651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 53869139124951655773528805 10100463585928435457536651)
                ·
                  refine ⟨15150695378892653186304977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10100463585928435457536651 15150695378892653186304977)
                  ·
                    refine ⟨11363021534169489889728733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15150695378892653186304977 11363021534169489889728733)
                    ·
                      refine ⟨4261133075313558708648275, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11363021534169489889728733 4261133075313558708648275)
                      ·
                        rfl

theorem cell23_8298527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 2, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 2, 4, 1, 2, 3].length) (baseStart_8298527 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8298527 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8298527 prefixEnd_8298527 := by exact prefixLift 8298527
  have htrace : WordTrace (prefixWord ++ tailWord_8298527) baseStart_8298527 baseEnd_8298527 := by
    simpa [prefixWord, tailWord_8298527, baseEnd_8298527] using wordTrace_append hprefix tailTrace_8298527
  have hstable : (prefixWord ++ tailWord_8298527).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8298527).length < 2 ^ (prefixWord ++ tailWord_8298527).sum := by decide
  have hdescent : baseEnd_8298527 < baseStart_8298527 := by decide
  rcases family_descends (prefixWord ++ tailWord_8298527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8298540 : List Nat := [2, 2, 1, 1, 1, 2, 2, 3, 3, 3, 3]
def baseStart_8298540 : Nat := 118140960795 + 8298540 * 2 ^ 59
def prefixEnd_8298540 : Nat := 4983230072969 + 3 ^ 40 * 8298540 * 2
def baseEnd_8298540 : Nat := 4261139750562067157785715

theorem tailTrace_8298540 : CollatzResearch.WordTrace tailWord_8298540 prefixEnd_8298540 4261139750562067157785715 := by
  unfold tailWord_8298540
  simp only [CollatzResearch.WordTrace]
  refine ⟨151336309677907166320930537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 201781746237209555094574049 151336309677907166320930537)
  ·
    refine ⟨113502232258430374740697903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 151336309677907166320930537 113502232258430374740697903)
    ·
      refine ⟨170253348387645562111046855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113502232258430374740697903 170253348387645562111046855)
      ·
        refine ⟨255380022581468343166570283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 170253348387645562111046855 255380022581468343166570283)
        ·
          refine ⟨383070033872202514749855425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 255380022581468343166570283 383070033872202514749855425)
          ·
            refine ⟨287302525404151886062391569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 383070033872202514749855425 287302525404151886062391569)
            ·
              refine ⟨215476894053113914546793677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 287302525404151886062391569 215476894053113914546793677)
              ·
                refine ⟨80803835269917717955047629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 215476894053113914546793677 80803835269917717955047629)
                ·
                  refine ⟨30301438226219144233142861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 80803835269917717955047629 30301438226219144233142861)
                  ·
                    refine ⟨11363039334832179087428573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 30301438226219144233142861 11363039334832179087428573)
                    ·
                      refine ⟨4261139750562067157785715, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11363039334832179087428573 4261139750562067157785715)
                      ·
                        rfl

theorem cell23_8298540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 3, 3].length) (baseStart_8298540 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8298540 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8298540 prefixEnd_8298540 := by exact prefixLift 8298540
  have htrace : WordTrace (prefixWord ++ tailWord_8298540) baseStart_8298540 baseEnd_8298540 := by
    simpa [prefixWord, tailWord_8298540, baseEnd_8298540] using wordTrace_append hprefix tailTrace_8298540
  have hstable : (prefixWord ++ tailWord_8298540).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8298540).length < 2 ^ (prefixWord ++ tailWord_8298540).sum := by decide
  have hdescent : baseEnd_8298540 < baseStart_8298540 := by decide
  rcases family_descends (prefixWord ++ tailWord_8298540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8298543 : List Nat := [1, 1, 2, 1, 2, 1, 1, 4, 1, 9]
def baseStart_8298543 : Nat := 118140960795 + 8298543 * 2 ^ 59
def prefixEnd_8298543 : Nat := 4983230072969 + 3 ^ 40 * 8298543 * 2
def baseEnd_8298543 : Nat := 1420380430334676882016067

theorem tailTrace_8298543 : CollatzResearch.WordTrace tailWord_8298543 prefixEnd_8298543 1420380430334676882016067 := by
  unfold tailWord_8298543
  simp only [CollatzResearch.WordTrace]
  refine ⟨302672728774803464154220283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201781819183202309436146855 302672728774803464154220283)
  ·
    refine ⟨454009093162205196231330425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 302672728774803464154220283 454009093162205196231330425)
    ·
      refine ⟨340506819871653897173497819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 454009093162205196231330425 340506819871653897173497819)
      ·
        refine ⟨510760229807480845760246729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 340506819871653897173497819 510760229807480845760246729)
        ·
          refine ⟨383070172355610634320185047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 510760229807480845760246729 383070172355610634320185047)
          ·
            refine ⟨574605258533415951480277571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 383070172355610634320185047 574605258533415951480277571)
            ·
              refine ⟨861907887800123927220416357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 574605258533415951480277571 861907887800123927220416357)
              ·
                refine ⟨161607728962523236353828067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 861907887800123927220416357 161607728962523236353828067)
                ·
                  refine ⟨242411593443784854530742101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 161607728962523236353828067 242411593443784854530742101)
                  ·
                    refine ⟨1420380430334676882016067, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 242411593443784854530742101 1420380430334676882016067)
                    ·
                      rfl

theorem cell23_8298543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 4, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 4, 1, 9].length) (baseStart_8298543 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8298543 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8298543 prefixEnd_8298543 := by exact prefixLift 8298543
  have htrace : WordTrace (prefixWord ++ tailWord_8298543) baseStart_8298543 baseEnd_8298543 := by
    simpa [prefixWord, tailWord_8298543, baseEnd_8298543] using wordTrace_append hprefix tailTrace_8298543
  have hstable : (prefixWord ++ tailWord_8298543).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8298543).length < 2 ^ (prefixWord ++ tailWord_8298543).sum := by decide
  have hdescent : baseEnd_8298543 < baseStart_8298543 := by decide
  rcases family_descends (prefixWord ++ tailWord_8298543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8298544 : List Nat := [2, 1, 1, 1, 2, 5, 4, 1, 1, 2, 3]
def baseStart_8298544 : Nat := 118140960795 + 8298544 * 2 ^ 59
def prefixEnd_8298544 : Nat := 4983230072969 + 3 ^ 40 * 8298544 * 2
def baseEnd_8298544 : Nat := 4261141804484685142135697

theorem tailTrace_8298544 : CollatzResearch.WordTrace tailWord_8298544 prefixEnd_8298544 4261141804484685142135697 := by
  unfold tailWord_8298544
  simp only [CollatzResearch.WordTrace]
  refine ⟨151336382623899920662503343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 201781843498533227550004457 151336382623899920662503343)
  ·
    refine ⟨227004573935849880993755015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151336382623899920662503343 227004573935849880993755015)
    ·
      refine ⟨340506860903774821490632523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 227004573935849880993755015 340506860903774821490632523)
      ·
        refine ⟨510760291355662232235948785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 340506860903774821490632523 510760291355662232235948785)
        ·
          refine ⟨383070218516746674176961589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 510760291355662232235948785 383070218516746674176961589)
          ·
            refine ⟨35912832985945000704090149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 383070218516746674176961589 35912832985945000704090149)
            ·
              refine ⟨6733656184864687632016903, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 35912832985945000704090149 6733656184864687632016903)
              ·
                refine ⟨10100484277297031448025355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6733656184864687632016903 10100484277297031448025355)
                ·
                  refine ⟨15150726415945547172038033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10100484277297031448025355 15150726415945547172038033)
                  ·
                    refine ⟨11363044811959160379028525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15150726415945547172038033 11363044811959160379028525)
                    ·
                      refine ⟨4261141804484685142135697, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11363044811959160379028525 4261141804484685142135697)
                      ·
                        rfl

theorem cell23_8298544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 5, 4, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 5, 4, 1, 1, 2, 3].length) (baseStart_8298544 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8298544 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8298544 prefixEnd_8298544 := by exact prefixLift 8298544
  have htrace : WordTrace (prefixWord ++ tailWord_8298544) baseStart_8298544 baseEnd_8298544 := by
    simpa [prefixWord, tailWord_8298544, baseEnd_8298544] using wordTrace_append hprefix tailTrace_8298544
  have hstable : (prefixWord ++ tailWord_8298544).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8298544).length < 2 ^ (prefixWord ++ tailWord_8298544).sum := by decide
  have hdescent : baseEnd_8298544 < baseStart_8298544 := by decide
  rcases family_descends (prefixWord ++ tailWord_8298544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8298558 : List Nat := [4, 2, 1, 3, 2, 1, 2, 1, 3, 2, 2]
def baseStart_8298558 : Nat := 118140960795 + 8298558 * 2 ^ 59
def prefixEnd_8298558 : Nat := 4983230072969 + 3 ^ 40 * 8298558 * 2
def baseEnd_8298558 : Nat := 4261148993213848087360633

theorem tailTrace_8298558 : CollatzResearch.WordTrace tailWord_8298558 prefixEnd_8298558 4261148993213848087360633 := by
  unfold tailWord_8298558
  simp only [CollatzResearch.WordTrace]
  refine ⟨37834159483718640214502041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 201782183913166081144010885 37834159483718640214502041)
  ·
    refine ⟨28375619612788980160876531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37834159483718640214502041 28375619612788980160876531)
    ·
      refine ⟨42563429419183470241314797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28375619612788980160876531 42563429419183470241314797)
      ·
        refine ⟨15961286032193801340493049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42563429419183470241314797 15961286032193801340493049)
        ·
          refine ⟨11970964524145351005369787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15961286032193801340493049 11970964524145351005369787)
          ·
            refine ⟨17956446786218026508054681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11970964524145351005369787 17956446786218026508054681)
            ·
              refine ⟨13467335089663519881041011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17956446786218026508054681 13467335089663519881041011)
              ·
                refine ⟨20201002634495279821561517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13467335089663519881041011 20201002634495279821561517)
                ·
                  refine ⟨7575375987935729933085569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20201002634495279821561517 7575375987935729933085569)
                  ·
                    refine ⟨5681531990951797449814177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7575375987935729933085569 5681531990951797449814177)
                    ·
                      refine ⟨4261148993213848087360633, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5681531990951797449814177 4261148993213848087360633)
                      ·
                        rfl

theorem cell23_8298558_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 2, 1, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 2, 1, 2, 1, 3, 2, 2].length) (baseStart_8298558 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8298558 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8298558 prefixEnd_8298558 := by exact prefixLift 8298558
  have htrace : WordTrace (prefixWord ++ tailWord_8298558) baseStart_8298558 baseEnd_8298558 := by
    simpa [prefixWord, tailWord_8298558, baseEnd_8298558] using wordTrace_append hprefix tailTrace_8298558
  have hstable : (prefixWord ++ tailWord_8298558).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8298558).length < 2 ^ (prefixWord ++ tailWord_8298558).sum := by decide
  have hdescent : baseEnd_8298558 < baseStart_8298558 := by decide
  rcases family_descends (prefixWord ++ tailWord_8298558) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8298574 : List Nat := [4, 1, 1, 1, 1, 6, 1, 1, 1, 3, 3]
def baseStart_8298574 : Nat := 118140960795 + 8298574 * 2 ^ 59
def prefixEnd_8298574 : Nat := 4983230072969 + 3 ^ 40 * 8298574 * 2
def baseEnd_8298574 : Nat := 4261157208904320024760559

theorem tailTrace_8298574 : CollatzResearch.WordTrace tailWord_8298574 prefixEnd_8298574 4261157208904320024760559 := by
  unfold tailWord_8298574
  simp only [CollatzResearch.WordTrace]
  refine ⟨37834232429711394556074847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 201782572958460770965732517 37834232429711394556074847)
  ·
    refine ⟨56751348644567091834112271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37834232429711394556074847 56751348644567091834112271)
    ·
      refine ⟨85127022966850637751168407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56751348644567091834112271 85127022966850637751168407)
      ·
        refine ⟨127690534450275956626752611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85127022966850637751168407 127690534450275956626752611)
        ·
          refine ⟨191535801675413934940128917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 127690534450275956626752611 191535801675413934940128917)
          ·
            refine ⟨8978240703535028200318543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 191535801675413934940128917 8978240703535028200318543)
            ·
              refine ⟨13467361055302542300477815, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8978240703535028200318543 13467361055302542300477815)
              ·
                refine ⟨20201041582953813450716723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13467361055302542300477815 20201041582953813450716723)
                ·
                  refine ⟨30301562374430720176075085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20201041582953813450716723 30301562374430720176075085)
                  ·
                    refine ⟨11363085890411520066028157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 30301562374430720176075085 11363085890411520066028157)
                    ·
                      refine ⟨4261157208904320024760559, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11363085890411520066028157 4261157208904320024760559)
                      ·
                        rfl

theorem cell23_8298574_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 6, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 6, 1, 1, 1, 3, 3].length) (baseStart_8298574 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8298574 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8298574 prefixEnd_8298574 := by exact prefixLift 8298574
  have htrace : WordTrace (prefixWord ++ tailWord_8298574) baseStart_8298574 baseEnd_8298574 := by
    simpa [prefixWord, tailWord_8298574, baseEnd_8298574] using wordTrace_append hprefix tailTrace_8298574
  have hstable : (prefixWord ++ tailWord_8298574).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8298574).length < 2 ^ (prefixWord ++ tailWord_8298574).sum := by decide
  have hdescent : baseEnd_8298574 < baseStart_8298574 := by decide
  rcases family_descends (prefixWord ++ tailWord_8298574) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8298584 : List Nat := [2, 1, 2, 2, 1, 4, 1, 4, 1, 3, 2]
def baseStart_8298584 : Nat := 118140960795 + 8298584 * 2 ^ 59
def prefixEnd_8298584 : Nat := 4983230072969 + 3 ^ 40 * 8298584 * 2
def baseEnd_8298584 : Nat := 4261162343710864985635513

theorem tailTrace_8298584 : CollatzResearch.WordTrace tailWord_8298584 prefixEnd_8298584 4261162343710864985635513 := by
  unfold tailWord_8298584
  simp only [CollatzResearch.WordTrace]
  refine ⟨151337112083827464078231403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 201782816111769952104308537 151337112083827464078231403)
  ·
    refine ⟨227005668125741196117347105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151337112083827464078231403 227005668125741196117347105)
    ·
      refine ⟨170254251094305897088010329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 227005668125741196117347105 170254251094305897088010329)
      ·
        refine ⟨127690688320729422816007747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 170254251094305897088010329 127690688320729422816007747)
        ·
          refine ⟨191536032481094134224011621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 127690688320729422816007747 191536032481094134224011621)
          ·
            refine ⟨35913006090205150167002179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 191536032481094134224011621 35913006090205150167002179)
            ·
              refine ⟨53869509135307725250503269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35913006090205150167002179 53869509135307725250503269)
              ·
                refine ⟨10100532962870198484469363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 53869509135307725250503269 10100532962870198484469363)
                ·
                  refine ⟨15150799444305297726704045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10100532962870198484469363 15150799444305297726704045)
                  ·
                    refine ⟨5681549791614486647514017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15150799444305297726704045 5681549791614486647514017)
                    ·
                      refine ⟨4261162343710864985635513, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5681549791614486647514017 4261162343710864985635513)
                      ·
                        rfl

theorem cell23_8298584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 4, 1, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 4, 1, 4, 1, 3, 2].length) (baseStart_8298584 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8298584 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8298584 prefixEnd_8298584 := by exact prefixLift 8298584
  have htrace : WordTrace (prefixWord ++ tailWord_8298584) baseStart_8298584 baseEnd_8298584 := by
    simpa [prefixWord, tailWord_8298584, baseEnd_8298584] using wordTrace_append hprefix tailTrace_8298584
  have hstable : (prefixWord ++ tailWord_8298584).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8298584).length < 2 ^ (prefixWord ++ tailWord_8298584).sum := by decide
  have hdescent : baseEnd_8298584 < baseStart_8298584 := by decide
  rcases family_descends (prefixWord ++ tailWord_8298584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8298625 : List Nat := [1, 2, 4, 2, 4, 1, 2, 1, 2, 1, 3]
def baseStart_8298625 : Nat := 118140960795 + 8298625 * 2 ^ 59
def prefixEnd_8298625 : Nat := 4983230072969 + 3 ^ 40 * 8298625 * 2
def baseEnd_8298625 : Nat := 4261183396417699325222825

theorem tailTrace_8298625 : CollatzResearch.WordTrace tailWord_8298625 prefixEnd_8298625 4261183396417699325222825 := by
  unfold tailWord_8298625
  simp only [CollatzResearch.WordTrace]
  refine ⟨302675719560506392158705329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201783813040337594772470219 302675719560506392158705329)
  ·
    refine ⟨227006789670379794119028997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 302675719560506392158705329 227006789670379794119028997)
    ·
      refine ⟨42563773063196211397317937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 227006789670379794119028997 42563773063196211397317937)
      ·
        refine ⟨31922829797397158547988453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42563773063196211397317937 31922829797397158547988453)
        ·
          refine ⟨5985530587011967227747835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 31922829797397158547988453 5985530587011967227747835)
          ·
            refine ⟨8978295880517950841621753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5985530587011967227747835 8978295880517950841621753)
            ·
              refine ⟨6733721910388463131216315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8978295880517950841621753 6733721910388463131216315)
              ·
                refine ⟨10100582865582694696824473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6733721910388463131216315 10100582865582694696824473)
                ·
                  refine ⟨7575437149187021022618355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10100582865582694696824473 7575437149187021022618355)
                  ·
                    refine ⟨11363155723780531533927533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7575437149187021022618355 11363155723780531533927533)
                    ·
                      refine ⟨4261183396417699325222825, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11363155723780531533927533 4261183396417699325222825)
                      ·
                        rfl

theorem cell23_8298625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 4, 1, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 4, 1, 2, 1, 2, 1, 3].length) (baseStart_8298625 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8298625 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8298625 prefixEnd_8298625 := by exact prefixLift 8298625
  have htrace : WordTrace (prefixWord ++ tailWord_8298625) baseStart_8298625 baseEnd_8298625 := by
    simpa [prefixWord, tailWord_8298625, baseEnd_8298625] using wordTrace_append hprefix tailTrace_8298625
  have hstable : (prefixWord ++ tailWord_8298625).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8298625).length < 2 ^ (prefixWord ++ tailWord_8298625).sum := by decide
  have hdescent : baseEnd_8298625 < baseStart_8298625 := by decide
  rcases family_descends (prefixWord ++ tailWord_8298625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8298764 : List Nat := [2, 2, 1, 2, 2, 2, 1, 3, 1, 5, 2]
def baseStart_8298764 : Nat := 118140960795 + 8298764 * 2 ^ 59
def prefixEnd_8298764 : Nat := 4983230072969 + 3 ^ 40 * 8298764 * 2
def baseEnd_8298764 : Nat := 4261254770228674281384685

theorem tailTrace_8298764 : CollatzResearch.WordTrace tailWord_8298764 prefixEnd_8298764 4261254770228674281384685 := by
  unfold tailWord_8298764
  simp only [CollatzResearch.WordTrace]
  refine ⟨151340394653501409449007673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 201787192871335212598676897 151340394653501409449007673)
  ·
    refine ⟨113505295990126057086755755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 151340394653501409449007673 113505295990126057086755755)
    ·
      refine ⟨170257943985189085630133633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113505295990126057086755755 170257943985189085630133633)
      ·
        refine ⟨127693457988891814222600225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 170257943985189085630133633 127693457988891814222600225)
        ·
          refine ⟨95770093491668860666950169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 127693457988891814222600225 95770093491668860666950169)
          ·
            refine ⟨71827570118751645500212627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 95770093491668860666950169 71827570118751645500212627)
            ·
              refine ⟨107741355178127468250318941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71827570118751645500212627 107741355178127468250318941)
              ·
                refine ⟨40403008191797800593869603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 107741355178127468250318941 40403008191797800593869603)
                ·
                  refine ⟨60604512287696700890804405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40403008191797800593869603 60604512287696700890804405)
                  ·
                    refine ⟨5681673026971565708512913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 60604512287696700890804405 5681673026971565708512913)
                    ·
                      refine ⟨4261254770228674281384685, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5681673026971565708512913 4261254770228674281384685)
                      ·
                        rfl

theorem cell23_8298764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 1, 3, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 1, 3, 1, 5, 2].length) (baseStart_8298764 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8298764 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8298764 prefixEnd_8298764 := by exact prefixLift 8298764
  have htrace : WordTrace (prefixWord ++ tailWord_8298764) baseStart_8298764 baseEnd_8298764 := by
    simpa [prefixWord, tailWord_8298764, baseEnd_8298764] using wordTrace_append hprefix tailTrace_8298764
  have hstable : (prefixWord ++ tailWord_8298764).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8298764).length < 2 ^ (prefixWord ++ tailWord_8298764).sum := by decide
  have hdescent : baseEnd_8298764 < baseStart_8298764 := by decide
  rcases family_descends (prefixWord ++ tailWord_8298764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8298782 : List Nat := [4, 3, 2, 1, 1, 2, 3, 2, 1, 4]
def baseStart_8298782 : Nat := 118140960795 + 8298782 * 2 ^ 59
def prefixEnd_8298782 : Nat := 4983230072969 + 3 ^ 40 * 8298782 * 2
def baseEnd_8298782 : Nat := 1420421337626818403653201

theorem tailTrace_8298782 : CollatzResearch.WordTrace tailWord_8298782 prefixEnd_8298782 1420421337626818403653201 := by
  unfold tailWord_8298782
  simp only [CollatzResearch.WordTrace]
  refine ⟨37835180727617200996521325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 201787630547291738648113733 37835180727617200996521325)
  ·
    refine ⟨14188192772856450373695497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37835180727617200996521325 14188192772856450373695497)
    ·
      refine ⟨10641144579642337780271623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14188192772856450373695497 10641144579642337780271623)
      ·
        refine ⟨15961716869463506670407435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10641144579642337780271623 15961716869463506670407435)
        ·
          refine ⟨23942575304195260005611153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15961716869463506670407435 23942575304195260005611153)
          ·
            refine ⟨17956931478146445004208365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23942575304195260005611153 17956931478146445004208365)
            ·
              refine ⟨6733849304304916876578137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17956931478146445004208365 6733849304304916876578137)
              ·
                refine ⟨5050386978228687657433603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6733849304304916876578137 5050386978228687657433603)
                ·
                  refine ⟨7575580467343031486150405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5050386978228687657433603 7575580467343031486150405)
                  ·
                    refine ⟨1420421337626818403653201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7575580467343031486150405 1420421337626818403653201)
                    ·
                      rfl

theorem cell23_8298782_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 2, 3, 2, 1, 4].length) (baseStart_8298782 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8298782 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8298782 prefixEnd_8298782 := by exact prefixLift 8298782
  have htrace : WordTrace (prefixWord ++ tailWord_8298782) baseStart_8298782 baseEnd_8298782 := by
    simpa [prefixWord, tailWord_8298782, baseEnd_8298782] using wordTrace_append hprefix tailTrace_8298782
  have hstable : (prefixWord ++ tailWord_8298782).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8298782).length < 2 ^ (prefixWord ++ tailWord_8298782).sum := by decide
  have hdescent : baseEnd_8298782 < baseStart_8298782 := by decide
  rcases family_descends (prefixWord ++ tailWord_8298782) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8298788 : List Nat := [2, 3, 1, 3, 1, 4, 1, 1, 3, 1, 3]
def baseStart_8298788 : Nat := 118140960795 + 8298788 * 2 ^ 59
def prefixEnd_8298788 : Nat := 4983230072969 + 3 ^ 40 * 8298788 * 2
def baseEnd_8298788 : Nat := 4261267093764382187484575

theorem tailTrace_8298788 : CollatzResearch.WordTrace tailWord_8298788 prefixEnd_8298788 4261267093764382187484575 := by
  unfold tailWord_8298788
  simp only [CollatzResearch.WordTrace]
  refine ⟨151340832329457935498444509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 201787776439277247331259345 151340832329457935498444509)
  ·
    refine ⟨56752812123546725811916691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 151340832329457935498444509 56752812123546725811916691)
    ·
      refine ⟨85129218185320088717875037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56752812123546725811916691 85129218185320088717875037)
      ·
        refine ⟨31923456819495033269203139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 85129218185320088717875037 31923456819495033269203139)
        ·
          refine ⟨47885185229242549903804709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31923456819495033269203139 47885185229242549903804709)
          ·
            refine ⟨8978472230482978106963383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 47885185229242549903804709 8978472230482978106963383)
            ·
              refine ⟨13467708345724467160445075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8978472230482978106963383 13467708345724467160445075)
              ·
                refine ⟨20201562518586700740667613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13467708345724467160445075 20201562518586700740667613)
                ·
                  refine ⟨7575585944470012777750355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20201562518586700740667613 7575585944470012777750355)
                  ·
                    refine ⟨11363378916705019166625533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7575585944470012777750355 11363378916705019166625533)
                    ·
                      refine ⟨4261267093764382187484575, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11363378916705019166625533 4261267093764382187484575)
                      ·
                        rfl

theorem cell23_8298788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 4, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 4, 1, 1, 3, 1, 3].length) (baseStart_8298788 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8298788 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8298788 prefixEnd_8298788 := by exact prefixLift 8298788
  have htrace : WordTrace (prefixWord ++ tailWord_8298788) baseStart_8298788 baseEnd_8298788 := by
    simpa [prefixWord, tailWord_8298788, baseEnd_8298788] using wordTrace_append hprefix tailTrace_8298788
  have hstable : (prefixWord ++ tailWord_8298788).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8298788).length < 2 ^ (prefixWord ++ tailWord_8298788).sum := by decide
  have hdescent : baseEnd_8298788 < baseStart_8298788 := by decide
  rcases family_descends (prefixWord ++ tailWord_8298788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8298807 : List Nat := [1, 1, 3, 1, 2, 1, 1, 2, 5, 2, 4]
def baseStart_8298807 : Nat := 118140960795 + 8298807 * 2 ^ 59
def prefixEnd_8298807 : Nat := 4983230072969 + 3 ^ 40 * 8298807 * 2
def baseEnd_8298807 : Nat := 4261276849896817613146987

theorem tailTrace_8298807 : CollatzResearch.WordTrace tailWord_8298807 prefixEnd_8298807 4261276849896817613146987 := by
  unfold tailWord_8298807
  simp only [CollatzResearch.WordTrace]
  refine ⟨302682357645847037241830675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201788238430564691494553783 302682357645847037241830675)
  ·
    refine ⟨454023536468770555862746013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 302682357645847037241830675 454023536468770555862746013)
    ·
      refine ⟨170258826175788958448529755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 454023536468770555862746013 170258826175788958448529755)
      ·
        refine ⟨255388239263683437672794633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 170258826175788958448529755 255388239263683437672794633)
        ·
          refine ⟨191541179447762578254595975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 255388239263683437672794633 191541179447762578254595975)
          ·
            refine ⟨287311769171643867381893963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 191541179447762578254595975 287311769171643867381893963)
            ·
              refine ⟨430967653757465801072840945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 287311769171643867381893963 430967653757465801072840945)
              ·
                refine ⟨323225740318099350804630709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 430967653757465801072840945 323225740318099350804630709)
                ·
                  refine ⟨30302413154821814137934129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 323225740318099350804630709 30302413154821814137934129)
                  ·
                    refine ⟨22726809866116360603450597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 30302413154821814137934129 22726809866116360603450597)
                    ·
                      refine ⟨4261276849896817613146987, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22726809866116360603450597 4261276849896817613146987)
                      ·
                        rfl

theorem cell23_8298807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 1, 2, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 1, 2, 5, 2, 4].length) (baseStart_8298807 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8298807 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8298807 prefixEnd_8298807 := by exact prefixLift 8298807
  have htrace : WordTrace (prefixWord ++ tailWord_8298807) baseStart_8298807 baseEnd_8298807 := by
    simpa [prefixWord, tailWord_8298807, baseEnd_8298807] using wordTrace_append hprefix tailTrace_8298807
  have hstable : (prefixWord ++ tailWord_8298807).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8298807).length < 2 ^ (prefixWord ++ tailWord_8298807).sum := by decide
  have hdescent : baseEnd_8298807 < baseStart_8298807 := by decide
  rcases family_descends (prefixWord ++ tailWord_8298807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8298847 : List Nat := [1, 1, 2, 3, 1, 2, 3, 1, 2, 7]
def baseStart_8298847 : Nat := 118140960795 + 8298847 * 2 ^ 59
def prefixEnd_8298847 : Nat := 4983230072969 + 3 ^ 40 * 8298847 * 2
def baseEnd_8298847 : Nat := 1420432463040999152215601

theorem tailTrace_8298847 : CollatzResearch.WordTrace tailWord_8298847 prefixEnd_8298847 1420432463040999152215601 := by
  unfold tailWord_8298847
  simp only [CollatzResearch.WordTrace]
  refine ⟨302683816565702124073286795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201789211043801416048857863 302683816565702124073286795)
  ·
    refine ⟨454025724848553186109930193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 302683816565702124073286795 454025724848553186109930193)
    ·
      refine ⟨340519293636414889582447645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 454025724848553186109930193 340519293636414889582447645)
      ·
        refine ⟨127694735113655583593417867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 340519293636414889582447645 127694735113655583593417867)
        ·
          refine ⟨191542102670483375390126801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 127694735113655583593417867 191542102670483375390126801)
          ·
            refine ⟨143656577002862531542595101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 191542102670483375390126801 143656577002862531542595101)
            ·
              refine ⟨53871216376073449328473163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 143656577002862531542595101 53871216376073449328473163)
              ·
                refine ⟨80806824564110173992709745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53871216376073449328473163 80806824564110173992709745)
                ·
                  refine ⟨60605118423082630494532309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 80806824564110173992709745 60605118423082630494532309)
                  ·
                    refine ⟨1420432463040999152215601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 60605118423082630494532309 1420432463040999152215601)
                    ·
                      rfl

theorem cell23_8298847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 3, 1, 2, 7].length) (baseStart_8298847 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8298847 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8298847 prefixEnd_8298847 := by exact prefixLift 8298847
  have htrace : WordTrace (prefixWord ++ tailWord_8298847) baseStart_8298847 baseEnd_8298847 := by
    simpa [prefixWord, tailWord_8298847, baseEnd_8298847] using wordTrace_append hprefix tailTrace_8298847
  have hstable : (prefixWord ++ tailWord_8298847).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8298847).length < 2 ^ (prefixWord ++ tailWord_8298847).sum := by decide
  have hdescent : baseEnd_8298847 < baseStart_8298847 := by decide
  rcases family_descends (prefixWord ++ tailWord_8298847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8298861 : List Nat := [1, 5, 1, 1, 1, 2, 4, 1, 1, 3, 3]
def baseStart_8298861 : Nat := 118140960795 + 8298861 * 2 ^ 59
def prefixEnd_8298861 : Nat := 4983230072969 + 3 ^ 40 * 8298861 * 2
def baseEnd_8298861 : Nat := 4261304577852160401871739

theorem tailTrace_8298861 : CollatzResearch.WordTrace tailWord_8298861 prefixEnd_8298861 4261304577852160401871739 := by
  unfold tailWord_8298861
  simp only [CollatzResearch.WordTrace]
  refine ⟨302684327187651404464296437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201789551458434269642864291 302684327187651404464296437)
  ·
    refine ⟨28376655673842319168527791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 302684327187651404464296437 28376655673842319168527791)
    ·
      refine ⟨42564983510763478752791687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28376655673842319168527791 42564983510763478752791687)
      ·
        refine ⟨63847475266145218129187531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42564983510763478752791687 63847475266145218129187531)
        ·
          refine ⟨95771212899217827193781297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63847475266145218129187531 95771212899217827193781297)
          ·
            refine ⟨71828409674413370395335973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 95771212899217827193781297 71828409674413370395335973)
            ·
              refine ⟨13467826813952506949125495, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 71828409674413370395335973 13467826813952506949125495)
              ·
                refine ⟨20201740220928760423688243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13467826813952506949125495 20201740220928760423688243)
                ·
                  refine ⟨30302610331393140635532365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20201740220928760423688243 30302610331393140635532365)
                  ·
                    refine ⟨11363478874272427738324637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 30302610331393140635532365 11363478874272427738324637)
                    ·
                      refine ⟨4261304577852160401871739, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11363478874272427738324637 4261304577852160401871739)
                      ·
                        rfl

theorem cell23_8298861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 4, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 4, 1, 1, 3, 3].length) (baseStart_8298861 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8298861 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8298861 prefixEnd_8298861 := by exact prefixLift 8298861
  have htrace : WordTrace (prefixWord ++ tailWord_8298861) baseStart_8298861 baseEnd_8298861 := by
    simpa [prefixWord, tailWord_8298861, baseEnd_8298861] using wordTrace_append hprefix tailTrace_8298861
  have hstable : (prefixWord ++ tailWord_8298861).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8298861).length < 2 ^ (prefixWord ++ tailWord_8298861).sum := by decide
  have hdescent : baseEnd_8298861 < baseStart_8298861 := by decide
  rcases family_descends (prefixWord ++ tailWord_8298861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8298888 : List Nat := [2, 1, 3, 3, 1, 1, 3, 3, 1, 3, 2]
def baseStart_8298888 : Nat := 118140960795 + 8298888 * 2 ^ 59
def prefixEnd_8298888 : Nat := 4983230072969 + 3 ^ 40 * 8298888 * 2
def baseEnd_8298888 : Nat := 4261318441829831796234115

theorem tailTrace_8298888 : CollatzResearch.WordTrace tailWord_8298888 prefixEnd_8298888 4261318441829831796234115 := by
  unfold tailWord_8298888
  simp only [CollatzResearch.WordTrace]
  refine ⟨151342655979276794037764659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 201790207972369058717019545 151342655979276794037764659)
  ·
    refine ⟨227013983968915191056646989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151342655979276794037764659 227013983968915191056646989)
    ·
      refine ⟨85130243988343196646242621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 227013983968915191056646989 85130243988343196646242621)
      ·
        refine ⟨31923841495628698742340983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 85130243988343196646242621 31923841495628698742340983)
        ·
          refine ⟨47885762243443048113511475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31923841495628698742340983 47885762243443048113511475)
          ·
            refine ⟨71828643365164572170267213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47885762243443048113511475 71828643365164572170267213)
            ·
              refine ⟨26935741261936714563850205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 71828643365164572170267213 26935741261936714563850205)
              ·
                refine ⟨10100902973226267961443827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26935741261936714563850205 10100902973226267961443827)
                ·
                  refine ⟨15151354459839401942165741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10100902973226267961443827 15151354459839401942165741)
                  ·
                    refine ⟨5681757922439775728312153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15151354459839401942165741 5681757922439775728312153)
                    ·
                      refine ⟨4261318441829831796234115, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5681757922439775728312153 4261318441829831796234115)
                      ·
                        rfl

theorem cell23_8298888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 3, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 3, 3, 1, 3, 2].length) (baseStart_8298888 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8298888 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8298888 prefixEnd_8298888 := by exact prefixLift 8298888
  have htrace : WordTrace (prefixWord ++ tailWord_8298888) baseStart_8298888 baseEnd_8298888 := by
    simpa [prefixWord, tailWord_8298888, baseEnd_8298888] using wordTrace_append hprefix tailTrace_8298888
  have hstable : (prefixWord ++ tailWord_8298888).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8298888).length < 2 ^ (prefixWord ++ tailWord_8298888).sum := by decide
  have hdescent : baseEnd_8298888 < baseStart_8298888 := by decide
  rcases family_descends (prefixWord ++ tailWord_8298888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8298897 : List Nat := [1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 6]
def baseStart_8298897 : Nat := 118140960795 + 8298897 * 2 ^ 59
def prefixEnd_8298897 : Nat := 4983230072969 + 3 ^ 40 * 8298897 * 2
def baseEnd_8298897 : Nat := 4261323063155722261021573

theorem tailTrace_8298897 : CollatzResearch.WordTrace tailWord_8298897 prefixEnd_8298897 4261323063155722261021573 := by
  unfold tailWord_8298897
  simp only [CollatzResearch.WordTrace]
  refine ⟨302685640215520982612606945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201790426810347321741737963 302685640215520982612606945)
  ·
    refine ⟨227014230161640736959455209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 302685640215520982612606945 227014230161640736959455209)
    ·
      refine ⟨170260672621230552719591407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 227014230161640736959455209 170260672621230552719591407)
      ·
        refine ⟨255391008931845829079387111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 170260672621230552719591407 255391008931845829079387111)
        ·
          refine ⟨383086513397768743619080667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 255391008931845829079387111 383086513397768743619080667)
          ·
            refine ⟨574629770096653115428621001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 383086513397768743619080667 574629770096653115428621001)
            ·
              refine ⟨430972327572489836571465751, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 574629770096653115428621001 430972327572489836571465751)
              ·
                refine ⟨646458491358734754857198627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 430972327572489836571465751 646458491358734754857198627)
                ·
                  refine ⟨969687737038102132285797941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 646458491358734754857198627 969687737038102132285797941)
                  ·
                    refine ⟨90908225347322074901793557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 969687737038102132285797941 90908225347322074901793557)
                    ·
                      refine ⟨4261323063155722261021573, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 90908225347322074901793557 4261323063155722261021573)
                      ·
                        rfl

theorem cell23_8298897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 6].length) (baseStart_8298897 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8298897 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8298897 prefixEnd_8298897 := by exact prefixLift 8298897
  have htrace : WordTrace (prefixWord ++ tailWord_8298897) baseStart_8298897 baseEnd_8298897 := by
    simpa [prefixWord, tailWord_8298897, baseEnd_8298897] using wordTrace_append hprefix tailTrace_8298897
  have hstable : (prefixWord ++ tailWord_8298897).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8298897).length < 2 ^ (prefixWord ++ tailWord_8298897).sum := by decide
  have hdescent : baseEnd_8298897 < baseStart_8298897 := by decide
  rcases family_descends (prefixWord ++ tailWord_8298897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8298991 : List Nat := [1, 1, 2, 1, 4, 1, 1, 2, 4, 4, 2]
def baseStart_8298991 : Nat := 118140960795 + 8298991 * 2 ^ 59
def prefixEnd_8298991 : Nat := 4983230072969 + 3 ^ 40 * 8298991 * 2
def baseEnd_8298991 : Nat := 4261371330337244893246141

theorem tailTrace_8298991 : CollatzResearch.WordTrace tailWord_8298991 prefixEnd_8298991 4261371330337244893246141 := by
  unfold tailWord_8298991
  simp only [CollatzResearch.WordTrace]
  refine ⟨302689068677180436666528827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201792712451453624444352551 302689068677180436666528827)
  ·
    refine ⟨454033603015770654999793241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 302689068677180436666528827 454033603015770654999793241)
    ·
      refine ⟨340525202261827991249844931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 454033603015770654999793241 340525202261827991249844931)
      ·
        refine ⟨510787803392741986874767397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 340525202261827991249844931 510787803392741986874767397)
        ·
          refine ⟨95772713136139122539018887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 510787803392741986874767397 95772713136139122539018887)
          ·
            refine ⟨143659069704208683808528331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 95772713136139122539018887 143659069704208683808528331)
            ·
              refine ⟨215488604556313025712792497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 143659069704208683808528331 215488604556313025712792497)
              ·
                refine ⟨161616453417234769284594373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 215488604556313025712792497 161616453417234769284594373)
                ·
                  refine ⟨30303085015731519240861445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 161616453417234769284594373 30303085015731519240861445)
                  ·
                    refine ⟨5681828440449659857661521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 30303085015731519240861445 5681828440449659857661521)
                    ·
                      refine ⟨4261371330337244893246141, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5681828440449659857661521 4261371330337244893246141)
                      ·
                        rfl

theorem cell23_8298991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 1, 2, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 1, 2, 4, 4, 2].length) (baseStart_8298991 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8298991 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8298991 prefixEnd_8298991 := by exact prefixLift 8298991
  have htrace : WordTrace (prefixWord ++ tailWord_8298991) baseStart_8298991 baseEnd_8298991 := by
    simpa [prefixWord, tailWord_8298991, baseEnd_8298991] using wordTrace_append hprefix tailTrace_8298991
  have hstable : (prefixWord ++ tailWord_8298991).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8298991).length < 2 ^ (prefixWord ++ tailWord_8298991).sum := by decide
  have hdescent : baseEnd_8298991 < baseStart_8298991 := by decide
  rcases family_descends (prefixWord ++ tailWord_8298991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8299004 : List Nat := [2, 2, 2, 1, 2, 1, 1, 3, 2, 1, 6]
def baseStart_8299004 : Nat := 118140960795 + 8299004 * 2 ^ 59
def prefixEnd_8299004 : Nat := 4983230072969 + 3 ^ 40 * 8299004 * 2
def baseEnd_8299004 : Nat := 4261378005585753342383581

theorem tailTrace_8299004 : CollatzResearch.WordTrace tailWord_8299004 prefixEnd_8299004 4261378005585753342383581 := by
  unfold tailWord_8299004
  simp only [CollatzResearch.WordTrace]
  refine ⟨151344771413066669943376033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 201793028550755559924501377 151344771413066669943376033)
  ·
    refine ⟨113508578559800002457532025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 151344771413066669943376033 113508578559800002457532025)
    ·
      refine ⟨85131433919850001843149019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 113508578559800002457532025 85131433919850001843149019)
      ·
        refine ⟨127697150879775002764723529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85131433919850001843149019 127697150879775002764723529)
        ·
          refine ⟨95772863159831252073542647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 127697150879775002764723529 95772863159831252073542647)
          ·
            refine ⟨143659294739746878110313971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 95772863159831252073542647 143659294739746878110313971)
            ·
              refine ⟨215488942109620317165470957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 143659294739746878110313971 215488942109620317165470957)
              ·
                refine ⟨80808353291107618937051609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 215488942109620317165470957 80808353291107618937051609)
                ·
                  refine ⟨60606264968330714202788707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 80808353291107618937051609 60606264968330714202788707)
                  ·
                    refine ⟨90909397452496071304183061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 60606264968330714202788707 90909397452496071304183061)
                    ·
                      refine ⟨4261378005585753342383581, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 90909397452496071304183061 4261378005585753342383581)
                      ·
                        rfl

theorem cell23_8299004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 1, 3, 2, 1, 6].length) (baseStart_8299004 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8299004 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8299004 prefixEnd_8299004 := by exact prefixLift 8299004
  have htrace : WordTrace (prefixWord ++ tailWord_8299004) baseStart_8299004 baseEnd_8299004 := by
    simpa [prefixWord, tailWord_8299004, baseEnd_8299004] using wordTrace_append hprefix tailTrace_8299004
  have hstable : (prefixWord ++ tailWord_8299004).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8299004).length < 2 ^ (prefixWord ++ tailWord_8299004).sum := by decide
  have hdescent : baseEnd_8299004 < baseStart_8299004 := by decide
  rcases family_descends (prefixWord ++ tailWord_8299004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8299011 : List Nat := [1, 1, 1, 3, 2, 1, 3, 4, 2, 2, 3]
def baseStart_8299011 : Nat := 118140960795 + 8299011 * 2 ^ 59
def prefixEnd_8299011 : Nat := 4983230072969 + 3 ^ 40 * 8299011 * 2
def baseEnd_8299011 : Nat := 4261381599950334814996049

theorem tailTrace_8299011 : CollatzResearch.WordTrace tailWord_8299011 prefixEnd_8299011 4261381599950334814996049 := by
  unfold tailWord_8299011
  simp only [CollatzResearch.WordTrace]
  refine ⟨302689798137107980082256887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201793198758071986721504591 302689798137107980082256887)
  ·
    refine ⟨454034697205661970123385331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 302689798137107980082256887 454034697205661970123385331)
    ·
      refine ⟨681052045808492955185077997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 454034697205661970123385331 681052045808492955185077997)
      ·
        refine ⟨255394517178184858194404249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 681052045808492955185077997 255394517178184858194404249)
        ·
          refine ⟨191545887883638643645803187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 255394517178184858194404249 191545887883638643645803187)
          ·
            refine ⟨287318831825457965468704781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 191545887883638643645803187 287318831825457965468704781)
            ·
              refine ⟨107744561934546737050764293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 287318831825457965468704781 107744561934546737050764293)
              ·
                refine ⟨20202105362727513197018305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 107744561934546737050764293 20202105362727513197018305)
                ·
                  refine ⟨15151579022045634897763729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20202105362727513197018305 15151579022045634897763729)
                  ·
                    refine ⟨11363684266534226173322797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15151579022045634897763729 11363684266534226173322797)
                    ·
                      refine ⟨4261381599950334814996049, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11363684266534226173322797 4261381599950334814996049)
                      ·
                        rfl

theorem cell23_8299011_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 3, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 3, 4, 2, 2, 3].length) (baseStart_8299011 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8299011 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8299011 prefixEnd_8299011 := by exact prefixLift 8299011
  have htrace : WordTrace (prefixWord ++ tailWord_8299011) baseStart_8299011 baseEnd_8299011 := by
    simpa [prefixWord, tailWord_8299011, baseEnd_8299011] using wordTrace_append hprefix tailTrace_8299011
  have hstable : (prefixWord ++ tailWord_8299011).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8299011).length < 2 ^ (prefixWord ++ tailWord_8299011).sum := by decide
  have hdescent : baseEnd_8299011 < baseStart_8299011 := by decide
  rcases family_descends (prefixWord ++ tailWord_8299011) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8299085 : List Nat := [1, 6, 1, 1, 2, 1, 1, 2, 1, 5, 2]
def baseStart_8299085 : Nat := 118140960795 + 8299085 * 2 ^ 59
def prefixEnd_8299085 : Nat := 4983230072969 + 3 ^ 40 * 8299085 * 2
def baseEnd_8299085 : Nat := 4261419597518767525470709

theorem tailTrace_8299085 : CollatzResearch.WordTrace tailWord_8299085 prefixEnd_8299085 4261419597518767525470709 := by
  unfold tailWord_8299085
  simp only [CollatzResearch.WordTrace]
  refine ⟨302692497138839890720450709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201794998092559927146967139 302692497138839890720450709)
  ·
    refine ⟨14188710803383119877521127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 302692497138839890720450709 14188710803383119877521127)
    ·
      refine ⟨21283066205074679816281691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14188710803383119877521127 21283066205074679816281691)
      ·
        refine ⟨31924599307612019724422537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21283066205074679816281691 31924599307612019724422537)
        ·
          refine ⟨23943449480709014793316903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31924599307612019724422537 23943449480709014793316903)
          ·
            refine ⟨35915174221063522189975355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23943449480709014793316903 35915174221063522189975355)
            ·
              refine ⟨53872761331595283284963033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35915174221063522189975355 53872761331595283284963033)
              ·
                refine ⟨40404570998696462463722275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53872761331595283284963033 40404570998696462463722275)
                ·
                  refine ⟨60606856498044693695583413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40404570998696462463722275 60606856498044693695583413)
                  ·
                    refine ⟨5681892796691690033960945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 60606856498044693695583413 5681892796691690033960945)
                    ·
                      refine ⟨4261419597518767525470709, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5681892796691690033960945 4261419597518767525470709)
                      ·
                        rfl

theorem cell23_8299085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 1, 1, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 1, 1, 2, 1, 5, 2].length) (baseStart_8299085 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8299085 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8299085 prefixEnd_8299085 := by exact prefixLift 8299085
  have htrace : WordTrace (prefixWord ++ tailWord_8299085) baseStart_8299085 baseEnd_8299085 := by
    simpa [prefixWord, tailWord_8299085, baseEnd_8299085] using wordTrace_append hprefix tailTrace_8299085
  have hstable : (prefixWord ++ tailWord_8299085).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8299085).length < 2 ^ (prefixWord ++ tailWord_8299085).sum := by decide
  have hdescent : baseEnd_8299085 < baseStart_8299085 := by decide
  rcases family_descends (prefixWord ++ tailWord_8299085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8299109 : List Nat := [1, 3, 1, 3, 4, 2, 1, 3, 1, 1, 3]
def baseStart_8299109 : Nat := 118140960795 + 8299109 * 2 ^ 59
def prefixEnd_8299109 : Nat := 4983230072969 + 3 ^ 40 * 8299109 * 2
def baseEnd_8299109 : Nat := 4261431921054475431570599

theorem tailTrace_8299109 : CollatzResearch.WordTrace tailWord_8299109 prefixEnd_8299109 4261431921054475431570599 := by
  unfold tailWord_8299109
  simp only [CollatzResearch.WordTrace]
  refine ⟨302693372490752942819324381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201795581660501961879549587 302693372490752942819324381)
  ·
    refine ⟨113510014684032353557246643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 302693372490752942819324381 113510014684032353557246643)
    ·
      refine ⟨170265022026048530335869965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113510014684032353557246643 170265022026048530335869965)
      ·
        refine ⟨63849383259768198875951237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 170265022026048530335869965 63849383259768198875951237)
        ·
          refine ⟨11971759361206537289240857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 63849383259768198875951237 11971759361206537289240857)
          ·
            refine ⟨8978819520904902966930643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11971759361206537289240857 8978819520904902966930643)
            ·
              refine ⟨13468229281357354450395965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8978819520904902966930643 13468229281357354450395965)
              ·
                refine ⟨5050585980509007918898487, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13468229281357354450395965 5050585980509007918898487)
                ·
                  refine ⟨7575878970763511878347731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5050585980509007918898487 7575878970763511878347731)
                  ·
                    refine ⟨11363818456145267817521597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7575878970763511878347731 11363818456145267817521597)
                    ·
                      refine ⟨4261431921054475431570599, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11363818456145267817521597 4261431921054475431570599)
                      ·
                        rfl

theorem cell23_8299109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 4, 2, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 4, 2, 1, 3, 1, 1, 3].length) (baseStart_8299109 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8299109 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8299109 prefixEnd_8299109 := by exact prefixLift 8299109
  have htrace : WordTrace (prefixWord ++ tailWord_8299109) baseStart_8299109 baseEnd_8299109 := by
    simpa [prefixWord, tailWord_8299109, baseEnd_8299109] using wordTrace_append hprefix tailTrace_8299109
  have hstable : (prefixWord ++ tailWord_8299109).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8299109).length < 2 ^ (prefixWord ++ tailWord_8299109).sum := by decide
  have hdescent : baseEnd_8299109 < baseStart_8299109 := by decide
  rcases family_descends (prefixWord ++ tailWord_8299109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8299111 : List Nat := [1, 1, 5, 1, 1, 1, 1, 3, 3, 2, 4]
def baseStart_8299111 : Nat := 118140960795 + 8299111 * 2 ^ 59
def prefixEnd_8299111 : Nat := 4983230072969 + 3 ^ 40 * 8299111 * 2
def baseEnd_8299111 : Nat := 4261432948015784423745589

theorem tailTrace_8299111 : CollatzResearch.WordTrace tailWord_8299111 prefixEnd_8299111 4261432948015784423745589 := by
  unfold tailWord_8299111
  simp only [CollatzResearch.WordTrace]
  refine ⟨302693445436745697160897187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201795630291163798107264791 302693445436745697160897187)
  ·
    refine ⟨454040168155118545741345781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 302693445436745697160897187 454040168155118545741345781)
    ·
      refine ⟨42566265764542363663251167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 454040168155118545741345781 42566265764542363663251167)
      ·
        refine ⟨63849398646813545494876751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42566265764542363663251167 63849398646813545494876751)
        ·
          refine ⟨95774097970220318242315127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63849398646813545494876751 95774097970220318242315127)
          ·
            refine ⟨143661146955330477363472691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 95774097970220318242315127 143661146955330477363472691)
            ·
              refine ⟨215491720432995716045209037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 143661146955330477363472691 215491720432995716045209037)
              ·
                refine ⟨80809395162373393516953389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 215491720432995716045209037 80809395162373393516953389)
                ·
                  refine ⟨30303523185890022568857521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 80809395162373393516953389 30303523185890022568857521)
                  ·
                    refine ⟨22727642389417516926643141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 30303523185890022568857521 22727642389417516926643141)
                    ·
                      refine ⟨4261432948015784423745589, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22727642389417516926643141 4261432948015784423745589)
                      ·
                        rfl

theorem cell23_8299111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 1, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 1, 3, 3, 2, 4].length) (baseStart_8299111 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8299111 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8299111 prefixEnd_8299111 := by exact prefixLift 8299111
  have htrace : WordTrace (prefixWord ++ tailWord_8299111) baseStart_8299111 baseEnd_8299111 := by
    simpa [prefixWord, tailWord_8299111, baseEnd_8299111] using wordTrace_append hprefix tailTrace_8299111
  have hstable : (prefixWord ++ tailWord_8299111).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8299111).length < 2 ^ (prefixWord ++ tailWord_8299111).sum := by decide
  have hdescent : baseEnd_8299111 < baseStart_8299111 := by decide
  rcases family_descends (prefixWord ++ tailWord_8299111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8299118 : List Nat := [4, 1, 2, 2, 2, 1, 1, 3, 1, 1, 5]
def baseStart_8299118 : Nat := 118140960795 + 8299118 * 2 ^ 59
def prefixEnd_8299118 : Nat := 4983230072969 + 3 ^ 40 * 8299118 * 2
def baseEnd_8299118 : Nat := 4261436542380365896358057

theorem tailTrace_8299118 : CollatzResearch.WordTrace tailWord_8299118 prefixEnd_8299118 4261436542380365896358057 := by
  unfold tailWord_8299118
  simp only [CollatzResearch.WordTrace]
  refine ⟨37836712593465042169550251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 201795800498480224904268005 37836712593465042169550251)
  ·
    refine ⟨56755068890197563254325377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37836712593465042169550251 56755068890197563254325377)
    ·
      refine ⟨42566301667648172440744033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56755068890197563254325377 42566301667648172440744033)
      ·
        refine ⟨31924726250736129330558025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42566301667648172440744033 31924726250736129330558025)
        ·
          refine ⟨23943544688052096997918519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31924726250736129330558025 23943544688052096997918519)
          ·
            refine ⟨35915317032078145496877779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23943544688052096997918519 35915317032078145496877779)
            ·
              refine ⟨53872975548117218245316669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35915317032078145496877779 53872975548117218245316669)
              ·
                refine ⟨20202365830543956841993751, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 53872975548117218245316669 20202365830543956841993751)
                ·
                  refine ⟨30303548745815935262990627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20202365830543956841993751 30303548745815935262990627)
                  ·
                    refine ⟨45455323118723902894485941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 30303548745815935262990627 45455323118723902894485941)
                    ·
                      refine ⟨4261436542380365896358057, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 45455323118723902894485941 4261436542380365896358057)
                      ·
                        rfl

theorem cell23_8299118_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 1, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 1, 1, 3, 1, 1, 5].length) (baseStart_8299118 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8299118 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8299118 prefixEnd_8299118 := by exact prefixLift 8299118
  have htrace : WordTrace (prefixWord ++ tailWord_8299118) baseStart_8299118 baseEnd_8299118 := by
    simpa [prefixWord, tailWord_8299118, baseEnd_8299118] using wordTrace_append hprefix tailTrace_8299118
  have hstable : (prefixWord ++ tailWord_8299118).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8299118).length < 2 ^ (prefixWord ++ tailWord_8299118).sum := by decide
  have hdescent : baseEnd_8299118 < baseStart_8299118 := by decide
  rcases family_descends (prefixWord ++ tailWord_8299118) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8299126 : List Nat := [5, 1, 1, 2, 3, 1, 3, 2, 1, 1, 3]
def baseStart_8299126 : Nat := 118140960795 + 8299126 * 2 ^ 59
def prefixEnd_8299126 : Nat := 4983230072969 + 3 ^ 40 * 8299126 * 2
def baseEnd_8299126 : Nat := 4261440650225601865058021

theorem tailTrace_8299126 : CollatzResearch.WordTrace tailWord_8299126 prefixEnd_8299126 4261440650225601865058021 := by
  unfold tailWord_8299126
  simp only [CollatzResearch.WordTrace]
  refine ⟨18918374533230709670168327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 201795995021127569815128821 18918374533230709670168327)
  ·
    refine ⟨28377561799846064505252491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18918374533230709670168327 28377561799846064505252491)
    ·
      refine ⟨42566342699769096757878737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28377561799846064505252491 42566342699769096757878737)
      ·
        refine ⟨31924757024826822568409053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42566342699769096757878737 31924757024826822568409053)
        ·
          refine ⟨11971783884310058463153395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31924757024826822568409053 11971783884310058463153395)
          ·
            refine ⟨17957675826465087694730093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11971783884310058463153395 17957675826465087694730093)
            ·
              refine ⟨6734128434924407885523785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17957675826465087694730093 6734128434924407885523785)
              ·
                refine ⟨5050596326193305914142839, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6734128434924407885523785 5050596326193305914142839)
                ·
                  refine ⟨7575894489289958871214259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5050596326193305914142839 7575894489289958871214259)
                  ·
                    refine ⟨11363841733934938306821389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7575894489289958871214259 11363841733934938306821389)
                    ·
                      refine ⟨4261440650225601865058021, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11363841733934938306821389 4261440650225601865058021)
                      ·
                        rfl

theorem cell23_8299126_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 3, 1, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 3, 1, 3, 2, 1, 1, 3].length) (baseStart_8299126 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8299126 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8299126 prefixEnd_8299126 := by exact prefixLift 8299126
  have htrace : WordTrace (prefixWord ++ tailWord_8299126) baseStart_8299126 baseEnd_8299126 := by
    simpa [prefixWord, tailWord_8299126, baseEnd_8299126] using wordTrace_append hprefix tailTrace_8299126
  have hstable : (prefixWord ++ tailWord_8299126).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8299126).length < 2 ^ (prefixWord ++ tailWord_8299126).sum := by decide
  have hdescent : baseEnd_8299126 < baseStart_8299126 := by decide
  rcases family_descends (prefixWord ++ tailWord_8299126) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8299131 : List Nat := [1, 1, 1, 1, 1, 4, 2, 1, 5, 3, 3]
def baseStart_8299131 : Nat := 118140960795 + 8299131 * 2 ^ 59
def prefixEnd_8299131 : Nat := 4983230072969 + 3 ^ 40 * 8299131 * 2
def baseEnd_8299131 : Nat := 4261443217628874345495497

theorem tailTrace_8299131 : CollatzResearch.WordTrace tailWord_8299131 prefixEnd_8299131 4261443217628874345495497 := by
  unfold tailWord_8299131
  simp only [CollatzResearch.WordTrace]
  refine ⟨302694174896673240576625247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201796116597782160384416831 302694174896673240576625247)
  ·
    refine ⟨454041262345009860864937871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 302694174896673240576625247 454041262345009860864937871)
    ·
      refine ⟨681061893517514791297406807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 454041262345009860864937871 681061893517514791297406807)
      ·
        refine ⟨1021592840276272186946110211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 681061893517514791297406807 1021592840276272186946110211)
        ·
          refine ⟨1532389260414408280419165317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1021592840276272186946110211 1532389260414408280419165317)
          ·
            refine ⟨287322986327701552578593497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1532389260414408280419165317 287322986327701552578593497)
            ·
              refine ⟨215492239745776164433945123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 287322986327701552578593497 215492239745776164433945123)
              ·
                refine ⟨323238359618664246650917685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 215492239745776164433945123 323238359618664246650917685)
                ·
                  refine ⟨30303596214249773123523533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 323238359618664246650917685 30303596214249773123523533)
                  ·
                    refine ⟨11363848580343664921321325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 30303596214249773123523533 11363848580343664921321325)
                    ·
                      refine ⟨4261443217628874345495497, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11363848580343664921321325 4261443217628874345495497)
                      ·
                        rfl

theorem cell23_8299131_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 2, 1, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 2, 1, 5, 3, 3].length) (baseStart_8299131 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8299131 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8299131 prefixEnd_8299131 := by exact prefixLift 8299131
  have htrace : WordTrace (prefixWord ++ tailWord_8299131) baseStart_8299131 baseEnd_8299131 := by
    simpa [prefixWord, tailWord_8299131, baseEnd_8299131] using wordTrace_append hprefix tailTrace_8299131
  have hstable : (prefixWord ++ tailWord_8299131).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8299131).length < 2 ^ (prefixWord ++ tailWord_8299131).sum := by decide
  have hdescent : baseEnd_8299131 < baseStart_8299131 := by decide
  rcases family_descends (prefixWord ++ tailWord_8299131) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8299132 : List Nat := [2, 2, 2, 1, 1, 2, 2, 6, 1, 2, 2]
def baseStart_8299132 : Nat := 118140960795 + 8299132 * 2 ^ 59
def prefixEnd_8299132 : Nat := 4983230072969 + 3 ^ 40 * 8299132 * 2
def baseEnd_8299132 : Nat := 4261443731109528841582993

theorem tailTrace_8299132 : CollatzResearch.WordTrace tailWord_8299132 prefixEnd_8299132 4261443731109528841582993 := by
  unfold tailWord_8299132
  simp only [CollatzResearch.WordTrace]
  refine ⟨151347105684834808873705825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 201796140913113078498274433 151347105684834808873705825)
  ·
    refine ⟨113510329263626106655279369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 151347105684834808873705825 113510329263626106655279369)
    ·
      refine ⟨85132746947719579991459527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 113510329263626106655279369 85132746947719579991459527)
      ·
        refine ⟨127699120421579369987189291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85132746947719579991459527 127699120421579369987189291)
        ·
          refine ⟨191548680632369054980783937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 127699120421579369987189291 191548680632369054980783937)
          ·
            refine ⟨143661510474276791235587953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 191548680632369054980783937 143661510474276791235587953)
            ·
              refine ⟨107746132855707593426690965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 143661510474276791235587953 107746132855707593426690965)
              ·
                refine ⟨5050599977611293441876139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 107746132855707593426690965 5050599977611293441876139)
                ·
                  refine ⟨7575899966416940162814209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5050599977611293441876139 7575899966416940162814209)
                  ·
                    refine ⟨5681924974812705122110657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7575899966416940162814209 5681924974812705122110657)
                    ·
                      refine ⟨4261443731109528841582993, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5681924974812705122110657 4261443731109528841582993)
                      ·
                        rfl

theorem cell23_8299132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 2, 6, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 2, 6, 1, 2, 2].length) (baseStart_8299132 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8299132 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8299132 prefixEnd_8299132 := by exact prefixLift 8299132
  have htrace : WordTrace (prefixWord ++ tailWord_8299132) baseStart_8299132 baseEnd_8299132 := by
    simpa [prefixWord, tailWord_8299132, baseEnd_8299132] using wordTrace_append hprefix tailTrace_8299132
  have hstable : (prefixWord ++ tailWord_8299132).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8299132).length < 2 ^ (prefixWord ++ tailWord_8299132).sum := by decide
  have hdescent : baseEnd_8299132 < baseStart_8299132 := by decide
  rcases family_descends (prefixWord ++ tailWord_8299132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
