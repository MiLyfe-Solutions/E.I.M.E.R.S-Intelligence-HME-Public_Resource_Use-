import V185TrunkScan23Chunk0190

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_1131315 : List Nat := [1, 1, 1, 2, 6, 1, 2, 1, 3, 2, 3]
def baseStart_1131315 : Nat := 118140960795 + 1131315 * 2 ^ 59
def prefixEnd_1131315 : Nat := 4983230072969 + 3 ^ 40 * 1131315 * 2
def baseEnd_1131315 : Nat := 580908366641346458559683

theorem tailTrace_1131315 : CollatzResearch.WordTrace tailWord_1131315 prefixEnd_1131315 580908366641346458559683 := by
  unfold tailWord_1131315
  simp only [CollatzResearch.WordTrace]
  refine ⟨41262447896446443064619399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27508298597630962043079599 41262447896446443064619399)
  ·
    refine ⟨61893671844669664596929099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41262447896446443064619399 61893671844669664596929099)
    ·
      refine ⟨92840507767004496895393649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61893671844669664596929099 92840507767004496895393649)
      ·
        refine ⟨69630380825253372671545237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 92840507767004496895393649 69630380825253372671545237)
        ·
          refine ⟨3263924101183751843978683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 69630380825253372671545237 3263924101183751843978683)
          ·
            refine ⟨4895886151775627765968025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3263924101183751843978683 4895886151775627765968025)
            ·
              refine ⟨3671914613831720824476019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4895886151775627765968025 3671914613831720824476019)
              ·
                refine ⟨5507871920747581236714029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3671914613831720824476019 5507871920747581236714029)
                ·
                  refine ⟨2065451970280342963767761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5507871920747581236714029 2065451970280342963767761)
                  ·
                    refine ⟨1549088977710257222825821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2065451970280342963767761 1549088977710257222825821)
                    ·
                      refine ⟨580908366641346458559683, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1549088977710257222825821 580908366641346458559683)
                      ·
                        rfl

theorem cell23_1131315_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 1, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 1, 2, 1, 3, 2, 3].length) (baseStart_1131315 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1131315 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1131315 prefixEnd_1131315 := by exact prefixLift 1131315
  have htrace : WordTrace (prefixWord ++ tailWord_1131315) baseStart_1131315 baseEnd_1131315 := by
    simpa [prefixWord, tailWord_1131315, baseEnd_1131315] using wordTrace_append hprefix tailTrace_1131315
  have hstable : (prefixWord ++ tailWord_1131315).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1131315).length < 2 ^ (prefixWord ++ tailWord_1131315).sum := by decide
  have hdescent : baseEnd_1131315 < baseStart_1131315 := by decide
  rcases family_descends (prefixWord ++ tailWord_1131315) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1131316 : List Nat := [2, 5, 1, 1, 3, 2, 1, 1, 2, 3, 2]
def baseStart_1131316 : Nat := 118140960795 + 1131316 * 2 ^ 59
def prefixEnd_1131316 : Nat := 4983230072969 + 3 ^ 40 * 1131316 * 2
def baseEnd_1131316 : Nat := 580908880122000954647179

theorem tailTrace_1131316 : CollatzResearch.WordTrace tailWord_1131316 prefixEnd_1131316 580908880122000954647179 := by
  unfold tailWord_1131316
  simp only [CollatzResearch.WordTrace]
  refine ⟨20631242184721410117702901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27508322912961880156937201 20631242184721410117702901)
  ·
    refine ⟨1934178954817632198534647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 20631242184721410117702901 1934178954817632198534647)
    ·
      refine ⟨2901268432226448297801971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1934178954817632198534647 2901268432226448297801971)
      ·
        refine ⟨4351902648339672446702957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2901268432226448297801971 4351902648339672446702957)
        ·
          refine ⟨1631963493127377167513609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4351902648339672446702957 1631963493127377167513609)
          ·
            refine ⟨1223972619845532875635207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1631963493127377167513609 1223972619845532875635207)
            ·
              refine ⟨1835958929768299313452811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1223972619845532875635207 1835958929768299313452811)
              ·
                refine ⟨2753938394652448970179217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1835958929768299313452811 2753938394652448970179217)
                ·
                  refine ⟨2065453795989336727634413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2753938394652448970179217 2065453795989336727634413)
                  ·
                    refine ⟨774545173496001272862905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2065453795989336727634413 774545173496001272862905)
                    ·
                      refine ⟨580908880122000954647179, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 774545173496001272862905 580908880122000954647179)
                      ·
                        rfl

theorem cell23_1131316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 3, 2, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 3, 2, 1, 1, 2, 3, 2].length) (baseStart_1131316 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1131316 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1131316 prefixEnd_1131316 := by exact prefixLift 1131316
  have htrace : WordTrace (prefixWord ++ tailWord_1131316) baseStart_1131316 baseEnd_1131316 := by
    simpa [prefixWord, tailWord_1131316, baseEnd_1131316] using wordTrace_append hprefix tailTrace_1131316
  have hstable : (prefixWord ++ tailWord_1131316).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1131316).length < 2 ^ (prefixWord ++ tailWord_1131316).sum := by decide
  have hdescent : baseEnd_1131316 < baseStart_1131316 := by decide
  rcases family_descends (prefixWord ++ tailWord_1131316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1131326 : List Nat := [4, 2, 1, 2, 4, 1, 2, 1, 1, 5]
def baseStart_1131326 : Nat := 118140960795 + 1131326 * 2 ^ 59
def prefixEnd_1131326 : Nat := 4983230072969 + 3 ^ 40 * 1131326 * 2
def baseEnd_1131326 : Nat := 193638004976181971840711

theorem tailTrace_1131326 : CollatzResearch.WordTrace tailWord_1131326 prefixEnd_1131326 193638004976181971840711 := by
  unfold tailWord_1131326
  simp only [CollatzResearch.WordTrace]
  refine ⟨5157856137425823992908729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 27508566066271061295513221 5157856137425823992908729)
  ·
    refine ⟨3868392103069367994681547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5157856137425823992908729 3868392103069367994681547)
    ·
      refine ⟨5802588154604051992022321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3868392103069367994681547 5802588154604051992022321)
      ·
        refine ⟨4351941115953038994016741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5802588154604051992022321 4351941115953038994016741)
        ·
          refine ⟨815988959241194811378139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4351941115953038994016741 815988959241194811378139)
          ·
            refine ⟨1223983438861792217067209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 815988959241194811378139 1223983438861792217067209)
            ·
              refine ⟨917987579146344162800407, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1223983438861792217067209 917987579146344162800407)
              ·
                refine ⟨1376981368719516244200611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 917987579146344162800407 1376981368719516244200611)
                ·
                  refine ⟨2065472053079274366300917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1376981368719516244200611 2065472053079274366300917)
                  ·
                    refine ⟨193638004976181971840711, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2065472053079274366300917 193638004976181971840711)
                    ·
                      rfl

theorem cell23_1131326_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 4, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 4, 1, 2, 1, 1, 5].length) (baseStart_1131326 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1131326 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1131326 prefixEnd_1131326 := by exact prefixLift 1131326
  have htrace : WordTrace (prefixWord ++ tailWord_1131326) baseStart_1131326 baseEnd_1131326 := by
    simpa [prefixWord, tailWord_1131326, baseEnd_1131326] using wordTrace_append hprefix tailTrace_1131326
  have hstable : (prefixWord ++ tailWord_1131326).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1131326).length < 2 ^ (prefixWord ++ tailWord_1131326).sum := by decide
  have hdescent : baseEnd_1131326 < baseStart_1131326 := by decide
  rcases family_descends (prefixWord ++ tailWord_1131326) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1131329 : List Nat := [1, 2, 5, 3, 1, 1, 1, 3, 1, 1, 4]
def baseStart_1131329 : Nat := 118140960795 + 1131329 * 2 ^ 59
def prefixEnd_1131329 : Nat := 4983230072969 + 3 ^ 40 * 1131329 * 2
def baseEnd_1131329 : Nat := 580915555370509403784619

theorem tailTrace_1131329 : CollatzResearch.WordTrace tailWord_1131329 prefixEnd_1131329 580915555370509403784619 := by
  unfold tailWord_1131329
  simp only [CollatzResearch.WordTrace]
  refine ⟨41262958518395723455629041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27508639012263815637086027 41262958518395723455629041)
  ·
    refine ⟨30947218888796792591721781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41262958518395723455629041 30947218888796792591721781)
    ·
      refine ⟨2901301770824699305473917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 30947218888796792591721781 2901301770824699305473917)
      ·
        refine ⟨1087988164059262239552719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2901301770824699305473917 1087988164059262239552719)
        ·
          refine ⟨1631982246088893359329079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1087988164059262239552719 1631982246088893359329079)
          ·
            refine ⟨2447973369133340038993619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1631982246088893359329079 2447973369133340038993619)
            ·
              refine ⟨3671960053700010058490429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2447973369133340038993619 3671960053700010058490429)
              ·
                refine ⟨1376985020137503771933911, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3671960053700010058490429 1376985020137503771933911)
                ·
                  refine ⟨2065477530206255657900867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1376985020137503771933911 2065477530206255657900867)
                  ·
                    refine ⟨3098216295309383486851301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2065477530206255657900867 3098216295309383486851301)
                    ·
                      refine ⟨580915555370509403784619, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3098216295309383486851301 580915555370509403784619)
                      ·
                        rfl

theorem cell23_1131329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 1, 1, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 1, 1, 1, 3, 1, 1, 4].length) (baseStart_1131329 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1131329 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1131329 prefixEnd_1131329 := by exact prefixLift 1131329
  have htrace : WordTrace (prefixWord ++ tailWord_1131329) baseStart_1131329 baseEnd_1131329 := by
    simpa [prefixWord, tailWord_1131329, baseEnd_1131329] using wordTrace_append hprefix tailTrace_1131329
  have hstable : (prefixWord ++ tailWord_1131329).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1131329).length < 2 ^ (prefixWord ++ tailWord_1131329).sum := by decide
  have hdescent : baseEnd_1131329 < baseStart_1131329 := by decide
  rcases family_descends (prefixWord ++ tailWord_1131329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1131378 : List Nat := [3, 2, 1, 2, 1, 1, 2, 2, 1, 8]
def baseStart_1131378 : Nat := 118140960795 + 1131378 * 2 ^ 59
def prefixEnd_1131378 : Nat := 4983230072969 + 3 ^ 40 * 1131378 * 2
def baseEnd_1131378 : Nat := 193646905307526570690631

theorem tailTrace_1131378 : CollatzResearch.WordTrace tailWord_1131378 prefixEnd_1131378 193646905307526570690631 := by
  unfold tailWord_1131378
  simp only [CollatzResearch.WordTrace]
  refine ⟨10316186423804551206040697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 27509830463478803216108525 10316186423804551206040697)
  ·
    refine ⟨7737139817853413404530523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10316186423804551206040697 7737139817853413404530523)
    ·
      refine ⟨11605709726780120106795785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7737139817853413404530523 11605709726780120106795785)
      ·
        refine ⟨8704282295085090080096839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11605709726780120106795785 8704282295085090080096839)
        ·
          refine ⟨13056423442627635120145259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8704282295085090080096839 13056423442627635120145259)
          ·
            refine ⟨19584635163941452680217889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13056423442627635120145259 19584635163941452680217889)
            ·
              refine ⟨14688476372956089510163417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19584635163941452680217889 14688476372956089510163417)
              ·
                refine ⟨11016357279717067132622563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14688476372956089510163417 11016357279717067132622563)
                ·
                  refine ⟨16524535919575600698933845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11016357279717067132622563 16524535919575600698933845)
                  ·
                    refine ⟨193646905307526570690631, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 16524535919575600698933845 193646905307526570690631)
                    ·
                      rfl

theorem cell23_1131378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 2, 2, 1, 8].length) (baseStart_1131378 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1131378 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1131378 prefixEnd_1131378 := by exact prefixLift 1131378
  have htrace : WordTrace (prefixWord ++ tailWord_1131378) baseStart_1131378 baseEnd_1131378 := by
    simpa [prefixWord, tailWord_1131378, baseEnd_1131378] using wordTrace_append hprefix tailTrace_1131378
  have hstable : (prefixWord ++ tailWord_1131378).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1131378).length < 2 ^ (prefixWord ++ tailWord_1131378).sum := by decide
  have hdescent : baseEnd_1131378 < baseStart_1131378 := by decide
  rcases family_descends (prefixWord ++ tailWord_1131378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1131505 : List Nat := [1, 2, 2, 2, 4, 1, 1, 1, 2, 1, 6]
def baseStart_1131505 : Nat := 118140960795 + 1131505 * 2 ^ 59
def prefixEnd_1131505 : Nat := 4983230072969 + 3 ^ 40 * 1131505 * 2
def baseEnd_1131505 : Nat := 581005927965700715183809

theorem tailTrace_1131505 : CollatzResearch.WordTrace tailWord_1131505 prefixEnd_1131505 581005927965700715183809 := by
  unfold tailWord_1131505
  simp only [CollatzResearch.WordTrace]
  refine ⟨41269377765758105514035969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27512918510505403676023979 41269377765758105514035969)
  ·
    refine ⟨30952033324318579135526977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41269377765758105514035969 30952033324318579135526977)
    ·
      refine ⟨23214024993238934351645233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30952033324318579135526977 23214024993238934351645233)
      ·
        refine ⟨17410518744929200763733925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23214024993238934351645233 17410518744929200763733925)
        ·
          refine ⟨3264472264674225143200111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 17410518744929200763733925 3264472264674225143200111)
          ·
            refine ⟨4896708397011337714800167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3264472264674225143200111 4896708397011337714800167)
            ·
              refine ⟨7345062595517006572200251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4896708397011337714800167 7345062595517006572200251)
              ·
                refine ⟨11017593893275509858300377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7345062595517006572200251 11017593893275509858300377)
                ·
                  refine ⟨8263195419956632393725283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11017593893275509858300377 8263195419956632393725283)
                  ·
                    refine ⟨12394793129934948590587925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8263195419956632393725283 12394793129934948590587925)
                    ·
                      refine ⟨581005927965700715183809, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 12394793129934948590587925 581005927965700715183809)
                      ·
                        rfl

theorem cell23_1131505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 1, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 1, 1, 1, 2, 1, 6].length) (baseStart_1131505 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1131505 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1131505 prefixEnd_1131505 := by exact prefixLift 1131505
  have htrace : WordTrace (prefixWord ++ tailWord_1131505) baseStart_1131505 baseEnd_1131505 := by
    simpa [prefixWord, tailWord_1131505, baseEnd_1131505] using wordTrace_append hprefix tailTrace_1131505
  have hstable : (prefixWord ++ tailWord_1131505).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1131505).length < 2 ^ (prefixWord ++ tailWord_1131505).sum := by decide
  have hdescent : baseEnd_1131505 < baseStart_1131505 := by decide
  rcases family_descends (prefixWord ++ tailWord_1131505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1131545 : List Nat := [1, 2, 1, 2, 1, 1, 4, 3, 3, 5]
def baseStart_1131545 : Nat := 118140960795 + 1131545 * 2 ^ 59
def prefixEnd_1131545 : Nat := 4983230072969 + 3 ^ 40 * 1131545 * 2
def baseEnd_1131545 : Nat := 193675489063960186227875

theorem tailTrace_1131545 : CollatzResearch.WordTrace tailWord_1131545 prefixEnd_1131545 193675489063960186227875 := by
  unfold tailWord_1131545
  simp only [CollatzResearch.WordTrace]
  refine ⟨41270836685613192345492089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27513891123742128230328059 41270836685613192345492089)
  ·
    refine ⟨30953127514209894259119067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41270836685613192345492089 30953127514209894259119067)
    ·
      refine ⟨46429691271314841388678601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30953127514209894259119067 46429691271314841388678601)
      ·
        refine ⟨34822268453486131041508951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46429691271314841388678601 34822268453486131041508951)
        ·
          refine ⟨52233402680229196562263427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34822268453486131041508951 52233402680229196562263427)
          ·
            refine ⟨78350104020343794843395141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 52233402680229196562263427 78350104020343794843395141)
            ·
              refine ⟨14690644503814461533136589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 78350104020343794843395141 14690644503814461533136589)
              ·
                refine ⟨5508991688930423074926221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14690644503814461533136589 5508991688930423074926221)
                ·
                  refine ⟨2065871883348908653097333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5508991688930423074926221 2065871883348908653097333)
                  ·
                    refine ⟨193675489063960186227875, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2065871883348908653097333 193675489063960186227875)
                    ·
                      rfl

theorem cell23_1131545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 4, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 4, 3, 3, 5].length) (baseStart_1131545 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1131545 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1131545 prefixEnd_1131545 := by exact prefixLift 1131545
  have htrace : WordTrace (prefixWord ++ tailWord_1131545) baseStart_1131545 baseEnd_1131545 := by
    simpa [prefixWord, tailWord_1131545, baseEnd_1131545] using wordTrace_append hprefix tailTrace_1131545
  have hstable : (prefixWord ++ tailWord_1131545).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1131545).length < 2 ^ (prefixWord ++ tailWord_1131545).sum := by decide
  have hdescent : baseEnd_1131545 < baseStart_1131545 := by decide
  rcases family_descends (prefixWord ++ tailWord_1131545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1131569 : List Nat := [1, 2, 2, 3, 1, 2, 3, 2, 2, 3, 2]
def baseStart_1131569 : Nat := 118140960795 + 1131569 * 2 ^ 59
def prefixEnd_1131569 : Nat := 4983230072969 + 3 ^ 40 * 1131569 * 2
def baseEnd_1131569 : Nat := 581038790727588464783515

theorem tailTrace_1131569 : CollatzResearch.WordTrace tailWord_1131569 prefixEnd_1131569 581038790727588464783515 := by
  unfold tailWord_1131569
  simp only [CollatzResearch.WordTrace]
  refine ⟨41271712037526244444365761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27514474691684162962910507 41271712037526244444365761)
  ·
    refine ⟨30953784028144683333274321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41271712037526244444365761 30953784028144683333274321)
    ·
      refine ⟨23215338021108512499955741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30953784028144683333274321 23215338021108512499955741)
      ·
        refine ⟨8705751757915692187483403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23215338021108512499955741 8705751757915692187483403)
        ·
          refine ⟨13058627636873538281225105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8705751757915692187483403 13058627636873538281225105)
          ·
            refine ⟨9793970727655153710918829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13058627636873538281225105 9793970727655153710918829)
            ·
              refine ⟨3672739022870682641594561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9793970727655153710918829 3672739022870682641594561)
              ·
                refine ⟨2754554267153011981195921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3672739022870682641594561 2754554267153011981195921)
                ·
                  refine ⟨2065915700364758985896941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2754554267153011981195921 2065915700364758985896941)
                  ·
                    refine ⟨774718387636784619711353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2065915700364758985896941 774718387636784619711353)
                    ·
                      refine ⟨581038790727588464783515, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 774718387636784619711353 581038790727588464783515)
                      ·
                        rfl

theorem cell23_1131569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 3, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 3, 2, 2, 3, 2].length) (baseStart_1131569 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1131569 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1131569 prefixEnd_1131569 := by exact prefixLift 1131569
  have htrace : WordTrace (prefixWord ++ tailWord_1131569) baseStart_1131569 baseEnd_1131569 := by
    simpa [prefixWord, tailWord_1131569, baseEnd_1131569] using wordTrace_append hprefix tailTrace_1131569
  have hstable : (prefixWord ++ tailWord_1131569).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1131569).length < 2 ^ (prefixWord ++ tailWord_1131569).sum := by decide
  have hdescent : baseEnd_1131569 < baseStart_1131569 := by decide
  rcases family_descends (prefixWord ++ tailWord_1131569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1131576 : List Nat := [2, 1, 2, 1, 5, 3, 1, 1, 3, 1, 3]
def baseStart_1131576 : Nat := 118140960795 + 1131576 * 2 ^ 59
def prefixEnd_1131576 : Nat := 4983230072969 + 3 ^ 40 * 1131576 * 2
def baseEnd_1131576 : Nat := 581042385092169937395983

theorem tailTrace_1131576 : CollatzResearch.WordTrace tailWord_1131576 prefixEnd_1131576 581042385092169937395983 := by
  unfold tailWord_1131576
  simp only [CollatzResearch.WordTrace]
  refine ⟨20635983674250442319935291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27514644899000589759913721 20635983674250442319935291)
  ·
    refine ⟨30953975511375663479902937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20635983674250442319935291 30953975511375663479902937)
    ·
      refine ⟨23215481633531747609927203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30953975511375663479902937 23215481633531747609927203)
      ·
        refine ⟨34823222450297621414890805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23215481633531747609927203 34823222450297621414890805)
        ·
          refine ⟨3264677104715402007646013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 34823222450297621414890805 3264677104715402007646013)
          ·
            refine ⟨1224253914268275752867255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3264677104715402007646013 1224253914268275752867255)
            ·
              refine ⟨1836380871402413629300883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1224253914268275752867255 1836380871402413629300883)
              ·
                refine ⟨2754571307103620443951325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1836380871402413629300883 2754571307103620443951325)
                ·
                  refine ⟨1032964240163857666481747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2754571307103620443951325 1032964240163857666481747)
                  ·
                    refine ⟨1549446360245786499722621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1032964240163857666481747 1549446360245786499722621)
                    ·
                      refine ⟨581042385092169937395983, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1549446360245786499722621 581042385092169937395983)
                      ·
                        rfl

theorem cell23_1131576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 3, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 3, 1, 1, 3, 1, 3].length) (baseStart_1131576 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1131576 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1131576 prefixEnd_1131576 := by exact prefixLift 1131576
  have htrace : WordTrace (prefixWord ++ tailWord_1131576) baseStart_1131576 baseEnd_1131576 := by
    simpa [prefixWord, tailWord_1131576, baseEnd_1131576] using wordTrace_append hprefix tailTrace_1131576
  have hstable : (prefixWord ++ tailWord_1131576).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1131576).length < 2 ^ (prefixWord ++ tailWord_1131576).sum := by decide
  have hdescent : baseEnd_1131576 < baseStart_1131576 := by decide
  rcases family_descends (prefixWord ++ tailWord_1131576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1131605 : List Nat := [1, 3, 2, 2, 1, 2, 1, 11]
def baseStart_1131605 : Nat := 118140960795 + 1131605 * 2 ^ 59
def prefixEnd_1131605 : Nat := 4983230072969 + 3 ^ 40 * 1131605 * 2
def baseEnd_1131605 : Nat := 21520639853005567553087

theorem tailTrace_1131605 : CollatzResearch.WordTrace tailWord_1131605 prefixEnd_1131605 21520639853005567553087 := by
  unfold tailWord_1131605
  simp only [CollatzResearch.WordTrace]
  refine ⟨41273025065395822592676269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27515350043597215061784179 41273025065395822592676269)
  ·
    refine ⟨15477384399523433472253601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 41273025065395822592676269 15477384399523433472253601)
    ·
      refine ⟨11608038299642575104190201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15477384399523433472253601 11608038299642575104190201)
      ·
        refine ⟨8706028724731931328142651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11608038299642575104190201 8706028724731931328142651)
        ·
          refine ⟨13059043087097896992213977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8706028724731931328142651 13059043087097896992213977)
          ·
            refine ⟨9794282315323422744160483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13059043087097896992213977 9794282315323422744160483)
            ·
              refine ⟨14691423472985134116240725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9794282315323422744160483 14691423472985134116240725)
              ·
                refine ⟨21520639853005567553087, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 14691423472985134116240725 21520639853005567553087)
                ·
                  rfl

theorem cell23_1131605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 1, 11].length) (baseStart_1131605 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1131605 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1131605 prefixEnd_1131605 := by exact prefixLift 1131605
  have htrace : WordTrace (prefixWord ++ tailWord_1131605) baseStart_1131605 baseEnd_1131605 := by
    simpa [prefixWord, tailWord_1131605, baseEnd_1131605] using wordTrace_append hprefix tailTrace_1131605
  have hstable : (prefixWord ++ tailWord_1131605).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1131605).length < 2 ^ (prefixWord ++ tailWord_1131605).sum := by decide
  have hdescent : baseEnd_1131605 < baseStart_1131605 := by decide
  rcases family_descends (prefixWord ++ tailWord_1131605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1131613 : List Nat := [1, 4, 4, 1, 2, 1, 3, 1, 1, 5]
def baseStart_1131613 : Nat := 118140960795 + 1131613 * 2 ^ 59
def prefixEnd_1131613 : Nat := 4983230072969 + 3 ^ 40 * 1131613 * 2
def baseEnd_1131613 : Nat := 193687127958795430877771

theorem tailTrace_1131613 : CollatzResearch.WordTrace tailWord_1131613 prefixEnd_1131613 193687127958795430877771 := by
  unfold tailWord_1131613
  simp only [CollatzResearch.WordTrace]
  refine ⟨41273316849366839958967493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27515544566244559972644995 41273316849366839958967493)
  ·
    refine ⟨7738746909256282492306405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 41273316849366839958967493 7738746909256282492306405)
    ·
      refine ⟨1451015045485552967307451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 7738746909256282492306405 1451015045485552967307451)
      ·
        refine ⟨2176522568228329450961177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1451015045485552967307451 2176522568228329450961177)
        ·
          refine ⟨1632391926171247088220883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2176522568228329450961177 1632391926171247088220883)
          ·
            refine ⟨2448587889256870632331325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1632391926171247088220883 2448587889256870632331325)
            ·
              refine ⟨918220458471326487124247, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2448587889256870632331325 918220458471326487124247)
              ·
                refine ⟨1377330687706989730686371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 918220458471326487124247 1377330687706989730686371)
                ·
                  refine ⟨2065996031560484596029557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1377330687706989730686371 2065996031560484596029557)
                  ·
                    refine ⟨193687127958795430877771, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2065996031560484596029557 193687127958795430877771)
                    ·
                      rfl

theorem cell23_1131613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 2, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 2, 1, 3, 1, 1, 5].length) (baseStart_1131613 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1131613 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1131613 prefixEnd_1131613 := by exact prefixLift 1131613
  have htrace : WordTrace (prefixWord ++ tailWord_1131613) baseStart_1131613 baseEnd_1131613 := by
    simpa [prefixWord, tailWord_1131613, baseEnd_1131613] using wordTrace_append hprefix tailTrace_1131613
  have hstable : (prefixWord ++ tailWord_1131613).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1131613).length < 2 ^ (prefixWord ++ tailWord_1131613).sum := by decide
  have hdescent : baseEnd_1131613 < baseStart_1131613 := by decide
  rcases family_descends (prefixWord ++ tailWord_1131613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1131626 : List Nat := [3, 1, 3, 2, 2, 2, 2, 2, 2, 4]
def baseStart_1131626 : Nat := 118140960795 + 1131626 * 2 ^ 59
def prefixEnd_1131626 : Nat := 4983230072969 + 3 ^ 40 * 1131626 * 2
def baseEnd_1131626 : Nat := 193689353041631580590251

theorem tailTrace_1131626 : CollatzResearch.WordTrace tailWord_1131626 prefixEnd_1131626 193689353041631580590251 := by
  unfold tailWord_1131626
  simp only [CollatzResearch.WordTrace]
  refine ⟨10318447749579935794797683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 27515860665546495452793821 10318447749579935794797683)
  ·
    refine ⟨15477671624369903692196525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10318447749579935794797683 15477671624369903692196525)
    ·
      refine ⟨5804126859138713884573697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15477671624369903692196525 5804126859138713884573697)
      ·
        refine ⟨4353095144354035413430273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5804126859138713884573697 4353095144354035413430273)
        ·
          refine ⟨3264821358265526560072705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4353095144354035413430273 3264821358265526560072705)
          ·
            refine ⟨2448616018699144920054529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3264821358265526560072705 2448616018699144920054529)
            ·
              refine ⟨1836462014024358690040897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2448616018699144920054529 1836462014024358690040897)
              ·
                refine ⟨1377346510518269017530673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1836462014024358690040897 1377346510518269017530673)
                ·
                  refine ⟨1033009882888701763148005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1377346510518269017530673 1033009882888701763148005)
                  ·
                    refine ⟨193689353041631580590251, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1033009882888701763148005 193689353041631580590251)
                    ·
                      rfl

theorem cell23_1131626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 2, 2, 2, 2, 4].length) (baseStart_1131626 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1131626 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1131626 prefixEnd_1131626 := by exact prefixLift 1131626
  have htrace : WordTrace (prefixWord ++ tailWord_1131626) baseStart_1131626 baseEnd_1131626 := by
    simpa [prefixWord, tailWord_1131626, baseEnd_1131626] using wordTrace_append hprefix tailTrace_1131626
  have hstable : (prefixWord ++ tailWord_1131626).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1131626).length < 2 ^ (prefixWord ++ tailWord_1131626).sum := by decide
  have hdescent : baseEnd_1131626 < baseStart_1131626 := by decide
  rcases family_descends (prefixWord ++ tailWord_1131626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1131632 : List Nat := [2, 1, 1, 1, 5, 1, 1, 2, 3, 3, 3]
def baseStart_1131632 : Nat := 118140960795 + 1131632 * 2 ^ 59
def prefixEnd_1131632 : Nat := 4983230072969 + 3 ^ 40 * 1131632 * 2
def baseEnd_1131632 : Nat := 581071140008821718295725

theorem tailTrace_1131632 : CollatzResearch.WordTrace tailWord_1131632 prefixEnd_1131632 581071140008821718295725 := by
  unfold tailWord_1131632
  simp only [CollatzResearch.WordTrace]
  refine ⟨20637004918149003101954575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27516006557532004135939433 20637004918149003101954575)
  ·
    refine ⟨30955507377223504652931863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20637004918149003101954575 30955507377223504652931863)
    ·
      refine ⟨46433261065835256979397795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30955507377223504652931863 46433261065835256979397795)
      ·
        refine ⟨69649891598752885469096693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46433261065835256979397795 69649891598752885469096693)
        ·
          refine ⟨6529677337383083012727815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 69649891598752885469096693 6529677337383083012727815)
          ·
            refine ⟨9794516006074624519091723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6529677337383083012727815 9794516006074624519091723)
            ·
              refine ⟨14691774009111936778637585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9794516006074624519091723 14691774009111936778637585)
              ·
                refine ⟨11018830506833952583978189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14691774009111936778637585 11018830506833952583978189)
                ·
                  refine ⟨4132061440062732218991821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11018830506833952583978189 4132061440062732218991821)
                  ·
                    refine ⟨1549523040023524582121933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4132061440062732218991821 1549523040023524582121933)
                    ·
                      refine ⟨581071140008821718295725, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1549523040023524582121933 581071140008821718295725)
                      ·
                        rfl

theorem cell23_1131632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 1, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 1, 2, 3, 3, 3].length) (baseStart_1131632 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1131632 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1131632 prefixEnd_1131632 := by exact prefixLift 1131632
  have htrace : WordTrace (prefixWord ++ tailWord_1131632) baseStart_1131632 baseEnd_1131632 := by
    simpa [prefixWord, tailWord_1131632, baseEnd_1131632] using wordTrace_append hprefix tailTrace_1131632
  have hstable : (prefixWord ++ tailWord_1131632).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1131632).length < 2 ^ (prefixWord ++ tailWord_1131632).sum := by decide
  have hdescent : baseEnd_1131632 < baseStart_1131632 := by decide
  rcases family_descends (prefixWord ++ tailWord_1131632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1131649 : List Nat := [1, 2, 4, 2, 2, 1, 1, 3, 1, 3, 3]
def baseStart_1131649 : Nat := 118140960795 + 1131649 * 2 ^ 59
def prefixEnd_1131649 : Nat := 4983230072969 + 3 ^ 40 * 1131649 * 2
def baseEnd_1131649 : Nat := 581079869179948151783147

theorem tailTrace_1131649 : CollatzResearch.WordTrace tailWord_1131649 prefixEnd_1131649 581079869179948151783147 := by
  unfold tailWord_1131649
  simp only [CollatzResearch.WordTrace]
  refine ⟨41274629877236418107278001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27516419918157612071518667 41274629877236418107278001)
  ·
    refine ⟨30955972407927313580458501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41274629877236418107278001 30955972407927313580458501)
    ·
      refine ⟨5804244826486371296335969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 30955972407927313580458501 5804244826486371296335969)
      ·
        refine ⟨4353183619864778472251977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5804244826486371296335969 4353183619864778472251977)
        ·
          refine ⟨3264887714898583854188983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4353183619864778472251977 3264887714898583854188983)
          ·
            refine ⟨4897331572347875781283475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3264887714898583854188983 4897331572347875781283475)
            ·
              refine ⟨7345997358521813671925213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4897331572347875781283475 7345997358521813671925213)
              ·
                refine ⟨2754749009445680126971955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7345997358521813671925213 2754749009445680126971955)
                ·
                  refine ⟨4132123514168520190457933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2754749009445680126971955 4132123514168520190457933)
                  ·
                    refine ⟨1549546317813195071421725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4132123514168520190457933 1549546317813195071421725)
                    ·
                      refine ⟨581079869179948151783147, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1549546317813195071421725 581079869179948151783147)
                      ·
                        rfl

theorem cell23_1131649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 1, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 1, 1, 3, 1, 3, 3].length) (baseStart_1131649 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1131649 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1131649 prefixEnd_1131649 := by exact prefixLift 1131649
  have htrace : WordTrace (prefixWord ++ tailWord_1131649) baseStart_1131649 baseEnd_1131649 := by
    simpa [prefixWord, tailWord_1131649, baseEnd_1131649] using wordTrace_append hprefix tailTrace_1131649
  have hstable : (prefixWord ++ tailWord_1131649).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1131649).length < 2 ^ (prefixWord ++ tailWord_1131649).sum := by decide
  have hdescent : baseEnd_1131649 < baseStart_1131649 := by decide
  rcases family_descends (prefixWord ++ tailWord_1131649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1131692 : List Nat := [2, 2, 1, 1, 1, 1, 1, 5, 2, 4, 3]
def baseStart_1131692 : Nat := 118140960795 + 1131692 * 2 ^ 59
def prefixEnd_1131692 : Nat := 4983230072969 + 3 ^ 40 * 1131692 * 2
def baseEnd_1131692 : Nat := 581101948848091483545449

theorem tailTrace_1131692 : CollatzResearch.WordTrace tailWord_1131692 prefixEnd_1131692 581101948848091483545449 := by
  unfold tailWord_1131692
  simp only [CollatzResearch.WordTrace]
  refine ⟨20638099108040318225546665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27517465477387090967395553 20638099108040318225546665)
  ·
    refine ⟨15478574331030238669159999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20638099108040318225546665 15478574331030238669159999)
    ·
      refine ⟨23217861496545358003739999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15478574331030238669159999 23217861496545358003739999)
      ·
        refine ⟨34826792244818037005609999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23217861496545358003739999 34826792244818037005609999)
        ·
          refine ⟨52240188367227055508414999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34826792244818037005609999 52240188367227055508414999)
          ·
            refine ⟨78360282550840583262622499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 52240188367227055508414999 78360282550840583262622499)
            ·
              refine ⟨117540423826260874893933749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 78360282550840583262622499 117540423826260874893933749)
              ·
                refine ⟨11019414733711957021306289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 117540423826260874893933749 11019414733711957021306289)
                ·
                  refine ⟨8264561050283967765979717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11019414733711957021306289 8264561050283967765979717)
                  ·
                    refine ⟨1549605196928243956121197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 8264561050283967765979717 1549605196928243956121197)
                    ·
                      refine ⟨581101948848091483545449, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1549605196928243956121197 581101948848091483545449)
                      ·
                        rfl

theorem cell23_1131692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 4, 3].length) (baseStart_1131692 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1131692 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1131692 prefixEnd_1131692 := by exact prefixLift 1131692
  have htrace : WordTrace (prefixWord ++ tailWord_1131692) baseStart_1131692 baseEnd_1131692 := by
    simpa [prefixWord, tailWord_1131692, baseEnd_1131692] using wordTrace_append hprefix tailTrace_1131692
  have hstable : (prefixWord ++ tailWord_1131692).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1131692).length < 2 ^ (prefixWord ++ tailWord_1131692).sum := by decide
  have hdescent : baseEnd_1131692 < baseStart_1131692 := by decide
  rcases family_descends (prefixWord ++ tailWord_1131692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1131718 : List Nat := [6, 1, 2, 2, 2, 1, 1, 3, 1, 2, 2]
def baseStart_1131718 : Nat := 118140960795 + 1131718 * 2 ^ 59
def prefixEnd_1131718 : Nat := 4983230072969 + 3 ^ 40 * 1131718 * 2
def baseEnd_1131718 : Nat := 581115299345108381820331

theorem tailTrace_1131718 : CollatzResearch.WordTrace tailWord_1131718 prefixEnd_1131718 581115299345108381820331 := by
  unfold tailWord_1131718
  simp only [CollatzResearch.WordTrace]
  refine ⟨1289910828562076340360619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 27518097675990961927693205 1289910828562076340360619)
  ·
    refine ⟨1934866242843114510540929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1289910828562076340360619 1934866242843114510540929)
    ·
      refine ⟨1451149682132335882905697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1934866242843114510540929 1451149682132335882905697)
      ·
        refine ⟨1088362261599251912179273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1451149682132335882905697 1088362261599251912179273)
        ·
          refine ⟨816271696199438934134455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1088362261599251912179273 816271696199438934134455)
          ·
            refine ⟨1224407544299158401201683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 816271696199438934134455 1224407544299158401201683)
            ·
              refine ⟨1836611316448737601802525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1224407544299158401201683 1836611316448737601802525)
              ·
                refine ⟨688729243668276600675947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1836611316448737601802525 688729243668276600675947)
                ·
                  refine ⟨1033093865502414901013921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 688729243668276600675947 1033093865502414901013921)
                  ·
                    refine ⟨774820399126811175760441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1033093865502414901013921 774820399126811175760441)
                    ·
                      refine ⟨581115299345108381820331, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 774820399126811175760441 581115299345108381820331)
                      ·
                        rfl

theorem cell23_1131718_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 2, 1, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 2, 1, 1, 3, 1, 2, 2].length) (baseStart_1131718 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1131718 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1131718 prefixEnd_1131718 := by exact prefixLift 1131718
  have htrace : WordTrace (prefixWord ++ tailWord_1131718) baseStart_1131718 baseEnd_1131718 := by
    simpa [prefixWord, tailWord_1131718, baseEnd_1131718] using wordTrace_append hprefix tailTrace_1131718
  have hstable : (prefixWord ++ tailWord_1131718).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1131718).length < 2 ^ (prefixWord ++ tailWord_1131718).sum := by decide
  have hdescent : baseEnd_1131718 < baseStart_1131718 := by decide
  rcases family_descends (prefixWord ++ tailWord_1131718) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1131757 : List Nat := [1, 5, 1, 2, 2, 3, 2, 1, 2, 2, 2]
def baseStart_1131757 : Nat := 118140960795 + 1131757 * 2 ^ 59
def prefixEnd_1131757 : Nat := 4983230072969 + 3 ^ 40 * 1131757 * 2
def baseEnd_1131757 : Nat := 581135325090633729232651

theorem tailTrace_1131757 : CollatzResearch.WordTrace tailWord_1131757 prefixEnd_1131757 581135325090633729232651 := by
  unfold tailWord_1131757
  simp only [CollatzResearch.WordTrace]
  refine ⟨41278568960845152552209525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27519045973896768368139683 41278568960845152552209525)
  ·
    refine ⟨3869865840079233051769643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 41278568960845152552209525 3869865840079233051769643)
    ·
      refine ⟨5804798760118849577654465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3869865840079233051769643 5804798760118849577654465)
      ·
        refine ⟨4353599070089137183240849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5804798760118849577654465 4353599070089137183240849)
        ·
          refine ⟨3265199302566852887430637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4353599070089137183240849 3265199302566852887430637)
          ·
            refine ⟨1224449738462569832786489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3265199302566852887430637 1224449738462569832786489)
            ·
              refine ⟨918337303846927374589867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1224449738462569832786489 918337303846927374589867)
              ·
                refine ⟨1377505955770391061884801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 918337303846927374589867 1377505955770391061884801)
                ·
                  refine ⟨1033129466827793296413601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1377505955770391061884801 1033129466827793296413601)
                  ·
                    refine ⟨774847100120844972310201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1033129466827793296413601 774847100120844972310201)
                    ·
                      refine ⟨581135325090633729232651, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 774847100120844972310201 581135325090633729232651)
                      ·
                        rfl

theorem cell23_1131757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 3, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 3, 2, 1, 2, 2, 2].length) (baseStart_1131757 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1131757 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1131757 prefixEnd_1131757 := by exact prefixLift 1131757
  have htrace : WordTrace (prefixWord ++ tailWord_1131757) baseStart_1131757 baseEnd_1131757 := by
    simpa [prefixWord, tailWord_1131757, baseEnd_1131757] using wordTrace_append hprefix tailTrace_1131757
  have hstable : (prefixWord ++ tailWord_1131757).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1131757).length < 2 ^ (prefixWord ++ tailWord_1131757).sum := by decide
  have hdescent : baseEnd_1131757 < baseStart_1131757 := by decide
  rcases family_descends (prefixWord ++ tailWord_1131757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1131779 : List Nat := [1, 1, 1, 3, 2, 4, 1, 3, 2, 1, 4]
def baseStart_1131779 : Nat := 118140960795 + 1131779 * 2 ^ 59
def prefixEnd_1131779 : Nat := 4983230072969 + 3 ^ 40 * 1131779 * 2
def baseEnd_1131779 : Nat := 581146621665032643157549

theorem tailTrace_1131779 : CollatzResearch.WordTrace tailWord_1131779 prefixEnd_1131779 581146621665032643157549 := by
  unfold tailWord_1131779
  simp only [CollatzResearch.WordTrace]
  refine ⟨41279371366765450309510391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27519580911176966873006927 41279371366765450309510391)
  ·
    refine ⟨61919057050148175464265587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41279371366765450309510391 61919057050148175464265587)
    ·
      refine ⟨92878585575222263196398381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61919057050148175464265587 92878585575222263196398381)
      ·
        refine ⟨34829469590708348698649393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 92878585575222263196398381 34829469590708348698649393)
        ·
          refine ⟨26122102193031261523987045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34829469590708348698649393 26122102193031261523987045)
          ·
            refine ⟨4897894161193361535747571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 26122102193031261523987045 4897894161193361535747571)
            ·
              refine ⟨7346841241790042303621357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4897894161193361535747571 7346841241790042303621357)
              ·
                refine ⟨2755065465671265863858009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7346841241790042303621357 2755065465671265863858009)
                ·
                  refine ⟨2066299099253449397893507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2755065465671265863858009 2066299099253449397893507)
                  ·
                    refine ⟨3099448648880174096840261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2066299099253449397893507 3099448648880174096840261)
                    ·
                      refine ⟨581146621665032643157549, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3099448648880174096840261 581146621665032643157549)
                      ·
                        rfl

theorem cell23_1131779_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 4, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 4, 1, 3, 2, 1, 4].length) (baseStart_1131779 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1131779 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1131779 prefixEnd_1131779 := by exact prefixLift 1131779
  have htrace : WordTrace (prefixWord ++ tailWord_1131779) baseStart_1131779 baseEnd_1131779 := by
    simpa [prefixWord, tailWord_1131779, baseEnd_1131779] using wordTrace_append hprefix tailTrace_1131779
  have hstable : (prefixWord ++ tailWord_1131779).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1131779).length < 2 ^ (prefixWord ++ tailWord_1131779).sum := by decide
  have hdescent : baseEnd_1131779 < baseStart_1131779 := by decide
  rcases family_descends (prefixWord ++ tailWord_1131779) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1131792 : List Nat := [2, 1, 1, 1, 1, 1, 1, 1, 6, 4, 4]
def baseStart_1131792 : Nat := 118140960795 + 1131792 * 2 ^ 59
def prefixEnd_1131792 : Nat := 4983230072969 + 3 ^ 40 * 1131792 * 2
def baseEnd_1131792 : Nat := 581153296913541092294989

theorem tailTrace_1131792 : CollatzResearch.WordTrace tailWord_1131792 prefixEnd_1131792 581153296913541092294989 := by
  unfold tailWord_1131792
  simp only [CollatzResearch.WordTrace]
  refine ⟨20639922757859176764866815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27519897010478902353155753 20639922757859176764866815)
  ·
    refine ⟨30959884136788765147300223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20639922757859176764866815 30959884136788765147300223)
    ·
      refine ⟨46439826205183147720950335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30959884136788765147300223 46439826205183147720950335)
      ·
        refine ⟨69659739307774721581425503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46439826205183147720950335 69659739307774721581425503)
        ·
          refine ⟨104489608961662082372138255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 69659739307774721581425503 104489608961662082372138255)
          ·
            refine ⟨156734413442493123558207383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 104489608961662082372138255 156734413442493123558207383)
            ·
              refine ⟨235101620163739685337311075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 156734413442493123558207383 235101620163739685337311075)
              ·
                refine ⟨352652430245609528005966613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 235101620163739685337311075 352652430245609528005966613)
                ·
                  refine ⟨16530582667762946625279685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 352652430245609528005966613 16530582667762946625279685)
                  ·
                    refine ⟨3099484250205552492239941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16530582667762946625279685 3099484250205552492239941)
                    ·
                      refine ⟨581153296913541092294989, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3099484250205552492239941 581153296913541092294989)
                      ·
                        rfl

theorem cell23_1131792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 6, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 6, 4, 4].length) (baseStart_1131792 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1131792 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1131792 prefixEnd_1131792 := by exact prefixLift 1131792
  have htrace : WordTrace (prefixWord ++ tailWord_1131792) baseStart_1131792 baseEnd_1131792 := by
    simpa [prefixWord, tailWord_1131792, baseEnd_1131792] using wordTrace_append hprefix tailTrace_1131792
  have hstable : (prefixWord ++ tailWord_1131792).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1131792).length < 2 ^ (prefixWord ++ tailWord_1131792).sum := by decide
  have hdescent : baseEnd_1131792 < baseStart_1131792 := by decide
  rcases family_descends (prefixWord ++ tailWord_1131792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1131853 : List Nat := [1, 6, 1, 3, 1, 1, 1, 1, 8]
def baseStart_1131853 : Nat := 118140960795 + 1131853 * 2 ^ 59
def prefixEnd_1131853 : Nat := 4983230072969 + 3 ^ 40 * 1131853 * 2
def baseEnd_1131853 : Nat := 64576068803718372625801

theorem tailTrace_1131853 : CollatzResearch.WordTrace tailWord_1131853 prefixEnd_1131853 64576068803718372625801 := by
  unfold tailWord_1131853
  simp only [CollatzResearch.WordTrace]
  refine ⟨41282070368497360947704213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27521380245664907298469475 41282070368497360947704213)
  ·
    refine ⟨1935097048523313794423635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 41282070368497360947704213 1935097048523313794423635)
    ·
      refine ⟨2902645572784970691635453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1935097048523313794423635 2902645572784970691635453)
      ·
        refine ⟨1088492089794364009363295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2902645572784970691635453 1088492089794364009363295)
        ·
          refine ⟨1632738134691546014044943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1088492089794364009363295 1632738134691546014044943)
          ·
            refine ⟨2449107202037319021067415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1632738134691546014044943 2449107202037319021067415)
            ·
              refine ⟨3673660803055978531601123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2449107202037319021067415 3673660803055978531601123)
              ·
                refine ⟨5510491204583967797401685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3673660803055978531601123 5510491204583967797401685)
                ·
                  refine ⟨64576068803718372625801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 5510491204583967797401685 64576068803718372625801)
                  ·
                    rfl

theorem cell23_1131853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 1, 1, 1, 1, 8].length) (baseStart_1131853 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1131853 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1131853 prefixEnd_1131853 := by exact prefixLift 1131853
  have htrace : WordTrace (prefixWord ++ tailWord_1131853) baseStart_1131853 baseEnd_1131853 := by
    simpa [prefixWord, tailWord_1131853, baseEnd_1131853] using wordTrace_append hprefix tailTrace_1131853
  have hstable : (prefixWord ++ tailWord_1131853).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1131853).length < 2 ^ (prefixWord ++ tailWord_1131853).sum := by decide
  have hdescent : baseEnd_1131853 < baseStart_1131853 := by decide
  rcases family_descends (prefixWord ++ tailWord_1131853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1131856 : List Nat := [2, 1, 1, 1, 1, 5, 2, 1, 4, 3, 2]
def baseStart_1131856 : Nat := 118140960795 + 1131856 * 2 ^ 59
def prefixEnd_1131856 : Nat := 4983230072969 + 3 ^ 40 * 1131856 * 2
def baseEnd_1131856 : Nat := 581186159675428841894695

theorem tailTrace_1131856 : CollatzResearch.WordTrace tailWord_1131856 prefixEnd_1131856 581186159675428841894695 := by
  unfold tailWord_1131856
  simp only [CollatzResearch.WordTrace]
  refine ⟨20641089893743246230031711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27521453191657661640042281 20641089893743246230031711)
  ·
    refine ⟨30961634840614869345047567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20641089893743246230031711 30961634840614869345047567)
    ·
      refine ⟨46442452260922304017571351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30961634840614869345047567 46442452260922304017571351)
      ·
        refine ⟨69663678391383456026357027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46442452260922304017571351 69663678391383456026357027)
        ·
          refine ⟨104495517587075184039535541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 69663678391383456026357027 104495517587075184039535541)
          ·
            refine ⟨9796454773788298503706457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 104495517587075184039535541 9796454773788298503706457)
            ·
              refine ⟨7347341080341223877779843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9796454773788298503706457 7347341080341223877779843)
              ·
                refine ⟨11021011620511835816669765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7347341080341223877779843 11021011620511835816669765)
                ·
                  refine ⟨2066439678845969215625581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11021011620511835816669765 2066439678845969215625581)
                  ·
                    refine ⟨774914879567238455859593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2066439678845969215625581 774914879567238455859593)
                    ·
                      refine ⟨581186159675428841894695, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 774914879567238455859593 581186159675428841894695)
                      ·
                        rfl

theorem cell23_1131856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 2, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 2, 1, 4, 3, 2].length) (baseStart_1131856 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1131856 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1131856 prefixEnd_1131856 := by exact prefixLift 1131856
  have htrace : WordTrace (prefixWord ++ tailWord_1131856) baseStart_1131856 baseEnd_1131856 := by
    simpa [prefixWord, tailWord_1131856, baseEnd_1131856] using wordTrace_append hprefix tailTrace_1131856
  have hstable : (prefixWord ++ tailWord_1131856).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1131856).length < 2 ^ (prefixWord ++ tailWord_1131856).sum := by decide
  have hdescent : baseEnd_1131856 < baseStart_1131856 := by decide
  rcases family_descends (prefixWord ++ tailWord_1131856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1131863 : List Nat := [1, 1, 3, 2, 3, 3, 2, 1, 3, 1, 3]
def baseStart_1131863 : Nat := 118140960795 + 1131863 * 2 ^ 59
def prefixEnd_1131863 : Nat := 4983230072969 + 3 ^ 40 * 1131863 * 2
def baseEnd_1131863 : Nat := 581189754040010314507163

theorem tailTrace_1131863 : CollatzResearch.WordTrace tailWord_1131863 prefixEnd_1131863 581189754040010314507163 := by
  unfold tailWord_1131863
  simp only [CollatzResearch.WordTrace]
  refine ⟨41282435098461132655568243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27521623398974088437045495 41282435098461132655568243)
  ·
    refine ⟨61923652647691698983352365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41282435098461132655568243 61923652647691698983352365)
    ·
      refine ⟨23221369742884387118757137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 61923652647691698983352365 23221369742884387118757137)
      ·
        refine ⟨17416027307163290339067853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23221369742884387118757137 17416027307163290339067853)
        ·
          refine ⟨6531010240186233877150445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17416027307163290339067853 6531010240186233877150445)
          ·
            refine ⟨2449128840069837703931417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6531010240186233877150445 2449128840069837703931417)
            ·
              refine ⟨1836846630052378277948563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2449128840069837703931417 1836846630052378277948563)
              ·
                refine ⟨2755269945078567416922845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1836846630052378277948563 2755269945078567416922845)
                ·
                  refine ⟨1033226229404462781346067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2755269945078567416922845 1033226229404462781346067)
                  ·
                    refine ⟨1549839344106694172019101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1033226229404462781346067 1549839344106694172019101)
                    ·
                      refine ⟨581189754040010314507163, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1549839344106694172019101 581189754040010314507163)
                      ·
                        rfl

theorem cell23_1131863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 3, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 3, 2, 1, 3, 1, 3].length) (baseStart_1131863 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1131863 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1131863 prefixEnd_1131863 := by exact prefixLift 1131863
  have htrace : WordTrace (prefixWord ++ tailWord_1131863) baseStart_1131863 baseEnd_1131863 := by
    simpa [prefixWord, tailWord_1131863, baseEnd_1131863] using wordTrace_append hprefix tailTrace_1131863
  have hstable : (prefixWord ++ tailWord_1131863).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1131863).length < 2 ^ (prefixWord ++ tailWord_1131863).sum := by decide
  have hdescent : baseEnd_1131863 < baseStart_1131863 := by decide
  rcases family_descends (prefixWord ++ tailWord_1131863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1131899 : List Nat := [1, 1, 1, 1, 1, 6, 2, 1, 3, 2, 4]
def baseStart_1131899 : Nat := 118140960795 + 1131899 * 2 ^ 59
def prefixEnd_1131899 : Nat := 4983230072969 + 3 ^ 40 * 1131899 * 2
def baseEnd_1131899 : Nat := 581208239343572173656997

theorem tailTrace_1131899 : CollatzResearch.WordTrace tailWord_1131899 prefixEnd_1131899 581208239343572173656997 := by
  unfold tailWord_1131899
  simp only [CollatzResearch.WordTrace]
  refine ⟨41283748126330710803878751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27522498750887140535919167 41283748126330710803878751)
  ·
    refine ⟨61925622189496066205818127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41283748126330710803878751 61925622189496066205818127)
    ·
      refine ⟨92888433284244099308727191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61925622189496066205818127 92888433284244099308727191)
      ·
        refine ⟨139332649926366148963090787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 92888433284244099308727191 139332649926366148963090787)
        ·
          refine ⟨208998974889549223444636181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 139332649926366148963090787 208998974889549223444636181)
          ·
            refine ⟨9796826947947619848967321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 208998974889549223444636181 9796826947947619848967321)
            ·
              refine ⟨7347620210960714886725491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9796826947947619848967321 7347620210960714886725491)
              ·
                refine ⟨11021430316441072330088237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7347620210960714886725491 11021430316441072330088237)
                ·
                  refine ⟨4133036368665402123783089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11021430316441072330088237 4133036368665402123783089)
                  ·
                    refine ⟨3099777276499051592837317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4133036368665402123783089 3099777276499051592837317)
                    ·
                      refine ⟨581208239343572173656997, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3099777276499051592837317 581208239343572173656997)
                      ·
                        rfl

theorem cell23_1131899_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 2, 1, 3, 2, 4].length) (baseStart_1131899 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1131899 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1131899 prefixEnd_1131899 := by exact prefixLift 1131899
  have htrace : WordTrace (prefixWord ++ tailWord_1131899) baseStart_1131899 baseEnd_1131899 := by
    simpa [prefixWord, tailWord_1131899, baseEnd_1131899] using wordTrace_append hprefix tailTrace_1131899
  have hstable : (prefixWord ++ tailWord_1131899).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1131899).length < 2 ^ (prefixWord ++ tailWord_1131899).sum := by decide
  have hdescent : baseEnd_1131899 < baseStart_1131899 := by decide
  rcases family_descends (prefixWord ++ tailWord_1131899) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1131936 : List Nat := [2, 1, 1, 4, 1, 2, 2, 3, 1, 3, 3]
def baseStart_1131936 : Nat := 118140960795 + 1131936 * 2 ^ 59
def prefixEnd_1131936 : Nat := 4983230072969 + 3 ^ 40 * 1131936 * 2
def baseEnd_1131936 : Nat := 581227238127788528894327

theorem tailTrace_1131936 : CollatzResearch.WordTrace tailWord_1131936 prefixEnd_1131936 581227238127788528894327 := by
  unfold tailWord_1131936
  simp only [CollatzResearch.WordTrace]
  refine ⟨20642548813598333061487831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27523398418131110748650441 20642548813598333061487831)
  ·
    refine ⟨30963823220397499592231747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20642548813598333061487831 30963823220397499592231747)
    ·
      refine ⟨46445734830596249388347621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30963823220397499592231747 46445734830596249388347621)
      ·
        refine ⟨8708575280736796760315179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 46445734830596249388347621 8708575280736796760315179)
        ·
          refine ⟨13062862921105195140472769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8708575280736796760315179 13062862921105195140472769)
          ·
            refine ⟨9797147190828896355354577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13062862921105195140472769 9797147190828896355354577)
            ·
              refine ⟨7347860393121672266515933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9797147190828896355354577 7347860393121672266515933)
              ·
                refine ⟨2755447647420627099943475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7347860393121672266515933 2755447647420627099943475)
                ·
                  refine ⟨4133171471130940649915213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2755447647420627099943475 4133171471130940649915213)
                  ·
                    refine ⟨1549939301674102743718205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4133171471130940649915213 1549939301674102743718205)
                    ·
                      refine ⟨581227238127788528894327, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1549939301674102743718205 581227238127788528894327)
                      ·
                        rfl

theorem cell23_1131936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 2, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 2, 3, 1, 3, 3].length) (baseStart_1131936 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1131936 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1131936 prefixEnd_1131936 := by exact prefixLift 1131936
  have htrace : WordTrace (prefixWord ++ tailWord_1131936) baseStart_1131936 baseEnd_1131936 := by
    simpa [prefixWord, tailWord_1131936, baseEnd_1131936] using wordTrace_append hprefix tailTrace_1131936
  have hstable : (prefixWord ++ tailWord_1131936).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1131936).length < 2 ^ (prefixWord ++ tailWord_1131936).sum := by decide
  have hdescent : baseEnd_1131936 < baseStart_1131936 := by decide
  rcases family_descends (prefixWord ++ tailWord_1131936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1131979 : List Nat := [1, 1, 1, 1, 3, 3, 2, 2, 1, 3, 5]
def baseStart_1131979 : Nat := 118140960795 + 1131979 * 2 ^ 59
def prefixEnd_1131979 : Nat := 4983230072969 + 3 ^ 40 * 1131979 * 2
def baseEnd_1131979 : Nat := 581249317795931860656629

theorem tailTrace_1131979 : CollatzResearch.WordTrace tailWord_1131979 prefixEnd_1131979 581249317795931860656629 := by
  unfold tailWord_1131979
  simp only [CollatzResearch.WordTrace]
  refine ⟨41286665966040884466790991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27524443977360589644527327 41286665966040884466790991)
  ·
    refine ⟨61929998949061326700186487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41286665966040884466790991 61929998949061326700186487)
    ·
      refine ⟨92894998423591990050279731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61929998949061326700186487 92894998423591990050279731)
      ·
        refine ⟨139342497635387985075419597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 92894998423591990050279731 139342497635387985075419597)
        ·
          refine ⟨52253436613270494403282349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 139342497635387985075419597 52253436613270494403282349)
          ·
            refine ⟨19595038729976435401230881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 52253436613270494403282349 19595038729976435401230881)
            ·
              refine ⟨14696279047482326550923161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19595038729976435401230881 14696279047482326550923161)
              ·
                refine ⟨11022209285611744913192371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14696279047482326550923161 11022209285611744913192371)
                ·
                  refine ⟨16533313928417617369788557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11022209285611744913192371 16533313928417617369788557)
                  ·
                    refine ⟨6199992723156606513670709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16533313928417617369788557 6199992723156606513670709)
                    ·
                      refine ⟨581249317795931860656629, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 6199992723156606513670709 581249317795931860656629)
                      ·
                        rfl

theorem cell23_1131979_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 2, 2, 1, 3, 5].length) (baseStart_1131979 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1131979 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1131979 prefixEnd_1131979 := by exact prefixLift 1131979
  have htrace : WordTrace (prefixWord ++ tailWord_1131979) baseStart_1131979 baseEnd_1131979 := by
    simpa [prefixWord, tailWord_1131979, baseEnd_1131979] using wordTrace_append hprefix tailTrace_1131979
  have hstable : (prefixWord ++ tailWord_1131979).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1131979).length < 2 ^ (prefixWord ++ tailWord_1131979).sum := by decide
  have hdescent : baseEnd_1131979 < baseStart_1131979 := by decide
  rcases family_descends (prefixWord ++ tailWord_1131979) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1131993 : List Nat := [1, 2, 1, 2, 4, 2, 1, 3, 1, 4, 2]
def baseStart_1131993 : Nat := 118140960795 + 1131993 * 2 ^ 59
def prefixEnd_1131993 : Nat := 4983230072969 + 3 ^ 40 * 1131993 * 2
def baseEnd_1131993 : Nat := 581256506525094805881565

theorem tailTrace_1131993 : CollatzResearch.WordTrace tailWord_1131993 prefixEnd_1131993 581256506525094805881565 := by
  unfold tailWord_1131993
  simp only [CollatzResearch.WordTrace]
  refine ⟨41287176587990164857800633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27524784391993443238533755 41287176587990164857800633)
  ·
    refine ⟨30965382440992623643350475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41287176587990164857800633 30965382440992623643350475)
    ·
      refine ⟨46448073661488935465025713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30965382440992623643350475 46448073661488935465025713)
      ·
        refine ⟨34836055246116701598769285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46448073661488935465025713 34836055246116701598769285)
        ·
          refine ⟨6531760358646881549769241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 34836055246116701598769285 6531760358646881549769241)
          ·
            refine ⟨4898820268985161162326931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6531760358646881549769241 4898820268985161162326931)
            ·
              refine ⟨7348230403477741743490397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4898820268985161162326931 7348230403477741743490397)
              ·
                refine ⟨2755586401304153153808899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7348230403477741743490397 2755586401304153153808899)
                ·
                  refine ⟨4133379601956229730713349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2755586401304153153808899 4133379601956229730713349)
                  ·
                    refine ⟨775008675366793074508753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4133379601956229730713349 775008675366793074508753)
                    ·
                      refine ⟨581256506525094805881565, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 775008675366793074508753 581256506525094805881565)
                      ·
                        rfl

theorem cell23_1131993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 2, 1, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 2, 1, 3, 1, 4, 2].length) (baseStart_1131993 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1131993 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1131993 prefixEnd_1131993 := by exact prefixLift 1131993
  have htrace : WordTrace (prefixWord ++ tailWord_1131993) baseStart_1131993 baseEnd_1131993 := by
    simpa [prefixWord, tailWord_1131993, baseEnd_1131993] using wordTrace_append hprefix tailTrace_1131993
  have hstable : (prefixWord ++ tailWord_1131993).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1131993).length < 2 ^ (prefixWord ++ tailWord_1131993).sum := by decide
  have hdescent : baseEnd_1131993 < baseStart_1131993 := by decide
  rcases family_descends (prefixWord ++ tailWord_1131993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1132026 : List Nat := [3, 1, 1, 1, 1, 2, 3, 1, 4, 3, 3]
def baseStart_1132026 : Nat := 118140960795 + 1132026 * 2 ^ 59
def prefixEnd_1132026 : Nat := 4983230072969 + 3 ^ 40 * 1132026 * 2
def baseEnd_1132026 : Nat := 581273451386693176768913

theorem tailTrace_1132026 : CollatzResearch.WordTrace tailWord_1132026 prefixEnd_1132026 581273451386693176768913 := by
  unfold tailWord_1132026
  simp only [CollatzResearch.WordTrace]
  refine ⟨10322095049217652873437983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 27525586797913740995834621 10322095049217652873437983)
  ·
    refine ⟨15483142573826479310156975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10322095049217652873437983 15483142573826479310156975)
    ·
      refine ⟨23224713860739718965235463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15483142573826479310156975 23224713860739718965235463)
      ·
        refine ⟨34837070791109578447853195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23224713860739718965235463 34837070791109578447853195)
        ·
          refine ⟨52255606186664367671779793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34837070791109578447853195 52255606186664367671779793)
          ·
            refine ⟨39191704639998275753834845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 52255606186664367671779793 39191704639998275753834845)
            ·
              refine ⟨14696889239999353407688067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 39191704639998275753834845 14696889239999353407688067)
              ·
                refine ⟨22045333859999030111532101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14696889239999353407688067 22045333859999030111532101)
                ·
                  refine ⟨4133500098749818145912269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 22045333859999030111532101 4133500098749818145912269)
                  ·
                    refine ⟨1550062537031181804717101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4133500098749818145912269 1550062537031181804717101)
                    ·
                      refine ⟨581273451386693176768913, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1550062537031181804717101 581273451386693176768913)
                      ·
                        rfl

theorem cell23_1132026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 3, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 3, 1, 4, 3, 3].length) (baseStart_1132026 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1132026 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1132026 prefixEnd_1132026 := by exact prefixLift 1132026
  have htrace : WordTrace (prefixWord ++ tailWord_1132026) baseStart_1132026 baseEnd_1132026 := by
    simpa [prefixWord, tailWord_1132026, baseEnd_1132026] using wordTrace_append hprefix tailTrace_1132026
  have hstable : (prefixWord ++ tailWord_1132026).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1132026).length < 2 ^ (prefixWord ++ tailWord_1132026).sum := by decide
  have hdescent : baseEnd_1132026 < baseStart_1132026 := by decide
  rcases family_descends (prefixWord ++ tailWord_1132026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1132033 : List Nat := [1, 2, 4, 1, 4, 1, 2, 1, 7]
def baseStart_1132033 : Nat := 118140960795 + 1132033 * 2 ^ 59
def prefixEnd_1132033 : Nat := 4983230072969 + 3 ^ 40 * 1132033 * 2
def baseEnd_1132033 : Nat := 64586338416808294375709

theorem tailTrace_1132033 : CollatzResearch.WordTrace tailWord_1132033 prefixEnd_1132033 64586338416808294375709 := by
  unfold tailWord_1132033
  simp only [CollatzResearch.WordTrace]
  refine ⟨41288635507845251689256753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27525757005230167792837835 41288635507845251689256753)
  ·
    refine ⟨30966476630883938766942565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41288635507845251689256753 30966476630883938766942565)
    ·
      refine ⟨5806214368290738518801731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 30966476630883938766942565 5806214368290738518801731)
      ·
        refine ⟨8709321552436107778202597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5806214368290738518801731 8709321552436107778202597)
        ·
          refine ⟨1632997791081770208412987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8709321552436107778202597 1632997791081770208412987)
          ·
            refine ⟨2449496686622655312619481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1632997791081770208412987 2449496686622655312619481)
            ·
              refine ⟨1837122514966991484464611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2449496686622655312619481 1837122514966991484464611)
              ·
                refine ⟨2755683772450487226696917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1837122514966991484464611 2755683772450487226696917)
                ·
                  refine ⟨64586338416808294375709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2755683772450487226696917 64586338416808294375709)
                  ·
                    rfl

theorem cell23_1132033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 4, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 4, 1, 2, 1, 7].length) (baseStart_1132033 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1132033 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1132033 prefixEnd_1132033 := by exact prefixLift 1132033
  have htrace : WordTrace (prefixWord ++ tailWord_1132033) baseStart_1132033 baseEnd_1132033 := by
    simpa [prefixWord, tailWord_1132033, baseEnd_1132033] using wordTrace_append hprefix tailTrace_1132033
  have hstable : (prefixWord ++ tailWord_1132033).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1132033).length < 2 ^ (prefixWord ++ tailWord_1132033).sum := by decide
  have hdescent : baseEnd_1132033 < baseStart_1132033 := by decide
  rcases family_descends (prefixWord ++ tailWord_1132033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1132038 : List Nat := [6, 2, 1, 1, 2, 1, 3, 1, 2, 1, 3]
def baseStart_1132038 : Nat := 118140960795 + 1132038 * 2 ^ 59
def prefixEnd_1132038 : Nat := 4983230072969 + 3 ^ 40 * 1132038 * 2
def baseEnd_1132038 : Nat := 581279613154547129818859

theorem tailTrace_1132038 : CollatzResearch.WordTrace tailWord_1132038 prefixEnd_1132038 581279613154547129818859 := by
  unfold tailWord_1132038
  simp only [CollatzResearch.WordTrace]
  refine ⟨1290275558525848048224649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 27525878581884758362125845 1290275558525848048224649)
  ·
    refine ⟨967706668894386036168487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1290275558525848048224649 967706668894386036168487)
    ·
      refine ⟨1451560003341579054252731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 967706668894386036168487 1451560003341579054252731)
      ·
        refine ⟨2177340005012368581379097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1451560003341579054252731 2177340005012368581379097)
        ·
          refine ⟨1633005003759276436034323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2177340005012368581379097 1633005003759276436034323)
          ·
            refine ⟨2449507505638914654051485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1633005003759276436034323 2449507505638914654051485)
            ·
              refine ⟨918565314614592995269307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2449507505638914654051485 918565314614592995269307)
              ·
                refine ⟨1377847971921889492903961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 918565314614592995269307 1377847971921889492903961)
                ·
                  refine ⟨1033385978941417119677971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1377847971921889492903961 1033385978941417119677971)
                  ·
                    refine ⟨1550078968412125679516957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1033385978941417119677971 1550078968412125679516957)
                    ·
                      refine ⟨581279613154547129818859, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1550078968412125679516957 581279613154547129818859)
                      ·
                        rfl

theorem cell23_1132038_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 2, 1, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 2, 1, 3, 1, 2, 1, 3].length) (baseStart_1132038 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1132038 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1132038 prefixEnd_1132038 := by exact prefixLift 1132038
  have htrace : WordTrace (prefixWord ++ tailWord_1132038) baseStart_1132038 baseEnd_1132038 := by
    simpa [prefixWord, tailWord_1132038, baseEnd_1132038] using wordTrace_append hprefix tailTrace_1132038
  have hstable : (prefixWord ++ tailWord_1132038).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1132038).length < 2 ^ (prefixWord ++ tailWord_1132038).sum := by decide
  have hdescent : baseEnd_1132038 < baseStart_1132038 := by decide
  rcases family_descends (prefixWord ++ tailWord_1132038) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1132044 : List Nat := [2, 2, 1, 2, 5, 1, 3, 1, 2, 2, 2]
def baseStart_1132044 : Nat := 118140960795 + 1132044 * 2 ^ 59
def prefixEnd_1132044 : Nat := 4983230072969 + 3 ^ 40 * 1132044 * 2
def baseEnd_1132044 : Nat := 581282694038474106343831

theorem tailTrace_1132044 : CollatzResearch.WordTrace tailWord_1132044 prefixEnd_1132044 581282694038474106343831 := by
  unfold tailWord_1132044
  simp only [CollatzResearch.WordTrace]
  refine ⟨20644518355402700283953593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27526024473870267045271457 20644518355402700283953593)
  ·
    refine ⟨15483388766552025212965195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20644518355402700283953593 15483388766552025212965195)
    ·
      refine ⟨23225083149828037819447793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15483388766552025212965195 23225083149828037819447793)
      ·
        refine ⟨17418812362371028364585845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23225083149828037819447793 17418812362371028364585845)
        ·
          refine ⟨1633013658972283909179923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 17418812362371028364585845 1633013658972283909179923)
          ·
            refine ⟨2449520488458425863769885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1633013658972283909179923 2449520488458425863769885)
            ·
              refine ⟨918570183171909698913707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2449520488458425863769885 918570183171909698913707)
              ·
                refine ⟨1377855274757864548370561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 918570183171909698913707 1377855274757864548370561)
                ·
                  refine ⟨1033391456068398411277921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1377855274757864548370561 1033391456068398411277921)
                  ·
                    refine ⟨775043592051298808458441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1033391456068398411277921 775043592051298808458441)
                    ·
                      refine ⟨581282694038474106343831, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 775043592051298808458441 581282694038474106343831)
                      ·
                        rfl

theorem cell23_1132044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 5, 1, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 5, 1, 3, 1, 2, 2, 2].length) (baseStart_1132044 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1132044 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1132044 prefixEnd_1132044 := by exact prefixLift 1132044
  have htrace : WordTrace (prefixWord ++ tailWord_1132044) baseStart_1132044 baseEnd_1132044 := by
    simpa [prefixWord, tailWord_1132044, baseEnd_1132044] using wordTrace_append hprefix tailTrace_1132044
  have hstable : (prefixWord ++ tailWord_1132044).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1132044).length < 2 ^ (prefixWord ++ tailWord_1132044).sum := by decide
  have hdescent : baseEnd_1132044 < baseStart_1132044 := by decide
  rcases family_descends (prefixWord ++ tailWord_1132044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1132067 : List Nat := [1, 1, 1, 4, 6, 1, 1, 3, 5]
def baseStart_1132067 : Nat := 118140960795 + 1132067 * 2 ^ 59
def prefixEnd_1132067 : Nat := 4983230072969 + 3 ^ 40 * 1132067 * 2
def baseEnd_1132067 : Nat := 64588278232614168484025

theorem tailTrace_1132067 : CollatzResearch.WordTrace tailWord_1132067 prefixEnd_1132067 64588278232614168484025 := by
  unfold tailWord_1132067
  simp only [CollatzResearch.WordTrace]
  refine ⟨41289875589722075495994455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27526583726481383663996303 41289875589722075495994455)
  ·
    refine ⟨61934813384583113243991683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41289875589722075495994455 61934813384583113243991683)
    ·
      refine ⟨92902220076874669865987525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61934813384583113243991683 92902220076874669865987525)
      ·
        refine ⟨17419166264414000599872661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 92902220076874669865987525 17419166264414000599872661)
        ·
          refine ⟨816523418644406278119031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 17419166264414000599872661 816523418644406278119031)
          ·
            refine ⟨1224785127966609417178547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 816523418644406278119031 1224785127966609417178547)
            ·
              refine ⟨1837177691949914125767821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1224785127966609417178547 1837177691949914125767821)
              ·
                refine ⟨688941634481217797162933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1837177691949914125767821 688941634481217797162933)
                ·
                  refine ⟨64588278232614168484025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 688941634481217797162933 64588278232614168484025)
                  ·
                    rfl

theorem cell23_1132067_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 6, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 6, 1, 1, 3, 5].length) (baseStart_1132067 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1132067 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1132067 prefixEnd_1132067 := by exact prefixLift 1132067
  have htrace : WordTrace (prefixWord ++ tailWord_1132067) baseStart_1132067 baseEnd_1132067 := by
    simpa [prefixWord, tailWord_1132067, baseEnd_1132067] using wordTrace_append hprefix tailTrace_1132067
  have hstable : (prefixWord ++ tailWord_1132067).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1132067).length < 2 ^ (prefixWord ++ tailWord_1132067).sum := by decide
  have hdescent : baseEnd_1132067 < baseStart_1132067 := by decide
  rcases family_descends (prefixWord ++ tailWord_1132067) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1132083 : List Nat := [1, 1, 1, 2, 4, 4, 1, 2, 2, 1, 4]
def baseStart_1132083 : Nat := 118140960795 + 1132083 * 2 ^ 59
def prefixEnd_1132083 : Nat := 4983230072969 + 3 ^ 40 * 1132083 * 2
def baseEnd_1132083 : Nat := 581302719783999453756151

theorem tailTrace_1132083 : CollatzResearch.WordTrace tailWord_1132083 prefixEnd_1132083 581302719783999453756151 := by
  unfold tailWord_1132083
  simp only [CollatzResearch.WordTrace]
  refine ⟨41290459157664110228576903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27526972771776073485717935 41290459157664110228576903)
  ·
    refine ⟨61935688736496165342865355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41290459157664110228576903 61935688736496165342865355)
    ·
      refine ⟨92903533104744248014298033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61935688736496165342865355 92903533104744248014298033)
      ·
        refine ⟨69677649828558186010723525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 92903533104744248014298033 69677649828558186010723525)
        ·
          refine ⟨13064559342854659877010661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 69677649828558186010723525 13064559342854659877010661)
          ·
            refine ⟨2449604876785248726939499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 13064559342854659877010661 2449604876785248726939499)
            ·
              refine ⟨3674407315177873090409249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2449604876785248726939499 3674407315177873090409249)
              ·
                refine ⟨2755805486383404817806937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3674407315177873090409249 2755805486383404817806937)
                ·
                  refine ⟨2066854114787553613355203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2755805486383404817806937 2066854114787553613355203)
                  ·
                    refine ⟨3100281172181330420032805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2066854114787553613355203 3100281172181330420032805)
                    ·
                      refine ⟨581302719783999453756151, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3100281172181330420032805 581302719783999453756151)
                      ·
                        rfl

theorem cell23_1132083_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 4, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 4, 1, 2, 2, 1, 4].length) (baseStart_1132083 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1132083 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1132083 prefixEnd_1132083 := by exact prefixLift 1132083
  have htrace : WordTrace (prefixWord ++ tailWord_1132083) baseStart_1132083 baseEnd_1132083 := by
    simpa [prefixWord, tailWord_1132083, baseEnd_1132083] using wordTrace_append hprefix tailTrace_1132083
  have hstable : (prefixWord ++ tailWord_1132083).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1132083).length < 2 ^ (prefixWord ++ tailWord_1132083).sum := by decide
  have hdescent : baseEnd_1132083 < baseStart_1132083 := by decide
  rcases family_descends (prefixWord ++ tailWord_1132083) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1132143 : List Nat := [1, 1, 2, 1, 3, 2, 1, 2, 3, 5, 2]
def baseStart_1132143 : Nat := 118140960795 + 1132143 * 2 ^ 59
def prefixEnd_1132143 : Nat := 4983230072969 + 3 ^ 40 * 1132143 * 2
def baseEnd_1132143 : Nat := 581333528623269219005875

theorem tailTrace_1132143 : CollatzResearch.WordTrace tailWord_1132143 prefixEnd_1132143 581333528623269219005875 := by
  unfold tailWord_1132143
  simp only [CollatzResearch.WordTrace]
  refine ⟨41292647537446740475761083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27528431691631160317174055 41292647537446740475761083)
  ·
    refine ⟨61938971306170110713641625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41292647537446740475761083 61938971306170110713641625)
    ·
      refine ⟨46454228479627583035231219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 61938971306170110713641625 46454228479627583035231219)
      ·
        refine ⟨69681342719441374552846829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46454228479627583035231219 69681342719441374552846829)
        ·
          refine ⟨26130503519790515457317561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 69681342719441374552846829 26130503519790515457317561)
          ·
            refine ⟨19597877639842886592988171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26130503519790515457317561 19597877639842886592988171)
            ·
              refine ⟨29396816459764329889482257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19597877639842886592988171 29396816459764329889482257)
              ·
                refine ⟨22047612344823247417111693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29396816459764329889482257 22047612344823247417111693)
                ·
                  refine ⟨8267854629308717781416885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 22047612344823247417111693 8267854629308717781416885)
                  ·
                    refine ⟨775111371497692292007833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8267854629308717781416885 775111371497692292007833)
                    ·
                      refine ⟨581333528623269219005875, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 775111371497692292007833 581333528623269219005875)
                      ·
                        rfl

theorem cell23_1132143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 1, 2, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 1, 2, 3, 5, 2].length) (baseStart_1132143 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1132143 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1132143 prefixEnd_1132143 := by exact prefixLift 1132143
  have htrace : WordTrace (prefixWord ++ tailWord_1132143) baseStart_1132143 baseEnd_1132143 := by
    simpa [prefixWord, tailWord_1132143, baseEnd_1132143] using wordTrace_append hprefix tailTrace_1132143
  have hstable : (prefixWord ++ tailWord_1132143).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1132143).length < 2 ^ (prefixWord ++ tailWord_1132143).sum := by decide
  have hdescent : baseEnd_1132143 < baseStart_1132143 := by decide
  rcases family_descends (prefixWord ++ tailWord_1132143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1132144 : List Nat := [2, 1, 1, 1, 6, 3, 2, 2, 1, 4]
def baseStart_1132144 : Nat := 118140960795 + 1132144 * 2 ^ 59
def prefixEnd_1132144 : Nat := 4983230072969 + 3 ^ 40 * 1132144 * 2
def baseEnd_1132144 : Nat := 193778014034641238364457

theorem tailTrace_1132144 : CollatzResearch.WordTrace tailWord_1132144 prefixEnd_1132144 193778014034641238364457 := by
  unfold tailWord_1132144
  simp only [CollatzResearch.WordTrace]
  refine ⟨20646342005221558823273743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27528456006962078431031657 20646342005221558823273743)
  ·
    refine ⟨30969513007832338234910615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20646342005221558823273743 30969513007832338234910615)
    ·
      refine ⟨46454269511748507352365923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30969513007832338234910615 46454269511748507352365923)
      ·
        refine ⟨69681404267622761028548885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46454269511748507352365923 69681404267622761028548885)
        ·
          refine ⟨3266315825044816923213229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 69681404267622761028548885 3266315825044816923213229)
          ·
            refine ⟨1224868434391806346204961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3266315825044816923213229 1224868434391806346204961)
            ·
              refine ⟨918651325793854759653721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1224868434391806346204961 918651325793854759653721)
              ·
                refine ⟨688988494345391069740291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 918651325793854759653721 688988494345391069740291)
                ·
                  refine ⟨1033482741518086604610437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 688988494345391069740291 1033482741518086604610437)
                  ·
                    refine ⟨193778014034641238364457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1033482741518086604610437 193778014034641238364457)
                    ·
                      rfl

theorem cell23_1132144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 3, 2, 2, 1, 4].length) (baseStart_1132144 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1132144 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1132144 prefixEnd_1132144 := by exact prefixLift 1132144
  have htrace : WordTrace (prefixWord ++ tailWord_1132144) baseStart_1132144 baseEnd_1132144 := by
    simpa [prefixWord, tailWord_1132144, baseEnd_1132144] using wordTrace_append hprefix tailTrace_1132144
  have hstable : (prefixWord ++ tailWord_1132144).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1132144).length < 2 ^ (prefixWord ++ tailWord_1132144).sum := by decide
  have hdescent : baseEnd_1132144 < baseStart_1132144 := by decide
  rcases family_descends (prefixWord ++ tailWord_1132144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1132183 : List Nat := [1, 1, 3, 3, 2, 2, 2, 2, 1, 6]
def baseStart_1132183 : Nat := 118140960795 + 1132183 * 2 ^ 59
def prefixEnd_1132183 : Nat := 4983230072969 + 3 ^ 40 * 1132183 * 2
def baseEnd_1132183 : Nat := 193784689283149687501897

theorem tailTrace_1132183 : CollatzResearch.WordTrace tailWord_1132183 prefixEnd_1132183 193784689283149687501897 := by
  unfold tailWord_1132183
  simp only [CollatzResearch.WordTrace]
  refine ⟨41294106457301827307217203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27529404304867884871478135 41294106457301827307217203)
  ·
    refine ⟨61941159685952740960825805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41294106457301827307217203 61941159685952740960825805)
    ·
      refine ⟨23227934882232277860309677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 61941159685952740960825805 23227934882232277860309677)
      ·
        refine ⟨8710475580837104197616129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23227934882232277860309677 8710475580837104197616129)
        ·
          refine ⟨6532856685627828148212097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8710475580837104197616129 6532856685627828148212097)
          ·
            refine ⟨4899642514220871111159073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6532856685627828148212097 4899642514220871111159073)
            ·
              refine ⟨3674731885665653333369305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4899642514220871111159073 3674731885665653333369305)
              ·
                refine ⟨2756048914249240000026979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3674731885665653333369305 2756048914249240000026979)
                ·
                  refine ⟨4134073371373860000040469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2756048914249240000026979 4134073371373860000040469)
                  ·
                    refine ⟨193784689283149687501897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4134073371373860000040469 193784689283149687501897)
                    ·
                      rfl

theorem cell23_1132183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 2, 2, 2, 1, 6].length) (baseStart_1132183 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1132183 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1132183 prefixEnd_1132183 := by exact prefixLift 1132183
  have htrace : WordTrace (prefixWord ++ tailWord_1132183) baseStart_1132183 baseEnd_1132183 := by
    simpa [prefixWord, tailWord_1132183, baseEnd_1132183] using wordTrace_append hprefix tailTrace_1132183
  have hstable : (prefixWord ++ tailWord_1132183).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1132183).length < 2 ^ (prefixWord ++ tailWord_1132183).sum := by decide
  have hdescent : baseEnd_1132183 < baseStart_1132183 := by decide
  rcases family_descends (prefixWord ++ tailWord_1132183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1132184 : List Nat := [2, 1, 2, 4, 1, 3, 2, 3, 1, 1, 3]
def baseStart_1132184 : Nat := 118140960795 + 1132184 * 2 ^ 59
def prefixEnd_1132184 : Nat := 4983230072969 + 3 ^ 40 * 1132184 * 2
def baseEnd_1132184 : Nat := 581354581330103558593187

theorem tailTrace_1132184 : CollatzResearch.WordTrace tailWord_1132184 prefixEnd_1132184 581354581330103558593187 := by
  unfold tailWord_1132184
  simp only [CollatzResearch.WordTrace]
  refine ⟨20647071465149102239001803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27529428620198802985335737 20647071465149102239001803)
  ·
    refine ⟨30970607197723653358502705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20647071465149102239001803 30970607197723653358502705)
    ·
      refine ⟨23227955398292740018877029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30970607197723653358502705 23227955398292740018877029)
      ·
        refine ⟨4355241637179888753539443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 23227955398292740018877029 4355241637179888753539443)
        ·
          refine ⟨6532862455769833130309165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4355241637179888753539443 6532862455769833130309165)
          ·
            refine ⟨2449823420913687423865937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6532862455769833130309165 2449823420913687423865937)
            ·
              refine ⟨1837367565685265567899453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2449823420913687423865937 1837367565685265567899453)
              ·
                refine ⟨689012837131974587962295, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1837367565685265567899453 689012837131974587962295)
                ·
                  refine ⟨1033519255697961881943443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 689012837131974587962295 1033519255697961881943443)
                  ·
                    refine ⟨1550278883546942822915165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1033519255697961881943443 1550278883546942822915165)
                    ·
                      refine ⟨581354581330103558593187, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1550278883546942822915165 581354581330103558593187)
                      ·
                        rfl

theorem cell23_1132184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 3, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 3, 2, 3, 1, 1, 3].length) (baseStart_1132184 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1132184 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1132184 prefixEnd_1132184 := by exact prefixLift 1132184
  have htrace : WordTrace (prefixWord ++ tailWord_1132184) baseStart_1132184 baseEnd_1132184 := by
    simpa [prefixWord, tailWord_1132184, baseEnd_1132184] using wordTrace_append hprefix tailTrace_1132184
  have hstable : (prefixWord ++ tailWord_1132184).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1132184).length < 2 ^ (prefixWord ++ tailWord_1132184).sum := by decide
  have hdescent : baseEnd_1132184 < baseStart_1132184 := by decide
  rcases family_descends (prefixWord ++ tailWord_1132184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1132207 : List Nat := [1, 1, 2, 1, 2, 4, 4, 1, 3, 2, 2]
def baseStart_1132207 : Nat := 118140960795 + 1132207 * 2 ^ 59
def prefixEnd_1132207 : Nat := 4983230072969 + 3 ^ 40 * 1132207 * 2
def baseEnd_1132207 : Nat := 581366391385156968605581

theorem tailTrace_1132207 : CollatzResearch.WordTrace tailWord_1132207 prefixEnd_1132207 581366391385156968605581 := by
  unfold tailWord_1132207
  simp only [CollatzResearch.WordTrace]
  refine ⟨41294981809214879406090875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27529987872809919604060583 41294981809214879406090875)
  ·
    refine ⟨61942472713822319109136313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41294981809214879406090875 61942472713822319109136313)
    ·
      refine ⟨46456854535366739331852235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 61942472713822319109136313 46456854535366739331852235)
      ·
        refine ⟨69685281803050108997778353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46456854535366739331852235 69685281803050108997778353)
        ·
          refine ⟨52263961352287581748333765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 69685281803050108997778353 52263961352287581748333765)
          ·
            refine ⟨9799492753553921577812581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 52263961352287581748333765 9799492753553921577812581)
            ·
              refine ⟨1837404891291360295839859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9799492753553921577812581 1837404891291360295839859)
              ·
                refine ⟨2756107336937040443759789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1837404891291360295839859 2756107336937040443759789)
                ·
                  refine ⟨1033540251351390166409921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2756107336937040443759789 1033540251351390166409921)
                  ·
                    refine ⟨775155188513542624807441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1033540251351390166409921 775155188513542624807441)
                    ·
                      refine ⟨581366391385156968605581, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 775155188513542624807441 581366391385156968605581)
                      ·
                        rfl

theorem cell23_1132207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 4, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 4, 1, 3, 2, 2].length) (baseStart_1132207 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1132207 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1132207 prefixEnd_1132207 := by exact prefixLift 1132207
  have htrace : WordTrace (prefixWord ++ tailWord_1132207) baseStart_1132207 baseEnd_1132207 := by
    simpa [prefixWord, tailWord_1132207, baseEnd_1132207] using wordTrace_append hprefix tailTrace_1132207
  have hstable : (prefixWord ++ tailWord_1132207).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1132207).length < 2 ^ (prefixWord ++ tailWord_1132207).sum := by decide
  have hdescent : baseEnd_1132207 < baseStart_1132207 := by decide
  rcases family_descends (prefixWord ++ tailWord_1132207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1132220 : List Nat := [2, 2, 2, 3, 1, 2, 3, 1, 1, 2, 4]
def baseStart_1132220 : Nat := 118140960795 + 1132220 * 2 ^ 59
def prefixEnd_1132220 : Nat := 4983230072969 + 3 ^ 40 * 1132220 * 2
def baseEnd_1132220 : Nat := 581373066633665417743021

theorem tailTrace_1132220 : CollatzResearch.WordTrace tailWord_1132220 prefixEnd_1132220 581373066633665417743021 := by
  unfold tailWord_1132220
  simp only [CollatzResearch.WordTrace]
  refine ⟨20647727979083891313157057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27530303972111855084209409 20647727979083891313157057)
  ·
    refine ⟨15485795984312918484867793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20647727979083891313157057 15485795984312918484867793)
    ·
      refine ⟨11614346988234688863650845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15485795984312918484867793 11614346988234688863650845)
      ·
        refine ⟨4355380120588008323869067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11614346988234688863650845 4355380120588008323869067)
        ·
          refine ⟨6533070180882012485803601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4355380120588008323869067 6533070180882012485803601)
          ·
            refine ⟨4899802635661509364352701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6533070180882012485803601 4899802635661509364352701)
            ·
              refine ⟨1837425988373066011632263, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4899802635661509364352701 1837425988373066011632263)
              ·
                refine ⟨2756138982559599017448395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1837425988373066011632263 2756138982559599017448395)
                ·
                  refine ⟨4134208473839398526172593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2756138982559599017448395 4134208473839398526172593)
                  ·
                    refine ⟨3100656355379548894629445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4134208473839398526172593 3100656355379548894629445)
                    ·
                      refine ⟨581373066633665417743021, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3100656355379548894629445 581373066633665417743021)
                      ·
                        rfl

theorem cell23_1132220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 2, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 2, 3, 1, 1, 2, 4].length) (baseStart_1132220 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1132220 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1132220 prefixEnd_1132220 := by exact prefixLift 1132220
  have htrace : WordTrace (prefixWord ++ tailWord_1132220) baseStart_1132220 baseEnd_1132220 := by
    simpa [prefixWord, tailWord_1132220, baseEnd_1132220] using wordTrace_append hprefix tailTrace_1132220
  have hstable : (prefixWord ++ tailWord_1132220).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1132220).length < 2 ^ (prefixWord ++ tailWord_1132220).sum := by decide
  have hdescent : baseEnd_1132220 < baseStart_1132220 := by decide
  rcases family_descends (prefixWord ++ tailWord_1132220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1132241 : List Nat := [1, 2, 2, 1, 2, 6, 1, 3, 1, 2, 2]
def baseStart_1132241 : Nat := 118140960795 + 1132241 * 2 ^ 59
def prefixEnd_1132241 : Nat := 4983230072969 + 3 ^ 40 * 1132241 * 2
def baseEnd_1132241 : Nat := 581383849727409835580425

theorem tailTrace_1132241 : CollatzResearch.WordTrace tailWord_1132241 prefixEnd_1132241 581383849727409835580425 := by
  unfold tailWord_1132241
  simp only [CollatzResearch.WordTrace]
  refine ⟨41296221891091703212828577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27530814594061135475219051 41296221891091703212828577)
  ·
    refine ⟨30972166418318777409621433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41296221891091703212828577 30972166418318777409621433)
    ·
      refine ⟨23229124813739083057216075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30972166418318777409621433 23229124813739083057216075)
      ·
        refine ⟨34843687220608624585824113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23229124813739083057216075 34843687220608624585824113)
        ·
          refine ⟨26132765415456468439368085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34843687220608624585824113 26132765415456468439368085)
          ·
            refine ⟨1224973378849521958095379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 26132765415456468439368085 1224973378849521958095379)
            ·
              refine ⟨1837460068274282937143069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1224973378849521958095379 1837460068274282937143069)
              ·
                refine ⟨689047525602856101428651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1837460068274282937143069 689047525602856101428651)
                ·
                  refine ⟨1033571288404284152142977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 689047525602856101428651 1033571288404284152142977)
                  ·
                    refine ⟨775178466303213114107233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1033571288404284152142977 775178466303213114107233)
                    ·
                      refine ⟨581383849727409835580425, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 775178466303213114107233 581383849727409835580425)
                      ·
                        rfl

theorem cell23_1132241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 6, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 6, 1, 3, 1, 2, 2].length) (baseStart_1132241 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1132241 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1132241 prefixEnd_1132241 := by exact prefixLift 1132241
  have htrace : WordTrace (prefixWord ++ tailWord_1132241) baseStart_1132241 baseEnd_1132241 := by
    simpa [prefixWord, tailWord_1132241, baseEnd_1132241] using wordTrace_append hprefix tailTrace_1132241
  have hstable : (prefixWord ++ tailWord_1132241).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1132241).length < 2 ^ (prefixWord ++ tailWord_1132241).sum := by decide
  have hdescent : baseEnd_1132241 < baseStart_1132241 := by decide
  rcases family_descends (prefixWord ++ tailWord_1132241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1132283 : List Nat := [1, 1, 1, 1, 1, 3, 1, 3, 4, 4, 3]
def baseStart_1132283 : Nat := 118140960795 + 1132283 * 2 ^ 59
def prefixEnd_1132283 : Nat := 4983230072969 + 3 ^ 40 * 1132283 * 2
def baseEnd_1132283 : Nat := 581405415914898671255231

theorem tailTrace_1132283 : CollatzResearch.WordTrace tailWord_1132283 prefixEnd_1132283 581405415914898671255231 := by
  unfold tailWord_1132283
  simp only [CollatzResearch.WordTrace]
  refine ⟨41297753756939544385857503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27531835837959696257238335 41297753756939544385857503)
  ·
    refine ⟨61946630635409316578786255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41297753756939544385857503 61946630635409316578786255)
    ·
      refine ⟨92919945953113974868179383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61946630635409316578786255 92919945953113974868179383)
      ·
        refine ⟨139379918929670962302269075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 92919945953113974868179383 139379918929670962302269075)
        ·
          refine ⟨209069878394506443453403613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 139379918929670962302269075 209069878394506443453403613)
          ·
            refine ⟨78401204397939916295026355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 209069878394506443453403613 78401204397939916295026355)
            ·
              refine ⟨117601806596909874442539533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 78401204397939916295026355 117601806596909874442539533)
              ·
                refine ⟨44100677473841202915952325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 117601806596909874442539533 44100677473841202915952325)
                ·
                  refine ⟨8268877026345225546741061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 44100677473841202915952325 8268877026345225546741061)
                  ·
                    refine ⟨1550414442439729790013949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 8268877026345225546741061 1550414442439729790013949)
                    ·
                      refine ⟨581405415914898671255231, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1550414442439729790013949 581405415914898671255231)
                      ·
                        rfl

theorem cell23_1132283_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 4, 4, 3].length) (baseStart_1132283 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1132283 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1132283 prefixEnd_1132283 := by exact prefixLift 1132283
  have htrace : WordTrace (prefixWord ++ tailWord_1132283) baseStart_1132283 baseEnd_1132283 := by
    simpa [prefixWord, tailWord_1132283, baseEnd_1132283] using wordTrace_append hprefix tailTrace_1132283
  have hstable : (prefixWord ++ tailWord_1132283).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1132283).length < 2 ^ (prefixWord ++ tailWord_1132283).sum := by decide
  have hdescent : baseEnd_1132283 < baseStart_1132283 := by decide
  rcases family_descends (prefixWord ++ tailWord_1132283) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1132293 : List Nat := [1, 3, 1, 1, 2, 1, 1, 1, 6, 2, 4]
def baseStart_1132293 : Nat := 118140960795 + 1132293 * 2 ^ 59
def prefixEnd_1132293 : Nat := 4983230072969 + 3 ^ 40 * 1132293 * 2
def baseEnd_1132293 : Nat := 581410550721443632130185

theorem tailTrace_1132293 : CollatzResearch.WordTrace tailWord_1132293 prefixEnd_1132293 581410550721443632130185 := by
  unfold tailWord_1132293
  simp only [CollatzResearch.WordTrace]
  refine ⟨41298118486903316093721533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27532078991268877395814355 41298118486903316093721533)
  ·
    refine ⟨15486794432588743535145575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 41298118486903316093721533 15486794432588743535145575)
    ·
      refine ⟨23230191648883115302718363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15486794432588743535145575 23230191648883115302718363)
      ·
        refine ⟨34845287473324672954077545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23230191648883115302718363 34845287473324672954077545)
        ·
          refine ⟨26133965604993504715558159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34845287473324672954077545 26133965604993504715558159)
          ·
            refine ⟨39200948407490257073337239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26133965604993504715558159 39200948407490257073337239)
            ·
              refine ⟨58801422611235385610005859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39200948407490257073337239 58801422611235385610005859)
              ·
                refine ⟨88202133916853078415008789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 58801422611235385610005859 88202133916853078415008789)
                ·
                  refine ⟨4134475027352488050703537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 88202133916853078415008789 4134475027352488050703537)
                  ·
                    refine ⟨3100856270514366038027653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4134475027352488050703537 3100856270514366038027653)
                    ·
                      refine ⟨581410550721443632130185, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3100856270514366038027653 581410550721443632130185)
                      ·
                        rfl

theorem cell23_1132293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 1, 1, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 1, 1, 6, 2, 4].length) (baseStart_1132293 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1132293 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1132293 prefixEnd_1132293 := by exact prefixLift 1132293
  have htrace : WordTrace (prefixWord ++ tailWord_1132293) baseStart_1132293 baseEnd_1132293 := by
    simpa [prefixWord, tailWord_1132293, baseEnd_1132293] using wordTrace_append hprefix tailTrace_1132293
  have hstable : (prefixWord ++ tailWord_1132293).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1132293).length < 2 ^ (prefixWord ++ tailWord_1132293).sum := by decide
  have hdescent : baseEnd_1132293 < baseStart_1132293 := by decide
  rcases family_descends (prefixWord ++ tailWord_1132293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1132314 : List Nat := [3, 1, 1, 3, 2, 2, 1, 4, 2, 2, 2]
def baseStart_1132314 : Nat := 118140960795 + 1132314 * 2 ^ 59
def prefixEnd_1132314 : Nat := 4983230072969 + 3 ^ 40 * 1132314 * 2
def baseEnd_1132314 : Nat := 581421333815188049967589

theorem tailTrace_1132314 : CollatzResearch.WordTrace tailWord_1132314 prefixEnd_1132314 581421333815188049967589 := by
  unfold tailWord_1132314
  simp only [CollatzResearch.WordTrace]
  refine ⟨10324721104956809170058999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 27532589613218157786823997 10324721104956809170058999)
  ·
    refine ⟨15487081657435213755088499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10324721104956809170058999 15487081657435213755088499)
    ·
      refine ⟨23230622486152820632632749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15487081657435213755088499 23230622486152820632632749)
      ·
        refine ⟨8711483432307307737237281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23230622486152820632632749 8711483432307307737237281)
        ·
          refine ⟨6533612574230480802927961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8711483432307307737237281 6533612574230480802927961)
          ·
            refine ⟨4900209430672860602195971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6533612574230480802927961 4900209430672860602195971)
            ·
              refine ⟨7350314146009290903293957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4900209430672860602195971 7350314146009290903293957)
              ·
                refine ⟨1378183902376742044367617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7350314146009290903293957 1378183902376742044367617)
                ·
                  refine ⟨1033637926782556533275713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1378183902376742044367617 1033637926782556533275713)
                  ·
                    refine ⟨775228445086917399956785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1033637926782556533275713 775228445086917399956785)
                    ·
                      refine ⟨581421333815188049967589, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 775228445086917399956785 581421333815188049967589)
                      ·
                        rfl

theorem cell23_1132314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 2, 1, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 2, 1, 4, 2, 2, 2].length) (baseStart_1132314 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1132314 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1132314 prefixEnd_1132314 := by exact prefixLift 1132314
  have htrace : WordTrace (prefixWord ++ tailWord_1132314) baseStart_1132314 baseEnd_1132314 := by
    simpa [prefixWord, tailWord_1132314, baseEnd_1132314] using wordTrace_append hprefix tailTrace_1132314
  have hstable : (prefixWord ++ tailWord_1132314).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1132314).length < 2 ^ (prefixWord ++ tailWord_1132314).sum := by decide
  have hdescent : baseEnd_1132314 < baseStart_1132314 := by decide
  rcases family_descends (prefixWord ++ tailWord_1132314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1132343 : List Nat := [1, 1, 3, 1, 2, 1, 2, 2, 3, 2, 5]
def baseStart_1132343 : Nat := 118140960795 + 1132343 * 2 ^ 59
def prefixEnd_1132343 : Nat := 4983230072969 + 3 ^ 40 * 1132343 * 2
def baseEnd_1132343 : Nat := 581436224754168436504955

theorem tailTrace_1132343 : CollatzResearch.WordTrace tailWord_1132343 prefixEnd_1132343 581436224754168436504955 := by
  unfold tailWord_1132343
  simp only [CollatzResearch.WordTrace]
  refine ⟨41299942136722174633041683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27533294757814783088694455 41299942136722174633041683)
  ·
    refine ⟨61949913205083261949562525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41299942136722174633041683 61949913205083261949562525)
    ·
      refine ⟨23231217451906223231085947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 61949913205083261949562525 23231217451906223231085947)
      ·
        refine ⟨34846826177859334846628921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23231217451906223231085947 34846826177859334846628921)
        ·
          refine ⟨26135119633394501134971691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34846826177859334846628921 26135119633394501134971691)
          ·
            refine ⟨39202679450091751702457537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26135119633394501134971691 39202679450091751702457537)
            ·
              refine ⟨29402009587568813776843153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 39202679450091751702457537 29402009587568813776843153)
              ·
                refine ⟨22051507190676610332632365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29402009587568813776843153 22051507190676610332632365)
                ·
                  refine ⟨8269315196503728874737137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 22051507190676610332632365 8269315196503728874737137)
                  ·
                    refine ⟨6201986397377796656052853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8269315196503728874737137 6201986397377796656052853)
                    ·
                      refine ⟨581436224754168436504955, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 6201986397377796656052853 581436224754168436504955)
                      ·
                        rfl

theorem cell23_1132343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 2, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 2, 2, 3, 2, 5].length) (baseStart_1132343 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1132343 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1132343 prefixEnd_1132343 := by exact prefixLift 1132343
  have htrace : WordTrace (prefixWord ++ tailWord_1132343) baseStart_1132343 baseEnd_1132343 := by
    simpa [prefixWord, tailWord_1132343, baseEnd_1132343] using wordTrace_append hprefix tailTrace_1132343
  have hstable : (prefixWord ++ tailWord_1132343).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1132343).length < 2 ^ (prefixWord ++ tailWord_1132343).sum := by decide
  have hdescent : baseEnd_1132343 < baseStart_1132343 := by decide
  rcases family_descends (prefixWord ++ tailWord_1132343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1132397 : List Nat := [1, 5, 1, 1, 1, 1, 4, 2, 3, 4]
def baseStart_1132397 : Nat := 118140960795 + 1132397 * 2 ^ 59
def prefixEnd_1132397 : Nat := 4983230072969 + 3 ^ 40 * 1132397 * 2
def baseEnd_1132397 : Nat := 193821317569837075076569

theorem tailTrace_1132397 : CollatzResearch.WordTrace tailWord_1132397 prefixEnd_1132397 193821317569837075076569 := by
  unfold tailWord_1132397
  simp only [CollatzResearch.WordTrace]
  refine ⟨41301911678526541855507445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27534607785684361237004963 41301911678526541855507445)
  ·
    refine ⟨3872054219861863298953823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 41301911678526541855507445 3872054219861863298953823)
    ·
      refine ⟨5808081329792794948430735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3872054219861863298953823 5808081329792794948430735)
      ·
        refine ⟨8712121994689192422646103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5808081329792794948430735 8712121994689192422646103)
        ·
          refine ⟨13068182992033788633969155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8712121994689192422646103 13068182992033788633969155)
          ·
            refine ⟨19602274488050682950953733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13068182992033788633969155 19602274488050682950953733)
            ·
              refine ⟨3675426466509503053303825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 19602274488050682950953733 3675426466509503053303825)
              ·
                refine ⟨2756569849882127289977869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3675426466509503053303825 2756569849882127289977869)
                ·
                  refine ⟨1033713693705797733741701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2756569849882127289977869 1033713693705797733741701)
                  ·
                    refine ⟨193821317569837075076569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1033713693705797733741701 193821317569837075076569)
                    ·
                      rfl

theorem cell23_1132397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 4, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 4, 2, 3, 4].length) (baseStart_1132397 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1132397 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1132397 prefixEnd_1132397 := by exact prefixLift 1132397
  have htrace : WordTrace (prefixWord ++ tailWord_1132397) baseStart_1132397 baseEnd_1132397 := by
    simpa [prefixWord, tailWord_1132397, baseEnd_1132397] using wordTrace_append hprefix tailTrace_1132397
  have hstable : (prefixWord ++ tailWord_1132397).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1132397).length < 2 ^ (prefixWord ++ tailWord_1132397).sum := by decide
  have hdescent : baseEnd_1132397 < baseStart_1132397 := by decide
  rcases family_descends (prefixWord ++ tailWord_1132397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1132424 : List Nat := [2, 1, 3, 3, 3, 1, 1, 2, 2, 2, 3]
def baseStart_1132424 : Nat := 118140960795 + 1132424 * 2 ^ 59
def prefixEnd_1132424 : Nat := 4983230072969 + 3 ^ 40 * 1132424 * 2
def baseEnd_1132424 : Nat := 581477816687182619592083

theorem tailTrace_1132424 : CollatzResearch.WordTrace tailWord_1132424 prefixEnd_1132424 581477816687182619592083 := by
  unfold tailWord_1132424
  simp only [CollatzResearch.WordTrace]
  refine ⟨20651448224714362733370163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27535264299619150311160217 20651448224714362733370163)
  ·
    refine ⟨30977172337071544100055245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20651448224714362733370163 30977172337071544100055245)
    ·
      refine ⟨11616439626401829037520717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 30977172337071544100055245 11616439626401829037520717)
      ·
        refine ⟨4356164859900685889070269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11616439626401829037520717 4356164859900685889070269)
        ·
          refine ⟨1633561822462757208401351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4356164859900685889070269 1633561822462757208401351)
          ·
            refine ⟨2450342733694135812602027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1633561822462757208401351 2450342733694135812602027)
            ·
              refine ⟨3675514100541203718903041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2450342733694135812602027 3675514100541203718903041)
              ·
                refine ⟨2756635575405902789177281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3675514100541203718903041 2756635575405902789177281)
                ·
                  refine ⟨2067476681554427091882961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2756635575405902789177281 2067476681554427091882961)
                  ·
                    refine ⟨1550607511165820318912221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2067476681554427091882961 1550607511165820318912221)
                    ·
                      refine ⟨581477816687182619592083, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1550607511165820318912221 581477816687182619592083)
                      ·
                        rfl

theorem cell23_1132424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 3, 1, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 3, 1, 1, 2, 2, 2, 3].length) (baseStart_1132424 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1132424 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1132424 prefixEnd_1132424 := by exact prefixLift 1132424
  have htrace : WordTrace (prefixWord ++ tailWord_1132424) baseStart_1132424 baseEnd_1132424 := by
    simpa [prefixWord, tailWord_1132424, baseEnd_1132424] using wordTrace_append hprefix tailTrace_1132424
  have hstable : (prefixWord ++ tailWord_1132424).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1132424).length < 2 ^ (prefixWord ++ tailWord_1132424).sum := by decide
  have hdescent : baseEnd_1132424 < baseStart_1132424 := by decide
  rcases family_descends (prefixWord ++ tailWord_1132424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1132444 : List Nat := [2, 2, 3, 3, 1, 1, 4, 1, 6]
def baseStart_1132444 : Nat := 118140960795 + 1132444 * 2 ^ 59
def prefixEnd_1132444 : Nat := 4983230072969 + 3 ^ 40 * 1132444 * 2
def baseEnd_1132444 : Nat := 64609787366696949037999

theorem tailTrace_1132444 : CollatzResearch.WordTrace tailWord_1132444 prefixEnd_1132444 64609787366696949037999 := by
  unfold tailWord_1132444
  simp only [CollatzResearch.WordTrace]
  refine ⟨20651812954678134441234193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27535750606237512588312257 20651812954678134441234193)
  ·
    refine ⟨15488859716008600830925645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20651812954678134441234193 15488859716008600830925645)
    ·
      refine ⟨5808322393503225311597117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15488859716008600830925645 5808322393503225311597117)
      ·
        refine ⟨2178120897563709491848919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5808322393503225311597117 2178120897563709491848919)
        ·
          refine ⟨3267181346345564237773379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2178120897563709491848919 3267181346345564237773379)
          ·
            refine ⟨4900772019518346356660069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3267181346345564237773379 4900772019518346356660069)
            ·
              refine ⟨918894753659689941873763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4900772019518346356660069 918894753659689941873763)
              ·
                refine ⟨1378342130489534912810645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 918894753659689941873763 1378342130489534912810645)
                ·
                  refine ⟨64609787366696949037999, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1378342130489534912810645 64609787366696949037999)
                  ·
                    rfl

theorem cell23_1132444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 1, 4, 1, 6].length) (baseStart_1132444 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1132444 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1132444 prefixEnd_1132444 := by exact prefixLift 1132444
  have htrace : WordTrace (prefixWord ++ tailWord_1132444) baseStart_1132444 baseEnd_1132444 := by
    simpa [prefixWord, tailWord_1132444, baseEnd_1132444] using wordTrace_append hprefix tailTrace_1132444
  have hstable : (prefixWord ++ tailWord_1132444).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1132444).length < 2 ^ (prefixWord ++ tailWord_1132444).sum := by decide
  have hdescent : baseEnd_1132444 < baseStart_1132444 := by decide
  rcases family_descends (prefixWord ++ tailWord_1132444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1132488 : List Nat := [2, 1, 3, 1, 4, 1, 4, 2, 1, 1, 3]
def baseStart_1132488 : Nat := 118140960795 + 1132488 * 2 ^ 59
def prefixEnd_1132488 : Nat := 4983230072969 + 3 ^ 40 * 1132488 * 2
def baseEnd_1132488 : Nat := 581510679449070369191789

theorem tailTrace_1132488 : CollatzResearch.WordTrace tailWord_1132488 prefixEnd_1132488 581510679449070369191789 := by
  unfold tailWord_1132488
  simp only [CollatzResearch.WordTrace]
  refine ⟨20652615360598432198535059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27536820480797909598046745 20652615360598432198535059)
  ·
    refine ⟨30978923040897648297802589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20652615360598432198535059 30978923040897648297802589)
    ·
      refine ⟨11617096140336618111675971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 30978923040897648297802589 11617096140336618111675971)
      ·
        refine ⟨17425644210504927167513957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11617096140336618111675971 17425644210504927167513957)
        ·
          refine ⟨3267308289469673843908867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 17425644210504927167513957 3267308289469673843908867)
          ·
            refine ⟨4900962434204510765863301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3267308289469673843908867 4900962434204510765863301)
            ·
              refine ⟨918930456413345768599369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4900962434204510765863301 918930456413345768599369)
              ·
                refine ⟨689197842310009326449527, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 918930456413345768599369 689197842310009326449527)
                ·
                  refine ⟨1033796763465013989674291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 689197842310009326449527 1033796763465013989674291)
                  ·
                    refine ⟨1550695145197520984511437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1033796763465013989674291 1550695145197520984511437)
                    ·
                      refine ⟨581510679449070369191789, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1550695145197520984511437 581510679449070369191789)
                      ·
                        rfl

theorem cell23_1132488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 1, 4, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 1, 4, 2, 1, 1, 3].length) (baseStart_1132488 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1132488 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1132488 prefixEnd_1132488 := by exact prefixLift 1132488
  have htrace : WordTrace (prefixWord ++ tailWord_1132488) baseStart_1132488 baseEnd_1132488 := by
    simpa [prefixWord, tailWord_1132488, baseEnd_1132488] using wordTrace_append hprefix tailTrace_1132488
  have hstable : (prefixWord ++ tailWord_1132488).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1132488).length < 2 ^ (prefixWord ++ tailWord_1132488).sum := by decide
  have hdescent : baseEnd_1132488 < baseStart_1132488 := by decide
  rcases family_descends (prefixWord ++ tailWord_1132488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1132490 : List Nat := [3, 1, 2, 1, 2, 1, 2, 1, 3, 1, 6]
def baseStart_1132490 : Nat := 118140960795 + 1132490 * 2 ^ 59
def prefixEnd_1132490 : Nat := 4983230072969 + 3 ^ 40 * 1132490 * 2
def baseEnd_1132490 : Nat := 581511706410379361366779

theorem tailTrace_1132490 : CollatzResearch.WordTrace tailWord_1132490 prefixEnd_1132490 581511706410379361366779 := by
  unfold tailWord_1132490
  simp only [CollatzResearch.WordTrace]
  refine ⟨10326325916797404684660731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 27536869111459745825761949 10326325916797404684660731)
  ·
    refine ⟨15489488875196107026991097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10326325916797404684660731 15489488875196107026991097)
    ·
      refine ⟨11617116656397080270243323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15489488875196107026991097 11617116656397080270243323)
      ·
        refine ⟨17425674984595620405364985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11617116656397080270243323 17425674984595620405364985)
        ·
          refine ⟨13069256238446715304023739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17425674984595620405364985 13069256238446715304023739)
          ·
            refine ⟨19603884357670072956035609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13069256238446715304023739 19603884357670072956035609)
            ·
              refine ⟨14702913268252554717026707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19603884357670072956035609 14702913268252554717026707)
              ·
                refine ⟨22054369902378832075540061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14702913268252554717026707 22054369902378832075540061)
                ·
                  refine ⟨8270388713392062028327523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 22054369902378832075540061 8270388713392062028327523)
                  ·
                    refine ⟨12405583070088093042491285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8270388713392062028327523 12405583070088093042491285)
                    ·
                      refine ⟨581511706410379361366779, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 12405583070088093042491285 581511706410379361366779)
                      ·
                        rfl

theorem cell23_1132490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 2, 1, 3, 1, 6].length) (baseStart_1132490 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1132490 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1132490 prefixEnd_1132490 := by exact prefixLift 1132490
  have htrace : WordTrace (prefixWord ++ tailWord_1132490) baseStart_1132490 baseEnd_1132490 := by
    simpa [prefixWord, tailWord_1132490, baseEnd_1132490] using wordTrace_append hprefix tailTrace_1132490
  have hstable : (prefixWord ++ tailWord_1132490).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1132490).length < 2 ^ (prefixWord ++ tailWord_1132490).sum := by decide
  have hdescent : baseEnd_1132490 < baseStart_1132490 := by decide
  rcases family_descends (prefixWord ++ tailWord_1132490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1132511 : List Nat := [1, 1, 2, 3, 4, 2, 1, 2, 3, 2, 2]
def baseStart_1132511 : Nat := 118140960795 + 1132511 * 2 ^ 59
def prefixEnd_1132511 : Nat := 4983230072969 + 3 ^ 40 * 1132511 * 2
def baseEnd_1132511 : Nat := 581522489504123779204183

theorem tailTrace_1132511 : CollatzResearch.WordTrace tailWord_1132511 prefixEnd_1132511 581522489504123779204183 := by
  unfold tailWord_1132511
  simp only [CollatzResearch.WordTrace]
  refine ⟨41306069600113539325157387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27537379733409026216771591 41306069600113539325157387)
  ·
    refine ⟨61959104400170308987736081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41306069600113539325157387 61959104400170308987736081)
    ·
      refine ⟨46469328300127731740802061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 61959104400170308987736081 46469328300127731740802061)
      ·
        refine ⟨17425998112547899402800773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 46469328300127731740802061 17425998112547899402800773)
        ·
          refine ⟨3267374646102731138025145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 17425998112547899402800773 3267374646102731138025145)
          ·
            refine ⟨2450530984577048353518859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3267374646102731138025145 2450530984577048353518859)
            ·
              refine ⟨3675796476865572530278289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2450530984577048353518859 3675796476865572530278289)
              ·
                refine ⟨2756847357649179397708717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3675796476865572530278289 2756847357649179397708717)
                ·
                  refine ⟨1033817759118442274140769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2756847357649179397708717 1033817759118442274140769)
                  ·
                    refine ⟨775363319338831705605577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1033817759118442274140769 775363319338831705605577)
                    ·
                      refine ⟨581522489504123779204183, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 775363319338831705605577 581522489504123779204183)
                      ·
                        rfl

theorem cell23_1132511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 2, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 2, 1, 2, 3, 2, 2].length) (baseStart_1132511 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1132511 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1132511 prefixEnd_1132511 := by exact prefixLift 1132511
  have htrace : WordTrace (prefixWord ++ tailWord_1132511) baseStart_1132511 baseEnd_1132511 := by
    simpa [prefixWord, tailWord_1132511, baseEnd_1132511] using wordTrace_append hprefix tailTrace_1132511
  have hstable : (prefixWord ++ tailWord_1132511).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1132511).length < 2 ^ (prefixWord ++ tailWord_1132511).sum := by decide
  have hdescent : baseEnd_1132511 < baseStart_1132511 := by decide
  rcases family_descends (prefixWord ++ tailWord_1132511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1132525 : List Nat := [1, 5, 1, 4, 2, 1, 2, 1, 1, 5]
def baseStart_1132525 : Nat := 118140960795 + 1132525 * 2 ^ 59
def prefixEnd_1132525 : Nat := 4983230072969 + 3 ^ 40 * 1132525 * 2
def baseEnd_1132525 : Nat := 193843226077762241476373

theorem tailTrace_1132525 : CollatzResearch.WordTrace tailWord_1132525 prefixEnd_1132525 193843226077762241476373 := by
  unfold tailWord_1132525
  simp only [CollatzResearch.WordTrace]
  refine ⟨41306580222062819716167029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27537720148041879810778019 41306580222062819716167029)
  ·
    refine ⟨3872491895818389348390659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 41306580222062819716167029 3872491895818389348390659)
    ·
      refine ⟨5808737843727584022585989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3872491895818389348390659 5808737843727584022585989)
      ·
        refine ⟨1089138345698922004234873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5808737843727584022585989 1089138345698922004234873)
        ·
          refine ⟨816853759274191503176155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1089138345698922004234873 816853759274191503176155)
          ·
            refine ⟨1225280638911287254764233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 816853759274191503176155 1225280638911287254764233)
            ·
              refine ⟨918960479183465441073175, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1225280638911287254764233 918960479183465441073175)
              ·
                refine ⟨1378440718775198161609763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 918960479183465441073175 1378440718775198161609763)
                ·
                  refine ⟨2067661078162797242414645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1378440718775198161609763 2067661078162797242414645)
                  ·
                    refine ⟨193843226077762241476373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2067661078162797242414645 193843226077762241476373)
                    ·
                      rfl

theorem cell23_1132525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 2, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 2, 1, 2, 1, 1, 5].length) (baseStart_1132525 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1132525 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1132525 prefixEnd_1132525 := by exact prefixLift 1132525
  have htrace : WordTrace (prefixWord ++ tailWord_1132525) baseStart_1132525 baseEnd_1132525 := by
    simpa [prefixWord, tailWord_1132525, baseEnd_1132525] using wordTrace_append hprefix tailTrace_1132525
  have hstable : (prefixWord ++ tailWord_1132525).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1132525).length < 2 ^ (prefixWord ++ tailWord_1132525).sum := by decide
  have hdescent : baseEnd_1132525 < baseStart_1132525 := by decide
  rcases family_descends (prefixWord ++ tailWord_1132525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1132527 : List Nat := [1, 1, 2, 1, 4, 2, 1, 4, 1, 3, 3]
def baseStart_1132527 : Nat := 118140960795 + 1132527 * 2 ^ 59
def prefixEnd_1132527 : Nat := 4983230072969 + 3 ^ 40 * 1132527 * 2
def baseEnd_1132527 : Nat := 581530705194595716604109

theorem tailTrace_1132527 : CollatzResearch.WordTrace tailWord_1132527 prefixEnd_1132527 581530705194595716604109 := by
  unfold tailWord_1132527
  simp only [CollatzResearch.WordTrace]
  refine ⟨41306653168055574057739835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27537768778703716038493223 41306653168055574057739835)
  ·
    refine ⟨61959979752083361086609753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41306653168055574057739835 61959979752083361086609753)
    ·
      refine ⟨46469984814062520814957315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 61959979752083361086609753 46469984814062520814957315)
      ·
        refine ⟨69704977221093781222435973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46469984814062520814957315 69704977221093781222435973)
        ·
          refine ⟨13069683228955083979206745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 69704977221093781222435973 13069683228955083979206745)
          ·
            refine ⟨9802262421716312984405059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13069683228955083979206745 9802262421716312984405059)
            ·
              refine ⟨14703393632574469476607589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9802262421716312984405059 14703393632574469476607589)
              ·
                refine ⟨2756886306107713026863923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14703393632574469476607589 2756886306107713026863923)
                ·
                  refine ⟨4135329459161569540295885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2756886306107713026863923 4135329459161569540295885)
                  ·
                    refine ⟨1550748547185588577610957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4135329459161569540295885 1550748547185588577610957)
                    ·
                      refine ⟨581530705194595716604109, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1550748547185588577610957 581530705194595716604109)
                      ·
                        rfl

theorem cell23_1132527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 1, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 1, 4, 1, 3, 3].length) (baseStart_1132527 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1132527 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1132527 prefixEnd_1132527 := by exact prefixLift 1132527
  have htrace : WordTrace (prefixWord ++ tailWord_1132527) baseStart_1132527 baseEnd_1132527 := by
    simpa [prefixWord, tailWord_1132527, baseEnd_1132527] using wordTrace_append hprefix tailTrace_1132527
  have hstable : (prefixWord ++ tailWord_1132527).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1132527).length < 2 ^ (prefixWord ++ tailWord_1132527).sum := by decide
  have hdescent : baseEnd_1132527 < baseStart_1132527 := by decide
  rcases family_descends (prefixWord ++ tailWord_1132527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1132544 : List Nat := [2, 1, 1, 2, 1, 1, 1, 8, 2, 1, 3]
def baseStart_1132544 : Nat := 118140960795 + 1132544 * 2 ^ 59
def prefixEnd_1132544 : Nat := 4983230072969 + 3 ^ 40 * 1132544 * 2
def baseEnd_1132544 : Nat := 581539434365722150091531

theorem tailTrace_1132544 : CollatzResearch.WordTrace tailWord_1132544 prefixEnd_1132544 581539434365722150091531 := by
  unfold tailWord_1132544
  simp only [CollatzResearch.WordTrace]
  refine ⟨20653636604496992980554343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27538182139329323974072457 20653636604496992980554343)
  ·
    refine ⟨30980454906745489470831515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20653636604496992980554343 30980454906745489470831515)
    ·
      refine ⟨46470682360118234206247273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30980454906745489470831515 46470682360118234206247273)
      ·
        refine ⟨34853011770088675654685455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46470682360118234206247273 34853011770088675654685455)
        ·
          refine ⟨52279517655133013482028183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34853011770088675654685455 52279517655133013482028183)
          ·
            refine ⟨78419276482699520223042275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 52279517655133013482028183 78419276482699520223042275)
            ·
              refine ⟨117628914724049280334563413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 78419276482699520223042275 117628914724049280334563413)
              ·
                refine ⟨1378463844422452503920665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 117628914724049280334563413 1378463844422452503920665)
                ·
                  refine ⟨1033847883316839377940499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1378463844422452503920665 1033847883316839377940499)
                  ·
                    refine ⟨1550771824975259066910749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1033847883316839377940499 1550771824975259066910749)
                    ·
                      refine ⟨581539434365722150091531, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1550771824975259066910749 581539434365722150091531)
                      ·
                        rfl

theorem cell23_1132544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 8, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 8, 2, 1, 3].length) (baseStart_1132544 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1132544 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1132544 prefixEnd_1132544 := by exact prefixLift 1132544
  have htrace : WordTrace (prefixWord ++ tailWord_1132544) baseStart_1132544 baseEnd_1132544 := by
    simpa [prefixWord, tailWord_1132544, baseEnd_1132544] using wordTrace_append hprefix tailTrace_1132544
  have hstable : (prefixWord ++ tailWord_1132544).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1132544).length < 2 ^ (prefixWord ++ tailWord_1132544).sum := by decide
  have hdescent : baseEnd_1132544 < baseStart_1132544 := by decide
  rcases family_descends (prefixWord ++ tailWord_1132544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1132597 : List Nat := [1, 3, 3, 1, 1, 1, 2, 1, 4, 2, 4]
def baseStart_1132597 : Nat := 118140960795 + 1132597 * 2 ^ 59
def prefixEnd_1132597 : Nat := 4983230072969 + 3 ^ 40 * 1132597 * 2
def baseEnd_1132597 : Nat := 581566648840410442728787

theorem tailTrace_1132597 : CollatzResearch.WordTrace tailWord_1132597 prefixEnd_1132597 581566648840410442728787 := by
  unfold tailWord_1132597
  simp only [CollatzResearch.WordTrace]
  refine ⟨41309206277801976012788045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27539470851867984008525363 41309206277801976012788045)
  ·
    refine ⟨15490952354175741004795517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 41309206277801976012788045 15490952354175741004795517)
    ·
      refine ⟨5809107132815902876798319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15490952354175741004795517 5809107132815902876798319)
      ·
        refine ⟨8713660699223854315197479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5809107132815902876798319 8713660699223854315197479)
        ·
          refine ⟨13070491048835781472796219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8713660699223854315197479 13070491048835781472796219)
          ·
            refine ⟨19605736573253672209194329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13070491048835781472796219 19605736573253672209194329)
            ·
              refine ⟨14704302429940254156895747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19605736573253672209194329 14704302429940254156895747)
              ·
                refine ⟨22056453644910381235343621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14704302429940254156895747 22056453644910381235343621)
                ·
                  refine ⟨4135585058420696481626929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 22056453644910381235343621 4135585058420696481626929)
                  ·
                    refine ⟨3101688793815522361220197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4135585058420696481626929 3101688793815522361220197)
                    ·
                      refine ⟨581566648840410442728787, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3101688793815522361220197 581566648840410442728787)
                      ·
                        rfl

theorem cell23_1132597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 2, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 2, 1, 4, 2, 4].length) (baseStart_1132597 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1132597 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1132597 prefixEnd_1132597 := by exact prefixLift 1132597
  have htrace : WordTrace (prefixWord ++ tailWord_1132597) baseStart_1132597 baseEnd_1132597 := by
    simpa [prefixWord, tailWord_1132597, baseEnd_1132597] using wordTrace_append hprefix tailTrace_1132597
  have hstable : (prefixWord ++ tailWord_1132597).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1132597).length < 2 ^ (prefixWord ++ tailWord_1132597).sum := by decide
  have hdescent : baseEnd_1132597 < baseStart_1132597 := by decide
  rcases family_descends (prefixWord ++ tailWord_1132597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1132607 : List Nat := [1, 1, 2, 2, 3, 1, 5, 1, 7]
def baseStart_1132607 : Nat := 118140960795 + 1132607 * 2 ^ 59
def prefixEnd_1132607 : Nat := 4983230072969 + 3 ^ 40 * 1132607 * 2
def baseEnd_1132607 : Nat := 64619087071883933733749

theorem tailTrace_1132607 : CollatzResearch.WordTrace tailWord_1132607 prefixEnd_1132607 64619087071883933733749 := by
  unfold tailWord_1132607
  simp only [CollatzResearch.WordTrace]
  refine ⟨41309571007765747720652075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27539714005177165147101383 41309571007765747720652075)
  ·
    refine ⟨61964356511648621580978113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41309571007765747720652075 61964356511648621580978113)
    ·
      refine ⟨46473267383736466185733585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 61964356511648621580978113 46473267383736466185733585)
      ·
        refine ⟨34854950537802349639300189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46473267383736466185733585 34854950537802349639300189)
        ·
          refine ⟨13070606451675881114737571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 34854950537802349639300189 13070606451675881114737571)
          ·
            refine ⟨19605909677513821672106357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13070606451675881114737571 19605909677513821672106357)
            ·
              refine ⟨1838054032266920781759971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 19605909677513821672106357 1838054032266920781759971)
              ·
                refine ⟨2757081048400381172639957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1838054032266920781759971 2757081048400381172639957)
                ·
                  refine ⟨64619087071883933733749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2757081048400381172639957 64619087071883933733749)
                  ·
                    rfl

theorem cell23_1132607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 5, 1, 7].length) (baseStart_1132607 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1132607 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1132607 prefixEnd_1132607 := by exact prefixLift 1132607
  have htrace : WordTrace (prefixWord ++ tailWord_1132607) baseStart_1132607 baseEnd_1132607 := by
    simpa [prefixWord, tailWord_1132607, baseEnd_1132607] using wordTrace_append hprefix tailTrace_1132607
  have hstable : (prefixWord ++ tailWord_1132607).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1132607).length < 2 ^ (prefixWord ++ tailWord_1132607).sum := by decide
  have hdescent : baseEnd_1132607 < baseStart_1132607 := by decide
  rcases family_descends (prefixWord ++ tailWord_1132607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1132617 : List Nat := [1, 2, 1, 1, 2, 2, 4, 1, 1, 5, 3]
def baseStart_1132617 : Nat := 118140960795 + 1132617 * 2 ^ 59
def prefixEnd_1132617 : Nat := 4983230072969 + 3 ^ 40 * 1132617 * 2
def baseEnd_1132617 : Nat := 581576918453500364478695

theorem tailTrace_1132617 : CollatzResearch.WordTrace tailWord_1132617 prefixEnd_1132617 581576918453500364478695 := by
  unfold tailWord_1132617
  simp only [CollatzResearch.WordTrace]
  refine ⟨41309935737729519428516105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27539957158486346285677403 41309935737729519428516105)
  ·
    refine ⟨30982451803297139571387079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41309935737729519428516105 30982451803297139571387079)
    ·
      refine ⟨46473677704945709357080619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30982451803297139571387079 46473677704945709357080619)
      ·
        refine ⟨69710516557418564035620929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46473677704945709357080619 69710516557418564035620929)
        ·
          refine ⟨52282887418063923026715697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 69710516557418564035620929 52282887418063923026715697)
          ·
            refine ⟨39212165563547942270036773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 52282887418063923026715697 39212165563547942270036773)
            ·
              refine ⟨7352281043165239175631895, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 39212165563547942270036773 7352281043165239175631895)
              ·
                refine ⟨11028421564747858763447843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7352281043165239175631895 11028421564747858763447843)
                ·
                  refine ⟨16542632347121788145171765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11028421564747858763447843 16542632347121788145171765)
                  ·
                    refine ⟨1550871782542667638609853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 16542632347121788145171765 1550871782542667638609853)
                    ·
                      refine ⟨581576918453500364478695, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1550871782542667638609853 581576918453500364478695)
                      ·
                        rfl

theorem cell23_1132617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 4, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 4, 1, 1, 5, 3].length) (baseStart_1132617 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1132617 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1132617 prefixEnd_1132617 := by exact prefixLift 1132617
  have htrace : WordTrace (prefixWord ++ tailWord_1132617) baseStart_1132617 baseEnd_1132617 := by
    simpa [prefixWord, tailWord_1132617, baseEnd_1132617] using wordTrace_append hprefix tailTrace_1132617
  have hstable : (prefixWord ++ tailWord_1132617).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1132617).length < 2 ^ (prefixWord ++ tailWord_1132617).sum := by decide
  have hdescent : baseEnd_1132617 < baseStart_1132617 := by decide
  rcases family_descends (prefixWord ++ tailWord_1132617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1132647 : List Nat := [1, 1, 5, 1, 1, 2, 1, 1, 3, 2, 5]
def baseStart_1132647 : Nat := 118140960795 + 1132647 * 2 ^ 59
def prefixEnd_1132647 : Nat := 4983230072969 + 3 ^ 40 * 1132647 * 2
def baseEnd_1132647 : Nat := 581592322873135247103557

theorem tailTrace_1132647 : CollatzResearch.WordTrace tailWord_1132647 prefixEnd_1132647 581592322873135247103557 := by
  unfold tailWord_1132647
  simp only [CollatzResearch.WordTrace]
  refine ⟨41311029927620834552108195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27540686618413889701405463 41311029927620834552108195)
  ·
    refine ⟨61966544891431251828162293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41311029927620834552108195 61966544891431251828162293)
    ·
      refine ⟨5809363583571679858890215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 61966544891431251828162293 5809363583571679858890215)
      ·
        refine ⟨8714045375357519788335323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5809363583571679858890215 8714045375357519788335323)
        ·
          refine ⟨13071068063036279682502985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8714045375357519788335323 13071068063036279682502985)
          ·
            refine ⟨9803301047277209761877239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13071068063036279682502985 9803301047277209761877239)
            ·
              refine ⟨14704951570915814642815859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9803301047277209761877239 14704951570915814642815859)
              ·
                refine ⟨22057427356373721964223789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14704951570915814642815859 22057427356373721964223789)
                ·
                  refine ⟨8271535258640145736583921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 22057427356373721964223789 8271535258640145736583921)
                  ·
                    refine ⟨6203651443980109302437941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8271535258640145736583921 6203651443980109302437941)
                    ·
                      refine ⟨581592322873135247103557, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 6203651443980109302437941 581592322873135247103557)
                      ·
                        rfl

theorem cell23_1132647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 1, 1, 3, 2, 5].length) (baseStart_1132647 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1132647 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1132647 prefixEnd_1132647 := by exact prefixLift 1132647
  have htrace : WordTrace (prefixWord ++ tailWord_1132647) baseStart_1132647 baseEnd_1132647 := by
    simpa [prefixWord, tailWord_1132647, baseEnd_1132647] using wordTrace_append hprefix tailTrace_1132647
  have hstable : (prefixWord ++ tailWord_1132647).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1132647).length < 2 ^ (prefixWord ++ tailWord_1132647).sum := by decide
  have hdescent : baseEnd_1132647 < baseStart_1132647 := by decide
  rcases family_descends (prefixWord ++ tailWord_1132647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1132654 : List Nat := [4, 1, 2, 2, 1, 1, 1, 4, 2, 5]
def baseStart_1132654 : Nat := 118140960795 + 1132654 * 2 ^ 59
def prefixEnd_1132654 : Nat := 4983230072969 + 3 ^ 40 * 1132654 * 2
def baseEnd_1132654 : Nat := 193865305745905573238675

theorem tailTrace_1132654 : CollatzResearch.WordTrace tailWord_1132654 prefixEnd_1132654 193865305745905573238675 := by
  unfold tailWord_1132654
  simp only [CollatzResearch.WordTrace]
  refine ⟨5163910654824434343451627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 27540856825730316498408677 5163910654824434343451627)
  ·
    refine ⟨7745865982236651515177441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5163910654824434343451627 7745865982236651515177441)
    ·
      refine ⟨5809399486677488636383081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7745865982236651515177441 5809399486677488636383081)
      ·
        refine ⟨4357049615008116477287311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5809399486677488636383081 4357049615008116477287311)
        ·
          refine ⟨6535574422512174715930967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4357049615008116477287311 6535574422512174715930967)
          ·
            refine ⟨9803361633768262073896451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6535574422512174715930967 9803361633768262073896451)
            ·
              refine ⟨14705042450652393110844677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9803361633768262073896451 14705042450652393110844677)
              ·
                refine ⟨2757195459497323708283377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14705042450652393110844677 2757195459497323708283377)
                ·
                  refine ⟨2067896594622992781212533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2757195459497323708283377 2067896594622992781212533)
                  ·
                    refine ⟨193865305745905573238675, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2067896594622992781212533 193865305745905573238675)
                    ·
                      rfl

theorem cell23_1132654_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 1, 4, 2, 5].length) (baseStart_1132654 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1132654 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1132654 prefixEnd_1132654 := by exact prefixLift 1132654
  have htrace : WordTrace (prefixWord ++ tailWord_1132654) baseStart_1132654 baseEnd_1132654 := by
    simpa [prefixWord, tailWord_1132654, baseEnd_1132654] using wordTrace_append hprefix tailTrace_1132654
  have hstable : (prefixWord ++ tailWord_1132654).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1132654).length < 2 ^ (prefixWord ++ tailWord_1132654).sum := by decide
  have hdescent : baseEnd_1132654 < baseStart_1132654 := by decide
  rcases family_descends (prefixWord ++ tailWord_1132654) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1132658 : List Nat := [3, 2, 1, 2, 2, 4, 2, 2, 5]
def baseStart_1132658 : Nat := 118140960795 + 1132658 * 2 ^ 59
def prefixEnd_1132658 : Nat := 4983230072969 + 3 ^ 40 * 1132658 * 2
def baseEnd_1132658 : Nat := 64621996795592744896223

theorem tailTrace_1132658 : CollatzResearch.WordTrace tailWord_1132658 prefixEnd_1132658 64621996795592744896223 := by
  unfold tailWord_1132658
  simp only [CollatzResearch.WordTrace]
  refine ⟨10327857782645245857689657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 27540954087053988953839085 10327857782645245857689657)
  ·
    refine ⟨7745893336983934393267243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10327857782645245857689657 7745893336983934393267243)
    ·
      refine ⟨11618840005475901589900865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7745893336983934393267243 11618840005475901589900865)
      ·
        refine ⟨8714130004106926192425649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11618840005475901589900865 8714130004106926192425649)
        ·
          refine ⟨6535597503080194644319237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8714130004106926192425649 6535597503080194644319237)
          ·
            refine ⟨1225424531827536495809857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6535597503080194644319237 1225424531827536495809857)
            ·
              refine ⟨919068398870652371857393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1225424531827536495809857 919068398870652371857393)
              ·
                refine ⟨689301299152989278893045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 919068398870652371857393 689301299152989278893045)
                ·
                  refine ⟨64621996795592744896223, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 689301299152989278893045 64621996795592744896223)
                  ·
                    rfl

theorem cell23_1132658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 4, 2, 2, 5].length) (baseStart_1132658 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1132658 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1132658 prefixEnd_1132658 := by exact prefixLift 1132658
  have htrace : WordTrace (prefixWord ++ tailWord_1132658) baseStart_1132658 baseEnd_1132658 := by
    simpa [prefixWord, tailWord_1132658, baseEnd_1132658] using wordTrace_append hprefix tailTrace_1132658
  have hstable : (prefixWord ++ tailWord_1132658).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1132658).length < 2 ^ (prefixWord ++ tailWord_1132658).sum := by decide
  have hdescent : baseEnd_1132658 < baseStart_1132658 := by decide
  rcases family_descends (prefixWord ++ tailWord_1132658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1132741 : List Nat := [1, 3, 1, 1, 1, 1, 6, 2, 3, 1, 3]
def baseStart_1132741 : Nat := 118140960795 + 1132741 * 2 ^ 59
def prefixEnd_1132741 : Nat := 4983230072969 + 3 ^ 40 * 1132741 * 2
def baseEnd_1132741 : Nat := 581640590054657879328125

theorem tailTrace_1132741 : CollatzResearch.WordTrace tailWord_1132741 prefixEnd_1132741 581640590054657879328125 := by
  unfold tailWord_1132741
  simp only [CollatzResearch.WordTrace]
  refine ⟨41314458389280288606030077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27542972259520192404020051 41314458389280288606030077)
  ·
    refine ⟨15492921895980108227261279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 41314458389280288606030077 15492921895980108227261279)
    ·
      refine ⟨23239382843970162340891919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15492921895980108227261279 23239382843970162340891919)
      ·
        refine ⟨34859074265955243511337879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23239382843970162340891919 34859074265955243511337879)
        ·
          refine ⟨52288611398932865267006819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34859074265955243511337879 52288611398932865267006819)
          ·
            refine ⟨78432917098399297900510229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 52288611398932865267006819 78432917098399297900510229)
            ·
              refine ⟨3676542988987467089086417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 78432917098399297900510229 3676542988987467089086417)
              ·
                refine ⟨2757407241740600316814813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3676542988987467089086417 2757407241740600316814813)
                ·
                  refine ⟨1034027715652725118805555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2757407241740600316814813 1034027715652725118805555)
                  ·
                    refine ⟨1551041573479087678208333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1034027715652725118805555 1551041573479087678208333)
                    ·
                      refine ⟨581640590054657879328125, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1551041573479087678208333 581640590054657879328125)
                      ·
                        rfl

theorem cell23_1132741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 6, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 6, 2, 3, 1, 3].length) (baseStart_1132741 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1132741 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1132741 prefixEnd_1132741 := by exact prefixLift 1132741
  have htrace : WordTrace (prefixWord ++ tailWord_1132741) baseStart_1132741 baseEnd_1132741 := by
    simpa [prefixWord, tailWord_1132741, baseEnd_1132741] using wordTrace_append hprefix tailTrace_1132741
  have hstable : (prefixWord ++ tailWord_1132741).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1132741).length < 2 ^ (prefixWord ++ tailWord_1132741).sum := by decide
  have hdescent : baseEnd_1132741 < baseStart_1132741 := by decide
  rcases family_descends (prefixWord ++ tailWord_1132741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1132751 : List Nat := [1, 1, 2, 1, 1, 3, 4, 3, 2, 3, 2]
def baseStart_1132751 : Nat := 118140960795 + 1132751 * 2 ^ 59
def prefixEnd_1132751 : Nat := 4983230072969 + 3 ^ 40 * 1132751 * 2
def baseEnd_1132751 : Nat := 581645724861202840203079

theorem tailTrace_1132751 : CollatzResearch.WordTrace tailWord_1132751 prefixEnd_1132751 581645724861202840203079 := by
  unfold tailWord_1132751
  simp only [CollatzResearch.WordTrace]
  refine ⟨41314823119244060313894107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27543215412829373542596071 41314823119244060313894107)
  ·
    refine ⟨61972234678866090470841161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41314823119244060313894107 61972234678866090470841161)
    ·
      refine ⟨46479176009149567853130871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 61972234678866090470841161 46479176009149567853130871)
      ·
        refine ⟨69718764013724351779696307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46479176009149567853130871 69718764013724351779696307)
        ·
          refine ⟨104578146020586527669544461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 69718764013724351779696307 104578146020586527669544461)
          ·
            refine ⟨39216804757719947876079173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 104578146020586527669544461 39216804757719947876079173)
            ·
              refine ⟨7353150892072490226764845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 39216804757719947876079173 7353150892072490226764845)
              ·
                refine ⟨2757431584527183835036817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7353150892072490226764845 2757431584527183835036817)
                ·
                  refine ⟨2068073688395387876277613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2757431584527183835036817 2068073688395387876277613)
                  ·
                    refine ⟨775527633148270453604105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2068073688395387876277613 775527633148270453604105)
                    ·
                      refine ⟨581645724861202840203079, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 775527633148270453604105 581645724861202840203079)
                      ·
                        rfl

theorem cell23_1132751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 4, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 4, 3, 2, 3, 2].length) (baseStart_1132751 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1132751 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1132751 prefixEnd_1132751 := by exact prefixLift 1132751
  have htrace : WordTrace (prefixWord ++ tailWord_1132751) baseStart_1132751 baseEnd_1132751 := by
    simpa [prefixWord, tailWord_1132751, baseEnd_1132751] using wordTrace_append hprefix tailTrace_1132751
  have hstable : (prefixWord ++ tailWord_1132751).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1132751).length < 2 ^ (prefixWord ++ tailWord_1132751).sum := by decide
  have hdescent : baseEnd_1132751 < baseStart_1132751 := by decide
  rcases family_descends (prefixWord ++ tailWord_1132751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1132775 : List Nat := [1, 1, 5, 3, 1, 3, 1, 1, 3, 1, 3]
def baseStart_1132775 : Nat := 118140960795 + 1132775 * 2 ^ 59
def prefixEnd_1132775 : Nat := 4983230072969 + 3 ^ 40 * 1132775 * 2
def baseEnd_1132775 : Nat := 581658048396910746302969

theorem tailTrace_1132775 : CollatzResearch.WordTrace tailWord_1132775 prefixEnd_1132775 581658048396910746302969 := by
  unfold tailWord_1132775
  simp only [CollatzResearch.WordTrace]
  refine ⟨41315698471157112412767779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27543798980771408275178519 41315698471157112412767779)
  ·
    refine ⟨61973547706735668619151669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41315698471157112412767779 61973547706735668619151669)
    ·
      refine ⟨5810020097506468933045469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 61973547706735668619151669 5810020097506468933045469)
      ·
        refine ⟨2178757536564925849892051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5810020097506468933045469 2178757536564925849892051)
        ·
          refine ⟨3268136304847388774838077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2178757536564925849892051 3268136304847388774838077)
          ·
            refine ⟨1225551114317770790564279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3268136304847388774838077 1225551114317770790564279)
            ·
              refine ⟨1838326671476656185846419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1225551114317770790564279 1838326671476656185846419)
              ·
                refine ⟨2757490007214984278769629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1838326671476656185846419 2757490007214984278769629)
                ·
                  refine ⟨1034058752705619104538611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2757490007214984278769629 1034058752705619104538611)
                  ·
                    refine ⟨1551088129058428656807917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1034058752705619104538611 1551088129058428656807917)
                    ·
                      refine ⟨581658048396910746302969, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1551088129058428656807917 581658048396910746302969)
                      ·
                        rfl

theorem cell23_1132775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 3, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 3, 1, 1, 3, 1, 3].length) (baseStart_1132775 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1132775 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1132775 prefixEnd_1132775 := by exact prefixLift 1132775
  have htrace : WordTrace (prefixWord ++ tailWord_1132775) baseStart_1132775 baseEnd_1132775 := by
    simpa [prefixWord, tailWord_1132775, baseEnd_1132775] using wordTrace_append hprefix tailTrace_1132775
  have hstable : (prefixWord ++ tailWord_1132775).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1132775).length < 2 ^ (prefixWord ++ tailWord_1132775).sum := by decide
  have hdescent : baseEnd_1132775 < baseStart_1132775 := by decide
  rcases family_descends (prefixWord ++ tailWord_1132775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1132794 : List Nat := [3, 1, 1, 1, 1, 5, 2, 1, 1, 1, 6]
def baseStart_1132794 : Nat := 118140960795 + 1132794 * 2 ^ 59
def prefixEnd_1132794 : Nat := 4983230072969 + 3 ^ 40 * 1132794 * 2
def baseEnd_1132794 : Nat := 581667804529346171965381

theorem tailTrace_1132794 : CollatzResearch.WordTrace tailWord_1132794 prefixEnd_1132794 581667804529346171965381 := by
  unfold tailWord_1132794
  simp only [CollatzResearch.WordTrace]
  refine ⟨10329097864522069664427359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 27544260972058852438472957 10329097864522069664427359)
  ·
    refine ⟨15493646796783104496641039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10329097864522069664427359 15493646796783104496641039)
    ·
      refine ⟨23240470195174656744961559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15493646796783104496641039 23240470195174656744961559)
      ·
        refine ⟨34860705292761985117442339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23240470195174656744961559 34860705292761985117442339)
        ·
          refine ⟨52291057939142977676163509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34860705292761985117442339 52291057939142977676163509)
          ·
            refine ⟨4902286681794654157140329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 52291057939142977676163509 4902286681794654157140329)
            ·
              refine ⟨3676715011345990617855247, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4902286681794654157140329 3676715011345990617855247)
              ·
                refine ⟨5515072517018985926782871, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3676715011345990617855247 5515072517018985926782871)
                ·
                  refine ⟨8272608775528478890174307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5515072517018985926782871 8272608775528478890174307)
                  ·
                    refine ⟨12408913163292718335261461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8272608775528478890174307 12408913163292718335261461)
                    ·
                      refine ⟨581667804529346171965381, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 12408913163292718335261461 581667804529346171965381)
                      ·
                        rfl

theorem cell23_1132794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 5, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 5, 2, 1, 1, 1, 6].length) (baseStart_1132794 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1132794 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1132794 prefixEnd_1132794 := by exact prefixLift 1132794
  have htrace : WordTrace (prefixWord ++ tailWord_1132794) baseStart_1132794 baseEnd_1132794 := by
    simpa [prefixWord, tailWord_1132794, baseEnd_1132794] using wordTrace_append hprefix tailTrace_1132794
  have hstable : (prefixWord ++ tailWord_1132794).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1132794).length < 2 ^ (prefixWord ++ tailWord_1132794).sum := by decide
  have hdescent : baseEnd_1132794 < baseStart_1132794 := by decide
  rcases family_descends (prefixWord ++ tailWord_1132794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1132801 : List Nat := [1, 2, 4, 1, 1, 2, 3, 1, 3, 2, 3]
def baseStart_1132801 : Nat := 118140960795 + 1132801 * 2 ^ 59
def prefixEnd_1132801 : Nat := 4983230072969 + 3 ^ 40 * 1132801 * 2
def baseEnd_1132801 : Nat := 581671398893927644577849

theorem tailTrace_1132801 : CollatzResearch.WordTrace tailWord_1132801 prefixEnd_1132801 581671398893927644577849 := by
  unfold tailWord_1132801
  simp only [CollatzResearch.WordTrace]
  refine ⟨41316646769062918853214257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27544431179375279235476171 41316646769062918853214257)
  ·
    refine ⟨30987485076797189139910693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41316646769062918853214257 30987485076797189139910693)
    ·
      refine ⟨5810153451899472963733255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 30987485076797189139910693 5810153451899472963733255)
      ·
        refine ⟨8715230177849209445599883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5810153451899472963733255 8715230177849209445599883)
        ·
          refine ⟨13072845266773814168399825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8715230177849209445599883 13072845266773814168399825)
          ·
            refine ⟨9804633950080360626299869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13072845266773814168399825 9804633950080360626299869)
            ·
              refine ⟨3676737731280135234862451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9804633950080360626299869 3676737731280135234862451)
              ·
                refine ⟨5515106596920202852293677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3676737731280135234862451 5515106596920202852293677)
                ·
                  refine ⟨2068164973845076069610129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5515106596920202852293677 2068164973845076069610129)
                  ·
                    refine ⟨1551123730383807052207597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2068164973845076069610129 1551123730383807052207597)
                    ·
                      refine ⟨581671398893927644577849, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1551123730383807052207597 581671398893927644577849)
                      ·
                        rfl

theorem cell23_1132801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 3, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 3, 1, 3, 2, 3].length) (baseStart_1132801 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1132801 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1132801 prefixEnd_1132801 := by exact prefixLift 1132801
  have htrace : WordTrace (prefixWord ++ tailWord_1132801) baseStart_1132801 baseEnd_1132801 := by
    simpa [prefixWord, tailWord_1132801, baseEnd_1132801] using wordTrace_append hprefix tailTrace_1132801
  have hstable : (prefixWord ++ tailWord_1132801).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1132801).length < 2 ^ (prefixWord ++ tailWord_1132801).sum := by decide
  have hdescent : baseEnd_1132801 < baseStart_1132801 := by decide
  rcases family_descends (prefixWord ++ tailWord_1132801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1132832 : List Nat := [2, 1, 1, 5, 2, 2, 1, 4, 1, 2, 2]
def baseStart_1132832 : Nat := 118140960795 + 1132832 * 2 ^ 59
def prefixEnd_1132832 : Nat := 4983230072969 + 3 ^ 40 * 1132832 * 2
def baseEnd_1132832 : Nat := 581687316794217023290207

theorem tailTrace_1132832 : CollatzResearch.WordTrace tailWord_1132832 prefixEnd_1132832 581687316794217023290207 := by
  unfold tailWord_1132832
  simp only [CollatzResearch.WordTrace]
  refine ⟨20658888715975305573796375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27545184954633740765061833 20658888715975305573796375)
  ·
    refine ⟨30988333073962958360694563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20658888715975305573796375 30988333073962958360694563)
    ·
      refine ⟨46482499610944437541041845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30988333073962958360694563 46482499610944437541041845)
      ·
        refine ⟨4357734338526041019472673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 46482499610944437541041845 4357734338526041019472673)
        ·
          refine ⟨3268300753894530764604505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4357734338526041019472673 3268300753894530764604505)
          ·
            refine ⟨2451225565420898073453379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3268300753894530764604505 2451225565420898073453379)
            ·
              refine ⟨3676838348131347110180069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2451225565420898073453379 3676838348131347110180069)
              ·
                refine ⟨689407190274627583158763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3676838348131347110180069 689407190274627583158763)
                ·
                  refine ⟨1034110785411941374738145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 689407190274627583158763 1034110785411941374738145)
                  ·
                    refine ⟨775583089058956031053609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1034110785411941374738145 775583089058956031053609)
                    ·
                      refine ⟨581687316794217023290207, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 775583089058956031053609 581687316794217023290207)
                      ·
                        rfl

theorem cell23_1132832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 2, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 2, 1, 4, 1, 2, 2].length) (baseStart_1132832 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1132832 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1132832 prefixEnd_1132832 := by exact prefixLift 1132832
  have htrace : WordTrace (prefixWord ++ tailWord_1132832) baseStart_1132832 baseEnd_1132832 := by
    simpa [prefixWord, tailWord_1132832, baseEnd_1132832] using wordTrace_append hprefix tailTrace_1132832
  have hstable : (prefixWord ++ tailWord_1132832).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1132832).length < 2 ^ (prefixWord ++ tailWord_1132832).sum := by decide
  have hdescent : baseEnd_1132832 < baseStart_1132832 := by decide
  rcases family_descends (prefixWord ++ tailWord_1132832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1132845 : List Nat := [1, 5, 3, 1, 2, 1, 2, 1, 1, 2, 4]
def baseStart_1132845 : Nat := 118140960795 + 1132845 * 2 ^ 59
def prefixEnd_1132845 : Nat := 4983230072969 + 3 ^ 40 * 1132845 * 2
def baseEnd_1132845 : Nat := 581693992042725472427647

theorem tailTrace_1132845 : CollatzResearch.WordTrace tailWord_1132845 prefixEnd_1132845 581693992042725472427647 := by
  unfold tailWord_1132845
  simp only [CollatzResearch.WordTrace]
  refine ⟨41318251580903514367815989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27545501053935676245210659 41318251580903514367815989)
  ·
    refine ⟨3873586085709704471982749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 41318251580903514367815989 3873586085709704471982749)
    ·
      refine ⟨1452594782141139176993531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3873586085709704471982749 1452594782141139176993531)
      ·
        refine ⟨2178892173211708765490297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1452594782141139176993531 2178892173211708765490297)
        ·
          refine ⟨1634169129908781574117723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2178892173211708765490297 1634169129908781574117723)
          ·
            refine ⟨2451253694863172361176585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1634169129908781574117723 2451253694863172361176585)
            ·
              refine ⟨1838440271147379270882439, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2451253694863172361176585 1838440271147379270882439)
              ·
                refine ⟨2757660406721068906323659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1838440271147379270882439 2757660406721068906323659)
                ·
                  refine ⟨4136490610081603359485489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2757660406721068906323659 4136490610081603359485489)
                  ·
                    refine ⟨3102367957561202519614117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4136490610081603359485489 3102367957561202519614117)
                    ·
                      refine ⟨581693992042725472427647, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3102367957561202519614117 581693992042725472427647)
                      ·
                        rfl

theorem cell23_1132845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 2, 1, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 2, 1, 2, 1, 1, 2, 4].length) (baseStart_1132845 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1132845 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1132845 prefixEnd_1132845 := by exact prefixLift 1132845
  have htrace : WordTrace (prefixWord ++ tailWord_1132845) baseStart_1132845 baseEnd_1132845 := by
    simpa [prefixWord, tailWord_1132845, baseEnd_1132845] using wordTrace_append hprefix tailTrace_1132845
  have hstable : (prefixWord ++ tailWord_1132845).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1132845).length < 2 ^ (prefixWord ++ tailWord_1132845).sum := by decide
  have hdescent : baseEnd_1132845 < baseStart_1132845 := by decide
  rcases family_descends (prefixWord ++ tailWord_1132845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1132858 : List Nat := [3, 1, 1, 1, 4, 2, 2, 1, 3, 3, 2]
def baseStart_1132858 : Nat := 118140960795 + 1132858 * 2 ^ 59
def prefixEnd_1132858 : Nat := 4983230072969 + 3 ^ 40 * 1132858 * 2
def baseEnd_1132858 : Nat := 581700667291233921565087

theorem tailTrace_1132858 : CollatzResearch.WordTrace tailWord_1132858 prefixEnd_1132858 581700667291233921565087 := by
  unfold tailWord_1132858
  simp only [CollatzResearch.WordTrace]
  refine ⟨10329681432464104397009807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 27545817153237611725359485 10329681432464104397009807)
  ·
    refine ⟨15494522148696156595514711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10329681432464104397009807 15494522148696156595514711)
    ·
      refine ⟨23241783223044234893272067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15494522148696156595514711 23241783223044234893272067)
      ·
        refine ⟨34862674834566352339908101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23241783223044234893272067 34862674834566352339908101)
        ·
          refine ⟨6536751531481191063732769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 34862674834566352339908101 6536751531481191063732769)
          ·
            refine ⟨4902563648610893297799577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6536751531481191063732769 4902563648610893297799577)
            ·
              refine ⟨3676922736458169973349683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4902563648610893297799577 3676922736458169973349683)
              ·
                refine ⟨5515384104687254960024525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3676922736458169973349683 5515384104687254960024525)
                ·
                  refine ⟨2068269039257720610009197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5515384104687254960024525 2068269039257720610009197)
                  ·
                    refine ⟨775600889721645228753449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2068269039257720610009197 775600889721645228753449)
                    ·
                      refine ⟨581700667291233921565087, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 775600889721645228753449 581700667291233921565087)
                      ·
                        rfl

theorem cell23_1132858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 2, 2, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 2, 2, 1, 3, 3, 2].length) (baseStart_1132858 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1132858 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1132858 prefixEnd_1132858 := by exact prefixLift 1132858
  have htrace : WordTrace (prefixWord ++ tailWord_1132858) baseStart_1132858 baseEnd_1132858 := by
    simpa [prefixWord, tailWord_1132858, baseEnd_1132858] using wordTrace_append hprefix tailTrace_1132858
  have hstable : (prefixWord ++ tailWord_1132858).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1132858).length < 2 ^ (prefixWord ++ tailWord_1132858).sum := by decide
  have hdescent : baseEnd_1132858 < baseStart_1132858 := by decide
  rcases family_descends (prefixWord ++ tailWord_1132858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1132901 : List Nat := [1, 3, 1, 3, 1, 3, 2, 1, 2, 2, 4]
def baseStart_1132901 : Nat := 118140960795 + 1132901 * 2 ^ 59
def prefixEnd_1132901 : Nat := 4983230072969 + 3 ^ 40 * 1132901 * 2
def baseEnd_1132901 : Nat := 581722746959377253327389

theorem tailTrace_1132901 : CollatzResearch.WordTrace tailWord_1132901 prefixEnd_1132901 581722746959377253327389 := by
  unfold tailWord_1132901
  simp only [CollatzResearch.WordTrace]
  refine ⟨41320294068700635931854557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27546862712467090621236371 41320294068700635931854557)
  ·
    refine ⟨15495110275762738474445459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 41320294068700635931854557 15495110275762738474445459)
    ·
      refine ⟨23242665413644107711668189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15495110275762738474445459 23242665413644107711668189)
      ·
        refine ⟨8715999530116540391875571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23242665413644107711668189 8715999530116540391875571)
        ·
          refine ⟨13073999295174810587813357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8715999530116540391875571 13073999295174810587813357)
          ·
            refine ⟨4902749735690553970430009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13073999295174810587813357 4902749735690553970430009)
            ·
              refine ⟨3677062301767915477822507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4902749735690553970430009 3677062301767915477822507)
              ·
                refine ⟨5515593452651873216733761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3677062301767915477822507 5515593452651873216733761)
                ·
                  refine ⟨4136695089488904912550321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5515593452651873216733761 4136695089488904912550321)
                  ·
                    refine ⟨3102521317116678684412741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4136695089488904912550321 3102521317116678684412741)
                    ·
                      refine ⟨581722746959377253327389, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3102521317116678684412741 581722746959377253327389)
                      ·
                        rfl

theorem cell23_1132901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 3, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 3, 2, 1, 2, 2, 4].length) (baseStart_1132901 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1132901 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1132901 prefixEnd_1132901 := by exact prefixLift 1132901
  have htrace : WordTrace (prefixWord ++ tailWord_1132901) baseStart_1132901 baseEnd_1132901 := by
    simpa [prefixWord, tailWord_1132901, baseEnd_1132901] using wordTrace_append hprefix tailTrace_1132901
  have hstable : (prefixWord ++ tailWord_1132901).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1132901).length < 2 ^ (prefixWord ++ tailWord_1132901).sum := by decide
  have hdescent : baseEnd_1132901 < baseStart_1132901 := by decide
  rcases family_descends (prefixWord ++ tailWord_1132901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1132950 : List Nat := [5, 3, 1, 2, 2, 1, 2, 1, 2, 1, 3]
def baseStart_1132950 : Nat := 118140960795 + 1132950 * 2 ^ 59
def prefixEnd_1132950 : Nat := 4983230072969 + 3 ^ 40 * 1132950 * 2
def baseEnd_1132950 : Nat := 581747907511447561614665

theorem tailTrace_1132950 : CollatzResearch.WordTrace tailWord_1132950 prefixEnd_1132950 581747907511447561614665 := by
  unfold tailWord_1132950
  simp only [CollatzResearch.WordTrace]
  refine ⟨2582630077845194831274269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 27548054163682078200258869 2582630077845194831274269)
  ·
    refine ⟨968486279191948061727851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2582630077845194831274269 968486279191948061727851)
    ·
      refine ⟨1452729418787922092591777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 968486279191948061727851 1452729418787922092591777)
      ·
        refine ⟨1089547064090941569443833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1452729418787922092591777 1089547064090941569443833)
        ·
          refine ⟨817160298068206177082875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1089547064090941569443833 817160298068206177082875)
          ·
            refine ⟨1225740447102309265624313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 817160298068206177082875 1225740447102309265624313)
            ·
              refine ⟨919305335326731949218235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1225740447102309265624313 919305335326731949218235)
              ·
                refine ⟨1378958002990097923827353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 919305335326731949218235 1378958002990097923827353)
                ·
                  refine ⟨1034218502242573442870515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1378958002990097923827353 1034218502242573442870515)
                  ·
                    refine ⟨1551327753363860164305773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1034218502242573442870515 1551327753363860164305773)
                    ·
                      refine ⟨581747907511447561614665, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1551327753363860164305773 581747907511447561614665)
                      ·
                        rfl

theorem cell23_1132950_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 2, 1, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 2, 1, 2, 1, 2, 1, 3].length) (baseStart_1132950 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1132950 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1132950 prefixEnd_1132950 := by exact prefixLift 1132950
  have htrace : WordTrace (prefixWord ++ tailWord_1132950) baseStart_1132950 baseEnd_1132950 := by
    simpa [prefixWord, tailWord_1132950, baseEnd_1132950] using wordTrace_append hprefix tailTrace_1132950
  have hstable : (prefixWord ++ tailWord_1132950).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1132950).length < 2 ^ (prefixWord ++ tailWord_1132950).sum := by decide
  have hdescent : baseEnd_1132950 < baseStart_1132950 := by decide
  rcases family_descends (prefixWord ++ tailWord_1132950) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1132978 : List Nat := [3, 2, 1, 1, 1, 1, 6, 1, 2, 1, 4]
def baseStart_1132978 : Nat := 118140960795 + 1132978 * 2 ^ 59
def prefixEnd_1132978 : Nat := 4983230072969 + 3 ^ 40 * 1132978 * 2
def baseEnd_1132978 : Nat := 581762284969773452064535

theorem tailTrace_1132978 : CollatzResearch.WordTrace tailWord_1132978 prefixEnd_1132978 581762284969773452064535 := by
  unfold tailWord_1132978
  simp only [CollatzResearch.WordTrace]
  refine ⟨10330775622355419520601897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 27548734992947785388271725 10330775622355419520601897)
  ·
    refine ⟨7748081716766564640451423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10330775622355419520601897 7748081716766564640451423)
    ·
      refine ⟨11622122575149846960677135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7748081716766564640451423 11622122575149846960677135)
      ·
        refine ⟨17433183862724770441015703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11622122575149846960677135 17433183862724770441015703)
        ·
          refine ⟨26149775794087155661523555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17433183862724770441015703 26149775794087155661523555)
          ·
            refine ⟨39224663691130733492285333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26149775794087155661523555 39224663691130733492285333)
            ·
              refine ⟨1838656110521753132450875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 39224663691130733492285333 1838656110521753132450875)
              ·
                refine ⟨2757984165782629698676313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1838656110521753132450875 2757984165782629698676313)
                ·
                  refine ⟨2068488124336972274007235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2757984165782629698676313 2068488124336972274007235)
                  ·
                    refine ⟨3102732186505458411010853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2068488124336972274007235 3102732186505458411010853)
                    ·
                      refine ⟨581762284969773452064535, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3102732186505458411010853 581762284969773452064535)
                      ·
                        rfl

theorem cell23_1132978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 6, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 6, 1, 2, 1, 4].length) (baseStart_1132978 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1132978 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1132978 prefixEnd_1132978 := by exact prefixLift 1132978
  have htrace : WordTrace (prefixWord ++ tailWord_1132978) baseStart_1132978 baseEnd_1132978 := by
    simpa [prefixWord, tailWord_1132978, baseEnd_1132978] using wordTrace_append hprefix tailTrace_1132978
  have hstable : (prefixWord ++ tailWord_1132978).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1132978).length < 2 ^ (prefixWord ++ tailWord_1132978).sum := by decide
  have hdescent : baseEnd_1132978 < baseStart_1132978 := by decide
  rcases family_descends (prefixWord ++ tailWord_1132978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1133001 : List Nat := [1, 2, 1, 1, 2, 1, 5, 4, 6]
def baseStart_1133001 : Nat := 118140960795 + 1133001 * 2 ^ 59
def prefixEnd_1133001 : Nat := 4983230072969 + 3 ^ 40 * 1133001 * 2
def baseEnd_1133001 : Nat := 64641566113869651341881

theorem tailTrace_1133001 : CollatzResearch.WordTrace tailWord_1133001 prefixEnd_1133001 64641566113869651341881 := by
  unfold tailWord_1133001
  simp only [CollatzResearch.WordTrace]
  refine ⟨41323941368338353010494857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27549294245558902006996571 41323941368338353010494857)
  ·
    refine ⟨30992956026253764757871143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41323941368338353010494857 30992956026253764757871143)
    ·
      refine ⟨46489434039380647136806715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30992956026253764757871143 46489434039380647136806715)
      ·
        refine ⟨69734151059070970705210073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46489434039380647136806715 69734151059070970705210073)
        ·
          refine ⟨52300613294303228028907555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 69734151059070970705210073 52300613294303228028907555)
          ·
            refine ⟨78450919941454842043361333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 52300613294303228028907555 78450919941454842043361333)
            ·
              refine ⟨7354773744511391441565125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 78450919941454842043361333 7354773744511391441565125)
              ·
                refine ⟨1379020077095885895293461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7354773744511391441565125 1379020077095885895293461)
                ·
                  refine ⟨64641566113869651341881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1379020077095885895293461 64641566113869651341881)
                  ·
                    rfl

theorem cell23_1133001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 5, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 5, 4, 6].length) (baseStart_1133001 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1133001 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1133001 prefixEnd_1133001 := by exact prefixLift 1133001
  have htrace : WordTrace (prefixWord ++ tailWord_1133001) baseStart_1133001 baseEnd_1133001 := by
    simpa [prefixWord, tailWord_1133001, baseEnd_1133001] using wordTrace_append hprefix tailTrace_1133001
  have hstable : (prefixWord ++ tailWord_1133001).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1133001).length < 2 ^ (prefixWord ++ tailWord_1133001).sum := by decide
  have hdescent : baseEnd_1133001 < baseStart_1133001 := by decide
  rcases family_descends (prefixWord ++ tailWord_1133001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1133048 : List Nat := [2, 1, 2, 1, 1, 4, 3, 3, 1, 5]
def baseStart_1133048 : Nat := 118140960795 + 1133048 * 2 ^ 59
def prefixEnd_1133048 : Nat := 4983230072969 + 3 ^ 40 * 1133048 * 2
def baseEnd_1133048 : Nat := 193932742871862726063071

theorem tailTrace_1133048 : CollatzResearch.WordTrace tailWord_1133048 prefixEnd_1133048 193932742871862726063071 := by
  unfold tailWord_1133048
  simp only [CollatzResearch.WordTrace]
  refine ⟨20662827799584040018727899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27550437066112053358303865 20662827799584040018727899)
  ·
    refine ⟨30994241699376060028091849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20662827799584040018727899 30994241699376060028091849)
    ·
      refine ⟨23245681274532045021068887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30994241699376060028091849 23245681274532045021068887)
      ·
        refine ⟨34868521911798067531603331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23245681274532045021068887 34868521911798067531603331)
        ·
          refine ⟨52302782867697101297404997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34868521911798067531603331 52302782867697101297404997)
          ·
            refine ⟨9806771787693206493263437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 52302782867697101297404997 9806771787693206493263437)
            ·
              refine ⟨3677539420384952434973789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9806771787693206493263437 3677539420384952434973789)
              ·
                refine ⟨1379077282644357163115171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3677539420384952434973789 1379077282644357163115171)
                ·
                  refine ⟨2068615923966535744672757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1379077282644357163115171 2068615923966535744672757)
                  ·
                    refine ⟨193932742871862726063071, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2068615923966535744672757 193932742871862726063071)
                    ·
                      rfl

theorem cell23_1133048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 3, 3, 1, 5].length) (baseStart_1133048 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1133048 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1133048 prefixEnd_1133048 := by exact prefixLift 1133048
  have htrace : WordTrace (prefixWord ++ tailWord_1133048) baseStart_1133048 baseEnd_1133048 := by
    simpa [prefixWord, tailWord_1133048, baseEnd_1133048] using wordTrace_append hprefix tailTrace_1133048
  have hstable : (prefixWord ++ tailWord_1133048).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1133048).length < 2 ^ (prefixWord ++ tailWord_1133048).sum := by decide
  have hdescent : baseEnd_1133048 < baseStart_1133048 := by decide
  rcases family_descends (prefixWord ++ tailWord_1133048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1133061 : List Nat := [1, 3, 1, 1, 2, 2, 2, 2, 3, 6]
def baseStart_1133061 : Nat := 118140960795 + 1133061 * 2 ^ 59
def prefixEnd_1133061 : Nat := 4983230072969 + 3 ^ 40 * 1133061 * 2
def baseEnd_1133061 : Nat := 193934967954698875775551

theorem tailTrace_1133061 : CollatzResearch.WordTrace tailWord_1133061 prefixEnd_1133061 193934967954698875775551 := by
  unfold tailWord_1133061
  simp only [CollatzResearch.WordTrace]
  refine ⟨41326129748120983257679037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27550753165413988838452691 41326129748120983257679037)
  ·
    refine ⟨15497298655545368721629639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 41326129748120983257679037 15497298655545368721629639)
    ·
      refine ⟨23245947983318053082444459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15497298655545368721629639 23245947983318053082444459)
      ·
        refine ⟨34868921974977079623666689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23245947983318053082444459 34868921974977079623666689)
        ·
          refine ⟨26151691481232809717750017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34868921974977079623666689 26151691481232809717750017)
          ·
            refine ⟨19613768610924607288312513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26151691481232809717750017 19613768610924607288312513)
            ·
              refine ⟨14710326458193455466234385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19613768610924607288312513 14710326458193455466234385)
              ·
                refine ⟨11032744843645091599675789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14710326458193455466234385 11032744843645091599675789)
                ·
                  refine ⟨4137279316366909349878421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11032744843645091599675789 4137279316366909349878421)
                  ·
                    refine ⟨193934967954698875775551, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4137279316366909349878421 193934967954698875775551)
                    ·
                      rfl

theorem cell23_1133061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 2, 2, 3, 6].length) (baseStart_1133061 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1133061 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1133061 prefixEnd_1133061 := by exact prefixLift 1133061
  have htrace : WordTrace (prefixWord ++ tailWord_1133061) baseStart_1133061 baseEnd_1133061 := by
    simpa [prefixWord, tailWord_1133061, baseEnd_1133061] using wordTrace_append hprefix tailTrace_1133061
  have hstable : (prefixWord ++ tailWord_1133061).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1133061).length < 2 ^ (prefixWord ++ tailWord_1133061).sum := by decide
  have hdescent : baseEnd_1133061 < baseStart_1133061 := by decide
  rcases family_descends (prefixWord ++ tailWord_1133061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1133069 : List Nat := [1, 7, 1, 1, 1, 2, 3, 1, 6]
def baseStart_1133069 : Nat := 118140960795 + 1133069 * 2 ^ 59
def prefixEnd_1133069 : Nat := 4983230072969 + 3 ^ 40 * 1133069 * 2
def baseEnd_1133069 : Nat := 64645445745481399558513

theorem tailTrace_1133069 : CollatzResearch.WordTrace tailWord_1133069 prefixEnd_1133069 64645445745481399558513 := by
  unfold tailWord_1133069
  simp only [CollatzResearch.WordTrace]
  refine ⟨41326421532092000623970261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27550947688061333749313507 41326421532092000623970261)
  ·
    refine ⟨968588004658406264624303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 41326421532092000623970261 968588004658406264624303)
    ·
      refine ⟨1452882006987609396936455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 968588004658406264624303 1452882006987609396936455)
      ·
        refine ⟨2179323010481414095404683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1452882006987609396936455 2179323010481414095404683)
        ·
          refine ⟨3268984515722121143107025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2179323010481414095404683 3268984515722121143107025)
          ·
            refine ⟨2451738386791590857330269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3268984515722121143107025 2451738386791590857330269)
            ·
              refine ⟨919401895046846571498851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2451738386791590857330269 919401895046846571498851)
              ·
                refine ⟨1379102842570269857248277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 919401895046846571498851 1379102842570269857248277)
                ·
                  refine ⟨64645445745481399558513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1379102842570269857248277 64645445745481399558513)
                  ·
                    rfl

theorem cell23_1133069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 2, 3, 1, 6].length) (baseStart_1133069 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1133069 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1133069 prefixEnd_1133069 := by exact prefixLift 1133069
  have htrace : WordTrace (prefixWord ++ tailWord_1133069) baseStart_1133069 baseEnd_1133069 := by
    simpa [prefixWord, tailWord_1133069, baseEnd_1133069] using wordTrace_append hprefix tailTrace_1133069
  have hstable : (prefixWord ++ tailWord_1133069).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1133069).length < 2 ^ (prefixWord ++ tailWord_1133069).sum := by decide
  have hdescent : baseEnd_1133069 < baseStart_1133069 := by decide
  rcases family_descends (prefixWord ++ tailWord_1133069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1133071 : List Nat := [1, 1, 2, 1, 1, 1, 2, 5, 3, 1, 5]
def baseStart_1133071 : Nat := 118140960795 + 1133071 * 2 ^ 59
def prefixEnd_1133071 : Nat := 4983230072969 + 3 ^ 40 * 1133071 * 2
def baseEnd_1133071 : Nat := 581810038670641588201607

theorem tailTrace_1133071 : CollatzResearch.WordTrace tailWord_1133071 prefixEnd_1133071 581810038670641588201607 := by
  unfold tailWord_1133071
  simp only [CollatzResearch.WordTrace]
  refine ⟨41326494478084754965543067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27550996318723169977028711 41326494478084754965543067)
  ·
    refine ⟨61989741717127132448314601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41326494478084754965543067 61989741717127132448314601)
    ·
      refine ⟨46492306287845349336235951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 61989741717127132448314601 46492306287845349336235951)
      ·
        refine ⟨69738459431768024004353927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46492306287845349336235951 69738459431768024004353927)
        ·
          refine ⟨104607689147652036006530891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 69738459431768024004353927 104607689147652036006530891)
          ·
            refine ⟨156911533721478054009796337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 104607689147652036006530891 156911533721478054009796337)
            ·
              refine ⟨117683650291108540507347253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 156911533721478054009796337 117683650291108540507347253)
              ·
                refine ⟨11032842214791425672563805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 117683650291108540507347253 11032842214791425672563805)
                ·
                  refine ⟨4137315830546784627211427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11032842214791425672563805 4137315830546784627211427)
                  ·
                    refine ⟨6205973745820176940817141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4137315830546784627211427 6205973745820176940817141)
                    ·
                      refine ⟨581810038670641588201607, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 6205973745820176940817141 581810038670641588201607)
                      ·
                        rfl

theorem cell23_1133071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 5, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 5, 3, 1, 5].length) (baseStart_1133071 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1133071 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1133071 prefixEnd_1133071 := by exact prefixLift 1133071
  have htrace : WordTrace (prefixWord ++ tailWord_1133071) baseStart_1133071 baseEnd_1133071 := by
    simpa [prefixWord, tailWord_1133071, baseEnd_1133071] using wordTrace_append hprefix tailTrace_1133071
  have hstable : (prefixWord ++ tailWord_1133071).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1133071).length < 2 ^ (prefixWord ++ tailWord_1133071).sum := by decide
  have hdescent : baseEnd_1133071 < baseStart_1133071 := by decide
  rcases family_descends (prefixWord ++ tailWord_1133071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1133081 : List Nat := [1, 2, 1, 2, 1, 1, 2, 5, 1, 1, 6]
def baseStart_1133081 : Nat := 118140960795 + 1133081 * 2 ^ 59
def prefixEnd_1133081 : Nat := 4983230072969 + 3 ^ 40 * 1133081 * 2
def baseEnd_1133081 : Nat := 581815173477186549076561

theorem tailTrace_1133081 : CollatzResearch.WordTrace tailWord_1133081 prefixEnd_1133081 581815173477186549076561 := by
  unfold tailWord_1133081
  simp only [CollatzResearch.WordTrace]
  refine ⟨41326859208048526673407097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27551239472032351115604731 41326859208048526673407097)
  ·
    refine ⟨30995144406036395005055323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41326859208048526673407097 30995144406036395005055323)
    ·
      refine ⟨46492716609054592507582985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30995144406036395005055323 46492716609054592507582985)
      ·
        refine ⟨34869537456790944380687239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46492716609054592507582985 34869537456790944380687239)
        ·
          refine ⟨52304306185186416571030859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34869537456790944380687239 52304306185186416571030859)
          ·
            refine ⟨78456459277779624856546289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 52304306185186416571030859 78456459277779624856546289)
            ·
              refine ⟨58842344458334718642409717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 78456459277779624856546289 58842344458334718642409717)
              ·
                refine ⟨5516469792968879872725911, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 58842344458334718642409717 5516469792968879872725911)
                ·
                  refine ⟨8274704689453319809088867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5516469792968879872725911 8274704689453319809088867)
                  ·
                    refine ⟨12412057034179979713633301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8274704689453319809088867 12412057034179979713633301)
                    ·
                      refine ⟨581815173477186549076561, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 12412057034179979713633301 581815173477186549076561)
                      ·
                        rfl

theorem cell23_1133081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 2, 5, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 2, 5, 1, 1, 6].length) (baseStart_1133081 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1133081 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1133081 prefixEnd_1133081 := by exact prefixLift 1133081
  have htrace : WordTrace (prefixWord ++ tailWord_1133081) baseStart_1133081 baseEnd_1133081 := by
    simpa [prefixWord, tailWord_1133081, baseEnd_1133081] using wordTrace_append hprefix tailTrace_1133081
  have hstable : (prefixWord ++ tailWord_1133081).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1133081).length < 2 ^ (prefixWord ++ tailWord_1133081).sum := by decide
  have hdescent : baseEnd_1133081 < baseStart_1133081 := by decide
  rcases family_descends (prefixWord ++ tailWord_1133081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1133085 : List Nat := [1, 4, 2, 2, 1, 2, 1, 4, 1, 1, 4]
def baseStart_1133085 : Nat := 118140960795 + 1133085 * 2 ^ 59
def prefixEnd_1133085 : Nat := 4983230072969 + 3 ^ 40 * 1133085 * 2
def baseEnd_1133085 : Nat := 581817227399804533426543

theorem tailTrace_1133085 : CollatzResearch.WordTrace tailWord_1133085 prefixEnd_1133085 581817227399804533426543 := by
  unfold tailWord_1133085
  simp only [CollatzResearch.WordTrace]
  refine ⟨41327005100034035356552709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27551336733356023571035139 41327005100034035356552709)
  ·
    refine ⟨7748813456256381629353633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 41327005100034035356552709 7748813456256381629353633)
    ·
      refine ⟨5811610092192286222015225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7748813456256381629353633 5811610092192286222015225)
      ·
        refine ⟨4358707569144214666511419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5811610092192286222015225 4358707569144214666511419)
        ·
          refine ⟨6538061353716321999767129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4358707569144214666511419 6538061353716321999767129)
          ·
            refine ⟨4903546015287241499825347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6538061353716321999767129 4903546015287241499825347)
            ·
              refine ⟨7355319022930862249738021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4903546015287241499825347 7355319022930862249738021)
              ·
                refine ⟨1379122316799536671825879, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7355319022930862249738021 1379122316799536671825879)
                ·
                  refine ⟨2068683475199305007738819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1379122316799536671825879 2068683475199305007738819)
                  ·
                    refine ⟨3103025212798957511608229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2068683475199305007738819 3103025212798957511608229)
                    ·
                      refine ⟨581817227399804533426543, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3103025212798957511608229 581817227399804533426543)
                      ·
                        rfl

theorem cell23_1133085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 2, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 2, 1, 4, 1, 1, 4].length) (baseStart_1133085 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1133085 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1133085 prefixEnd_1133085 := by exact prefixLift 1133085
  have htrace : WordTrace (prefixWord ++ tailWord_1133085) baseStart_1133085 baseEnd_1133085 := by
    simpa [prefixWord, tailWord_1133085, baseEnd_1133085] using wordTrace_append hprefix tailTrace_1133085
  have hstable : (prefixWord ++ tailWord_1133085).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1133085).length < 2 ^ (prefixWord ++ tailWord_1133085).sum := by decide
  have hdescent : baseEnd_1133085 < baseStart_1133085 := by decide
  rcases family_descends (prefixWord ++ tailWord_1133085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1133096 : List Nat := [2, 1, 5, 2, 1, 3, 1, 3, 1, 1, 3]
def baseStart_1133096 : Nat := 118140960795 + 1133096 * 2 ^ 59
def prefixEnd_1133096 : Nat := 4983230072969 + 3 ^ 40 * 1133096 * 2
def baseEnd_1133096 : Nat := 581822875687003990388993

theorem tailTrace_1133096 : CollatzResearch.WordTrace tailWord_1133096 prefixEnd_1133096 581822875687003990388993 := by
  unfold tailWord_1133096
  simp only [CollatzResearch.WordTrace]
  refine ⟨20663703151497092117601571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27551604201996122823468761 20663703151497092117601571)
  ·
    refine ⟨30995554727245638176402357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20663703151497092117601571 30995554727245638176402357)
    ·
      refine ⟨2905833255679278579037721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 30995554727245638176402357 2905833255679278579037721)
      ·
        refine ⟨2179374941759458934278291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2905833255679278579037721 2179374941759458934278291)
        ·
          refine ⟨3269062412639188401417437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2179374941759458934278291 3269062412639188401417437)
          ·
            refine ⟨1225898404739695650531539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3269062412639188401417437 1225898404739695650531539)
            ·
              refine ⟨1838847607109543475797309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1225898404739695650531539 1838847607109543475797309)
              ·
                refine ⟨689567852666078803423991, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1838847607109543475797309 689567852666078803423991)
                ·
                  refine ⟨1034351778999118205135987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 689567852666078803423991 1034351778999118205135987)
                  ·
                    refine ⟨1551527668498677307703981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1034351778999118205135987 1551527668498677307703981)
                    ·
                      refine ⟨581822875687003990388993, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1551527668498677307703981 581822875687003990388993)
                      ·
                        rfl

theorem cell23_1133096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 3, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 3, 1, 3, 1, 1, 3].length) (baseStart_1133096 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1133096 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1133096 prefixEnd_1133096 := by exact prefixLift 1133096
  have htrace : WordTrace (prefixWord ++ tailWord_1133096) baseStart_1133096 baseEnd_1133096 := by
    simpa [prefixWord, tailWord_1133096, baseEnd_1133096] using wordTrace_append hprefix tailTrace_1133096
  have hstable : (prefixWord ++ tailWord_1133096).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1133096).length < 2 ^ (prefixWord ++ tailWord_1133096).sum := by decide
  have hdescent : baseEnd_1133096 < baseStart_1133096 := by decide
  rcases family_descends (prefixWord ++ tailWord_1133096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1133105 : List Nat := [1, 2, 2, 3, 1, 1, 4, 3, 1, 2, 3]
def baseStart_1133105 : Nat := 118140960795 + 1133105 * 2 ^ 59
def prefixEnd_1133105 : Nat := 4983230072969 + 3 ^ 40 * 1133105 * 2
def baseEnd_1133105 : Nat := 581827497012894455176451

theorem tailTrace_1133105 : CollatzResearch.WordTrace tailWord_1133105 prefixEnd_1133105 581827497012894455176451 := by
  unfold tailWord_1133105
  simp only [CollatzResearch.WordTrace]
  refine ⟨41327734559961578772280769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27551823039974385848187179 41327734559961578772280769)
  ·
    refine ⟨30995800919971184079210577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41327734559961578772280769 30995800919971184079210577)
    ·
      refine ⟨23246850689978388059407933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30995800919971184079210577 23246850689978388059407933)
      ·
        refine ⟨8717569008741895522277975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23246850689978388059407933 8717569008741895522277975)
        ·
          refine ⟨13076353513112843283416963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8717569008741895522277975 13076353513112843283416963)
          ·
            refine ⟨19614530269669264925125445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13076353513112843283416963 19614530269669264925125445)
            ·
              refine ⟨3677724425562987173461021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 19614530269669264925125445 3677724425562987173461021)
              ·
                refine ⟨1379146659586120190047883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3677724425562987173461021 1379146659586120190047883)
                ·
                  refine ⟨2068719989379180285071825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1379146659586120190047883 2068719989379180285071825)
                  ·
                    refine ⟨1551539992034385213803869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2068719989379180285071825 1551539992034385213803869)
                    ·
                      refine ⟨581827497012894455176451, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1551539992034385213803869 581827497012894455176451)
                      ·
                        rfl

theorem cell23_1133105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 4, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 4, 3, 1, 2, 3].length) (baseStart_1133105 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1133105 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1133105 prefixEnd_1133105 := by exact prefixLift 1133105
  have htrace : WordTrace (prefixWord ++ tailWord_1133105) baseStart_1133105 baseEnd_1133105 := by
    simpa [prefixWord, tailWord_1133105, baseEnd_1133105] using wordTrace_append hprefix tailTrace_1133105
  have hstable : (prefixWord ++ tailWord_1133105).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1133105).length < 2 ^ (prefixWord ++ tailWord_1133105).sum := by decide
  have hdescent : baseEnd_1133105 < baseStart_1133105 := by decide
  rcases family_descends (prefixWord ++ tailWord_1133105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1133170 : List Nat := [3, 2, 1, 2, 5, 1, 2, 2, 1, 2, 2]
def baseStart_1133170 : Nat := 118140960795 + 1133170 * 2 ^ 59
def prefixEnd_1133170 : Nat := 4983230072969 + 3 ^ 40 * 1133170 * 2
def baseEnd_1133170 : Nat := 581860873255436700863653

theorem tailTrace_1133170 : CollatzResearch.WordTrace tailWord_1133170 prefixEnd_1133170 581860873255436700863653 := by
  unfold tailWord_1133170
  simp only [CollatzResearch.WordTrace]
  refine ⟨10332526326181523718349241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 27553403536484063248931309 10332526326181523718349241)
  ·
    refine ⟨7749394744636142788761931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10332526326181523718349241 7749394744636142788761931)
    ·
      refine ⟨11624092116954214183142897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7749394744636142788761931 11624092116954214183142897)
      ·
        refine ⟨8718069087715660637357173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11624092116954214183142897 8718069087715660637357173)
        ·
          refine ⟨817318976973343184752235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 8718069087715660637357173 817318976973343184752235)
          ·
            refine ⟨1225978465460014777128353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 817318976973343184752235 1225978465460014777128353)
            ·
              refine ⟨919483849095011082846265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1225978465460014777128353 919483849095011082846265)
              ·
                refine ⟨689612886821258312134699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 919483849095011082846265 689612886821258312134699)
                ·
                  refine ⟨1034419330231887468202049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 689612886821258312134699 1034419330231887468202049)
                  ·
                    refine ⟨775814497673915601151537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1034419330231887468202049 775814497673915601151537)
                    ·
                      refine ⟨581860873255436700863653, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 775814497673915601151537 581860873255436700863653)
                      ·
                        rfl

theorem cell23_1133170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 5, 1, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 5, 1, 2, 2, 1, 2, 2].length) (baseStart_1133170 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1133170 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1133170 prefixEnd_1133170 := by exact prefixLift 1133170
  have htrace : WordTrace (prefixWord ++ tailWord_1133170) baseStart_1133170 baseEnd_1133170 := by
    simpa [prefixWord, tailWord_1133170, baseEnd_1133170] using wordTrace_append hprefix tailTrace_1133170
  have hstable : (prefixWord ++ tailWord_1133170).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1133170).length < 2 ^ (prefixWord ++ tailWord_1133170).sum := by decide
  have hdescent : baseEnd_1133170 < baseStart_1133170 := by decide
  rcases family_descends (prefixWord ++ tailWord_1133170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1133265 : List Nat := [1, 2, 2, 1, 2, 3, 2, 3, 2, 1, 4]
def baseStart_1133265 : Nat := 118140960795 + 1133265 * 2 ^ 59
def prefixEnd_1133265 : Nat := 4983230072969 + 3 ^ 40 * 1133265 * 2
def baseEnd_1133265 : Nat := 581909653917613829175715

theorem tailTrace_1133265 : CollatzResearch.WordTrace tailWord_1133265 prefixEnd_1133265 581909653917613829175715 := by
  unfold tailWord_1133265
  simp only [CollatzResearch.WordTrace]
  refine ⟨41333570239381926098105249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27555713492921284065403499 41333570239381926098105249)
  ·
    refine ⟨31000177679536444573578937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41333570239381926098105249 31000177679536444573578937)
    ·
      refine ⟨23250133259652333430184203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31000177679536444573578937 23250133259652333430184203)
      ·
        refine ⟨34875199889478500145276305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23250133259652333430184203 34875199889478500145276305)
        ·
          refine ⟨26156399917108875108957229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34875199889478500145276305 26156399917108875108957229)
          ·
            refine ⟨9808649968915828165858961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 26156399917108875108957229 9808649968915828165858961)
            ·
              refine ⟨7356487476686871124394221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9808649968915828165858961 7356487476686871124394221)
              ·
                refine ⟨2758682803757576671647833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7356487476686871124394221 2758682803757576671647833)
                ·
                  refine ⟨2069012102818182503735875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2758682803757576671647833 2069012102818182503735875)
                  ·
                    refine ⟨3103518154227273755603813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2069012102818182503735875 3103518154227273755603813)
                    ·
                      refine ⟨581909653917613829175715, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3103518154227273755603813 581909653917613829175715)
                      ·
                        rfl

theorem cell23_1133265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 2, 3, 2, 1, 4].length) (baseStart_1133265 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1133265 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1133265 prefixEnd_1133265 := by exact prefixLift 1133265
  have htrace : WordTrace (prefixWord ++ tailWord_1133265) baseStart_1133265 baseEnd_1133265 := by
    simpa [prefixWord, tailWord_1133265, baseEnd_1133265] using wordTrace_append hprefix tailTrace_1133265
  have hstable : (prefixWord ++ tailWord_1133265).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1133265).length < 2 ^ (prefixWord ++ tailWord_1133265).sum := by decide
  have hdescent : baseEnd_1133265 < baseStart_1133265 := by decide
  rcases family_descends (prefixWord ++ tailWord_1133265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1133266 : List Nat := [3, 2, 2, 2, 4, 1, 1, 3, 5]
def baseStart_1133266 : Nat := 118140960795 + 1133266 * 2 ^ 59
def prefixEnd_1133266 : Nat := 4983230072969 + 3 ^ 40 * 1133266 * 2
def baseEnd_1133266 : Nat := 64656685266474258362579

theorem tailTrace_1133266 : CollatzResearch.WordTrace tailWord_1133266 prefixEnd_1133266 64656685266474258362579 := by
  unfold tailWord_1133266
  simp only [CollatzResearch.WordTrace]
  refine ⟨10333401678094575817222913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 27555737808252202179261101 10333401678094575817222913)
  ·
    refine ⟨7750051258570931862917185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10333401678094575817222913 7750051258570931862917185)
    ·
      refine ⟨5812538443928198897187889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7750051258570931862917185 5812538443928198897187889)
      ·
        refine ⟨4359403832946149172890917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5812538443928198897187889 4359403832946149172890917)
        ·
          refine ⟨817388218677402969917047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4359403832946149172890917 817388218677402969917047)
          ·
            refine ⟨1226082328016104454875571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 817388218677402969917047 1226082328016104454875571)
            ·
              refine ⟨1839123492024156682313357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1226082328016104454875571 1839123492024156682313357)
              ·
                refine ⟨689671309509058755867509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1839123492024156682313357 689671309509058755867509)
                ·
                  refine ⟨64656685266474258362579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 689671309509058755867509 64656685266474258362579)
                  ·
                    rfl

theorem cell23_1133266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 4, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 4, 1, 1, 3, 5].length) (baseStart_1133266 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1133266 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1133266 prefixEnd_1133266 := by exact prefixLift 1133266
  have htrace : WordTrace (prefixWord ++ tailWord_1133266) baseStart_1133266 baseEnd_1133266 := by
    simpa [prefixWord, tailWord_1133266, baseEnd_1133266] using wordTrace_append hprefix tailTrace_1133266
  have hstable : (prefixWord ++ tailWord_1133266).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1133266).length < 2 ^ (prefixWord ++ tailWord_1133266).sum := by decide
  have hdescent : baseEnd_1133266 < baseStart_1133266 := by decide
  rcases family_descends (prefixWord ++ tailWord_1133266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1133302 : List Nat := [5, 1, 1, 1, 1, 2, 1, 2, 4, 2, 3]
def baseStart_1133302 : Nat := 118140960795 + 1133302 * 2 ^ 59
def prefixEnd_1133302 : Nat := 4983230072969 + 3 ^ 40 * 1133302 * 2
def baseEnd_1133302 : Nat := 581928652701830184413045

theorem tailTrace_1133302 : CollatzResearch.WordTrace tailWord_1133302 prefixEnd_1133302 581928652701830184413045 := by
  unfold tailWord_1133302
  simp only [CollatzResearch.WordTrace]
  refine ⟨2583432483765492588575135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 27556613160165254278134773 2583432483765492588575135)
  ·
    refine ⟨3875148725648238882862703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2583432483765492588575135 3875148725648238882862703)
    ·
      refine ⟨5812723088472358324294055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3875148725648238882862703 5812723088472358324294055)
      ·
        refine ⟨8719084632708537486441083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5812723088472358324294055 8719084632708537486441083)
        ·
          refine ⟨13078626949062806229661625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8719084632708537486441083 13078626949062806229661625)
          ·
            refine ⟨9808970211797104672246219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13078626949062806229661625 9808970211797104672246219)
            ·
              refine ⟨14713455317695657008369329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9808970211797104672246219 14713455317695657008369329)
              ·
                refine ⟨11035091488271742756276997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14713455317695657008369329 11035091488271742756276997)
                ·
                  refine ⟨2069079654050951766801937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11035091488271742756276997 2069079654050951766801937)
                  ·
                    refine ⟨1551809740538213825101453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2069079654050951766801937 1551809740538213825101453)
                    ·
                      refine ⟨581928652701830184413045, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1551809740538213825101453 581928652701830184413045)
                      ·
                        rfl

theorem cell23_1133302_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 1, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 1, 2, 4, 2, 3].length) (baseStart_1133302 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1133302 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1133302 prefixEnd_1133302 := by exact prefixLift 1133302
  have htrace : WordTrace (prefixWord ++ tailWord_1133302) baseStart_1133302 baseEnd_1133302 := by
    simpa [prefixWord, tailWord_1133302, baseEnd_1133302] using wordTrace_append hprefix tailTrace_1133302
  have hstable : (prefixWord ++ tailWord_1133302).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1133302).length < 2 ^ (prefixWord ++ tailWord_1133302).sum := by decide
  have hdescent : baseEnd_1133302 < baseStart_1133302 := by decide
  rcases family_descends (prefixWord ++ tailWord_1133302) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1133319 : List Nat := [1, 1, 4, 4, 1, 2, 2, 1, 2, 2, 3]
def baseStart_1133319 : Nat := 118140960795 + 1133319 * 2 ^ 59
def prefixEnd_1133319 : Nat := 4983230072969 + 3 ^ 40 * 1133319 * 2
def baseEnd_1133319 : Nat := 581937381872956617900467

theorem tailTrace_1133319 : CollatzResearch.WordTrace tailWord_1133319 prefixEnd_1133319 581937381872956617900467 := by
  unfold tailWord_1133319
  simp only [CollatzResearch.WordTrace]
  refine ⟨41335539781186293320571011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27557026520790862213714007 41335539781186293320571011)
  ·
    refine ⟨62003309671779439980856517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41335539781186293320571011 62003309671779439980856517)
    ·
      refine ⟨11625620563458644996410597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 62003309671779439980856517 11625620563458644996410597)
      ·
        refine ⟨2179803855648495936826987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 11625620563458644996410597 2179803855648495936826987)
        ·
          refine ⟨3269705783472743905240481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2179803855648495936826987 3269705783472743905240481)
          ·
            refine ⟨2452279337604557928930361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3269705783472743905240481 2452279337604557928930361)
            ·
              refine ⟨1839209503203418446697771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2452279337604557928930361 1839209503203418446697771)
              ·
                refine ⟨2758814254805127670046657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1839209503203418446697771 2758814254805127670046657)
                ·
                  refine ⟨2069110691103845752534993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2758814254805127670046657 2069110691103845752534993)
                  ·
                    refine ⟨1551833018327884314401245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2069110691103845752534993 1551833018327884314401245)
                    ·
                      refine ⟨581937381872956617900467, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1551833018327884314401245 581937381872956617900467)
                      ·
                        rfl

theorem cell23_1133319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 2, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 2, 2, 1, 2, 2, 3].length) (baseStart_1133319 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1133319 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1133319 prefixEnd_1133319 := by exact prefixLift 1133319
  have htrace : WordTrace (prefixWord ++ tailWord_1133319) baseStart_1133319 baseEnd_1133319 := by
    simpa [prefixWord, tailWord_1133319, baseEnd_1133319] using wordTrace_append hprefix tailTrace_1133319
  have hstable : (prefixWord ++ tailWord_1133319).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1133319).length < 2 ^ (prefixWord ++ tailWord_1133319).sum := by decide
  have hdescent : baseEnd_1133319 < baseStart_1133319 := by decide
  rcases family_descends (prefixWord ++ tailWord_1133319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1133355 : List Nat := [1, 1, 1, 1, 2, 1, 2, 6, 3, 1, 4]
def baseStart_1133355 : Nat := 118140960795 + 1133355 * 2 ^ 59
def prefixEnd_1133355 : Nat := 4983230072969 + 3 ^ 40 * 1133355 * 2
def baseEnd_1133355 : Nat := 581955867176518477050301

theorem tailTrace_1133355 : CollatzResearch.WordTrace tailWord_1133355 prefixEnd_1133355 581955867176518477050301 := by
  unfold tailWord_1133355
  simp only [CollatzResearch.WordTrace]
  refine ⟨41336852809055871468881519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27557901872703914312587679 41336852809055871468881519)
  ·
    refine ⟨62005279213583807203322279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41336852809055871468881519 62005279213583807203322279)
    ·
      refine ⟨93007918820375710804983419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62005279213583807203322279 93007918820375710804983419)
      ·
        refine ⟨139511878230563566207475129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 93007918820375710804983419 139511878230563566207475129)
        ·
          refine ⟨104633908672922674655606347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 139511878230563566207475129 104633908672922674655606347)
          ·
            refine ⟨156950863009384011983409521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 104633908672922674655606347 156950863009384011983409521)
            ·
              refine ⟨117713147257038008987557141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 156950863009384011983409521 117713147257038008987557141)
              ·
                refine ⟨5517803777673656671291741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 117713147257038008987557141 5517803777673656671291741)
                ·
                  refine ⟨2069176416627621251734403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5517803777673656671291741 2069176416627621251734403)
                  ·
                    refine ⟨3103764624941431877601605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2069176416627621251734403 3103764624941431877601605)
                    ·
                      refine ⟨581955867176518477050301, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3103764624941431877601605 581955867176518477050301)
                      ·
                        rfl

theorem cell23_1133355_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 6, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 6, 3, 1, 4].length) (baseStart_1133355 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1133355 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1133355 prefixEnd_1133355 := by exact prefixLift 1133355
  have htrace : WordTrace (prefixWord ++ tailWord_1133355) baseStart_1133355 baseEnd_1133355 := by
    simpa [prefixWord, tailWord_1133355, baseEnd_1133355] using wordTrace_append hprefix tailTrace_1133355
  have hstable : (prefixWord ++ tailWord_1133355).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1133355).length < 2 ^ (prefixWord ++ tailWord_1133355).sum := by decide
  have hdescent : baseEnd_1133355 < baseStart_1133355 := by decide
  rcases family_descends (prefixWord ++ tailWord_1133355) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1133372 : List Nat := [2, 2, 2, 2, 1, 1, 1, 6, 1, 1, 4]
def baseStart_1133372 : Nat := 118140960795 + 1133372 * 2 ^ 59
def prefixEnd_1133372 : Nat := 4983230072969 + 3 ^ 40 * 1133372 * 2
def baseEnd_1133372 : Nat := 581964596347644910537723

theorem tailTrace_1133372 : CollatzResearch.WordTrace tailWord_1133372 prefixEnd_1133372 581964596347644910537723 := by
  unfold tailWord_1133372
  simp only [CollatzResearch.WordTrace]
  refine ⟨20668736424997141686125185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27558315233329522248166913 20668736424997141686125185)
  ·
    refine ⟨15501552318747856264593889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20668736424997141686125185 15501552318747856264593889)
    ·
      refine ⟨11626164239060892198445417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15501552318747856264593889 11626164239060892198445417)
      ·
        refine ⟨8719623179295669148834063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11626164239060892198445417 8719623179295669148834063)
        ·
          refine ⟨13079434768943503723251095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8719623179295669148834063 13079434768943503723251095)
          ·
            refine ⟨19619152153415255584876643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13079434768943503723251095 19619152153415255584876643)
            ·
              refine ⟨29428728230122883377314965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19619152153415255584876643 29428728230122883377314965)
              ·
                refine ⟨1379471635787010158311639, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 29428728230122883377314965 1379471635787010158311639)
                ·
                  refine ⟨2069207453680515237467459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1379471635787010158311639 2069207453680515237467459)
                  ·
                    refine ⟨3103811180520772856201189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2069207453680515237467459 3103811180520772856201189)
                    ·
                      refine ⟨581964596347644910537723, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3103811180520772856201189 581964596347644910537723)
                      ·
                        rfl

theorem cell23_1133372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 1, 6, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 1, 6, 1, 1, 4].length) (baseStart_1133372 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1133372 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1133372 prefixEnd_1133372 := by exact prefixLift 1133372
  have htrace : WordTrace (prefixWord ++ tailWord_1133372) baseStart_1133372 baseEnd_1133372 := by
    simpa [prefixWord, tailWord_1133372, baseEnd_1133372] using wordTrace_append hprefix tailTrace_1133372
  have hstable : (prefixWord ++ tailWord_1133372).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1133372).length < 2 ^ (prefixWord ++ tailWord_1133372).sum := by decide
  have hdescent : baseEnd_1133372 < baseStart_1133372 := by decide
  rcases family_descends (prefixWord ++ tailWord_1133372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1133399 : List Nat := [1, 1, 3, 2, 4, 1, 3, 2, 2, 4]
def baseStart_1133399 : Nat := 118140960795 + 1133399 * 2 ^ 59
def prefixEnd_1133399 : Nat := 4983230072969 + 3 ^ 40 * 1133399 * 2
def baseEnd_1133399 : Nat := 193992820108438768300033

theorem tailTrace_1133399 : CollatzResearch.WordTrace tailWord_1133399 prefixEnd_1133399 193992820108438768300033 := by
  unfold tailWord_1133399
  simp only [CollatzResearch.WordTrace]
  refine ⟨41338457620896466983483251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27558971747264311322322167 41338457620896466983483251)
  ·
    refine ⟨62007686431344700475224877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41338457620896466983483251 62007686431344700475224877)
    ·
      refine ⟨23252882411754262678209329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 62007686431344700475224877 23252882411754262678209329)
      ·
        refine ⟨17439661808815697008656997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23252882411754262678209329 17439661808815697008656997)
        ·
          refine ⟨3269936589152943189123187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 17439661808815697008656997 3269936589152943189123187)
          ·
            refine ⟨4904904883729414783684781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3269936589152943189123187 4904904883729414783684781)
            ·
              refine ⟨1839339331398530543881793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4904904883729414783684781 1839339331398530543881793)
              ·
                refine ⟨1379504498548897907911345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1839339331398530543881793 1379504498548897907911345)
                ·
                  refine ⟨1034628373911673430933509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1379504498548897907911345 1034628373911673430933509)
                  ·
                    refine ⟨193992820108438768300033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1034628373911673430933509 193992820108438768300033)
                    ·
                      rfl

theorem cell23_1133399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 1, 3, 2, 2, 4].length) (baseStart_1133399 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1133399 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1133399 prefixEnd_1133399 := by exact prefixLift 1133399
  have htrace : WordTrace (prefixWord ++ tailWord_1133399) baseStart_1133399 baseEnd_1133399 := by
    simpa [prefixWord, tailWord_1133399, baseEnd_1133399] using wordTrace_append hprefix tailTrace_1133399
  have hstable : (prefixWord ++ tailWord_1133399).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1133399).length < 2 ^ (prefixWord ++ tailWord_1133399).sum := by decide
  have hdescent : baseEnd_1133399 < baseStart_1133399 := by decide
  rcases family_descends (prefixWord ++ tailWord_1133399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1133416 : List Nat := [2, 1, 4, 2, 1, 3, 3, 1, 2, 4]
def baseStart_1133416 : Nat := 118140960795 + 1133416 * 2 ^ 59
def prefixEnd_1133416 : Nat := 4983230072969 + 3 ^ 40 * 1133416 * 2
def baseEnd_1133416 : Nat := 193995729832147579462507

theorem tailTrace_1133416 : CollatzResearch.WordTrace tailWord_1133416 prefixEnd_1133416 193995729832147579462507 := by
  unfold tailWord_1133416
  simp only [CollatzResearch.WordTrace]
  refine ⟨20669538830917439443426051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27559385107889919257901401 20669538830917439443426051)
  ·
    refine ⟨31004308246376159165139077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20669538830917439443426051 31004308246376159165139077)
    ·
      refine ⟨5813307796195529843463577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 31004308246376159165139077 5813307796195529843463577)
      ·
        refine ⟨4359980847146647382597683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5813307796195529843463577 4359980847146647382597683)
        ·
          refine ⟨6539971270719971073896525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4359980847146647382597683 6539971270719971073896525)
          ·
            refine ⟨2452489226519989152711197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6539971270719971073896525 2452489226519989152711197)
            ·
              refine ⟨919683459944995932266699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2452489226519989152711197 919683459944995932266699)
              ·
                refine ⟨1379525189917493898400049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 919683459944995932266699 1379525189917493898400049)
                ·
                  refine ⟨1034643892438120423800037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1379525189917493898400049 1034643892438120423800037)
                  ·
                    refine ⟨193995729832147579462507, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1034643892438120423800037 193995729832147579462507)
                    ·
                      rfl

theorem cell23_1133416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 3, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 3, 3, 1, 2, 4].length) (baseStart_1133416 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1133416 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1133416 prefixEnd_1133416 := by exact prefixLift 1133416
  have htrace : WordTrace (prefixWord ++ tailWord_1133416) baseStart_1133416 baseEnd_1133416 := by
    simpa [prefixWord, tailWord_1133416, baseEnd_1133416] using wordTrace_append hprefix tailTrace_1133416
  have hstable : (prefixWord ++ tailWord_1133416).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1133416).length < 2 ^ (prefixWord ++ tailWord_1133416).sum := by decide
  have hdescent : baseEnd_1133416 < baseStart_1133416 := by decide
  rcases family_descends (prefixWord ++ tailWord_1133416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1133429 : List Nat := [1, 3, 4, 1, 1, 4, 2, 7]
def baseStart_1133429 : Nat := 118140960795 + 1133429 * 2 ^ 59
def prefixEnd_1133429 : Nat := 4983230072969 + 3 ^ 40 * 1133429 * 2
def baseEnd_1133429 : Nat := 21555328323887081019443

theorem tailTrace_1133429 : CollatzResearch.WordTrace tailWord_1133429 prefixEnd_1133429 21555328323887081019443 := by
  unfold tailWord_1133429
  simp only [CollatzResearch.WordTrace]
  refine ⟨41339551810787782107075341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27559701207191854738050227 41339551810787782107075341)
  ·
    refine ⟨15502331929045418290153253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 41339551810787782107075341 15502331929045418290153253)
    ·
      refine ⟨2906687236696015929403735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 15502331929045418290153253 2906687236696015929403735)
      ·
        refine ⟨4360030855044023894105603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2906687236696015929403735 4360030855044023894105603)
        ·
          refine ⟨6540046282566035841158405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4360030855044023894105603 6540046282566035841158405)
          ·
            refine ⟨1226258677981131720217201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6540046282566035841158405 1226258677981131720217201)
            ·
              refine ⟨919694008485848790162901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1226258677981131720217201 919694008485848790162901)
              ·
                refine ⟨21555328323887081019443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 919694008485848790162901 21555328323887081019443)
                ·
                  rfl

theorem cell23_1133429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 4, 2, 7].length) (baseStart_1133429 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1133429 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1133429 prefixEnd_1133429 := by exact prefixLift 1133429
  have htrace : WordTrace (prefixWord ++ tailWord_1133429) baseStart_1133429 baseEnd_1133429 := by
    simpa [prefixWord, tailWord_1133429, baseEnd_1133429] using wordTrace_append hprefix tailTrace_1133429
  have hstable : (prefixWord ++ tailWord_1133429).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1133429).length < 2 ^ (prefixWord ++ tailWord_1133429).sum := by decide
  have hdescent : baseEnd_1133429 < baseStart_1133429 := by decide
  rcases family_descends (prefixWord ++ tailWord_1133429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1133435 : List Nat := [1, 1, 1, 1, 1, 5, 3, 1, 2, 2, 5]
def baseStart_1133435 : Nat := 118140960795 + 1133435 * 2 ^ 59
def prefixEnd_1133435 : Nat := 4983230072969 + 3 ^ 40 * 1133435 * 2
def baseEnd_1133435 : Nat := 581996945628878164049933

theorem tailTrace_1133435 : CollatzResearch.WordTrace tailWord_1133435 prefixEnd_1133435 581996945628878164049933 := by
  unfold tailWord_1133435
  simp only [CollatzResearch.WordTrace]
  refine ⟨41339770648766045131793759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27559847099177363421195839 41339770648766045131793759)
  ·
    refine ⟨62009655973149067697690639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41339770648766045131793759 62009655973149067697690639)
    ·
      refine ⟨93014483959723601546535959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62009655973149067697690639 93014483959723601546535959)
      ·
        refine ⟨139521725939585402319803939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 93014483959723601546535959 139521725939585402319803939)
        ·
          refine ⟨209282588909378103479705909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 139521725939585402319803939 209282588909378103479705909)
          ·
            refine ⟨19620242710254197201222429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 209282588909378103479705909 19620242710254197201222429)
            ·
              refine ⟨7357591016345323950458411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19620242710254197201222429 7357591016345323950458411)
              ·
                refine ⟨11036386524517985925687617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7357591016345323950458411 11036386524517985925687617)
                ·
                  refine ⟨8277289893388489444265713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11036386524517985925687617 8277289893388489444265713)
                  ·
                    refine ⟨6207967420041367083199285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8277289893388489444265713 6207967420041367083199285)
                    ·
                      refine ⟨581996945628878164049933, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 6207967420041367083199285 581996945628878164049933)
                      ·
                        rfl

theorem cell23_1133435_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 3, 1, 2, 2, 5].length) (baseStart_1133435 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1133435 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1133435 prefixEnd_1133435 := by exact prefixLift 1133435
  have htrace : WordTrace (prefixWord ++ tailWord_1133435) baseStart_1133435 baseEnd_1133435 := by
    simpa [prefixWord, tailWord_1133435, baseEnd_1133435] using wordTrace_append hprefix tailTrace_1133435
  have hstable : (prefixWord ++ tailWord_1133435).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1133435).length < 2 ^ (prefixWord ++ tailWord_1133435).sum := by decide
  have hdescent : baseEnd_1133435 < baseStart_1133435 := by decide
  rcases family_descends (prefixWord ++ tailWord_1133435) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1133465 : List Nat := [1, 2, 1, 2, 1, 3, 1, 1, 3, 3, 5]
def baseStart_1133465 : Nat := 118140960795 + 1133465 * 2 ^ 59
def prefixEnd_1133465 : Nat := 4983230072969 + 3 ^ 40 * 1133465 * 2
def baseEnd_1133465 : Nat := 582012350048513046674795

theorem tailTrace_1133465 : CollatzResearch.WordTrace tailWord_1133465 prefixEnd_1133465 582012350048513046674795 := by
  unfold tailWord_1133465
  simp only [CollatzResearch.WordTrace]
  refine ⟨41340864838657360255385849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27560576559104906836923899 41340864838657360255385849)
  ·
    refine ⟨31005648628993020191539387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41340864838657360255385849 31005648628993020191539387)
    ·
      refine ⟨46508472943489530287309081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31005648628993020191539387 46508472943489530287309081)
      ·
        refine ⟨34881354707617147715481811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46508472943489530287309081 34881354707617147715481811)
        ·
          refine ⟨52322032061425721573222717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34881354707617147715481811 52322032061425721573222717)
          ·
            refine ⟨19620762023034645589958519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 52322032061425721573222717 19620762023034645589958519)
            ·
              refine ⟨29431143034551968384937779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19620762023034645589958519 29431143034551968384937779)
              ·
                refine ⟨44146714551827952577406669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29431143034551968384937779 44146714551827952577406669)
                ·
                  refine ⟨16555017956935482216527501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 44146714551827952577406669 16555017956935482216527501)
                  ·
                    refine ⟨6208131733850805831197813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16555017956935482216527501 6208131733850805831197813)
                    ·
                      refine ⟨582012350048513046674795, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 6208131733850805831197813 582012350048513046674795)
                      ·
                        rfl

theorem cell23_1133465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 1, 1, 3, 3, 5].length) (baseStart_1133465 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1133465 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1133465 prefixEnd_1133465 := by exact prefixLift 1133465
  have htrace : WordTrace (prefixWord ++ tailWord_1133465) baseStart_1133465 baseEnd_1133465 := by
    simpa [prefixWord, tailWord_1133465, baseEnd_1133465] using wordTrace_append hprefix tailTrace_1133465
  have hstable : (prefixWord ++ tailWord_1133465).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1133465).length < 2 ^ (prefixWord ++ tailWord_1133465).sum := by decide
  have hdescent : baseEnd_1133465 < baseStart_1133465 := by decide
  rcases family_descends (prefixWord ++ tailWord_1133465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1133473 : List Nat := [1, 2, 3, 4, 1, 1, 4, 1, 2, 1, 3]
def baseStart_1133473 : Nat := 118140960795 + 1133473 * 2 ^ 59
def prefixEnd_1133473 : Nat := 4983230072969 + 3 ^ 40 * 1133473 * 2
def baseEnd_1133473 : Nat := 582016457893749015374759

theorem tailTrace_1133473 : CollatzResearch.WordTrace tailWord_1133473 prefixEnd_1133473 582016457893749015374759 := by
  unfold tailWord_1133473
  simp only [CollatzResearch.WordTrace]
  refine ⟨41341156622628377621677073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27560771081752251747784715 41341156622628377621677073)
  ·
    refine ⟨31005867466971283216257805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41341156622628377621677073 31005867466971283216257805)
    ·
      refine ⟨11627200300114231206096677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 31005867466971283216257805 11627200300114231206096677)
      ·
        refine ⟨2180100056271418351143127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 11627200300114231206096677 2180100056271418351143127)
        ·
          refine ⟨3270150084407127526714691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2180100056271418351143127 3270150084407127526714691)
          ·
            refine ⟨4905225126610691290072037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3270150084407127526714691 4905225126610691290072037)
            ·
              refine ⟨919729711239504616888507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4905225126610691290072037 919729711239504616888507)
              ·
                refine ⟨1379594566859256925332761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 919729711239504616888507 1379594566859256925332761)
                ·
                  refine ⟨1034695925144442693999571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1379594566859256925332761 1034695925144442693999571)
                  ·
                    refine ⟨1552043887716664040999357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1034695925144442693999571 1552043887716664040999357)
                    ·
                      refine ⟨582016457893749015374759, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1552043887716664040999357 582016457893749015374759)
                      ·
                        rfl

theorem cell23_1133473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 1, 4, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 1, 4, 1, 2, 1, 3].length) (baseStart_1133473 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1133473 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1133473 prefixEnd_1133473 := by exact prefixLift 1133473
  have htrace : WordTrace (prefixWord ++ tailWord_1133473) baseStart_1133473 baseEnd_1133473 := by
    simpa [prefixWord, tailWord_1133473, baseEnd_1133473] using wordTrace_append hprefix tailTrace_1133473
  have hstable : (prefixWord ++ tailWord_1133473).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1133473).length < 2 ^ (prefixWord ++ tailWord_1133473).sum := by decide
  have hdescent : baseEnd_1133473 < baseStart_1133473 := by decide
  rcases family_descends (prefixWord ++ tailWord_1133473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1133519 : List Nat := [1, 1, 2, 1, 1, 7, 1, 4, 5]
def baseStart_1133519 : Nat := 118140960795 + 1133519 * 2 ^ 59
def prefixEnd_1133519 : Nat := 4983230072969 + 3 ^ 40 * 1133519 * 2
def baseEnd_1133519 : Nat := 64671119778206203933283

theorem tailTrace_1133519 : CollatzResearch.WordTrace tailWord_1133519 prefixEnd_1133519 64671119778206203933283 := by
  unfold tailWord_1133519
  simp only [CollatzResearch.WordTrace]
  refine ⟨41342834380461727477851611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27561889586974484985234407 41342834380461727477851611)
  ·
    refine ⟨62014251570692591216777417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41342834380461727477851611 62014251570692591216777417)
    ·
      refine ⟨46510688678019443412583063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 62014251570692591216777417 46510688678019443412583063)
      ·
        refine ⟨69766033017029165118874595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46510688678019443412583063 69766033017029165118874595)
        ·
          refine ⟨104649049525543747678311893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 69766033017029165118874595 104649049525543747678311893)
          ·
            refine ⟨2452712098254931586210435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 104649049525543747678311893 2452712098254931586210435)
            ·
              refine ⟨3679068147382397379315653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2452712098254931586210435 3679068147382397379315653)
              ·
                refine ⟨689825277634199508621685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3679068147382397379315653 689825277634199508621685)
                ·
                  refine ⟨64671119778206203933283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 689825277634199508621685 64671119778206203933283)
                  ·
                    rfl

theorem cell23_1133519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 7, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 7, 1, 4, 5].length) (baseStart_1133519 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1133519 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1133519 prefixEnd_1133519 := by exact prefixLift 1133519
  have htrace : WordTrace (prefixWord ++ tailWord_1133519) baseStart_1133519 baseEnd_1133519 := by
    simpa [prefixWord, tailWord_1133519, baseEnd_1133519] using wordTrace_append hprefix tailTrace_1133519
  have hstable : (prefixWord ++ tailWord_1133519).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1133519).length < 2 ^ (prefixWord ++ tailWord_1133519).sum := by decide
  have hdescent : baseEnd_1133519 < baseStart_1133519 := by decide
  rcases family_descends (prefixWord ++ tailWord_1133519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1133526 : List Nat := [5, 2, 1, 1, 2, 2, 1, 1, 2, 2, 4]
def baseStart_1133526 : Nat := 118140960795 + 1133526 * 2 ^ 59
def prefixEnd_1133526 : Nat := 4983230072969 + 3 ^ 40 * 1133526 * 2
def baseEnd_1133526 : Nat := 582043672368437308012015

theorem tailTrace_1133526 : CollatzResearch.WordTrace tailWord_1133526 prefixEnd_1133526 582043672368437308012015 := by
  unfold tailWord_1133526
  simp only [CollatzResearch.WordTrace]
  refine ⟨2583943105714772979584777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 27562059794290911782237621 2583943105714772979584777)
  ·
    refine ⟨1937957329286079734688583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2583943105714772979584777 1937957329286079734688583)
    ·
      refine ⟨2906935993929119602032875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1937957329286079734688583 2906935993929119602032875)
      ·
        refine ⟨4360403990893679403049313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2906935993929119602032875 4360403990893679403049313)
        ·
          refine ⟨3270302993170259552286985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4360403990893679403049313 3270302993170259552286985)
          ·
            refine ⟨2452727244877694664215239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3270302993170259552286985 2452727244877694664215239)
            ·
              refine ⟨3679090867316541996322859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2452727244877694664215239 3679090867316541996322859)
              ·
                refine ⟨5518636300974812994484289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3679090867316541996322859 5518636300974812994484289)
                ·
                  refine ⟨4138977225731109745863217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5518636300974812994484289 4138977225731109745863217)
                  ·
                    refine ⟨3104232919298332309397413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4138977225731109745863217 3104232919298332309397413)
                    ·
                      refine ⟨582043672368437308012015, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3104232919298332309397413 582043672368437308012015)
                      ·
                        rfl

theorem cell23_1133526_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 2, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 2, 1, 1, 2, 2, 4].length) (baseStart_1133526 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1133526 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1133526 prefixEnd_1133526 := by exact prefixLift 1133526
  have htrace : WordTrace (prefixWord ++ tailWord_1133526) baseStart_1133526 baseEnd_1133526 := by
    simpa [prefixWord, tailWord_1133526, baseEnd_1133526] using wordTrace_append hprefix tailTrace_1133526
  have hstable : (prefixWord ++ tailWord_1133526).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1133526).length < 2 ^ (prefixWord ++ tailWord_1133526).sum := by decide
  have hdescent : baseEnd_1133526 < baseStart_1133526 := by decide
  rcases family_descends (prefixWord ++ tailWord_1133526) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1133529 : List Nat := [1, 2, 1, 2, 5, 2, 1, 1, 2, 3, 3]
def baseStart_1133529 : Nat := 118140960795 + 1133529 * 2 ^ 59
def prefixEnd_1133529 : Nat := 4983230072969 + 3 ^ 40 * 1133529 * 2
def baseEnd_1133529 : Nat := 582045212810400796274501

theorem tailTrace_1133529 : CollatzResearch.WordTrace tailWord_1133529 prefixEnd_1133529 582045212810400796274501 := by
  unfold tailWord_1133529
  simp only [CollatzResearch.WordTrace]
  refine ⟨41343199110425499185715641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27562132740283666123810427 41343199110425499185715641)
  ·
    refine ⟨31007399332819124389286731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41343199110425499185715641 31007399332819124389286731)
    ·
      refine ⟨46511098999228686583930097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31007399332819124389286731 46511098999228686583930097)
      ·
        refine ⟨34883324249421514937947573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46511098999228686583930097 34883324249421514937947573)
        ·
          refine ⟨3270311648383267025432585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 34883324249421514937947573 3270311648383267025432585)
          ·
            refine ⟨2452733736287450269074439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3270311648383267025432585 2452733736287450269074439)
            ·
              refine ⟨3679100604431175403611659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2452733736287450269074439 3679100604431175403611659)
              ·
                refine ⟨5518650906646763105417489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3679100604431175403611659 5518650906646763105417489)
                ·
                  refine ⟨4138988179985072329063117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5518650906646763105417489 4138988179985072329063117)
                  ·
                    refine ⟨1552120567494402123398669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4138988179985072329063117 1552120567494402123398669)
                    ·
                      refine ⟨582045212810400796274501, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1552120567494402123398669 582045212810400796274501)
                      ·
                        rfl

theorem cell23_1133529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 2, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 2, 1, 1, 2, 3, 3].length) (baseStart_1133529 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1133529 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1133529 prefixEnd_1133529 := by exact prefixLift 1133529
  have htrace : WordTrace (prefixWord ++ tailWord_1133529) baseStart_1133529 baseEnd_1133529 := by
    simpa [prefixWord, tailWord_1133529, baseEnd_1133529] using wordTrace_append hprefix tailTrace_1133529
  have hstable : (prefixWord ++ tailWord_1133529).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1133529).length < 2 ^ (prefixWord ++ tailWord_1133529).sum := by decide
  have hdescent : baseEnd_1133529 < baseStart_1133529 := by decide
  rcases family_descends (prefixWord ++ tailWord_1133529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1133539 : List Nat := [1, 1, 1, 6, 1, 1, 1, 2, 2, 5, 2]
def baseStart_1133539 : Nat := 118140960795 + 1133539 * 2 ^ 59
def prefixEnd_1133539 : Nat := 4983230072969 + 3 ^ 40 * 1133539 * 2
def baseEnd_1133539 : Nat := 582050347616945757149455

theorem tailTrace_1133539 : CollatzResearch.WordTrace tailWord_1133539 prefixEnd_1133539 582050347616945757149455 := by
  unfold tailWord_1133539
  simp only [CollatzResearch.WordTrace]
  refine ⟨41343563840389270893579671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27562375893592847262386447 41343563840389270893579671)
  ·
    refine ⟨62015345760583906340369507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41343563840389270893579671 62015345760583906340369507)
    ·
      refine ⟨93023018640875859510554261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62015345760583906340369507 93023018640875859510554261)
      ·
        refine ⟨4360453998791055914557231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 93023018640875859510554261 4360453998791055914557231)
        ·
          refine ⟨6540680998186583871835847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4360453998791055914557231 6540680998186583871835847)
          ·
            refine ⟨9811021497279875807753771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6540680998186583871835847 9811021497279875807753771)
            ·
              refine ⟨14716532245919813711630657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9811021497279875807753771 14716532245919813711630657)
              ·
                refine ⟨11037399184439860283722993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14716532245919813711630657 11037399184439860283722993)
                ·
                  refine ⟨8278049388329895212792245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11037399184439860283722993 8278049388329895212792245)
                  ·
                    refine ⟨776067130155927676199273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8278049388329895212792245 776067130155927676199273)
                    ·
                      refine ⟨582050347616945757149455, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 776067130155927676199273 582050347616945757149455)
                      ·
                        rfl

theorem cell23_1133539_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 1, 2, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 1, 2, 2, 5, 2].length) (baseStart_1133539 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1133539 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1133539 prefixEnd_1133539 := by exact prefixLift 1133539
  have htrace : WordTrace (prefixWord ++ tailWord_1133539) baseStart_1133539 baseEnd_1133539 := by
    simpa [prefixWord, tailWord_1133539, baseEnd_1133539] using wordTrace_append hprefix tailTrace_1133539
  have hstable : (prefixWord ++ tailWord_1133539).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1133539).length < 2 ^ (prefixWord ++ tailWord_1133539).sum := by decide
  have hdescent : baseEnd_1133539 < baseStart_1133539 := by decide
  rcases family_descends (prefixWord ++ tailWord_1133539) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1133579 : List Nat := [1, 1, 1, 1, 6, 2, 1, 3, 3, 4]
def baseStart_1133579 : Nat := 118140960795 + 1133579 * 2 ^ 59
def prefixEnd_1133579 : Nat := 4983230072969 + 3 ^ 40 * 1133579 * 2
def baseEnd_1133579 : Nat := 194023628947708533549757

theorem tailTrace_1133579 : CollatzResearch.WordTrace tailWord_1133579 prefixEnd_1133579 194023628947708533549757 := by
  unfold tailWord_1133579
  simp only [CollatzResearch.WordTrace]
  refine ⟨41345022760244357725035791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27563348506829571816690527 41345022760244357725035791)
  ·
    refine ⟨62017534140366536587553687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41345022760244357725035791 62017534140366536587553687)
    ·
      refine ⟨93026301210549804881330531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62017534140366536587553687 93026301210549804881330531)
      ·
        refine ⟨139539451815824707321995797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 93026301210549804881330531 139539451815824707321995797)
        ·
          refine ⟨6540911803866783155718553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 139539451815824707321995797 6540911803866783155718553)
          ·
            refine ⟨4905683852900087366788915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6540911803866783155718553 4905683852900087366788915)
            ·
              refine ⟨7358525779350131050183373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4905683852900087366788915 7358525779350131050183373)
              ·
                refine ⟨2759447167256299143818765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7358525779350131050183373 2759447167256299143818765)
                ·
                  refine ⟨1034792687721112178932037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2759447167256299143818765 1034792687721112178932037)
                  ·
                    refine ⟨194023628947708533549757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1034792687721112178932037 194023628947708533549757)
                    ·
                      rfl

theorem cell23_1133579_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 2, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 2, 1, 3, 3, 4].length) (baseStart_1133579 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1133579 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1133579 prefixEnd_1133579 := by exact prefixLift 1133579
  have htrace : WordTrace (prefixWord ++ tailWord_1133579) baseStart_1133579 baseEnd_1133579 := by
    simpa [prefixWord, tailWord_1133579, baseEnd_1133579] using wordTrace_append hprefix tailTrace_1133579
  have hstable : (prefixWord ++ tailWord_1133579).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1133579).length < 2 ^ (prefixWord ++ tailWord_1133579).sum := by decide
  have hdescent : baseEnd_1133579 < baseStart_1133579 := by decide
  rcases family_descends (prefixWord ++ tailWord_1133579) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1133589 : List Nat := [1, 3, 2, 1, 4, 1, 1, 2, 1, 4, 3]
def baseStart_1133589 : Nat := 118140960795 + 1133589 * 2 ^ 59
def prefixEnd_1133589 : Nat := 4983230072969 + 3 ^ 40 * 1133589 * 2
def baseEnd_1133589 : Nat := 582076021649670561524225

theorem tailTrace_1133589 : CollatzResearch.WordTrace tailWord_1133589 prefixEnd_1133589 582076021649670561524225 := by
  unfold tailWord_1133589
  simp only [CollatzResearch.WordTrace]
  refine ⟨41345387490208129432899821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27563591660138752955266547 41345387490208129432899821)
  ·
    refine ⟨15504520308828048537337433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 41345387490208129432899821 15504520308828048537337433)
    ·
      refine ⟨11628390231621036403003075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15504520308828048537337433 11628390231621036403003075)
      ·
        refine ⟨17442585347431554604504613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11628390231621036403003075 17442585347431554604504613)
        ·
          refine ⟨3270484752643416488344615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 17442585347431554604504613 3270484752643416488344615)
          ·
            refine ⟨4905727128965124732516923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3270484752643416488344615 4905727128965124732516923)
            ·
              refine ⟨7358590693447687098775385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4905727128965124732516923 7358590693447687098775385)
              ·
                refine ⟨5518943020085765324081539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7358590693447687098775385 5518943020085765324081539)
                ·
                  refine ⟨8278414530128647986122309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5518943020085765324081539 8278414530128647986122309)
                  ·
                    refine ⟨1552202724399121497397933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 8278414530128647986122309 1552202724399121497397933)
                    ·
                      refine ⟨582076021649670561524225, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1552202724399121497397933 582076021649670561524225)
                      ·
                        rfl

theorem cell23_1133589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 1, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 1, 1, 2, 1, 4, 3].length) (baseStart_1133589 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1133589 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1133589 prefixEnd_1133589 := by exact prefixLift 1133589
  have htrace : WordTrace (prefixWord ++ tailWord_1133589) baseStart_1133589 baseEnd_1133589 := by
    simpa [prefixWord, tailWord_1133589, baseEnd_1133589] using wordTrace_append hprefix tailTrace_1133589
  have hstable : (prefixWord ++ tailWord_1133589).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1133589).length < 2 ^ (prefixWord ++ tailWord_1133589).sum := by decide
  have hdescent : baseEnd_1133589 < baseStart_1133589 := by decide
  rcases family_descends (prefixWord ++ tailWord_1133589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1133646 : List Nat := [4, 1, 1, 1, 1, 3, 1, 2, 4, 3, 2]
def baseStart_1133646 : Nat := 118140960795 + 1133646 * 2 ^ 59
def prefixEnd_1133646 : Nat := 4983230072969 + 3 ^ 40 * 1133646 * 2
def baseEnd_1133646 : Nat := 582105290046976838511463

theorem tailTrace_1133646 : CollatzResearch.WordTrace tailWord_1133646 prefixEnd_1133646 582105290046976838511463 := by
  unfold tailWord_1133646
  simp only [CollatzResearch.WordTrace]
  refine ⟨5168433306375203520965599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 27564977634001085445149861 5168433306375203520965599)
  ·
    refine ⟨7752649959562805281448399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5168433306375203520965599 7752649959562805281448399)
    ·
      refine ⟨11628974939344207922172599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7752649959562805281448399 11628974939344207922172599)
      ·
        refine ⟨17443462409016311883258899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11628974939344207922172599 17443462409016311883258899)
        ·
          refine ⟨26165193613524467824888349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17443462409016311883258899 26165193613524467824888349)
          ·
            refine ⟨9811947605071675434333131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 26165193613524467824888349 9811947605071675434333131)
            ·
              refine ⟨14717921407607513151499697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9811947605071675434333131 14717921407607513151499697)
              ·
                refine ⟨11038441055705634863624773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14717921407607513151499697 11038441055705634863624773)
                ·
                  refine ⟨2069707697944806536929645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11038441055705634863624773 2069707697944806536929645)
                  ·
                    refine ⟨776140386729302451348617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2069707697944806536929645 776140386729302451348617)
                    ·
                      refine ⟨582105290046976838511463, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 776140386729302451348617 582105290046976838511463)
                      ·
                        rfl

theorem cell23_1133646_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 1, 2, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 1, 2, 4, 3, 2].length) (baseStart_1133646 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1133646 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1133646 prefixEnd_1133646 := by exact prefixLift 1133646
  have htrace : WordTrace (prefixWord ++ tailWord_1133646) baseStart_1133646 baseEnd_1133646 := by
    simpa [prefixWord, tailWord_1133646, baseEnd_1133646] using wordTrace_append hprefix tailTrace_1133646
  have hstable : (prefixWord ++ tailWord_1133646).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1133646).length < 2 ^ (prefixWord ++ tailWord_1133646).sum := by decide
  have hdescent : baseEnd_1133646 < baseStart_1133646 := by decide
  rcases family_descends (prefixWord ++ tailWord_1133646) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1133669 : List Nat := [1, 3, 1, 3, 2, 1, 3, 2, 1, 6]
def baseStart_1133669 : Nat := 118140960795 + 1133669 * 2 ^ 59
def prefixEnd_1133669 : Nat := 4983230072969 + 3 ^ 40 * 1133669 * 2
def baseEnd_1133669 : Nat := 194039033367343416174619

theorem tailTrace_1133669 : CollatzResearch.WordTrace tailWord_1133669 prefixEnd_1133669 194039033367343416174619 := by
  unfold tailWord_1133669
  simp only [CollatzResearch.WordTrace]
  refine ⟨41348305329918303095812061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27565536886612202063874707 41348305329918303095812061)
  ·
    refine ⟨15505614498719363660929523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 41348305329918303095812061 15505614498719363660929523)
    ·
      refine ⟨23258421748079045491394285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15505614498719363660929523 23258421748079045491394285)
      ·
        refine ⟨8721908155529642059272857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23258421748079045491394285 8721908155529642059272857)
        ·
          refine ⟨6541431116647231544454643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8721908155529642059272857 6541431116647231544454643)
          ·
            refine ⟨9812146674970847316681965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6541431116647231544454643 9812146674970847316681965)
            ·
              refine ⟨3679555003114067743755737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9812146674970847316681965 3679555003114067743755737)
              ·
                refine ⟨2759666252335550807816803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3679555003114067743755737 2759666252335550807816803)
                ·
                  refine ⟨4139499378503326211725205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2759666252335550807816803 4139499378503326211725205)
                  ·
                    refine ⟨194039033367343416174619, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4139499378503326211725205 194039033367343416174619)
                    ·
                      rfl

theorem cell23_1133669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 3, 2, 1, 6].length) (baseStart_1133669 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1133669 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1133669 prefixEnd_1133669 := by exact prefixLift 1133669
  have htrace : WordTrace (prefixWord ++ tailWord_1133669) baseStart_1133669 baseEnd_1133669 := by
    simpa [prefixWord, tailWord_1133669, baseEnd_1133669] using wordTrace_append hprefix tailTrace_1133669
  have hstable : (prefixWord ++ tailWord_1133669).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1133669).length < 2 ^ (prefixWord ++ tailWord_1133669).sum := by decide
  have hdescent : baseEnd_1133669 < baseStart_1133669 := by decide
  rcases family_descends (prefixWord ++ tailWord_1133669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1133693 : List Nat := [1, 4, 1, 1, 3, 1, 2, 3, 3, 2, 2]
def baseStart_1133693 : Nat := 118140960795 + 1133693 * 2 ^ 59
def prefixEnd_1133693 : Nat := 4983230072969 + 3 ^ 40 * 1133693 * 2
def baseEnd_1133693 : Nat := 582129423637738154623747

theorem tailTrace_1133693 : CollatzResearch.WordTrace tailWord_1133693 prefixEnd_1133693 582129423637738154623747 := by
  unfold tailWord_1133693
  simp only [CollatzResearch.WordTrace]
  refine ⟨41349180681831355194685733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27566120454554236796457155 41349180681831355194685733)
  ·
    refine ⟨7752971377843379099003575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 41349180681831355194685733 7752971377843379099003575)
    ·
      refine ⟨11629457066765068648505363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7752971377843379099003575 11629457066765068648505363)
      ·
        refine ⟨17444185600147602972758045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11629457066765068648505363 17444185600147602972758045)
        ·
          refine ⟨6541569600055351114784267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17444185600147602972758045 6541569600055351114784267)
          ·
            refine ⟨9812354400083026672176401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6541569600055351114784267 9812354400083026672176401)
            ·
              refine ⟨7359265800062270004132301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9812354400083026672176401 7359265800062270004132301)
              ·
                refine ⟨2759724675023351251549613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7359265800062270004132301 2759724675023351251549613)
                ·
                  refine ⟨1034896753133756719331105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2759724675023351251549613 1034896753133756719331105)
                  ·
                    refine ⟨776172564850317539498329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1034896753133756719331105 776172564850317539498329)
                    ·
                      refine ⟨582129423637738154623747, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 776172564850317539498329 582129423637738154623747)
                      ·
                        rfl

theorem cell23_1133693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 2, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 2, 3, 3, 2, 2].length) (baseStart_1133693 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1133693 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1133693 prefixEnd_1133693 := by exact prefixLift 1133693
  have htrace : WordTrace (prefixWord ++ tailWord_1133693) baseStart_1133693 baseEnd_1133693 := by
    simpa [prefixWord, tailWord_1133693, baseEnd_1133693] using wordTrace_append hprefix tailTrace_1133693
  have hstable : (prefixWord ++ tailWord_1133693).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1133693).length < 2 ^ (prefixWord ++ tailWord_1133693).sum := by decide
  have hdescent : baseEnd_1133693 < baseStart_1133693 := by decide
  rcases family_descends (prefixWord ++ tailWord_1133693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1133706 : List Nat := [3, 1, 2, 3, 1, 1, 4, 1, 1, 2, 4]
def baseStart_1133706 : Nat := 118140960795 + 1133706 * 2 ^ 59
def prefixEnd_1133706 : Nat := 4983230072969 + 3 ^ 40 * 1133706 * 2
def baseEnd_1133706 : Nat := 582136098886246603761187

theorem tailTrace_1133706 : CollatzResearch.WordTrace tailWord_1133706 prefixEnd_1133706 582136098886246603761187 := by
  unfold tailWord_1133706
  simp only [CollatzResearch.WordTrace]
  refine ⟨10337413707696064603727243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 27566436553856172276605981 10337413707696064603727243)
  ·
    refine ⟨15506120561544096905590865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10337413707696064603727243 15506120561544096905590865)
    ·
      refine ⟨11629590421158072679193149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15506120561544096905590865 11629590421158072679193149)
      ·
        refine ⟨4361096407934277254697431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11629590421158072679193149 4361096407934277254697431)
        ·
          refine ⟨6541644611901415882046147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4361096407934277254697431 6541644611901415882046147)
          ·
            refine ⟨9812466917852123823069221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6541644611901415882046147 9812466917852123823069221)
            ·
              refine ⟨1839837547097273216825479, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9812466917852123823069221 1839837547097273216825479)
              ·
                refine ⟨2759756320645909825238219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1839837547097273216825479 2759756320645909825238219)
                ·
                  refine ⟨4139634480968864737857329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2759756320645909825238219 4139634480968864737857329)
                  ·
                    refine ⟨3104725860726648553392997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4139634480968864737857329 3104725860726648553392997)
                    ·
                      refine ⟨582136098886246603761187, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3104725860726648553392997 582136098886246603761187)
                      ·
                        rfl

theorem cell23_1133706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 4, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 4, 1, 1, 2, 4].length) (baseStart_1133706 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1133706 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1133706 prefixEnd_1133706 := by exact prefixLift 1133706
  have htrace : WordTrace (prefixWord ++ tailWord_1133706) baseStart_1133706 baseEnd_1133706 := by
    simpa [prefixWord, tailWord_1133706, baseEnd_1133706] using wordTrace_append hprefix tailTrace_1133706
  have hstable : (prefixWord ++ tailWord_1133706).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1133706).length < 2 ^ (prefixWord ++ tailWord_1133706).sum := by decide
  have hdescent : baseEnd_1133706 < baseStart_1133706 := by decide
  rcases family_descends (prefixWord ++ tailWord_1133706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1133710 : List Nat := [4, 1, 1, 3, 2, 2, 1, 2, 3, 2, 2]
def baseStart_1133710 : Nat := 118140960795 + 1133710 * 2 ^ 59
def prefixEnd_1133710 : Nat := 4983230072969 + 3 ^ 40 * 1133710 * 2
def baseEnd_1133710 : Nat := 582138152808864588111169

theorem tailTrace_1133710 : CollatzResearch.WordTrace tailWord_1133710 prefixEnd_1133710 582138152808864588111169 := by
  unfold tailWord_1133710
  simp only [CollatzResearch.WordTrace]
  refine ⟨5168725090346220887256823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 27566533815179844732036389 5168725090346220887256823)
  ·
    refine ⟨7753087635519331330885235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5168725090346220887256823 7753087635519331330885235)
    ·
      refine ⟨11629631453278996996327853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7753087635519331330885235 11629631453278996996327853)
      ·
        refine ⟨4361111794979623873622945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11629631453278996996327853 4361111794979623873622945)
        ·
          refine ⟨3270833846234717905217209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4361111794979623873622945 3270833846234717905217209)
          ·
            refine ⟨2453125384676038428912907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3270833846234717905217209 2453125384676038428912907)
            ·
              refine ⟨3679688077014057643369361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2453125384676038428912907 3679688077014057643369361)
              ·
                refine ⟨2759766057760543232527021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3679688077014057643369361 2759766057760543232527021)
                ·
                  refine ⟨1034912271660203712197633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2759766057760543232527021 1034912271660203712197633)
                  ·
                    refine ⟨776184203745152784148225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1034912271660203712197633 776184203745152784148225)
                    ·
                      refine ⟨582138152808864588111169, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 776184203745152784148225 582138152808864588111169)
                      ·
                        rfl

theorem cell23_1133710_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 2, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 2, 1, 2, 3, 2, 2].length) (baseStart_1133710 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1133710 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1133710 prefixEnd_1133710 := by exact prefixLift 1133710
  have htrace : WordTrace (prefixWord ++ tailWord_1133710) baseStart_1133710 baseEnd_1133710 := by
    simpa [prefixWord, tailWord_1133710, baseEnd_1133710] using wordTrace_append hprefix tailTrace_1133710
  have hstable : (prefixWord ++ tailWord_1133710).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1133710).length < 2 ^ (prefixWord ++ tailWord_1133710).sum := by decide
  have hdescent : baseEnd_1133710 < baseStart_1133710 := by decide
  rcases family_descends (prefixWord ++ tailWord_1133710) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1133727 : List Nat := [1, 1, 2, 6, 3, 1, 2, 1, 1, 1, 4]
def baseStart_1133727 : Nat := 118140960795 + 1133727 * 2 ^ 59
def prefixEnd_1133727 : Nat := 4983230072969 + 3 ^ 40 * 1133727 * 2
def baseEnd_1133727 : Nat := 582146881979991021598591

theorem tailTrace_1133727 : CollatzResearch.WordTrace tailWord_1133727 prefixEnd_1133727 582146881979991021598591 := by
  unfold tailWord_1133727
  simp only [CollatzResearch.WordTrace]
  refine ⟨41350420763708179001423435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27566947175805452667615623 41350420763708179001423435)
  ·
    refine ⟨62025631145562268502135153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41350420763708179001423435 62025631145562268502135153)
    ·
      refine ⟨46519223359171701376601365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 62025631145562268502135153 46519223359171701376601365)
      ·
        refine ⟨2180588594961173502028189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 46519223359171701376601365 2180588594961173502028189)
        ·
          refine ⟨817720723110440063260571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2180588594961173502028189 817720723110440063260571)
          ·
            refine ⟨1226581084665660094890857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 817720723110440063260571 1226581084665660094890857)
            ·
              refine ⟨919935813499245071168143, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1226581084665660094890857 919935813499245071168143)
              ·
                refine ⟨1379903720248867606752215, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 919935813499245071168143 1379903720248867606752215)
                ·
                  refine ⟨2069855580373301410128323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1379903720248867606752215 2069855580373301410128323)
                  ·
                    refine ⟨3104783370559952115192485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2069855580373301410128323 3104783370559952115192485)
                    ·
                      refine ⟨582146881979991021598591, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3104783370559952115192485 582146881979991021598591)
                      ·
                        rfl

theorem cell23_1133727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 3, 1, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 3, 1, 2, 1, 1, 1, 4].length) (baseStart_1133727 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1133727 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1133727 prefixEnd_1133727 := by exact prefixLift 1133727
  have htrace : WordTrace (prefixWord ++ tailWord_1133727) baseStart_1133727 baseEnd_1133727 := by
    simpa [prefixWord, tailWord_1133727, baseEnd_1133727] using wordTrace_append hprefix tailTrace_1133727
  have hstable : (prefixWord ++ tailWord_1133727).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1133727).length < 2 ^ (prefixWord ++ tailWord_1133727).sum := by decide
  have hdescent : baseEnd_1133727 < baseStart_1133727 := by decide
  rcases family_descends (prefixWord ++ tailWord_1133727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1133730 : List Nat := [3, 3, 1, 3, 2, 1, 1, 3, 1, 2, 3]
def baseStart_1133730 : Nat := 118140960795 + 1133730 * 2 ^ 59
def prefixEnd_1133730 : Nat := 4983230072969 + 3 ^ 40 * 1133730 * 2
def baseEnd_1133730 : Nat := 582148422421954509861077

theorem tailTrace_1133730 : CollatzResearch.WordTrace tailWord_1133730 prefixEnd_1133730 582148422421954509861077 := by
  unfold tailWord_1133730
  simp only [CollatzResearch.WordTrace]
  refine ⟨10337632545674327628445661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 27567020121798207009188429 10337632545674327628445661)
  ·
    refine ⟨3876612204627872860667123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10337632545674327628445661 3876612204627872860667123)
    ·
      refine ⟨5814918306941809291000685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3876612204627872860667123 5814918306941809291000685)
      ·
        refine ⟨2180594365103178484125257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5814918306941809291000685 2180594365103178484125257)
        ·
          refine ⟨1635445773827383863093943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2180594365103178484125257 1635445773827383863093943)
          ·
            refine ⟨2453168660741075794640915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1635445773827383863093943 2453168660741075794640915)
            ·
              refine ⟨3679752991111613691961373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2453168660741075794640915 3679752991111613691961373)
              ·
                refine ⟨1379907371666855134485515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3679752991111613691961373 1379907371666855134485515)
                ·
                  refine ⟨2069861057500282701728273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1379907371666855134485515 2069861057500282701728273)
                  ·
                    refine ⟨1552395793125212026296205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2069861057500282701728273 1552395793125212026296205)
                    ·
                      refine ⟨582148422421954509861077, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1552395793125212026296205 582148422421954509861077)
                      ·
                        rfl

theorem cell23_1133730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 2, 1, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 2, 1, 1, 3, 1, 2, 3].length) (baseStart_1133730 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1133730 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1133730 prefixEnd_1133730 := by exact prefixLift 1133730
  have htrace : WordTrace (prefixWord ++ tailWord_1133730) baseStart_1133730 baseEnd_1133730 := by
    simpa [prefixWord, tailWord_1133730, baseEnd_1133730] using wordTrace_append hprefix tailTrace_1133730
  have hstable : (prefixWord ++ tailWord_1133730).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1133730).length < 2 ^ (prefixWord ++ tailWord_1133730).sum := by decide
  have hdescent : baseEnd_1133730 < baseStart_1133730 := by decide
  rcases family_descends (prefixWord ++ tailWord_1133730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1133743 : List Nat := [1, 1, 2, 1, 2, 3, 5, 2, 2, 1, 3]
def baseStart_1133743 : Nat := 118140960795 + 1133743 * 2 ^ 59
def prefixEnd_1133743 : Nat := 4983230072969 + 3 ^ 40 * 1133743 * 2
def baseEnd_1133743 : Nat := 582155097670462958998517

theorem tailTrace_1133743 : CollatzResearch.WordTrace tailWord_1133743 prefixEnd_1133743 582155097670462958998517 := by
  unfold tailWord_1133743
  simp only [CollatzResearch.WordTrace]
  refine ⟨41351004331650213734005883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27567336221100142489337255 41351004331650213734005883)
  ·
    refine ⟨62026506497475320601008825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41351004331650213734005883 62026506497475320601008825)
    ·
      refine ⟨46519879873106490450756619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 62026506497475320601008825 46519879873106490450756619)
      ·
        refine ⟨69779819809659735676134929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46519879873106490450756619 69779819809659735676134929)
        ·
          refine ⟨52334864857244801757101197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 69779819809659735676134929 52334864857244801757101197)
          ·
            refine ⟨19625574321466800658912949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 52334864857244801757101197 19625574321466800658912949)
            ·
              refine ⟨1839897592637512561773089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 19625574321466800658912949 1839897592637512561773089)
              ·
                refine ⟨1379923194478134421329817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1839897592637512561773089 1379923194478134421329817)
                ·
                  refine ⟨1034942395858600815997363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1379923194478134421329817 1034942395858600815997363)
                  ·
                    refine ⟨1552413593787901223996045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1034942395858600815997363 1552413593787901223996045)
                    ·
                      refine ⟨582155097670462958998517, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1552413593787901223996045 582155097670462958998517)
                      ·
                        rfl

theorem cell23_1133743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 5, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 5, 2, 2, 1, 3].length) (baseStart_1133743 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1133743 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1133743 prefixEnd_1133743 := by exact prefixLift 1133743
  have htrace : WordTrace (prefixWord ++ tailWord_1133743) baseStart_1133743 baseEnd_1133743 := by
    simpa [prefixWord, tailWord_1133743, baseEnd_1133743] using wordTrace_append hprefix tailTrace_1133743
  have hstable : (prefixWord ++ tailWord_1133743).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1133743).length < 2 ^ (prefixWord ++ tailWord_1133743).sum := by decide
  have hdescent : baseEnd_1133743 < baseStart_1133743 := by decide
  rcases family_descends (prefixWord ++ tailWord_1133743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1133759 : List Nat := [1, 1, 2, 2, 2, 2, 4, 1, 2, 6]
def baseStart_1133759 : Nat := 118140960795 + 1133759 * 2 ^ 59
def prefixEnd_1133759 : Nat := 4983230072969 + 3 ^ 40 * 1133759 * 2
def baseEnd_1133759 : Nat := 194054437786978298799481

theorem tailTrace_1133759 : CollatzResearch.WordTrace tailWord_1133759 prefixEnd_1133759 194054437786978298799481 := by
  unfold tailWord_1133759
  simp only [CollatzResearch.WordTrace]
  refine ⟨41351587899592248466588331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27567725266394832311058887 41351587899592248466588331)
  ·
    refine ⟨62027381849388372699882497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41351587899592248466588331 62027381849388372699882497)
    ·
      refine ⟨46520536387041279524911873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 62027381849388372699882497 46520536387041279524911873)
      ·
        refine ⟨34890402290280959643683905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46520536387041279524911873 34890402290280959643683905)
        ·
          refine ⟨26167801717710719732762929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34890402290280959643683905 26167801717710719732762929)
          ·
            refine ⟨19625851288283039799572197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26167801717710719732762929 19625851288283039799572197)
            ·
              refine ⟨3679847116553069962419787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 19625851288283039799572197 3679847116553069962419787)
              ·
                refine ⟨5519770674829604943629681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3679847116553069962419787 5519770674829604943629681)
                ·
                  refine ⟨4139828006122203707722261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5519770674829604943629681 4139828006122203707722261)
                  ·
                    refine ⟨194054437786978298799481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4139828006122203707722261 194054437786978298799481)
                    ·
                      rfl

theorem cell23_1133759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 4, 1, 2, 6].length) (baseStart_1133759 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1133759 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1133759 prefixEnd_1133759 := by exact prefixLift 1133759
  have htrace : WordTrace (prefixWord ++ tailWord_1133759) baseStart_1133759 baseEnd_1133759 := by
    simpa [prefixWord, tailWord_1133759, baseEnd_1133759] using wordTrace_append hprefix tailTrace_1133759
  have hstable : (prefixWord ++ tailWord_1133759).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1133759).length < 2 ^ (prefixWord ++ tailWord_1133759).sum := by decide
  have hdescent : baseEnd_1133759 < baseStart_1133759 := by decide
  rcases family_descends (prefixWord ++ tailWord_1133759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1133760 : List Nat := [2, 1, 1, 2, 7, 1, 1, 1, 1, 3, 3]
def baseStart_1133760 : Nat := 118140960795 + 1133760 * 2 ^ 59
def prefixEnd_1133760 : Nat := 4983230072969 + 3 ^ 40 * 1133760 * 2
def baseEnd_1133760 : Nat := 582163826841589392485939

theorem tailTrace_1133760 : CollatzResearch.WordTrace tailWord_1133760 prefixEnd_1133760 582163826841589392485939 := by
  unfold tailWord_1133760
  simp only [CollatzResearch.WordTrace]
  refine ⟨20675812186294312818687367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27567749581725750424916489 20675812186294312818687367)
  ·
    refine ⟨31013718279441469228031051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20675812186294312818687367 31013718279441469228031051)
    ·
      refine ⟨46520577419162203842046577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31013718279441469228031051 46520577419162203842046577)
      ·
        refine ⟨34890433064371652881534933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46520577419162203842046577 34890433064371652881534933)
        ·
          refine ⟨817744524946210614410975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 34890433064371652881534933 817744524946210614410975)
          ·
            refine ⟨1226616787419315921616463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 817744524946210614410975 1226616787419315921616463)
            ·
              refine ⟨1839925181128973882424695, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1226616787419315921616463 1839925181128973882424695)
              ·
                refine ⟨2759887771693460823637043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1839925181128973882424695 2759887771693460823637043)
                ·
                  refine ⟨4139831657540191235455565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2759887771693460823637043 4139831657540191235455565)
                  ·
                    refine ⟨1552436871577571713295837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4139831657540191235455565 1552436871577571713295837)
                    ·
                      refine ⟨582163826841589392485939, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1552436871577571713295837 582163826841589392485939)
                      ·
                        rfl

theorem cell23_1133760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 7, 1, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 7, 1, 1, 1, 1, 3, 3].length) (baseStart_1133760 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1133760 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1133760 prefixEnd_1133760 := by exact prefixLift 1133760
  have htrace : WordTrace (prefixWord ++ tailWord_1133760) baseStart_1133760 baseEnd_1133760 := by
    simpa [prefixWord, tailWord_1133760, baseEnd_1133760] using wordTrace_append hprefix tailTrace_1133760
  have hstable : (prefixWord ++ tailWord_1133760).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1133760).length < 2 ^ (prefixWord ++ tailWord_1133760).sum := by decide
  have hdescent : baseEnd_1133760 < baseStart_1133760 := by decide
  rcases family_descends (prefixWord ++ tailWord_1133760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1133769 : List Nat := [1, 2, 1, 1, 2, 1, 1, 2, 3, 6, 3]
def baseStart_1133769 : Nat := 118140960795 + 1133769 * 2 ^ 59
def prefixEnd_1133769 : Nat := 4983230072969 + 3 ^ 40 * 1133769 * 2
def baseEnd_1133769 : Nat := 582168448167479857273397

theorem tailTrace_1133769 : CollatzResearch.WordTrace tailWord_1133769 prefixEnd_1133769 582168448167479857273397 := by
  unfold tailWord_1133769
  simp only [CollatzResearch.WordTrace]
  refine ⟨41351952629556020174452361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27567968419704013449634907 41351952629556020174452361)
  ·
    refine ⟨31013964472167015130839271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41351952629556020174452361 31013964472167015130839271)
    ·
      refine ⟨46520946708250522696258907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31013964472167015130839271 46520946708250522696258907)
      ·
        refine ⟨69781420062375784044388361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46520946708250522696258907 69781420062375784044388361)
        ·
          refine ⟨52336065046781838033291271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 69781420062375784044388361 52336065046781838033291271)
          ·
            refine ⟨78504097570172757049936907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 52336065046781838033291271 78504097570172757049936907)
            ·
              refine ⟨117756146355259135574905361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 78504097570172757049936907 117756146355259135574905361)
              ·
                refine ⟨88317109766444351681179021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 117756146355259135574905361 88317109766444351681179021)
                ·
                  refine ⟨33118916162416631880442133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 88317109766444351681179021 33118916162416631880442133)
                  ·
                    refine ⟨1552449195113279619395725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 33118916162416631880442133 1552449195113279619395725)
                    ·
                      refine ⟨582168448167479857273397, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1552449195113279619395725 582168448167479857273397)
                      ·
                        rfl

theorem cell23_1133769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 2, 3, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 2, 3, 6, 3].length) (baseStart_1133769 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1133769 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1133769 prefixEnd_1133769 := by exact prefixLift 1133769
  have htrace : WordTrace (prefixWord ++ tailWord_1133769) baseStart_1133769 baseEnd_1133769 := by
    simpa [prefixWord, tailWord_1133769, baseEnd_1133769] using wordTrace_append hprefix tailTrace_1133769
  have hstable : (prefixWord ++ tailWord_1133769).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1133769).length < 2 ^ (prefixWord ++ tailWord_1133769).sum := by decide
  have hdescent : baseEnd_1133769 < baseStart_1133769 := by decide
  rcases family_descends (prefixWord ++ tailWord_1133769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1133770 : List Nat := [3, 1, 2, 1, 3, 3, 2, 2, 1, 3, 2]
def baseStart_1133770 : Nat := 118140960795 + 1133770 * 2 ^ 59
def prefixEnd_1133770 : Nat := 4983230072969 + 3 ^ 40 * 1133770 * 2
def baseEnd_1133770 : Nat := 582168961648134353360893

theorem tailTrace_1133770 : CollatzResearch.WordTrace tailWord_1133770 prefixEnd_1133770 582168961648134353360893 := by
  unfold tailWord_1133770
  simp only [CollatzResearch.WordTrace]
  refine ⟨10337997275638099336309691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 27567992735034931563492509 10337997275638099336309691)
  ·
    refine ⟨15506995913457149004464537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10337997275638099336309691 15506995913457149004464537)
    ·
      refine ⟨11630246935092861753348403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15506995913457149004464537 11630246935092861753348403)
      ·
        refine ⟨17445370402639292630022605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11630246935092861753348403 17445370402639292630022605)
        ·
          refine ⟨6542013900989734736258477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17445370402639292630022605 6542013900989734736258477)
          ·
            refine ⟨2453255212871150526096929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6542013900989734736258477 2453255212871150526096929)
            ·
              refine ⟨1839941409653362894572697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2453255212871150526096929 1839941409653362894572697)
              ·
                refine ⟨1379956057240022170929523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1839941409653362894572697 1379956057240022170929523)
                ·
                  refine ⟨2069934085860033256394285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1379956057240022170929523 2069934085860033256394285)
                  ·
                    refine ⟨776225282197512471147857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2069934085860033256394285 776225282197512471147857)
                    ·
                      refine ⟨582168961648134353360893, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 776225282197512471147857 582168961648134353360893)
                      ·
                        rfl

theorem cell23_1133770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 3, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 3, 2, 2, 1, 3, 2].length) (baseStart_1133770 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1133770 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1133770 prefixEnd_1133770 := by exact prefixLift 1133770
  have htrace : WordTrace (prefixWord ++ tailWord_1133770) baseStart_1133770 baseEnd_1133770 := by
    simpa [prefixWord, tailWord_1133770, baseEnd_1133770] using wordTrace_append hprefix tailTrace_1133770
  have hstable : (prefixWord ++ tailWord_1133770).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1133770).length < 2 ^ (prefixWord ++ tailWord_1133770).sum := by decide
  have hdescent : baseEnd_1133770 < baseStart_1133770 := by decide
  rcases family_descends (prefixWord ++ tailWord_1133770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1133783 : List Nat := [1, 1, 3, 2, 1, 2, 3, 2, 4, 2, 2]
def baseStart_1133783 : Nat := 118140960795 + 1133783 * 2 ^ 59
def prefixEnd_1133783 : Nat := 4983230072969 + 3 ^ 40 * 1133783 * 2
def baseEnd_1133783 : Nat := 582175636896642802498333

theorem tailTrace_1133783 : CollatzResearch.WordTrace tailWord_1133783 prefixEnd_1133783 582175636896642802498333 := by
  unfold tailWord_1133783
  simp only [CollatzResearch.WordTrace]
  refine ⟨41352463251505300565462003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27568308834336867043641335 41352463251505300565462003)
  ·
    refine ⟨62028694877257950848193005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41352463251505300565462003 62028694877257950848193005)
    ·
      refine ⟨23260760578971731568072377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 62028694877257950848193005 23260760578971731568072377)
      ·
        refine ⟨17445570434228798676054283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23260760578971731568072377 17445570434228798676054283)
        ·
          refine ⟨26168355651343198014081425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17445570434228798676054283 26168355651343198014081425)
          ·
            refine ⟨19626266738507398510561069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26168355651343198014081425 19626266738507398510561069)
            ·
              refine ⟨7359850026940274441460401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19626266738507398510561069 7359850026940274441460401)
              ·
                refine ⟨5519887520205205831095301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7359850026940274441460401 5519887520205205831095301)
                ·
                  refine ⟨1034978910038476093330369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5519887520205205831095301 1034978910038476093330369)
                  ·
                    refine ⟨776234182528857069997777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1034978910038476093330369 776234182528857069997777)
                    ·
                      refine ⟨582175636896642802498333, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 776234182528857069997777 582175636896642802498333)
                      ·
                        rfl

theorem cell23_1133783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 3, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 3, 2, 4, 2, 2].length) (baseStart_1133783 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1133783 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1133783 prefixEnd_1133783 := by exact prefixLift 1133783
  have htrace : WordTrace (prefixWord ++ tailWord_1133783) baseStart_1133783 baseEnd_1133783 := by
    simpa [prefixWord, tailWord_1133783, baseEnd_1133783] using wordTrace_append hprefix tailTrace_1133783
  have hstable : (prefixWord ++ tailWord_1133783).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1133783).length < 2 ^ (prefixWord ++ tailWord_1133783).sum := by decide
  have hdescent : baseEnd_1133783 < baseStart_1133783 := by decide
  rcases family_descends (prefixWord ++ tailWord_1133783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1133800 : List Nat := [2, 1, 4, 1, 2, 1, 2, 4, 2, 2, 2]
def baseStart_1133800 : Nat := 118140960795 + 1133800 * 2 ^ 59
def prefixEnd_1133800 : Nat := 4983230072969 + 3 ^ 40 * 1133800 * 2
def baseEnd_1133800 : Nat := 582184366067769235985755

theorem tailTrace_1133800 : CollatzResearch.WordTrace tailWord_1133800 prefixEnd_1133800 582184366067769235985755 := by
  unfold tailWord_1133800
  simp only [CollatzResearch.WordTrace]
  refine ⟨20676541646221856234415427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27568722194962474979220569 20676541646221856234415427)
  ·
    refine ⟨31014812469332784351623141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20676541646221856234415427 31014812469332784351623141)
    ·
      refine ⟨5815277337999897065929339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 31014812469332784351623141 5815277337999897065929339)
      ·
        refine ⟨8722916006999845598894009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5815277337999897065929339 8722916006999845598894009)
        ·
          refine ⟨6542187005249884199170507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8722916006999845598894009 6542187005249884199170507)
          ·
            refine ⟨9813280507874826298755761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6542187005249884199170507 9813280507874826298755761)
            ·
              refine ⟨7359960380906119724066821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9813280507874826298755761 7359960380906119724066821)
              ·
                refine ⟨1379992571419897448262529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7359960380906119724066821 1379992571419897448262529)
                ·
                  refine ⟨1034994428564923086196897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1379992571419897448262529 1034994428564923086196897)
                  ·
                    refine ⟨776245821423692314647673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1034994428564923086196897 776245821423692314647673)
                    ·
                      refine ⟨582184366067769235985755, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 776245821423692314647673 582184366067769235985755)
                      ·
                        rfl

theorem cell23_1133800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 2, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 2, 4, 2, 2, 2].length) (baseStart_1133800 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1133800 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1133800 prefixEnd_1133800 := by exact prefixLift 1133800
  have htrace : WordTrace (prefixWord ++ tailWord_1133800) baseStart_1133800 baseEnd_1133800 := by
    simpa [prefixWord, tailWord_1133800, baseEnd_1133800] using wordTrace_append hprefix tailTrace_1133800
  have hstable : (prefixWord ++ tailWord_1133800).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1133800).length < 2 ^ (prefixWord ++ tailWord_1133800).sum := by decide
  have hdescent : baseEnd_1133800 < baseStart_1133800 := by decide
  rcases family_descends (prefixWord ++ tailWord_1133800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1133806 : List Nat := [4, 1, 2, 1, 1, 1, 5, 1, 7]
def baseStart_1133806 : Nat := 118140960795 + 1133806 * 2 ^ 59
def prefixEnd_1133806 : Nat := 4983230072969 + 3 ^ 40 * 1133806 * 2
def baseEnd_1133806 : Nat := 64687494105744023612303

theorem tailTrace_1133806 : CollatzResearch.WordTrace tailWord_1133806 prefixEnd_1133806 64687494105744023612303 := by
  unfold tailWord_1133806
  simp only [CollatzResearch.WordTrace]
  refine ⟨5169162766302746936693659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 27568868086947983662366181 5169162766302746936693659)
  ·
    refine ⟨7753744149454120405040489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5169162766302746936693659 7753744149454120405040489)
    ·
      refine ⟨5815308112090590303780367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7753744149454120405040489 5815308112090590303780367)
      ·
        refine ⟨8722962168135885455670551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5815308112090590303780367 8722962168135885455670551)
        ·
          refine ⟨13084443252203828183505827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8722962168135885455670551 13084443252203828183505827)
          ·
            refine ⟨19626664878305742275258741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13084443252203828183505827 19626664878305742275258741)
            ·
              refine ⟨1839999832341163338305507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 19626664878305742275258741 1839999832341163338305507)
              ·
                refine ⟨2759999748511745007458261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1839999832341163338305507 2759999748511745007458261)
                ·
                  refine ⟨64687494105744023612303, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2759999748511745007458261 64687494105744023612303)
                  ·
                    rfl

theorem cell23_1133806_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 5, 1, 7].length) (baseStart_1133806 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1133806 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1133806 prefixEnd_1133806 := by exact prefixLift 1133806
  have htrace : WordTrace (prefixWord ++ tailWord_1133806) baseStart_1133806 baseEnd_1133806 := by
    simpa [prefixWord, tailWord_1133806, baseEnd_1133806] using wordTrace_append hprefix tailTrace_1133806
  have hstable : (prefixWord ++ tailWord_1133806).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1133806).length < 2 ^ (prefixWord ++ tailWord_1133806).sum := by decide
  have hdescent : baseEnd_1133806 < baseStart_1133806 := by decide
  rcases family_descends (prefixWord ++ tailWord_1133806) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1133829 : List Nat := [1, 3, 1, 1, 2, 1, 3, 2, 1, 1, 7]
def baseStart_1133829 : Nat := 118140960795 + 1133829 * 2 ^ 59
def prefixEnd_1133829 : Nat := 4983230072969 + 3 ^ 40 * 1133829 * 2
def baseEnd_1133829 : Nat := 582199257006749622523121

theorem tailTrace_1133829 : CollatzResearch.WordTrace tailWord_1133829 prefixEnd_1133829 582199257006749622523121 := by
  unfold tailWord_1133829
  simp only [CollatzResearch.WordTrace]
  refine ⟨41354141009338650421636541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27569427339559100281091027 41354141009338650421636541)
  ·
    refine ⟨15507802878501993908113703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 41354141009338650421636541 15507802878501993908113703)
    ·
      refine ⟨23261704317752990862170555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15507802878501993908113703 23261704317752990862170555)
      ·
        refine ⟨34892556476629486293255833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23261704317752990862170555 34892556476629486293255833)
        ·
          refine ⟨26169417357472114719941875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34892556476629486293255833 26169417357472114719941875)
          ·
            refine ⟨39254126036208172079912813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26169417357472114719941875 39254126036208172079912813)
            ·
              refine ⟨14720297263578064529967305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 39254126036208172079912813 14720297263578064529967305)
              ·
                refine ⟨11040222947683548397475479, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14720297263578064529967305 11040222947683548397475479)
                ·
                  refine ⟨16560334421525322596213219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11040222947683548397475479 16560334421525322596213219)
                  ·
                    refine ⟨24840501632287983894319829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 16560334421525322596213219 24840501632287983894319829)
                    ·
                      refine ⟨582199257006749622523121, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 24840501632287983894319829 582199257006749622523121)
                      ·
                        rfl

theorem cell23_1133829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 3, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 3, 2, 1, 1, 7].length) (baseStart_1133829 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1133829 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1133829 prefixEnd_1133829 := by exact prefixLift 1133829
  have htrace : WordTrace (prefixWord ++ tailWord_1133829) baseStart_1133829 baseEnd_1133829 := by
    simpa [prefixWord, tailWord_1133829, baseEnd_1133829] using wordTrace_append hprefix tailTrace_1133829
  have hstable : (prefixWord ++ tailWord_1133829).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1133829).length < 2 ^ (prefixWord ++ tailWord_1133829).sum := by decide
  have hdescent : baseEnd_1133829 < baseStart_1133829 := by decide
  rcases family_descends (prefixWord ++ tailWord_1133829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1133836 : List Nat := [2, 2, 1, 2, 2, 3, 1, 3, 2, 5]
def baseStart_1133836 : Nat := 118140960795 + 1133836 * 2 ^ 59
def prefixEnd_1133836 : Nat := 4983230072969 + 3 ^ 40 * 1133836 * 2
def baseEnd_1133836 : Nat := 194067617123777031711863

theorem tailTrace_1133836 : CollatzResearch.WordTrace tailWord_1133836 prefixEnd_1133836 194067617123777031711863 := by
  unfold tailWord_1133836
  simp only [CollatzResearch.WordTrace]
  refine ⟨20677198160156645308570681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27569597546875527078094241 20677198160156645308570681)
  ·
    refine ⟨15507898620117483981428011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20677198160156645308570681 15507898620117483981428011)
    ·
      refine ⟨23261847930176225972142017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15507898620117483981428011 23261847930176225972142017)
      ·
        refine ⟨17446385947632169479106513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23261847930176225972142017 17446385947632169479106513)
        ·
          refine ⟨13084789460724127109329885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17446385947632169479106513 13084789460724127109329885)
          ·
            refine ⟨4906796047771547665998707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13084789460724127109329885 4906796047771547665998707)
            ·
              refine ⟨7360194071657321498998061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4906796047771547665998707 7360194071657321498998061)
              ·
                refine ⟨2760072776871495562124273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7360194071657321498998061 2760072776871495562124273)
                ·
                  refine ⟨2070054582653621671593205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2760072776871495562124273 2070054582653621671593205)
                  ·
                    refine ⟨194067617123777031711863, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2070054582653621671593205 194067617123777031711863)
                    ·
                      rfl

theorem cell23_1133836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 3, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 3, 1, 3, 2, 5].length) (baseStart_1133836 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1133836 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1133836 prefixEnd_1133836 := by exact prefixLift 1133836
  have htrace : WordTrace (prefixWord ++ tailWord_1133836) baseStart_1133836 baseEnd_1133836 := by
    simpa [prefixWord, tailWord_1133836, baseEnd_1133836] using wordTrace_append hprefix tailTrace_1133836
  have hstable : (prefixWord ++ tailWord_1133836).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1133836).length < 2 ^ (prefixWord ++ tailWord_1133836).sum := by decide
  have hdescent : baseEnd_1133836 < baseStart_1133836 := by decide
  rcases family_descends (prefixWord ++ tailWord_1133836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1133853 : List Nat := [1, 4, 2, 3, 1, 1, 2, 2, 2, 5]
def baseStart_1133853 : Nat := 118140960795 + 1133853 * 2 ^ 59
def prefixEnd_1133853 : Nat := 4983230072969 + 3 ^ 40 * 1133853 * 2
def baseEnd_1133853 : Nat := 194070526847485842874337

theorem tailTrace_1133853 : CollatzResearch.WordTrace tailWord_1133853 prefixEnd_1133853 194070526847485842874337 := by
  unfold tailWord_1133853
  simp only [CollatzResearch.WordTrace]
  refine ⟨41355016361251702520510213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27570010907501135013673475 41355016361251702520510213)
  ·
    refine ⟨7754065567734694222595665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 41355016361251702520510213 7754065567734694222595665)
    ·
      refine ⟨5815549175801020666946749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7754065567734694222595665 5815549175801020666946749)
      ·
        refine ⟨2180830940925382750105031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5815549175801020666946749 2180830940925382750105031)
        ·
          refine ⟨3271246411388074125157547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2180830940925382750105031 3271246411388074125157547)
          ·
            refine ⟨4906869617082111187736321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3271246411388074125157547 4906869617082111187736321)
            ·
              refine ⟨3680152212811583390802241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4906869617082111187736321 3680152212811583390802241)
              ·
                refine ⟨2760114159608687543101681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3680152212811583390802241 2760114159608687543101681)
                ·
                  refine ⟨2070085619706515657326261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2760114159608687543101681 2070085619706515657326261)
                  ·
                    refine ⟨194070526847485842874337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2070085619706515657326261 194070526847485842874337)
                    ·
                      rfl

theorem cell23_1133853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 1, 2, 2, 2, 5].length) (baseStart_1133853 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1133853 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1133853 prefixEnd_1133853 := by exact prefixLift 1133853
  have htrace : WordTrace (prefixWord ++ tailWord_1133853) baseStart_1133853 baseEnd_1133853 := by
    simpa [prefixWord, tailWord_1133853, baseEnd_1133853] using wordTrace_append hprefix tailTrace_1133853
  have hstable : (prefixWord ++ tailWord_1133853).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1133853).length < 2 ^ (prefixWord ++ tailWord_1133853).sum := by decide
  have hdescent : baseEnd_1133853 < baseStart_1133853 := by decide
  rcases family_descends (prefixWord ++ tailWord_1133853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1133873 : List Nat := [1, 2, 2, 3, 3, 1, 1, 1, 1, 6, 2]
def baseStart_1133873 : Nat := 118140960795 + 1133873 * 2 ^ 59
def prefixEnd_1133873 : Nat := 4983230072969 + 3 ^ 40 * 1133873 * 2
def baseEnd_1133873 : Nat := 582221850155547450372919

theorem tailTrace_1133873 : CollatzResearch.WordTrace tailWord_1133873 prefixEnd_1133873 582221850155547450372919 := by
  unfold tailWord_1133873
  simp only [CollatzResearch.WordTrace]
  refine ⟨41355745821179245936238273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27570497214119497290825515 41355745821179245936238273)
  ·
    refine ⟨31016809365884434452178705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41355745821179245936238273 31016809365884434452178705)
    ·
      refine ⟨23262607024413325839134029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31016809365884434452178705 23262607024413325839134029)
      ·
        refine ⟨8723477634154997189675261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23262607024413325839134029 8723477634154997189675261)
        ·
          refine ⟨3271304112808123946128223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8723477634154997189675261 3271304112808123946128223)
          ·
            refine ⟨4906956169212185919192335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3271304112808123946128223 4906956169212185919192335)
            ·
              refine ⟨7360434253818278878788503, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4906956169212185919192335 7360434253818278878788503)
              ·
                refine ⟨11040651380727418318182755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7360434253818278878788503 11040651380727418318182755)
                ·
                  refine ⟨16560977071091127477274133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11040651380727418318182755 16560977071091127477274133)
                  ·
                    refine ⟨776295800207396600497225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16560977071091127477274133 776295800207396600497225)
                    ·
                      refine ⟨582221850155547450372919, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 776295800207396600497225 582221850155547450372919)
                      ·
                        rfl

theorem cell23_1133873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 1, 1, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 1, 1, 1, 1, 6, 2].length) (baseStart_1133873 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1133873 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1133873 prefixEnd_1133873 := by exact prefixLift 1133873
  have htrace : WordTrace (prefixWord ++ tailWord_1133873) baseStart_1133873 baseEnd_1133873 := by
    simpa [prefixWord, tailWord_1133873, baseEnd_1133873] using wordTrace_append hprefix tailTrace_1133873
  have hstable : (prefixWord ++ tailWord_1133873).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1133873).length < 2 ^ (prefixWord ++ tailWord_1133873).sum := by decide
  have hdescent : baseEnd_1133873 < baseStart_1133873 := by decide
  rcases family_descends (prefixWord ++ tailWord_1133873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1133879 : List Nat := [1, 1, 3, 1, 2, 1, 1, 1, 12]
def baseStart_1133879 : Nat := 118140960795 + 1133879 * 2 ^ 59
def prefixEnd_1133879 : Nat := 4983230072969 + 3 ^ 40 * 1133879 * 2
def baseEnd_1133879 : Nat := 64691659004386047433099

theorem tailTrace_1133879 : CollatzResearch.WordTrace tailWord_1133879 prefixEnd_1133879 64691659004386047433099 := by
  unfold tailWord_1133879
  simp only [CollatzResearch.WordTrace]
  refine ⟨41355964659157508960956691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27570643106105005973971127 41355964659157508960956691)
  ·
    refine ⟨62033946988736263441435037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41355964659157508960956691 62033946988736263441435037)
    ·
      refine ⟨23262730120776098790538139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 62033946988736263441435037 23262730120776098790538139)
      ·
        refine ⟨34894095181164148185807209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23262730120776098790538139 34894095181164148185807209)
        ·
          refine ⟨26170571385873111139355407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34894095181164148185807209 26170571385873111139355407)
          ·
            refine ⟨39255857078809666709033111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26170571385873111139355407 39255857078809666709033111)
            ·
              refine ⟨58883785618214500063549667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39255857078809666709033111 58883785618214500063549667)
              ·
                refine ⟨88325678427321750095324501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 58883785618214500063549667 88325678427321750095324501)
                ·
                  refine ⟨64691659004386047433099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 12 88325678427321750095324501 64691659004386047433099)
                  ·
                    rfl

theorem cell23_1133879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 12].length) (baseStart_1133879 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1133879 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1133879 prefixEnd_1133879 := by exact prefixLift 1133879
  have htrace : WordTrace (prefixWord ++ tailWord_1133879) baseStart_1133879 baseEnd_1133879 := by
    simpa [prefixWord, tailWord_1133879, baseEnd_1133879] using wordTrace_append hprefix tailTrace_1133879
  have hstable : (prefixWord ++ tailWord_1133879).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1133879).length < 2 ^ (prefixWord ++ tailWord_1133879).sum := by decide
  have hdescent : baseEnd_1133879 < baseStart_1133879 := by decide
  rcases family_descends (prefixWord ++ tailWord_1133879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1133900 : List Nat := [2, 2, 1, 3, 2, 2, 1, 5, 1, 4]
def baseStart_1133900 : Nat := 118140960795 + 1133900 * 2 ^ 59
def prefixEnd_1133900 : Nat := 4983230072969 + 3 ^ 40 * 1133900 * 2
def baseEnd_1133900 : Nat := 194078571377739614911765

theorem tailTrace_1133900 : CollatzResearch.WordTrace tailWord_1133900 prefixEnd_1133900 194078571377739614911765 := by
  unfold tailWord_1133900
  simp only [CollatzResearch.WordTrace]
  refine ⟨20678365296040714773735577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27571153728054286364980769 20678365296040714773735577)
  ·
    refine ⟨15508773972030536080301683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20678365296040714773735577 15508773972030536080301683)
    ·
      refine ⟨23263160958045804120452525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15508773972030536080301683 23263160958045804120452525)
      ·
        refine ⟨8723685359267176545169697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23263160958045804120452525 8723685359267176545169697)
        ·
          refine ⟨6542764019450382408877273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8723685359267176545169697 6542764019450382408877273)
          ·
            refine ⟨4907073014587786806657955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6542764019450382408877273 4907073014587786806657955)
            ·
              refine ⟨7360609521881680209986933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4907073014587786806657955 7360609521881680209986933)
              ·
                refine ⟨690057142676407519686275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 7360609521881680209986933 690057142676407519686275)
                ·
                  refine ⟨1035085714014611279529413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 690057142676407519686275 1035085714014611279529413)
                  ·
                    refine ⟨194078571377739614911765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1035085714014611279529413 194078571377739614911765)
                    ·
                      rfl

theorem cell23_1133900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 2, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 2, 1, 5, 1, 4].length) (baseStart_1133900 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1133900 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1133900 prefixEnd_1133900 := by exact prefixLift 1133900
  have htrace : WordTrace (prefixWord ++ tailWord_1133900) baseStart_1133900 baseEnd_1133900 := by
    simpa [prefixWord, tailWord_1133900, baseEnd_1133900] using wordTrace_append hprefix tailTrace_1133900
  have hstable : (prefixWord ++ tailWord_1133900).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1133900).length < 2 ^ (prefixWord ++ tailWord_1133900).sum := by decide
  have hdescent : baseEnd_1133900 < baseStart_1133900 := by decide
  rcases family_descends (prefixWord ++ tailWord_1133900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1133943 : List Nat := [1, 1, 3, 1, 1, 2, 6, 2, 1, 5]
def baseStart_1133943 : Nat := 118140960795 + 1133943 * 2 ^ 59
def prefixEnd_1133943 : Nat := 4983230072969 + 3 ^ 40 * 1133943 * 2
def baseEnd_1133943 : Nat := 194085931267120725499199

theorem tailTrace_1133943 : CollatzResearch.WordTrace tailWord_1133943 prefixEnd_1133943 194085931267120725499199 := by
  unfold tailWord_1133943
  simp only [CollatzResearch.WordTrace]
  refine ⟨41358298930925647891286483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27572199287283765260857655 41358298930925647891286483)
  ·
    refine ⟨62037448396388471836929725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41358298930925647891286483 62037448396388471836929725)
    ·
      refine ⟨23264043148645676938848647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 62037448396388471836929725 23264043148645676938848647)
      ·
        refine ⟨34896064722968515408272971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23264043148645676938848647 34896064722968515408272971)
        ·
          refine ⟨52344097084452773112409457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34896064722968515408272971 52344097084452773112409457)
          ·
            refine ⟨39258072813339579834307093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 52344097084452773112409457 39258072813339579834307093)
            ·
              refine ⟨1840222163125292804733145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 39258072813339579834307093 1840222163125292804733145)
              ·
                refine ⟨1380166622343969603549859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1840222163125292804733145 1380166622343969603549859)
                ·
                  refine ⟨2070249933515954405324789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1380166622343969603549859 2070249933515954405324789)
                  ·
                    refine ⟨194085931267120725499199, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2070249933515954405324789 194085931267120725499199)
                    ·
                      rfl

theorem cell23_1133943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 6, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 6, 2, 1, 5].length) (baseStart_1133943 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1133943 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1133943 prefixEnd_1133943 := by exact prefixLift 1133943
  have htrace : WordTrace (prefixWord ++ tailWord_1133943) baseStart_1133943 baseEnd_1133943 := by
    simpa [prefixWord, tailWord_1133943, baseEnd_1133943] using wordTrace_append hprefix tailTrace_1133943
  have hstable : (prefixWord ++ tailWord_1133943).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1133943).length < 2 ^ (prefixWord ++ tailWord_1133943).sum := by decide
  have hdescent : baseEnd_1133943 < baseStart_1133943 := by decide
  rcases family_descends (prefixWord ++ tailWord_1133943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1133957 : List Nat := [1, 3, 1, 1, 3, 1, 5, 3, 1, 1, 3]
def baseStart_1133957 : Nat := 118140960795 + 1133957 * 2 ^ 59
def prefixEnd_1133957 : Nat := 4983230072969 + 3 ^ 40 * 1133957 * 2
def baseEnd_1133957 : Nat := 582264982530525121722533

theorem tailTrace_1133957 : CollatzResearch.WordTrace tailWord_1133957 prefixEnd_1133957 582264982530525121722533 := by
  unfold tailWord_1133957
  simp only [CollatzResearch.WordTrace]
  refine ⟨41358809552874928282296125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27572539701916618854864083 41358809552874928282296125)
  ·
    refine ⟨15509553582328098105861047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 41358809552874928282296125 15509553582328098105861047)
    ·
      refine ⟨23264330373492147158791571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15509553582328098105861047 23264330373492147158791571)
      ·
        refine ⟨34896495560238220738187357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23264330373492147158791571 34896495560238220738187357)
        ·
          refine ⟨13086185835089332776820259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 34896495560238220738187357 13086185835089332776820259)
          ·
            refine ⟨19629278752633999165230389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13086185835089332776820259 19629278752633999165230389)
            ·
              refine ⟨1840244883059437421740349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 19629278752633999165230389 1840244883059437421740349)
              ·
                refine ⟨690091831147289033152631, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1840244883059437421740349 690091831147289033152631)
                ·
                  refine ⟨1035137746720933549728947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 690091831147289033152631 1035137746720933549728947)
                  ·
                    refine ⟨1552706620081400324593421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1035137746720933549728947 1552706620081400324593421)
                    ·
                      refine ⟨582264982530525121722533, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1552706620081400324593421 582264982530525121722533)
                      ·
                        rfl

theorem cell23_1133957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 5, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 5, 3, 1, 1, 3].length) (baseStart_1133957 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1133957 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1133957 prefixEnd_1133957 := by exact prefixLift 1133957
  have htrace : WordTrace (prefixWord ++ tailWord_1133957) baseStart_1133957 baseEnd_1133957 := by
    simpa [prefixWord, tailWord_1133957, baseEnd_1133957] using wordTrace_append hprefix tailTrace_1133957
  have hstable : (prefixWord ++ tailWord_1133957).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1133957).length < 2 ^ (prefixWord ++ tailWord_1133957).sum := by decide
  have hdescent : baseEnd_1133957 < baseStart_1133957 := by decide
  rcases family_descends (prefixWord ++ tailWord_1133957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1133963 : List Nat := [1, 1, 1, 1, 4, 3, 1, 5, 1, 1, 4]
def baseStart_1133963 : Nat := 118140960795 + 1133963 * 2 ^ 59
def prefixEnd_1133963 : Nat := 4983230072969 + 3 ^ 40 * 1133963 * 2
def baseEnd_1133963 : Nat := 582268063414452098247505

theorem tailTrace_1133963 : CollatzResearch.WordTrace tailWord_1133963 prefixEnd_1133963 582268063414452098247505 := by
  unfold tailWord_1133963
  simp only [CollatzResearch.WordTrace]
  refine ⟨41359028390853191307014543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27572685593902127538009695 41359028390853191307014543)
  ·
    refine ⟨62038542586279786960521815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41359028390853191307014543 62038542586279786960521815)
    ·
      refine ⟨93057813879419680440782723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62038542586279786960521815 93057813879419680440782723)
      ·
        refine ⟨139586720819129520661174085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 93057813879419680440782723 139586720819129520661174085)
        ·
          refine ⟨26172510153586785123970141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 139586720819129520661174085 26172510153586785123970141)
          ·
            refine ⟨9814691307595044421488803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 26172510153586785123970141 9814691307595044421488803)
            ·
              refine ⟨14722036961392566632233205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9814691307595044421488803 14722036961392566632233205)
              ·
                refine ⟨1380190965130553121771863, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 14722036961392566632233205 1380190965130553121771863)
                ·
                  refine ⟨2070286447695829682657795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1380190965130553121771863 2070286447695829682657795)
                  ·
                    refine ⟨3105429671543744523986693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2070286447695829682657795 3105429671543744523986693)
                    ·
                      refine ⟨582268063414452098247505, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3105429671543744523986693 582268063414452098247505)
                      ·
                        rfl

theorem cell23_1133963_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 1, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 1, 5, 1, 1, 4].length) (baseStart_1133963 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1133963 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1133963 prefixEnd_1133963 := by exact prefixLift 1133963
  have htrace : WordTrace (prefixWord ++ tailWord_1133963) baseStart_1133963 baseEnd_1133963 := by
    simpa [prefixWord, tailWord_1133963, baseEnd_1133963] using wordTrace_append hprefix tailTrace_1133963
  have hstable : (prefixWord ++ tailWord_1133963).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1133963).length < 2 ^ (prefixWord ++ tailWord_1133963).sum := by decide
  have hdescent : baseEnd_1133963 < baseStart_1133963 := by decide
  rcases family_descends (prefixWord ++ tailWord_1133963) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1133973 : List Nat := [1, 3, 2, 1, 1, 2, 4, 1, 4, 4]
def baseStart_1133973 : Nat := 118140960795 + 1133973 * 2 ^ 59
def prefixEnd_1133973 : Nat := 4983230072969 + 3 ^ 40 * 1133973 * 2
def baseEnd_1133973 : Nat := 194091066073665686374153

theorem tailTrace_1133973 : CollatzResearch.WordTrace tailWord_1133973 prefixEnd_1133973 194091066073665686374153 := by
  unfold tailWord_1133973
  simp only [CollatzResearch.WordTrace]
  refine ⟨41359393120816963014878573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27572928747211308676585715 41359393120816963014878573)
  ·
    refine ⟨15509772420306361130579465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 41359393120816963014878573 15509772420306361130579465)
    ·
      refine ⟨11632329315229770847934599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15509772420306361130579465 11632329315229770847934599)
      ·
        refine ⟨17448493972844656271901899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11632329315229770847934599 17448493972844656271901899)
        ·
          refine ⟨26172740959266984407852849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17448493972844656271901899 26172740959266984407852849)
          ·
            refine ⟨19629555719450238305889637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26172740959266984407852849 19629555719450238305889637)
            ·
              refine ⟨3680541697396919682354307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 19629555719450238305889637 3680541697396919682354307)
              ·
                refine ⟨5520812546095379523531461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3680541697396919682354307 5520812546095379523531461)
                ·
                  refine ⟨1035152352392883660662149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5520812546095379523531461 1035152352392883660662149)
                  ·
                    refine ⟨194091066073665686374153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1035152352392883660662149 194091066073665686374153)
                    ·
                      rfl

theorem cell23_1133973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 4, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 4, 1, 4, 4].length) (baseStart_1133973 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1133973 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1133973 prefixEnd_1133973 := by exact prefixLift 1133973
  have htrace : WordTrace (prefixWord ++ tailWord_1133973) baseStart_1133973 baseEnd_1133973 := by
    simpa [prefixWord, tailWord_1133973, baseEnd_1133973] using wordTrace_append hprefix tailTrace_1133973
  have hstable : (prefixWord ++ tailWord_1133973).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1133973).length < 2 ^ (prefixWord ++ tailWord_1133973).sum := by decide
  have hdescent : baseEnd_1133973 < baseStart_1133973 := by decide
  rcases family_descends (prefixWord ++ tailWord_1133973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1133983 : List Nat := [1, 1, 2, 5, 1, 2, 2, 2, 1, 1, 5]
def baseStart_1133983 : Nat := 118140960795 + 1133983 * 2 ^ 59
def prefixEnd_1133983 : Nat := 4983230072969 + 3 ^ 40 * 1133983 * 2
def baseEnd_1133983 : Nat := 582278333027542019997413

theorem tailTrace_1133983 : CollatzResearch.WordTrace tailWord_1133983 prefixEnd_1133983 582278333027542019997413 := by
  unfold tailWord_1133983
  simp only [CollatzResearch.WordTrace]
  refine ⟨41359757850780734722742603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27573171900520489815161735 41359757850780734722742603)
  ·
    refine ⟨62039636776171102084113905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41359757850780734722742603 62039636776171102084113905)
    ·
      refine ⟨46529727582128326563085429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 62039636776171102084113905 46529727582128326563085429)
      ·
        refine ⟨4362161960824530615289259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 46529727582128326563085429 4362161960824530615289259)
        ·
          refine ⟨6543242941236795922933889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4362161960824530615289259 6543242941236795922933889)
          ·
            refine ⟨4907432205927596942200417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6543242941236795922933889 4907432205927596942200417)
            ·
              refine ⟨3680574154445697706650313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4907432205927596942200417 3680574154445697706650313)
              ·
                refine ⟨2760430615834273279987735, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3680574154445697706650313 2760430615834273279987735)
                ·
                  refine ⟨4140645923751409919981603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2760430615834273279987735 4140645923751409919981603)
                  ·
                    refine ⟨6210968885627114879972405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4140645923751409919981603 6210968885627114879972405)
                    ·
                      refine ⟨582278333027542019997413, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 6210968885627114879972405 582278333027542019997413)
                      ·
                        rfl

theorem cell23_1133983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 2, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 2, 2, 2, 1, 1, 5].length) (baseStart_1133983 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1133983 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1133983 prefixEnd_1133983 := by exact prefixLift 1133983
  have htrace : WordTrace (prefixWord ++ tailWord_1133983) baseStart_1133983 baseEnd_1133983 := by
    simpa [prefixWord, tailWord_1133983, baseEnd_1133983] using wordTrace_append hprefix tailTrace_1133983
  have hstable : (prefixWord ++ tailWord_1133983).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1133983).length < 2 ^ (prefixWord ++ tailWord_1133983).sum := by decide
  have hdescent : baseEnd_1133983 < baseStart_1133983 := by decide
  rcases family_descends (prefixWord ++ tailWord_1133983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1133997 : List Nat := [1, 5, 2, 2, 1, 1, 3, 2, 1, 1, 4]
def baseStart_1133997 : Nat := 118140960795 + 1133997 * 2 ^ 59
def prefixEnd_1133997 : Nat := 4983230072969 + 3 ^ 40 * 1133997 * 2
def baseEnd_1133997 : Nat := 582285521756704965222349

theorem tailTrace_1133997 : CollatzResearch.WordTrace tailWord_1133997 prefixEnd_1133997 582285521756704965222349 := by
  unfold tailWord_1133997
  simp only [CollatzResearch.WordTrace]
  refine ⟨41360268472730015113752245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27573512315153343409168163 41360268472730015113752245)
  ·
    refine ⟨3877525169318438916914273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 41360268472730015113752245 3877525169318438916914273)
    ·
      refine ⟨2908143876988829187685705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3877525169318438916914273 2908143876988829187685705)
      ·
        refine ⟨2181107907741621890764279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2908143876988829187685705 2181107907741621890764279)
        ·
          refine ⟨3271661861612432836146419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2181107907741621890764279 3271661861612432836146419)
          ·
            refine ⟨4907492792418649254219629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3271661861612432836146419 4907492792418649254219629)
            ·
              refine ⟨1840309797156993470332361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4907492792418649254219629 1840309797156993470332361)
              ·
                refine ⟨1380232347867745102749271, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1840309797156993470332361 1380232347867745102749271)
                ·
                  refine ⟨2070348521801617654123907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1380232347867745102749271 2070348521801617654123907)
                  ·
                    refine ⟨3105522782702426481185861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2070348521801617654123907 3105522782702426481185861)
                    ·
                      refine ⟨582285521756704965222349, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3105522782702426481185861 582285521756704965222349)
                      ·
                        rfl

theorem cell23_1133997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 1, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 1, 3, 2, 1, 1, 4].length) (baseStart_1133997 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1133997 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1133997 prefixEnd_1133997 := by exact prefixLift 1133997
  have htrace : WordTrace (prefixWord ++ tailWord_1133997) baseStart_1133997 baseEnd_1133997 := by
    simpa [prefixWord, tailWord_1133997, baseEnd_1133997] using wordTrace_append hprefix tailTrace_1133997
  have hstable : (prefixWord ++ tailWord_1133997).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1133997).length < 2 ^ (prefixWord ++ tailWord_1133997).sum := by decide
  have hdescent : baseEnd_1133997 < baseStart_1133997 := by decide
  rcases family_descends (prefixWord ++ tailWord_1133997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1134014 : List Nat := [4, 2, 1, 1, 1, 1, 1, 7, 1, 2, 2]
def baseStart_1134014 : Nat := 118140960795 + 1134014 * 2 ^ 59
def prefixEnd_1134014 : Nat := 4983230072969 + 3 ^ 40 * 1134014 * 2
def baseEnd_1134014 : Nat := 582294250927831398709771

theorem tailTrace_1134014 : CollatzResearch.WordTrace tailWord_1134014 prefixEnd_1134014 582294250927831398709771 := by
  unfold tailWord_1134014
  simp only [CollatzResearch.WordTrace]
  refine ⟨5170111064208553377140137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 27573925675778951344747397 5170111064208553377140137)
  ·
    refine ⟨3877583298156415032855103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5170111064208553377140137 3877583298156415032855103)
    ·
      refine ⟨5816374947234622549282655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3877583298156415032855103 5816374947234622549282655)
      ·
        refine ⟨8724562420851933823923983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5816374947234622549282655 8724562420851933823923983)
        ·
          refine ⟨13086843631277900735885975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8724562420851933823923983 13086843631277900735885975)
          ·
            refine ⟨19630265446916851103828963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13086843631277900735885975 19630265446916851103828963)
            ·
              refine ⟨29445398170375276655743445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19630265446916851103828963 29445398170375276655743445)
              ·
                refine ⟨690126519618170546618987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 29445398170375276655743445 690126519618170546618987)
                ·
                  refine ⟨1035189779427255819928481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 690126519618170546618987 1035189779427255819928481)
                  ·
                    refine ⟨776392334570441864946361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1035189779427255819928481 776392334570441864946361)
                    ·
                      refine ⟨582294250927831398709771, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 776392334570441864946361 582294250927831398709771)
                      ·
                        rfl

theorem cell23_1134014_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 1, 7, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 1, 7, 1, 2, 2].length) (baseStart_1134014 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1134014 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1134014 prefixEnd_1134014 := by exact prefixLift 1134014
  have htrace : WordTrace (prefixWord ++ tailWord_1134014) baseStart_1134014 baseEnd_1134014 := by
    simpa [prefixWord, tailWord_1134014, baseEnd_1134014] using wordTrace_append hprefix tailTrace_1134014
  have hstable : (prefixWord ++ tailWord_1134014).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1134014).length < 2 ^ (prefixWord ++ tailWord_1134014).sum := by decide
  have hdescent : baseEnd_1134014 < baseStart_1134014 := by decide
  rcases family_descends (prefixWord ++ tailWord_1134014) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1134030 : List Nat := [4, 1, 1, 1, 2, 1, 2, 3, 4, 1, 3]
def baseStart_1134030 : Nat := 118140960795 + 1134030 * 2 ^ 59
def prefixEnd_1134030 : Nat := 4983230072969 + 3 ^ 40 * 1134030 * 2
def baseEnd_1134030 : Nat := 582302466618303336109697

theorem tailTrace_1134030 : CollatzResearch.WordTrace tailWord_1134030 prefixEnd_1134030 582302466618303336109697 := by
  unfold tailWord_1134030
  simp only [CollatzResearch.WordTrace]
  refine ⟨5170184010201307718712943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 27574314721073641166469029 5170184010201307718712943)
  ·
    refine ⟨7755276015301961578069415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5170184010201307718712943 7755276015301961578069415)
    ·
      refine ⟨11632914022952942367104123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7755276015301961578069415 11632914022952942367104123)
      ·
        refine ⟨17449371034429413550656185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11632914022952942367104123 17449371034429413550656185)
        ·
          refine ⟨13087028275822060162992139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17449371034429413550656185 13087028275822060162992139)
          ·
            refine ⟨19630542413733090244488209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13087028275822060162992139 19630542413733090244488209)
            ·
              refine ⟨14722906810299817683366157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19630542413733090244488209 14722906810299817683366157)
              ·
                refine ⟨5521090053862431631262309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14722906810299817683366157 5521090053862431631262309)
                ·
                  refine ⟨1035204385099205930861683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5521090053862431631262309 1035204385099205930861683)
                  ·
                    refine ⟨1552806577648808896292525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1035204385099205930861683 1552806577648808896292525)
                    ·
                      refine ⟨582302466618303336109697, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1552806577648808896292525 582302466618303336109697)
                      ·
                        rfl

theorem cell23_1134030_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 2, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 2, 3, 4, 1, 3].length) (baseStart_1134030 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1134030 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1134030 prefixEnd_1134030 := by exact prefixLift 1134030
  have htrace : WordTrace (prefixWord ++ tailWord_1134030) baseStart_1134030 baseEnd_1134030 := by
    simpa [prefixWord, tailWord_1134030, baseEnd_1134030] using wordTrace_append hprefix tailTrace_1134030
  have hstable : (prefixWord ++ tailWord_1134030).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1134030).length < 2 ^ (prefixWord ++ tailWord_1134030).sum := by decide
  have hdescent : baseEnd_1134030 < baseStart_1134030 := by decide
  rcases family_descends (prefixWord ++ tailWord_1134030) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1134040 : List Nat := [2, 1, 2, 2, 2, 1, 3, 2, 3, 3, 2]
def baseStart_1134040 : Nat := 118140960795 + 1134040 * 2 ^ 59
def prefixEnd_1134040 : Nat := 4983230072969 + 3 ^ 40 * 1134040 * 2
def baseEnd_1134040 : Nat := 582307601424848296984651

theorem tailTrace_1134040 : CollatzResearch.WordTrace tailWord_1134040 prefixEnd_1134040 582307601424848296984651 := by
  unfold tailWord_1134040
  simp only [CollatzResearch.WordTrace]
  refine ⟨20680918405787116728783787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27574557874382822305045049 20680918405787116728783787)
  ·
    refine ⟨31021377608680675093175681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20680918405787116728783787 31021377608680675093175681)
    ·
      refine ⟨23266033206510506319881761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31021377608680675093175681 23266033206510506319881761)
      ·
        refine ⟨17449524904882879739911321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23266033206510506319881761 17449524904882879739911321)
        ·
          refine ⟨13087143678662159804933491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17449524904882879739911321 13087143678662159804933491)
          ·
            refine ⟨19630715517993239707400237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13087143678662159804933491 19630715517993239707400237)
            ·
              refine ⟨7361518319247464890275089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19630715517993239707400237 7361518319247464890275089)
              ·
                refine ⟨5521138739435598667706317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7361518319247464890275089 5521138739435598667706317)
                ·
                  refine ⟨2070427027288349500389869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5521138739435598667706317 2070427027288349500389869)
                  ·
                    refine ⟨776410135233131062646201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2070427027288349500389869 776410135233131062646201)
                    ·
                      refine ⟨582307601424848296984651, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 776410135233131062646201 582307601424848296984651)
                      ·
                        rfl

theorem cell23_1134040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 3, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 3, 2, 3, 3, 2].length) (baseStart_1134040 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1134040 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1134040 prefixEnd_1134040 := by exact prefixLift 1134040
  have htrace : WordTrace (prefixWord ++ tailWord_1134040) baseStart_1134040 baseEnd_1134040 := by
    simpa [prefixWord, tailWord_1134040, baseEnd_1134040] using wordTrace_append hprefix tailTrace_1134040
  have hstable : (prefixWord ++ tailWord_1134040).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1134040).length < 2 ^ (prefixWord ++ tailWord_1134040).sum := by decide
  have hdescent : baseEnd_1134040 < baseStart_1134040 := by decide
  rcases family_descends (prefixWord ++ tailWord_1134040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1134081 : List Nat := [1, 2, 4, 1, 5, 1, 1, 2, 2, 1, 3]
def baseStart_1134081 : Nat := 118140960795 + 1134081 * 2 ^ 59
def prefixEnd_1134081 : Nat := 4983230072969 + 3 ^ 40 * 1134081 * 2
def baseEnd_1134081 : Nat := 582328654131682636571963

theorem tailTrace_1134081 : CollatzResearch.WordTrace tailWord_1134081 prefixEnd_1134081 582328654131682636571963 := by
  unfold tailWord_1134081
  simp only [CollatzResearch.WordTrace]
  refine ⟨41363332204425697459810097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27575554802950464973206731 41363332204425697459810097)
  ·
    refine ⟨31022499153319273094857573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41363332204425697459810097 31022499153319273094857573)
    ·
      refine ⟨5816718591247363705285795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 31022499153319273094857573 5816718591247363705285795)
      ·
        refine ⟨8725077886871045557928693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5816718591247363705285795 8725077886871045557928693)
        ·
          refine ⟨817976051894160521055815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 8725077886871045557928693 817976051894160521055815)
          ·
            refine ⟨1226964077841240781583723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 817976051894160521055815 1226964077841240781583723)
            ·
              refine ⟨1840446116761861172375585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1226964077841240781583723 1840446116761861172375585)
              ·
                refine ⟨1380334587571395879281689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1840446116761861172375585 1380334587571395879281689)
                ·
                  refine ⟨1035250940678546909461267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1380334587571395879281689 1035250940678546909461267)
                  ·
                    refine ⟨1552876411017820364191901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1035250940678546909461267 1552876411017820364191901)
                    ·
                      refine ⟨582328654131682636571963, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1552876411017820364191901 582328654131682636571963)
                      ·
                        rfl

theorem cell23_1134081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 5, 1, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 5, 1, 1, 2, 2, 1, 3].length) (baseStart_1134081 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1134081 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1134081 prefixEnd_1134081 := by exact prefixLift 1134081
  have htrace : WordTrace (prefixWord ++ tailWord_1134081) baseStart_1134081 baseEnd_1134081 := by
    simpa [prefixWord, tailWord_1134081, baseEnd_1134081] using wordTrace_append hprefix tailTrace_1134081
  have hstable : (prefixWord ++ tailWord_1134081).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1134081).length < 2 ^ (prefixWord ++ tailWord_1134081).sum := by decide
  have hdescent : baseEnd_1134081 < baseStart_1134081 := by decide
  rcases family_descends (prefixWord ++ tailWord_1134081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1134104 : List Nat := [2, 1, 2, 3, 4, 2, 1, 1, 1, 4, 2]
def baseStart_1134104 : Nat := 118140960795 + 1134104 * 2 ^ 59
def prefixEnd_1134104 : Nat := 4983230072969 + 3 ^ 40 * 1134104 * 2
def baseEnd_1134104 : Nat := 582340464186736046584357

theorem tailTrace_1134104 : CollatzResearch.WordTrace tailWord_1134104 prefixEnd_1134104 582340464186736046584357 := by
  unfold tailWord_1134104
  simp only [CollatzResearch.WordTrace]
  refine ⟨20682085541671186193948683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27576114055561581591931577 20682085541671186193948683)
  ·
    refine ⟨31023128312506779290923025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20682085541671186193948683 31023128312506779290923025)
    ·
      refine ⟨23267346234380084468192269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31023128312506779290923025 23267346234380084468192269)
      ·
        refine ⟨8725254837892531675572101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23267346234380084468192269 8725254837892531675572101)
        ·
          refine ⟨1635985282104849689169769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8725254837892531675572101 1635985282104849689169769)
          ·
            refine ⟨1226988961578637266877327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1635985282104849689169769 1226988961578637266877327)
            ·
              refine ⟨1840483442367955900315991, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1226988961578637266877327 1840483442367955900315991)
              ·
                refine ⟨2760725163551933850473987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1840483442367955900315991 2760725163551933850473987)
                ·
                  refine ⟨4141087745327900775710981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2760725163551933850473987 4141087745327900775710981)
                  ·
                    refine ⟨776453952248981395445809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4141087745327900775710981 776453952248981395445809)
                    ·
                      refine ⟨582340464186736046584357, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 776453952248981395445809 582340464186736046584357)
                      ·
                        rfl

theorem cell23_1134104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 4, 2, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 4, 2, 1, 1, 1, 4, 2].length) (baseStart_1134104 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1134104 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1134104 prefixEnd_1134104 := by exact prefixLift 1134104
  have htrace : WordTrace (prefixWord ++ tailWord_1134104) baseStart_1134104 baseEnd_1134104 := by
    simpa [prefixWord, tailWord_1134104, baseEnd_1134104] using wordTrace_append hprefix tailTrace_1134104
  have hstable : (prefixWord ++ tailWord_1134104).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1134104).length < 2 ^ (prefixWord ++ tailWord_1134104).sum := by decide
  have hdescent : baseEnd_1134104 < baseStart_1134104 := by decide
  rcases family_descends (prefixWord ++ tailWord_1134104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1134130 : List Nat := [3, 2, 1, 1, 2, 1, 1, 2, 1, 7, 2]
def baseStart_1134130 : Nat := 118140960795 + 1134130 * 2 ^ 59
def prefixEnd_1134130 : Nat := 4983230072969 + 3 ^ 40 * 1134130 * 2
def baseEnd_1134130 : Nat := 582353814683752944859237

theorem tailTrace_1134130 : CollatzResearch.WordTrace tailWord_1134130 prefixEnd_1134130 582353814683752944859237 := by
  unfold tailWord_1134130
  simp only [CollatzResearch.WordTrace]
  refine ⟨10341279845312044707085961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 27576746254165452552229229 10341279845312044707085961)
  ·
    refine ⟨7755959883984033530314471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10341279845312044707085961 7755959883984033530314471)
    ·
      refine ⟨11633939825976050295471707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7755959883984033530314471 11633939825976050295471707)
      ·
        refine ⟨17450909738964075443207561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11633939825976050295471707 17450909738964075443207561)
        ·
          refine ⟨13088182304223056582405671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17450909738964075443207561 13088182304223056582405671)
          ·
            refine ⟨19632273456334584873608507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13088182304223056582405671 19632273456334584873608507)
            ·
              refine ⟨29448410184501877310412761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19632273456334584873608507 29448410184501877310412761)
              ·
                refine ⟨22086307638376407982809571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29448410184501877310412761 22086307638376407982809571)
                ·
                  refine ⟨33129461457564611974214357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22086307638376407982809571 33129461457564611974214357)
                  ·
                    refine ⟨776471752911670593145649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 33129461457564611974214357 776471752911670593145649)
                    ·
                      refine ⟨582353814683752944859237, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 776471752911670593145649 582353814683752944859237)
                      ·
                        rfl

theorem cell23_1134130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 1, 2, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 1, 2, 1, 7, 2].length) (baseStart_1134130 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1134130 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1134130 prefixEnd_1134130 := by exact prefixLift 1134130
  have htrace : WordTrace (prefixWord ++ tailWord_1134130) baseStart_1134130 baseEnd_1134130 := by
    simpa [prefixWord, tailWord_1134130, baseEnd_1134130] using wordTrace_append hprefix tailTrace_1134130
  have hstable : (prefixWord ++ tailWord_1134130).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1134130).length < 2 ^ (prefixWord ++ tailWord_1134130).sum := by decide
  have hdescent : baseEnd_1134130 < baseStart_1134130 := by decide
  rcases family_descends (prefixWord ++ tailWord_1134130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1134160 : List Nat := [2, 1, 1, 1, 1, 3, 4, 1, 1, 6, 2]
def baseStart_1134160 : Nat := 118140960795 + 1134160 * 2 ^ 59
def prefixEnd_1134160 : Nat := 4983230072969 + 3 ^ 40 * 1134160 * 2
def baseEnd_1134160 : Nat := 582369219103387827484099

theorem tailTrace_1134160 : CollatzResearch.WordTrace tailWord_1134160 prefixEnd_1134160 582369219103387827484099 := by
  unfold tailWord_1134160
  simp only [CollatzResearch.WordTrace]
  refine ⟨20683106785569746975967967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27577475714092995967957289 20683106785569746975967967)
  ·
    refine ⟨31024660178354620463951951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20683106785569746975967967 31024660178354620463951951)
    ·
      refine ⟨46536990267531930695927927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31024660178354620463951951 46536990267531930695927927)
      ·
        refine ⟨69805485401297896043891891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46536990267531930695927927 69805485401297896043891891)
        ·
          refine ⟨104708228101946844065837837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 69805485401297896043891891 104708228101946844065837837)
          ·
            refine ⟨39265585538230066524689189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 104708228101946844065837837 39265585538230066524689189)
            ·
              refine ⟨7362297288418137473379223, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 39265585538230066524689189 7362297288418137473379223)
              ·
                refine ⟨11043445932627206210068835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7362297288418137473379223 11043445932627206210068835)
                ·
                  refine ⟨16565168898940809315103253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11043445932627206210068835 16565168898940809315103253)
                  ·
                    refine ⟨776492292137850436645465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16565168898940809315103253 776492292137850436645465)
                    ·
                      refine ⟨582369219103387827484099, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 776492292137850436645465 582369219103387827484099)
                      ·
                        rfl

theorem cell23_1134160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 4, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 4, 1, 1, 6, 2].length) (baseStart_1134160 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1134160 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1134160 prefixEnd_1134160 := by exact prefixLift 1134160
  have htrace : WordTrace (prefixWord ++ tailWord_1134160) baseStart_1134160 baseEnd_1134160 := by
    simpa [prefixWord, tailWord_1134160, baseEnd_1134160] using wordTrace_append hprefix tailTrace_1134160
  have hstable : (prefixWord ++ tailWord_1134160).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1134160).length < 2 ^ (prefixWord ++ tailWord_1134160).sum := by decide
  have hdescent : baseEnd_1134160 < baseStart_1134160 := by decide
  rcases family_descends (prefixWord ++ tailWord_1134160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1134170 : List Nat := [3, 1, 1, 2, 1, 1, 1, 6, 3, 4]
def baseStart_1134170 : Nat := 118140960795 + 1134170 * 2 ^ 59
def prefixEnd_1134170 : Nat := 4983230072969 + 3 ^ 40 * 1134170 * 2
def baseEnd_1134170 : Nat := 194124784636644262786351

theorem tailTrace_1134170 : CollatzResearch.WordTrace tailWord_1134170 prefixEnd_1134170 194124784636644262786351 := by
  unfold tailWord_1134170
  simp only [CollatzResearch.WordTrace]
  refine ⟨10341644575275816414949991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 27577718867402177106533309 10341644575275816414949991)
  ·
    refine ⟨15512466862913724622424987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10341644575275816414949991 15512466862913724622424987)
    ·
      refine ⟨23268700294370586933637481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15512466862913724622424987 23268700294370586933637481)
      ·
        refine ⟨17451525220777940200228111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23268700294370586933637481 17451525220777940200228111)
        ·
          refine ⟨26177287831166910300342167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17451525220777940200228111 26177287831166910300342167)
          ·
            refine ⟨39265931746750365450513251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26177287831166910300342167 39265931746750365450513251)
            ·
              refine ⟨58898897620125548175769877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39265931746750365450513251 58898897620125548175769877)
              ·
                refine ⟨2760885825943385070739213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 58898897620125548175769877 2760885825943385070739213)
                ·
                  refine ⟨1035332184728769401527205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2760885825943385070739213 1035332184728769401527205)
                  ·
                    refine ⟨194124784636644262786351, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1035332184728769401527205 194124784636644262786351)
                    ·
                      rfl

theorem cell23_1134170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 1, 6, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 1, 6, 3, 4].length) (baseStart_1134170 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1134170 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1134170 prefixEnd_1134170 := by exact prefixLift 1134170
  have htrace : WordTrace (prefixWord ++ tailWord_1134170) baseStart_1134170 baseEnd_1134170 := by
    simpa [prefixWord, tailWord_1134170, baseEnd_1134170] using wordTrace_append hprefix tailTrace_1134170
  have hstable : (prefixWord ++ tailWord_1134170).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1134170).length < 2 ^ (prefixWord ++ tailWord_1134170).sum := by decide
  have hdescent : baseEnd_1134170 < baseStart_1134170 := by decide
  rcases family_descends (prefixWord ++ tailWord_1134170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1134183 : List Nat := [1, 1, 5, 1, 1, 1, 2, 1, 10]
def baseStart_1134183 : Nat := 118140960795 + 1134183 * 2 ^ 59
def prefixEnd_1134183 : Nat := 4983230072969 + 3 ^ 40 * 1134183 * 2
def baseEnd_1134183 : Nat := 64709003239826804166277

theorem tailTrace_1134183 : CollatzResearch.WordTrace tailWord_1134183 prefixEnd_1134183 64709003239826804166277 := by
  unfold tailWord_1134183
  simp only [CollatzResearch.WordTrace]
  refine ⟨41367052450056168880023203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27578034966704112586682135 41367052450056168880023203)
  ·
    refine ⟨62050578675084253320034805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41367052450056168880023203 62050578675084253320034805)
    ·
      refine ⟨5817241750789148748753263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 62050578675084253320034805 5817241750789148748753263)
      ·
        refine ⟨8725862626183723123129895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5817241750789148748753263 8725862626183723123129895)
        ·
          refine ⟨13088793939275584684694843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8725862626183723123129895 13088793939275584684694843)
          ·
            refine ⟨19633190908913377027042265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13088793939275584684694843 19633190908913377027042265)
            ·
              refine ⟨14724893181685032770281699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19633190908913377027042265 14724893181685032770281699)
              ·
                refine ⟨22087339772527549155422549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14724893181685032770281699 22087339772527549155422549)
                ·
                  refine ⟨64709003239826804166277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 22087339772527549155422549 64709003239826804166277)
                  ·
                    rfl

theorem cell23_1134183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 2, 1, 10].length) (baseStart_1134183 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1134183 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1134183 prefixEnd_1134183 := by exact prefixLift 1134183
  have htrace : WordTrace (prefixWord ++ tailWord_1134183) baseStart_1134183 baseEnd_1134183 := by
    simpa [prefixWord, tailWord_1134183, baseEnd_1134183] using wordTrace_append hprefix tailTrace_1134183
  have hstable : (prefixWord ++ tailWord_1134183).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1134183).length < 2 ^ (prefixWord ++ tailWord_1134183).sum := by decide
  have hdescent : baseEnd_1134183 < baseStart_1134183 := by decide
  rcases family_descends (prefixWord ++ tailWord_1134183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1134203 : List Nat := [1, 1, 1, 1, 1, 4, 4, 1, 1, 2, 6]
def baseStart_1134203 : Nat := 118140960795 + 1134203 * 2 ^ 59
def prefixEnd_1134203 : Nat := 4983230072969 + 3 ^ 40 * 1134203 * 2
def baseEnd_1134203 : Nat := 582391298771531159246401

theorem tailTrace_1134203 : CollatzResearch.WordTrace tailWord_1134203 prefixEnd_1134203 582391298771531159246401 := by
  unfold tailWord_1134203
  simp only [CollatzResearch.WordTrace]
  refine ⟨41367781909983712295751263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27578521273322474863834175 41367781909983712295751263)
  ·
    refine ⟨62051672864975568443626895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41367781909983712295751263 62051672864975568443626895)
    ·
      refine ⟨93077509297463352665440343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62051672864975568443626895 93077509297463352665440343)
      ·
        refine ⟨139616263946195028998160515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 93077509297463352665440343 139616263946195028998160515)
        ·
          refine ⟨209424395919292543497240773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 139616263946195028998160515 209424395919292543497240773)
          ·
            refine ⟨39267074234867351905732645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 209424395919292543497240773 39267074234867351905732645)
            ·
              refine ⟨7362576419037628482324871, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 39267074234867351905732645 7362576419037628482324871)
              ·
                refine ⟨11043864628556442723487307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7362576419037628482324871 11043864628556442723487307)
                ·
                  refine ⟨16565796942834664085230961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11043864628556442723487307 16565796942834664085230961)
                  ·
                    refine ⟨12424347707125998063923221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 16565796942834664085230961 12424347707125998063923221)
                    ·
                      refine ⟨582391298771531159246401, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 12424347707125998063923221 582391298771531159246401)
                      ·
                        rfl

theorem cell23_1134203_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 4, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 4, 1, 1, 2, 6].length) (baseStart_1134203 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1134203 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1134203 prefixEnd_1134203 := by exact prefixLift 1134203
  have htrace : WordTrace (prefixWord ++ tailWord_1134203) baseStart_1134203 baseEnd_1134203 := by
    simpa [prefixWord, tailWord_1134203, baseEnd_1134203] using wordTrace_append hprefix tailTrace_1134203
  have hstable : (prefixWord ++ tailWord_1134203).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1134203).length < 2 ^ (prefixWord ++ tailWord_1134203).sum := by decide
  have hdescent : baseEnd_1134203 < baseStart_1134203 := by decide
  rcases family_descends (prefixWord ++ tailWord_1134203) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1134261 : List Nat := [1, 3, 3, 3, 2, 1, 2, 1, 3, 1, 3]
def baseStart_1134261 : Nat := 118140960795 + 1134261 * 2 ^ 59
def prefixEnd_1134261 : Nat := 4983230072969 + 3 ^ 40 * 1134261 * 2
def baseEnd_1134261 : Nat := 582421080649491932321135

theorem tailTrace_1134261 : CollatzResearch.WordTrace tailWord_1134261 prefixEnd_1134261 582421080649491932321135 := by
  unfold tailWord_1134261
  simp only [CollatzResearch.WordTrace]
  refine ⟨41369897343773588201362637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27579931562515725467575091 41369897343773588201362637)
  ·
    refine ⟨15513711503915095575510989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 41369897343773588201362637 15513711503915095575510989)
    ·
      refine ⟨5817641813968160840816621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15513711503915095575510989 5817641813968160840816621)
      ·
        refine ⟨2181615680238060315306233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5817641813968160840816621 2181615680238060315306233)
        ·
          refine ⟨1636211760178545236479675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2181615680238060315306233 1636211760178545236479675)
          ·
            refine ⟨2454317640267817854719513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1636211760178545236479675 2454317640267817854719513)
            ·
              refine ⟨1840738230200863391039635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2454317640267817854719513 1840738230200863391039635)
              ·
                refine ⟨2761107345301295086559453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1840738230200863391039635 2761107345301295086559453)
                ·
                  refine ⟨1035415254487985657459795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2761107345301295086559453 1035415254487985657459795)
                  ·
                    refine ⟨1553122881731978486189693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1035415254487985657459795 1553122881731978486189693)
                    ·
                      refine ⟨582421080649491932321135, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1553122881731978486189693 582421080649491932321135)
                      ·
                        rfl

theorem cell23_1134261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 2, 1, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 2, 1, 2, 1, 3, 1, 3].length) (baseStart_1134261 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1134261 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1134261 prefixEnd_1134261 := by exact prefixLift 1134261
  have htrace : WordTrace (prefixWord ++ tailWord_1134261) baseStart_1134261 baseEnd_1134261 := by
    simpa [prefixWord, tailWord_1134261, baseEnd_1134261] using wordTrace_append hprefix tailTrace_1134261
  have hstable : (prefixWord ++ tailWord_1134261).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1134261).length < 2 ^ (prefixWord ++ tailWord_1134261).sum := by decide
  have hdescent : baseEnd_1134261 < baseStart_1134261 := by decide
  rcases family_descends (prefixWord ++ tailWord_1134261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1134278 : List Nat := [6, 1, 2, 1, 1, 1, 2, 2, 3, 1, 3]
def baseStart_1134278 : Nat := 118140960795 + 1134278 * 2 ^ 59
def prefixEnd_1134278 : Nat := 4983230072969 + 3 ^ 40 * 1134278 * 2
def baseEnd_1134278 : Nat := 582429809820618365808557

theorem tailTrace_1134278 : CollatzResearch.WordTrace tailWord_1134278 prefixEnd_1134278 582429809820618365808557 := by
  unfold tailWord_1134278
  simp only [CollatzResearch.WordTrace]
  refine ⟨1292828668272250003272859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 27580344923141333403154325 1292828668272250003272859)
  ·
    refine ⟨1939243002408375004909289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1292828668272250003272859 1939243002408375004909289)
    ·
      refine ⟨1454432251806281253681967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1939243002408375004909289 1454432251806281253681967)
      ·
        refine ⟨2181648377709421880522951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1454432251806281253681967 2181648377709421880522951)
        ·
          refine ⟨3272472566564132820784427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2181648377709421880522951 3272472566564132820784427)
          ·
            refine ⟨4908708849846199231176641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3272472566564132820784427 4908708849846199231176641)
            ·
              refine ⟨3681531637384649423382481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4908708849846199231176641 3681531637384649423382481)
              ·
                refine ⟨2761148728038487067536861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3681531637384649423382481 2761148728038487067536861)
                ·
                  refine ⟨1035430773014432650326323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2761148728038487067536861 1035430773014432650326323)
                  ·
                    refine ⟨1553146159521648975489485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1035430773014432650326323 1553146159521648975489485)
                    ·
                      refine ⟨582429809820618365808557, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1553146159521648975489485 582429809820618365808557)
                      ·
                        rfl

theorem cell23_1134278_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 1, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 1, 2, 2, 3, 1, 3].length) (baseStart_1134278 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1134278 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1134278 prefixEnd_1134278 := by exact prefixLift 1134278
  have htrace : WordTrace (prefixWord ++ tailWord_1134278) baseStart_1134278 baseEnd_1134278 := by
    simpa [prefixWord, tailWord_1134278, baseEnd_1134278] using wordTrace_append hprefix tailTrace_1134278
  have hstable : (prefixWord ++ tailWord_1134278).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1134278).length < 2 ^ (prefixWord ++ tailWord_1134278).sum := by decide
  have hdescent : baseEnd_1134278 < baseStart_1134278 := by decide
  rcases family_descends (prefixWord ++ tailWord_1134278) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1134280 : List Nat := [2, 1, 3, 1, 2, 2, 3, 1, 1, 1, 6]
def baseStart_1134280 : Nat := 118140960795 + 1134280 * 2 ^ 59
def prefixEnd_1134280 : Nat := 4983230072969 + 3 ^ 40 * 1134280 * 2
def baseEnd_1134280 : Nat := 582430836781927357983547

theorem tailTrace_1134280 : CollatzResearch.WordTrace tailWord_1134280 prefixEnd_1134280 582430836781927357983547 := by
  unfold tailWord_1134280
  simp only [CollatzResearch.WordTrace]
  refine ⟨20685295165352377223152147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27580393553803169630869529 20685295165352377223152147)
  ·
    refine ⟨31027942748028565834728221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20685295165352377223152147 31027942748028565834728221)
    ·
      refine ⟨11635478530510712188023083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 31027942748028565834728221 11635478530510712188023083)
      ·
        refine ⟨17453217795766068282034625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11635478530510712188023083 17453217795766068282034625)
        ·
          refine ⟨13089913346824551211525969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17453217795766068282034625 13089913346824551211525969)
          ·
            refine ⟨9817435010118413408644477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13089913346824551211525969 9817435010118413408644477)
            ·
              refine ⟨3681538128794405028241679, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9817435010118413408644477 3681538128794405028241679)
              ·
                refine ⟨5522307193191607542362519, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3681538128794405028241679 5522307193191607542362519)
                ·
                  refine ⟨8283460789787411313543779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5522307193191607542362519 8283460789787411313543779)
                  ·
                    refine ⟨12425191184681116970315669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8283460789787411313543779 12425191184681116970315669)
                    ·
                      refine ⟨582430836781927357983547, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 12425191184681116970315669 582430836781927357983547)
                      ·
                        rfl

theorem cell23_1134280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 3, 1, 1, 1, 6].length) (baseStart_1134280 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1134280 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1134280 prefixEnd_1134280 := by exact prefixLift 1134280
  have htrace : WordTrace (prefixWord ++ tailWord_1134280) baseStart_1134280 baseEnd_1134280 := by
    simpa [prefixWord, tailWord_1134280, baseEnd_1134280] using wordTrace_append hprefix tailTrace_1134280
  have hstable : (prefixWord ++ tailWord_1134280).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1134280).length < 2 ^ (prefixWord ++ tailWord_1134280).sum := by decide
  have hdescent : baseEnd_1134280 < baseStart_1134280 := by decide
  rcases family_descends (prefixWord ++ tailWord_1134280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1134307 : List Nat := [1, 1, 1, 7, 2, 2, 9]
def baseStart_1134307 : Nat := 118140960795 + 1134307 * 2 ^ 59
def prefixEnd_1134307 : Nat := 4983230072969 + 3 ^ 40 * 1134307 * 2
def baseEnd_1134307 : Nat := 7190675318019737683283

theorem tailTrace_1134307 : CollatzResearch.WordTrace tailWord_1134307 prefixEnd_1134307 7190675318019737683283 := by
  unfold tailWord_1134307
  simp only [CollatzResearch.WordTrace]
  refine ⟨41371575101606938057537175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27581050067737958705024783 41371575101606938057537175)
  ·
    refine ⟨62057362652410407086305763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41371575101606938057537175 62057362652410407086305763)
    ·
      refine ⟨93086043978615610629458645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62057362652410407086305763 93086043978615610629458645)
      ·
        refine ⟨2181704155748803374127937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 93086043978615610629458645 2181704155748803374127937)
        ·
          refine ⟨1636278116811602530595953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2181704155748803374127937 1636278116811602530595953)
          ·
            refine ⟨1227208587608701897946965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1636278116811602530595953 1227208587608701897946965)
            ·
              refine ⟨7190675318019737683283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 1227208587608701897946965 7190675318019737683283)
              ·
                rfl

theorem cell23_1134307_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 2, 2, 9].length) (baseStart_1134307 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1134307 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1134307 prefixEnd_1134307 := by exact prefixLift 1134307
  have htrace : WordTrace (prefixWord ++ tailWord_1134307) baseStart_1134307 baseEnd_1134307 := by
    simpa [prefixWord, tailWord_1134307, baseEnd_1134307] using wordTrace_append hprefix tailTrace_1134307
  have hstable : (prefixWord ++ tailWord_1134307).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1134307).length < 2 ^ (prefixWord ++ tailWord_1134307).sum := by decide
  have hdescent : baseEnd_1134307 < baseStart_1134307 := by decide
  rcases family_descends (prefixWord ++ tailWord_1134307) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1134324 : List Nat := [2, 6, 1, 1, 1, 1, 1, 10]
def baseStart_1134324 : Nat := 118140960795 + 1134324 * 2 ^ 59
def prefixEnd_1134324 : Nat := 4983230072969 + 3 ^ 40 * 1134324 * 2
def baseEnd_1134324 : Nat := 21572349256693525401235

theorem tailTrace_1134324 : CollatzResearch.WordTrace tailWord_1134324 prefixEnd_1134324 21572349256693525401235 := by
  unfold tailWord_1134324
  simp only [CollatzResearch.WordTrace]
  refine ⟨20686097571272674980453013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27581463428363566640604017 20686097571272674980453013)
  ·
    refine ⟨969660823653406639708735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 20686097571272674980453013 969660823653406639708735)
    ·
      refine ⟨1454491235480109959563103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 969660823653406639708735 1454491235480109959563103)
      ·
        refine ⟨2181736853220164939344655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1454491235480109959563103 2181736853220164939344655)
        ·
          refine ⟨3272605279830247409016983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2181736853220164939344655 3272605279830247409016983)
          ·
            refine ⟨4908907919745371113525475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3272605279830247409016983 4908907919745371113525475)
            ·
              refine ⟨7363361879618056670288213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4908907919745371113525475 7363361879618056670288213)
              ·
                refine ⟨21572349256693525401235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 7363361879618056670288213 21572349256693525401235)
                ·
                  rfl

theorem cell23_1134324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 1, 1, 10].length) (baseStart_1134324 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1134324 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1134324 prefixEnd_1134324 := by exact prefixLift 1134324
  have htrace : WordTrace (prefixWord ++ tailWord_1134324) baseStart_1134324 baseEnd_1134324 := by
    simpa [prefixWord, tailWord_1134324, baseEnd_1134324] using wordTrace_append hprefix tailTrace_1134324
  have hstable : (prefixWord ++ tailWord_1134324).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1134324).length < 2 ^ (prefixWord ++ tailWord_1134324).sum := by decide
  have hdescent : baseEnd_1134324 < baseStart_1134324 := by decide
  rcases family_descends (prefixWord ++ tailWord_1134324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1134344 : List Nat := [2, 1, 3, 2, 2, 1, 3, 1, 3, 3, 2]
def baseStart_1134344 : Nat := 118140960795 + 1134344 * 2 ^ 59
def prefixEnd_1134344 : Nat := 4983230072969 + 3 ^ 40 * 1134344 * 2
def baseEnd_1134344 : Nat := 582463699543815107583253

theorem tailTrace_1134344 : CollatzResearch.WordTrace tailWord_1134344 prefixEnd_1134344 582463699543815107583253 := by
  unfold tailWord_1134344
  simp only [CollatzResearch.WordTrace]
  refine ⟨20686462301236446688317043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27581949734981928917756057 20686462301236446688317043)
  ·
    refine ⟨31029693451854670032475565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20686462301236446688317043 31029693451854670032475565)
    ·
      refine ⟨11636135044445501262178337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 31029693451854670032475565 11636135044445501262178337)
      ·
        refine ⟨8727101283334125946633753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11636135044445501262178337 8727101283334125946633753)
        ·
          refine ⟨6545325962500594459975315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8727101283334125946633753 6545325962500594459975315)
          ·
            refine ⟨9817988943750891689962973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6545325962500594459975315 9817988943750891689962973)
            ·
              refine ⟨3681745853906584383736115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9817988943750891689962973 3681745853906584383736115)
              ·
                refine ⟨5522618780859876575604173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3681745853906584383736115 5522618780859876575604173)
                ·
                  refine ⟨2070982042822453715851565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5522618780859876575604173 2070982042822453715851565)
                  ·
                    refine ⟨776618266058420143444337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2070982042822453715851565 776618266058420143444337)
                    ·
                      refine ⟨582463699543815107583253, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 776618266058420143444337 582463699543815107583253)
                      ·
                        rfl

theorem cell23_1134344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 3, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 3, 1, 3, 3, 2].length) (baseStart_1134344 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1134344 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1134344 prefixEnd_1134344 := by exact prefixLift 1134344
  have htrace : WordTrace (prefixWord ++ tailWord_1134344) baseStart_1134344 baseEnd_1134344 := by
    simpa [prefixWord, tailWord_1134344, baseEnd_1134344] using wordTrace_append hprefix tailTrace_1134344
  have hstable : (prefixWord ++ tailWord_1134344).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1134344).length < 2 ^ (prefixWord ++ tailWord_1134344).sum := by decide
  have hdescent : baseEnd_1134344 < baseStart_1134344 := by decide
  rcases family_descends (prefixWord ++ tailWord_1134344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1134397 : List Nat := [1, 4, 1, 4, 1, 1, 1, 1, 9]
def baseStart_1134397 : Nat := 118140960795 + 1134397 * 2 ^ 59
def prefixEnd_1134397 : Nat := 4983230072969 + 3 ^ 40 * 1134397 * 2
def baseEnd_1134397 : Nat := 64721212668722600024501

theorem tailTrace_1134397 : CollatzResearch.WordTrace tailWord_1134397 prefixEnd_1134397 64721212668722600024501 := by
  unfold tailWord_1134397
  simp only [CollatzResearch.WordTrace]
  refine ⟨41374857671280883428313445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27583238447520588952208963 41374857671280883428313445)
  ·
    refine ⟨7757785813365165642808771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 41374857671280883428313445 7757785813365165642808771)
    ·
      refine ⟨11636678720047748464213157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7757785813365165642808771 11636678720047748464213157)
      ·
        refine ⟨2181877260008952837039967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 11636678720047748464213157 2181877260008952837039967)
        ·
          refine ⟨3272815890013429255559951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2181877260008952837039967 3272815890013429255559951)
          ·
            refine ⟨4909223835020143883339927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3272815890013429255559951 4909223835020143883339927)
            ·
              refine ⟨7363835752530215825009891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4909223835020143883339927 7363835752530215825009891)
              ·
                refine ⟨11045753628795323737514837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7363835752530215825009891 11045753628795323737514837)
                ·
                  refine ⟨64721212668722600024501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 11045753628795323737514837 64721212668722600024501)
                  ·
                    rfl

theorem cell23_1134397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 1, 1, 1, 9].length) (baseStart_1134397 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1134397 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1134397 prefixEnd_1134397 := by exact prefixLift 1134397
  have htrace : WordTrace (prefixWord ++ tailWord_1134397) baseStart_1134397 baseEnd_1134397 := by
    simpa [prefixWord, tailWord_1134397, baseEnd_1134397] using wordTrace_append hprefix tailTrace_1134397
  have hstable : (prefixWord ++ tailWord_1134397).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1134397).length < 2 ^ (prefixWord ++ tailWord_1134397).sum := by decide
  have hdescent : baseEnd_1134397 < baseStart_1134397 := by decide
  rcases family_descends (prefixWord ++ tailWord_1134397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1134442 : List Nat := [3, 1, 3, 4, 1, 1, 3, 1, 2, 2, 2]
def baseStart_1134442 : Nat := 118140960795 + 1134442 * 2 ^ 59
def prefixEnd_1134442 : Nat := 4983230072969 + 3 ^ 40 * 1134442 * 2
def baseEnd_1134442 : Nat := 582514020647955724157803

theorem tailTrace_1134442 : CollatzResearch.WordTrace tailWord_1134442 prefixEnd_1134442 582514020647955724157803 := by
  unfold tailWord_1134442
  simp only [CollatzResearch.WordTrace]
  refine ⟨10344124739029464028425395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 27584332637411904075801053 10344124739029464028425395)
  ·
    refine ⟨15516187108544196042638093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10344124739029464028425395 15516187108544196042638093)
    ·
      refine ⟨5818570165704073515989285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15516187108544196042638093 5818570165704073515989285)
      ·
        refine ⟨1090981906069513784247991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5818570165704073515989285 1090981906069513784247991)
        ·
          refine ⟨1636472859104270676371987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1090981906069513784247991 1636472859104270676371987)
          ·
            refine ⟨2454709288656406014557981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1636472859104270676371987 2454709288656406014557981)
            ·
              refine ⟨920515983246152255459243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2454709288656406014557981 920515983246152255459243)
              ·
                refine ⟨1380773974869228383188865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 920515983246152255459243 1380773974869228383188865)
                ·
                  refine ⟨1035580481151921287391649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1380773974869228383188865 1035580481151921287391649)
                  ·
                    refine ⟨776685360863940965543737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1035580481151921287391649 776685360863940965543737)
                    ·
                      refine ⟨582514020647955724157803, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 776685360863940965543737 582514020647955724157803)
                      ·
                        rfl

theorem cell23_1134442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 1, 1, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 1, 1, 3, 1, 2, 2, 2].length) (baseStart_1134442 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1134442 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1134442 prefixEnd_1134442 := by exact prefixLift 1134442
  have htrace : WordTrace (prefixWord ++ tailWord_1134442) baseStart_1134442 baseEnd_1134442 := by
    simpa [prefixWord, tailWord_1134442, baseEnd_1134442] using wordTrace_append hprefix tailTrace_1134442
  have hstable : (prefixWord ++ tailWord_1134442).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1134442).length < 2 ^ (prefixWord ++ tailWord_1134442).sum := by decide
  have hdescent : baseEnd_1134442 < baseStart_1134442 := by decide
  rcases family_descends (prefixWord ++ tailWord_1134442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1134465 : List Nat := [1, 2, 4, 4, 2, 1, 1, 3, 5]
def baseStart_1134465 : Nat := 118140960795 + 1134465 * 2 ^ 59
def prefixEnd_1134465 : Nat := 4983230072969 + 3 ^ 40 * 1134465 * 2
def baseEnd_1134465 : Nat := 64725092300334348241133

theorem tailTrace_1134465 : CollatzResearch.WordTrace tailWord_1134465 prefixEnd_1134465 64725092300334348241133 := by
  unfold tailWord_1134465
  simp only [CollatzResearch.WordTrace]
  refine ⟨41377337835034531041788849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27584891890023020694525899 41377337835034531041788849)
  ·
    refine ⟨31033003376275898281341637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41377337835034531041788849 31033003376275898281341637)
    ·
      refine ⟨5818688133051730927751557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 31033003376275898281341637 5818688133051730927751557)
      ·
        refine ⟨1091004024947199548953417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5818688133051730927751557 1091004024947199548953417)
        ·
          refine ⟨818253018710399661715063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1091004024947199548953417 818253018710399661715063)
          ·
            refine ⟨1227379528065599492572595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 818253018710399661715063 1227379528065599492572595)
            ·
              refine ⟨1841069292098399238858893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1227379528065599492572595 1841069292098399238858893)
              ·
                refine ⟨690400984536899714572085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1841069292098399238858893 690400984536899714572085)
                ·
                  refine ⟨64725092300334348241133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 690400984536899714572085 64725092300334348241133)
                  ·
                    rfl

theorem cell23_1134465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 2, 1, 1, 3, 5].length) (baseStart_1134465 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1134465 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1134465 prefixEnd_1134465 := by exact prefixLift 1134465
  have htrace : WordTrace (prefixWord ++ tailWord_1134465) baseStart_1134465 baseEnd_1134465 := by
    simpa [prefixWord, tailWord_1134465, baseEnd_1134465] using wordTrace_append hprefix tailTrace_1134465
  have hstable : (prefixWord ++ tailWord_1134465).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1134465).length < 2 ^ (prefixWord ++ tailWord_1134465).sum := by decide
  have hdescent : baseEnd_1134465 < baseStart_1134465 := by decide
  rcases family_descends (prefixWord ++ tailWord_1134465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1134487 : List Nat := [1, 1, 3, 3, 1, 3, 2, 1, 8]
def baseStart_1134487 : Nat := 118140960795 + 1134487 * 2 ^ 59
def prefixEnd_1134487 : Nat := 4983230072969 + 3 ^ 40 * 1134487 * 2
def baseEnd_1134487 : Nat := 64726347475267560899455

theorem tailTrace_1134487 : CollatzResearch.WordTrace tailWord_1134487 prefixEnd_1134487 64726347475267560899455 := by
  unfold tailWord_1134487
  simp only [CollatzResearch.WordTrace]
  refine ⟨41378140240954828799089715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27585426827303219199393143 41378140240954828799089715)
  ·
    refine ⟨62067210361432243198634573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41378140240954828799089715 62067210361432243198634573)
    ·
      refine ⟨23275203885537091199487965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 62067210361432243198634573 23275203885537091199487965)
      ·
        refine ⟨8728201457076409199807987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23275203885537091199487965 8728201457076409199807987)
        ·
          refine ⟨13092302185614613799711981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8728201457076409199807987 13092302185614613799711981)
          ·
            refine ⟨4909613319605480174891993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13092302185614613799711981 4909613319605480174891993)
            ·
              refine ⟨3682209989704110131168995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4909613319605480174891993 3682209989704110131168995)
              ·
                refine ⟨5523314984556165196753493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3682209989704110131168995 5523314984556165196753493)
                ·
                  refine ⟨64726347475267560899455, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 5523314984556165196753493 64726347475267560899455)
                  ·
                    rfl

theorem cell23_1134487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 3, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 3, 2, 1, 8].length) (baseStart_1134487 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1134487 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1134487 prefixEnd_1134487 := by exact prefixLift 1134487
  have htrace : WordTrace (prefixWord ++ tailWord_1134487) baseStart_1134487 baseEnd_1134487 := by
    simpa [prefixWord, tailWord_1134487, baseEnd_1134487] using wordTrace_append hprefix tailTrace_1134487
  have hstable : (prefixWord ++ tailWord_1134487).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1134487).length < 2 ^ (prefixWord ++ tailWord_1134487).sum := by decide
  have hdescent : baseEnd_1134487 < baseStart_1134487 := by decide
  rcases family_descends (prefixWord ++ tailWord_1134487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1134564 : List Nat := [2, 3, 1, 1, 1, 1, 6, 1, 1, 6]
def baseStart_1134564 : Nat := 118140960795 + 1134564 * 2 ^ 59
def prefixEnd_1134564 : Nat := 4983230072969 + 3 ^ 40 * 1134564 * 2
def baseEnd_1134564 : Nat := 194192221762601415610747

theorem tailTrace_1134564 : CollatzResearch.WordTrace tailWord_1134564 prefixEnd_1134564 194192221762601415610747 := by
  unfold tailWord_1134564
  simp only [CollatzResearch.WordTrace]
  refine ⟨20690474330837935474821373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27587299107783913966428497 20690474330837935474821373)
  ·
    refine ⟨7758927874064225803058015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20690474330837935474821373 7758927874064225803058015)
    ·
      refine ⟨11638391811096338704587023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7758927874064225803058015 11638391811096338704587023)
      ·
        refine ⟨17457587716644508056880535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11638391811096338704587023 17457587716644508056880535)
        ·
          refine ⟨26186381574966762085320803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17457587716644508056880535 26186381574966762085320803)
          ·
            refine ⟨39279572362450143127981205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26186381574966762085320803 39279572362450143127981205)
            ·
              refine ⟨1841229954489850459124119, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 39279572362450143127981205 1841229954489850459124119)
              ·
                refine ⟨2761844931734775688686179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1841229954489850459124119 2761844931734775688686179)
                ·
                  refine ⟨4142767397602163533029269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2761844931734775688686179 4142767397602163533029269)
                  ·
                    refine ⟨194192221762601415610747, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4142767397602163533029269 194192221762601415610747)
                    ·
                      rfl

theorem cell23_1134564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 6, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 6, 1, 1, 6].length) (baseStart_1134564 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1134564 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1134564 prefixEnd_1134564 := by exact prefixLift 1134564
  have htrace : WordTrace (prefixWord ++ tailWord_1134564) baseStart_1134564 baseEnd_1134564 := by
    simpa [prefixWord, tailWord_1134564, baseEnd_1134564] using wordTrace_append hprefix tailTrace_1134564
  have hstable : (prefixWord ++ tailWord_1134564).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1134564).length < 2 ^ (prefixWord ++ tailWord_1134564).sum := by decide
  have hdescent : baseEnd_1134564 < baseStart_1134564 := by decide
  rcases family_descends (prefixWord ++ tailWord_1134564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1134582 : List Nat := [5, 1, 1, 1, 4, 1, 2, 3, 1, 1, 3]
def baseStart_1134582 : Nat := 118140960795 + 1134582 * 2 ^ 59
def prefixEnd_1134582 : Nat := 4983230072969 + 3 ^ 40 * 1134582 * 2
def baseEnd_1134582 : Nat := 582585907939585176407159

theorem tailTrace_1134582 : CollatzResearch.WordTrace tailWord_1134582 prefixEnd_1134582 582585907939585176407159 := by
  unfold tailWord_1134582
  simp only [CollatzResearch.WordTrace]
  refine ⟨2586350323475666251487375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 27587736783740440015865333 2586350323475666251487375)
  ·
    refine ⟨3879525485213499377231063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2586350323475666251487375 3879525485213499377231063)
    ·
      refine ⟨5819288227820249065846595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3879525485213499377231063 5819288227820249065846595)
      ·
        refine ⟨8728932341730373598769893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5819288227820249065846595 8728932341730373598769893)
        ·
          refine ⟨1636674814074445049769355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8728932341730373598769893 1636674814074445049769355)
          ·
            refine ⟨2455012221111667574654033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1636674814074445049769355 2455012221111667574654033)
            ·
              refine ⟨1841259165833750680990525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2455012221111667574654033 1841259165833750680990525)
              ·
                refine ⟨690472187187656505371447, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1841259165833750680990525 690472187187656505371447)
                ·
                  refine ⟨1035708280781484758057171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 690472187187656505371447 1035708280781484758057171)
                  ·
                    refine ⟨1553562421172227137085757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1035708280781484758057171 1553562421172227137085757)
                    ·
                      refine ⟨582585907939585176407159, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1553562421172227137085757 582585907939585176407159)
                      ·
                        rfl

theorem cell23_1134582_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 4, 1, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 4, 1, 2, 3, 1, 1, 3].length) (baseStart_1134582 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1134582 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1134582 prefixEnd_1134582 := by exact prefixLift 1134582
  have htrace : WordTrace (prefixWord ++ tailWord_1134582) baseStart_1134582 baseEnd_1134582 := by
    simpa [prefixWord, tailWord_1134582, baseEnd_1134582] using wordTrace_append hprefix tailTrace_1134582
  have hstable : (prefixWord ++ tailWord_1134582).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1134582).length < 2 ^ (prefixWord ++ tailWord_1134582).sum := by decide
  have hdescent : baseEnd_1134582 < baseStart_1134582 := by decide
  rcases family_descends (prefixWord ++ tailWord_1134582) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1134584 : List Nat := [2, 1, 2, 1, 1, 3, 4, 2, 1, 2, 4]
def baseStart_1134584 : Nat := 118140960795 + 1134584 * 2 ^ 59
def prefixEnd_1134584 : Nat := 4983230072969 + 3 ^ 40 * 1134584 * 2
def baseEnd_1134584 : Nat := 582586934900894168582149

theorem tailTrace_1134584 : CollatzResearch.WordTrace tailWord_1134584 prefixEnd_1134584 582586934900894168582149 := by
  unfold tailWord_1134584
  simp only [CollatzResearch.WordTrace]
  refine ⟨20690839060801707182685403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27587785414402276243580537 20690839060801707182685403)
  ·
    refine ⟨31036258591202560774028105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20690839060801707182685403 31036258591202560774028105)
    ·
      refine ⟨23277193943401920580521079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31036258591202560774028105 23277193943401920580521079)
      ·
        refine ⟨34915790915102880870781619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23277193943401920580521079 34915790915102880870781619)
        ·
          refine ⟨52373686372654321306172429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34915790915102880870781619 52373686372654321306172429)
          ·
            refine ⟨19640132389745370489814661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 52373686372654321306172429 19640132389745370489814661)
            ·
              refine ⟨3682524823077256966840249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 19640132389745370489814661 3682524823077256966840249)
              ·
                refine ⟨2761893617307942725130187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3682524823077256966840249 2761893617307942725130187)
                ·
                  refine ⟨4142840425961914087695281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2761893617307942725130187 4142840425961914087695281)
                  ·
                    refine ⟨3107130319471435565771461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4142840425961914087695281 3107130319471435565771461)
                    ·
                      refine ⟨582586934900894168582149, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3107130319471435565771461 582586934900894168582149)
                      ·
                        rfl

theorem cell23_1134584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 4, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 4, 2, 1, 2, 4].length) (baseStart_1134584 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1134584 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1134584 prefixEnd_1134584 := by exact prefixLift 1134584
  have htrace : WordTrace (prefixWord ++ tailWord_1134584) baseStart_1134584 baseEnd_1134584 := by
    simpa [prefixWord, tailWord_1134584, baseEnd_1134584] using wordTrace_append hprefix tailTrace_1134584
  have hstable : (prefixWord ++ tailWord_1134584).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1134584).length < 2 ^ (prefixWord ++ tailWord_1134584).sum := by decide
  have hdescent : baseEnd_1134584 < baseStart_1134584 := by decide
  rcases family_descends (prefixWord ++ tailWord_1134584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1134615 : List Nat := [1, 1, 3, 5, 2, 1, 3, 1, 2, 4]
def baseStart_1134615 : Nat := 118140960795 + 1134615 * 2 ^ 59
def prefixEnd_1134615 : Nat := 4983230072969 + 3 ^ 40 * 1134615 * 2
def baseEnd_1134615 : Nat := 194200950933727849098169

theorem tailTrace_1134615 : CollatzResearch.WordTrace tailWord_1134615 prefixEnd_1134615 194200950933727849098169 := by
  unfold tailWord_1134615
  simp only [CollatzResearch.WordTrace]
  refine ⟨41382808784491106659749299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27588539189660737773166199 41382808784491106659749299)
  ·
    refine ⟨62074213176736659989623949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41382808784491106659749299 62074213176736659989623949)
    ·
      refine ⟨23277829941276247496108981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 62074213176736659989623949 23277829941276247496108981)
      ·
        refine ⟨2182296556994648202760217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 23277829941276247496108981 2182296556994648202760217)
        ·
          refine ⟨1636722417745986152070163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2182296556994648202760217 1636722417745986152070163)
          ·
            refine ⟨2455083626618979228105245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1636722417745986152070163 2455083626618979228105245)
            ·
              refine ⟨920656359982117210539467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2455083626618979228105245 920656359982117210539467)
              ·
                refine ⟨1380984539973175815809201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 920656359982117210539467 1380984539973175815809201)
                ·
                  refine ⟨1035738404979881861856901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1380984539973175815809201 1035738404979881861856901)
                  ·
                    refine ⟨194200950933727849098169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1035738404979881861856901 194200950933727849098169)
                    ·
                      rfl

theorem cell23_1134615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 2, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 2, 1, 3, 1, 2, 4].length) (baseStart_1134615 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1134615 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1134615 prefixEnd_1134615 := by exact prefixLift 1134615
  have htrace : WordTrace (prefixWord ++ tailWord_1134615) baseStart_1134615 baseEnd_1134615 := by
    simpa [prefixWord, tailWord_1134615, baseEnd_1134615] using wordTrace_append hprefix tailTrace_1134615
  have hstable : (prefixWord ++ tailWord_1134615).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1134615).length < 2 ^ (prefixWord ++ tailWord_1134615).sum := by decide
  have hdescent : baseEnd_1134615 < baseStart_1134615 := by decide
  rcases family_descends (prefixWord ++ tailWord_1134615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1134628 : List Nat := [2, 3, 1, 4, 2, 2, 2, 7]
def baseStart_1134628 : Nat := 118140960795 + 1134628 * 2 ^ 59
def prefixEnd_1134628 : Nat := 4983230072969 + 3 ^ 40 * 1134628 * 2
def baseEnd_1134628 : Nat := 21578130668507110978961

theorem tailTrace_1134628 : CollatzResearch.WordTrace tailWord_1134628 prefixEnd_1134628 21578130668507110978961 := by
  unfold tailWord_1134628
  simp only [CollatzResearch.WordTrace]
  refine ⟨20691641466722004939986269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27588855288962673253315025 20691641466722004939986269)
  ·
    refine ⟨7759365550020751852494851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20691641466722004939986269 7759365550020751852494851)
    ·
      refine ⟨11639048325031127778742277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7759365550020751852494851 11639048325031127778742277)
      ·
        refine ⟨2182321560943336458514177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 11639048325031127778742277 2182321560943336458514177)
        ·
          refine ⟨1636741170707502343885633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2182321560943336458514177 1636741170707502343885633)
          ·
            refine ⟨1227555878030626757914225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1636741170707502343885633 1227555878030626757914225)
            ·
              refine ⟨920666908522970068435669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1227555878030626757914225 920666908522970068435669)
              ·
                refine ⟨21578130668507110978961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 920666908522970068435669 21578130668507110978961)
                ·
                  rfl

theorem cell23_1134628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 2, 2, 2, 7].length) (baseStart_1134628 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1134628 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1134628 prefixEnd_1134628 := by exact prefixLift 1134628
  have htrace : WordTrace (prefixWord ++ tailWord_1134628) baseStart_1134628 baseEnd_1134628 := by
    simpa [prefixWord, tailWord_1134628, baseEnd_1134628] using wordTrace_append hprefix tailTrace_1134628
  have hstable : (prefixWord ++ tailWord_1134628).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1134628).length < 2 ^ (prefixWord ++ tailWord_1134628).sum := by decide
  have hdescent : baseEnd_1134628 < baseStart_1134628 := by decide
  rcases family_descends (prefixWord ++ tailWord_1134628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1134638 : List Nat := [4, 1, 3, 1, 1, 2, 1, 2, 4, 1, 3]
def baseStart_1134638 : Nat := 118140960795 + 1134638 * 2 ^ 59
def prefixEnd_1134638 : Nat := 4983230072969 + 3 ^ 40 * 1134638 * 2
def baseEnd_1134638 : Nat := 582614662856236957306901

theorem tailTrace_1134638 : CollatzResearch.WordTrace tailWord_1134638 prefixEnd_1134638 582614662856236957306901 := by
  unfold tailWord_1134638
  simp only [CollatzResearch.WordTrace]
  refine ⟨5172955957925972698479571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 27589098442271854391891045 5172955957925972698479571)
  ·
    refine ⟨7759433936888959047719357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5172955957925972698479571 7759433936888959047719357)
    ·
      refine ⟨2909787726333359642894759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7759433936888959047719357 2909787726333359642894759)
      ·
        refine ⟨4364681589500039464342139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2909787726333359642894759 4364681589500039464342139)
        ·
          refine ⟨6547022384250059196513209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4364681589500039464342139 6547022384250059196513209)
          ·
            refine ⟨4910266788187544397384907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6547022384250059196513209 4910266788187544397384907)
            ·
              refine ⟨7365400182281316596077361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4910266788187544397384907 7365400182281316596077361)
              ·
                refine ⟨5524050136710987447058021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7365400182281316596077361 5524050136710987447058021)
                ·
                  refine ⟨1035759400633310146323379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5524050136710987447058021 1035759400633310146323379)
                  ·
                    refine ⟨1553639100949965219485069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1035759400633310146323379 1553639100949965219485069)
                    ·
                      refine ⟨582614662856236957306901, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1553639100949965219485069 582614662856236957306901)
                      ·
                        rfl

theorem cell23_1134638_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 2, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 2, 1, 2, 4, 1, 3].length) (baseStart_1134638 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1134638 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1134638 prefixEnd_1134638 := by exact prefixLift 1134638
  have htrace : WordTrace (prefixWord ++ tailWord_1134638) baseStart_1134638 baseEnd_1134638 := by
    simpa [prefixWord, tailWord_1134638, baseEnd_1134638] using wordTrace_append hprefix tailTrace_1134638
  have hstable : (prefixWord ++ tailWord_1134638).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1134638).length < 2 ^ (prefixWord ++ tailWord_1134638).sum := by decide
  have hdescent : baseEnd_1134638 < baseStart_1134638 := by decide
  rcases family_descends (prefixWord ++ tailWord_1134638) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1134728 : List Nat := [2, 1, 3, 4, 1, 2, 1, 1, 2, 3, 3]
def baseStart_1134728 : Nat := 118140960795 + 1134728 * 2 ^ 59
def prefixEnd_1134728 : Nat := 4983230072969 + 3 ^ 40 * 1134728 * 2
def baseEnd_1134728 : Nat := 582660876115141605181487

theorem tailTrace_1134728 : CollatzResearch.WordTrace tailWord_1134728 prefixEnd_1134728 582660876115141605181487 := by
  unfold tailWord_1134728
  simp only [CollatzResearch.WordTrace]
  refine ⟨20693465116540863479306419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27591286822054484639075225 20693465116540863479306419)
  ·
    refine ⟨31040197674811295218959629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20693465116540863479306419 31040197674811295218959629)
    ·
      refine ⟨11640074128054235707109861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 31040197674811295218959629 11640074128054235707109861)
      ·
        refine ⟨2182513899010169195083099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 11640074128054235707109861 2182513899010169195083099)
        ·
          refine ⟨3273770848515253792624649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2182513899010169195083099 3273770848515253792624649)
          ·
            refine ⟨2455328136386440344468487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3273770848515253792624649 2455328136386440344468487)
            ·
              refine ⟨3682992204579660516702731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2455328136386440344468487 3682992204579660516702731)
              ·
                refine ⟨5524488306869490775054097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3682992204579660516702731 5524488306869490775054097)
                ·
                  refine ⟨4143366230152118081290573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5524488306869490775054097 4143366230152118081290573)
                  ·
                    refine ⟨1553762336307044280483965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4143366230152118081290573 1553762336307044280483965)
                    ·
                      refine ⟨582660876115141605181487, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1553762336307044280483965 582660876115141605181487)
                      ·
                        rfl

theorem cell23_1134728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 2, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 2, 1, 1, 2, 3, 3].length) (baseStart_1134728 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1134728 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1134728 prefixEnd_1134728 := by exact prefixLift 1134728
  have htrace : WordTrace (prefixWord ++ tailWord_1134728) baseStart_1134728 baseEnd_1134728 := by
    simpa [prefixWord, tailWord_1134728, baseEnd_1134728] using wordTrace_append hprefix tailTrace_1134728
  have hstable : (prefixWord ++ tailWord_1134728).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1134728).length < 2 ^ (prefixWord ++ tailWord_1134728).sum := by decide
  have hdescent : baseEnd_1134728 < baseStart_1134728 := by decide
  rcases family_descends (prefixWord ++ tailWord_1134728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1134738 : List Nat := [3, 2, 3, 1, 1, 1, 1, 2, 2, 5, 2]
def baseStart_1134738 : Nat := 118140960795 + 1134738 * 2 ^ 59
def prefixEnd_1134738 : Nat := 4983230072969 + 3 ^ 40 * 1134738 * 2
def baseEnd_1134738 : Nat := 582666010921686566056441

theorem tailTrace_1134738 : CollatzResearch.WordTrace tailWord_1134738 prefixEnd_1134738 582666010921686566056441 := by
  unfold tailWord_1134738
  simp only [CollatzResearch.WordTrace]
  refine ⟨10346823740761374666619217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 27591529975363665777651245 10346823740761374666619217)
  ·
    refine ⟨7760117805571030999964413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10346823740761374666619217 7760117805571030999964413)
    ·
      refine ⟨2910044177089136624986655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7760117805571030999964413 2910044177089136624986655)
      ·
        refine ⟨4365066265633704937479983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2910044177089136624986655 4365066265633704937479983)
        ·
          refine ⟨6547599398450557406219975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4365066265633704937479983 6547599398450557406219975)
          ·
            refine ⟨9821399097675836109329963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6547599398450557406219975 9821399097675836109329963)
            ·
              refine ⟨14732098646513754163994945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9821399097675836109329963 14732098646513754163994945)
              ·
                refine ⟨11049073984885315622996209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14732098646513754163994945 11049073984885315622996209)
                ·
                  refine ⟨8286805488663986717247157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11049073984885315622996209 8286805488663986717247157)
                  ·
                    refine ⟨776888014562248754741921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8286805488663986717247157 776888014562248754741921)
                    ·
                      refine ⟨582666010921686566056441, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 776888014562248754741921 582666010921686566056441)
                      ·
                        rfl

theorem cell23_1134738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 1, 2, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 1, 2, 2, 5, 2].length) (baseStart_1134738 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1134738 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1134738 prefixEnd_1134738 := by exact prefixLift 1134738
  have htrace : WordTrace (prefixWord ++ tailWord_1134738) baseStart_1134738 baseEnd_1134738 := by
    simpa [prefixWord, tailWord_1134738, baseEnd_1134738] using wordTrace_append hprefix tailTrace_1134738
  have hstable : (prefixWord ++ tailWord_1134738).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1134738).length < 2 ^ (prefixWord ++ tailWord_1134738).sum := by decide
  have hdescent : baseEnd_1134738 < baseStart_1134738 := by decide
  rcases family_descends (prefixWord ++ tailWord_1134738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1134771 : List Nat := [1, 1, 1, 2, 3, 2, 1, 3, 4, 2, 3]
def baseStart_1134771 : Nat := 118140960795 + 1134771 * 2 ^ 59
def prefixEnd_1134771 : Nat := 4983230072969 + 3 ^ 40 * 1134771 * 2
def baseEnd_1134771 : Nat := 582682955783284936943789

theorem tailTrace_1134771 : CollatzResearch.WordTrace tailWord_1134771 prefixEnd_1134771 582682955783284936943789 := by
  unfold tailWord_1134771
  simp only [CollatzResearch.WordTrace]
  refine ⟨41388498571925945302428167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27592332381283963534952111 41388498571925945302428167)
  ·
    refine ⟨62082747857888917953642251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41388498571925945302428167 62082747857888917953642251)
    ·
      refine ⟨93124121786833376930463377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62082747857888917953642251 93124121786833376930463377)
      ·
        refine ⟨69843091340125032697847533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 93124121786833376930463377 69843091340125032697847533)
        ·
          refine ⟨26191159252546887261692825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 69843091340125032697847533 26191159252546887261692825)
          ·
            refine ⟨19643369439410165446269619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26191159252546887261692825 19643369439410165446269619)
            ·
              refine ⟨29465054159115248169404429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19643369439410165446269619 29465054159115248169404429)
              ·
                refine ⟨11049395309668218063526661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 29465054159115248169404429 11049395309668218063526661)
                ·
                  refine ⟨2071761620562790886911249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11049395309668218063526661 2071761620562790886911249)
                  ·
                    refine ⟨1553821215422093165183437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2071761620562790886911249 1553821215422093165183437)
                    ·
                      refine ⟨582682955783284936943789, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1553821215422093165183437 582682955783284936943789)
                      ·
                        rfl

theorem cell23_1134771_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 1, 3, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 1, 3, 4, 2, 3].length) (baseStart_1134771 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1134771 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1134771 prefixEnd_1134771 := by exact prefixLift 1134771
  have htrace : WordTrace (prefixWord ++ tailWord_1134771) baseStart_1134771 baseEnd_1134771 := by
    simpa [prefixWord, tailWord_1134771, baseEnd_1134771] using wordTrace_append hprefix tailTrace_1134771
  have hstable : (prefixWord ++ tailWord_1134771).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1134771).length < 2 ^ (prefixWord ++ tailWord_1134771).sum := by decide
  have hdescent : baseEnd_1134771 < baseStart_1134771 := by decide
  rcases family_descends (prefixWord ++ tailWord_1134771) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1134788 : List Nat := [2, 3, 3, 1, 2, 1, 1, 2, 1, 4, 3]
def baseStart_1134788 : Nat := 118140960795 + 1134788 * 2 ^ 59
def prefixEnd_1134788 : Nat := 4983230072969 + 3 ^ 40 * 1134788 * 2
def baseEnd_1134788 : Nat := 582691684954411370431211

theorem tailTrace_1134788 : CollatzResearch.WordTrace tailWord_1134788 prefixEnd_1134788 582691684954411370431211 := by
  unfold tailWord_1134788
  simp only [CollatzResearch.WordTrace]
  refine ⟨20694559306432178602898509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27592745741909571470531345 20694559306432178602898509)
  ·
    refine ⟨7760459739912066976086941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20694559306432178602898509 7760459739912066976086941)
    ·
      refine ⟨2910172402467025116032603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7760459739912066976086941 2910172402467025116032603)
      ·
        refine ⟨4365258603700537674048905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2910172402467025116032603 4365258603700537674048905)
        ·
          refine ⟨3273943952775403255536679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4365258603700537674048905 3273943952775403255536679)
          ·
            refine ⟨4910915929163104883305019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3273943952775403255536679 4910915929163104883305019)
            ·
              refine ⟨7366373893744657324957529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4910915929163104883305019 7366373893744657324957529)
              ·
                refine ⟨5524780420308492993718147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7366373893744657324957529 5524780420308492993718147)
                ·
                  refine ⟨8287170630462739490577221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5524780420308492993718147 8287170630462739490577221)
                  ·
                    refine ⟨1553844493211763654483229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 8287170630462739490577221 1553844493211763654483229)
                    ·
                      refine ⟨582691684954411370431211, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1553844493211763654483229 582691684954411370431211)
                      ·
                        rfl

theorem cell23_1134788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 1, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 1, 1, 2, 1, 4, 3].length) (baseStart_1134788 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1134788 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1134788 prefixEnd_1134788 := by exact prefixLift 1134788
  have htrace : WordTrace (prefixWord ++ tailWord_1134788) baseStart_1134788 baseEnd_1134788 := by
    simpa [prefixWord, tailWord_1134788, baseEnd_1134788] using wordTrace_append hprefix tailTrace_1134788
  have hstable : (prefixWord ++ tailWord_1134788).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1134788).length < 2 ^ (prefixWord ++ tailWord_1134788).sum := by decide
  have hdescent : baseEnd_1134788 < baseStart_1134788 := by decide
  rcases family_descends (prefixWord ++ tailWord_1134788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1134829 : List Nat := [1, 5, 1, 2, 3, 1, 3, 2, 1, 4]
def baseStart_1134829 : Nat := 118140960795 + 1134829 * 2 ^ 59
def prefixEnd_1134829 : Nat := 4983230072969 + 3 ^ 40 * 1134829 * 2
def baseEnd_1134829 : Nat := 194237579220415236672841

theorem tailTrace_1134829 : CollatzResearch.WordTrace tailWord_1134829 prefixEnd_1134829 194237579220415236672841 := by
  unfold tailWord_1134829
  simp only [CollatzResearch.WordTrace]
  refine ⟨41390614005715821208039541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27593742670477214138693027 41390614005715821208039541)
  ·
    refine ⟨3880370063035858238253707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 41390614005715821208039541 3880370063035858238253707)
    ·
      refine ⟨5820555094553787357380561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3880370063035858238253707 5820555094553787357380561)
      ·
        refine ⟨4365416320915340518035421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5820555094553787357380561 4365416320915340518035421)
        ·
          refine ⟨1637031120343252694263283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4365416320915340518035421 1637031120343252694263283)
          ·
            refine ⟨2455546680514879041394925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1637031120343252694263283 2455546680514879041394925)
            ·
              refine ⟨920830005193079640523097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2455546680514879041394925 920830005193079640523097)
              ·
                refine ⟨690622503894809730392323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 920830005193079640523097 690622503894809730392323)
                ·
                  refine ⟨1035933755842214595588485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 690622503894809730392323 1035933755842214595588485)
                  ·
                    refine ⟨194237579220415236672841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1035933755842214595588485 194237579220415236672841)
                    ·
                      rfl

theorem cell23_1134829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 3, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 3, 1, 3, 2, 1, 4].length) (baseStart_1134829 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1134829 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1134829 prefixEnd_1134829 := by exact prefixLift 1134829
  have htrace : WordTrace (prefixWord ++ tailWord_1134829) baseStart_1134829 baseEnd_1134829 := by
    simpa [prefixWord, tailWord_1134829, baseEnd_1134829] using wordTrace_append hprefix tailTrace_1134829
  have hstable : (prefixWord ++ tailWord_1134829).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1134829).length < 2 ^ (prefixWord ++ tailWord_1134829).sum := by decide
  have hdescent : baseEnd_1134829 < baseStart_1134829 := by decide
  rcases family_descends (prefixWord ++ tailWord_1134829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1134851 : List Nat := [1, 1, 1, 3, 2, 3, 2, 3, 1, 6]
def baseStart_1134851 : Nat := 118140960795 + 1134851 * 2 ^ 59
def prefixEnd_1134851 : Nat := 4983230072969 + 3 ^ 40 * 1134851 * 2
def baseEnd_1134851 : Nat := 194241344745214874647807

theorem tailTrace_1134851 : CollatzResearch.WordTrace tailWord_1134851 prefixEnd_1134851 194241344745214874647807 := by
  unfold tailWord_1134851
  simp only [CollatzResearch.WordTrace]
  refine ⟨41391416411636118965340407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27594277607757412643560271 41391416411636118965340407)
  ·
    refine ⟨62087124617454178448010611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41391416411636118965340407 62087124617454178448010611)
    ·
      refine ⟨93130686926181267672015917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62087124617454178448010611 93130686926181267672015917)
      ·
        refine ⟨34924007597317975377005969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 93130686926181267672015917 34924007597317975377005969)
        ·
          refine ⟨26193005697988481532754477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34924007597317975377005969 26193005697988481532754477)
          ·
            refine ⟨9822377136745680574782929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 26193005697988481532754477 9822377136745680574782929)
            ·
              refine ⟨7366782852559260431087197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9822377136745680574782929 7366782852559260431087197)
              ·
                refine ⟨2762543569709722661657699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7366782852559260431087197 2762543569709722661657699)
                ·
                  refine ⟨4143815354564583992486549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2762543569709722661657699 4143815354564583992486549)
                  ·
                    refine ⟨194241344745214874647807, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4143815354564583992486549 194241344745214874647807)
                    ·
                      rfl

theorem cell23_1134851_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 2, 3, 1, 6].length) (baseStart_1134851 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1134851 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1134851 prefixEnd_1134851 := by exact prefixLift 1134851
  have htrace : WordTrace (prefixWord ++ tailWord_1134851) baseStart_1134851 baseEnd_1134851 := by
    simpa [prefixWord, tailWord_1134851, baseEnd_1134851] using wordTrace_append hprefix tailTrace_1134851
  have hstable : (prefixWord ++ tailWord_1134851).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1134851).length < 2 ^ (prefixWord ++ tailWord_1134851).sum := by decide
  have hdescent : baseEnd_1134851 < baseStart_1134851 := by decide
  rcases family_descends (prefixWord ++ tailWord_1134851) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1134855 : List Nat := [1, 1, 4, 5, 1, 1, 1, 1, 3, 5]
def baseStart_1134855 : Nat := 118140960795 + 1134855 * 2 ^ 59
def prefixEnd_1134855 : Nat := 4983230072969 + 3 ^ 40 * 1134855 * 2
def baseEnd_1134855 : Nat := 194242029386087536097801

theorem tailTrace_1134855 : CollatzResearch.WordTrace tailWord_1134855 prefixEnd_1134855 194242029386087536097801 := by
  unfold tailWord_1134855
  simp only [CollatzResearch.WordTrace]
  refine ⟨41391562303621627648486019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27594374869081085098990679 41391562303621627648486019)
  ·
    refine ⟨62087343455432441472729029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41391562303621627648486019 62087343455432441472729029)
    ·
      refine ⟨11641376897893582776136693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 62087343455432441472729029 11641376897893582776136693)
      ·
        refine ⟨1091379084177523385262815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 11641376897893582776136693 1091379084177523385262815)
        ·
          refine ⟨1637068626266285077894223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1091379084177523385262815 1637068626266285077894223)
          ·
            refine ⟨2455602939399427616841335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1637068626266285077894223 2455602939399427616841335)
            ·
              refine ⟨3683404409099141425262003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2455602939399427616841335 3683404409099141425262003)
              ·
                refine ⟨5525106613648712137893005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3683404409099141425262003 5525106613648712137893005)
                ·
                  refine ⟨2071914980118267051709877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5525106613648712137893005 2071914980118267051709877)
                  ·
                    refine ⟨194242029386087536097801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2071914980118267051709877 194242029386087536097801)
                    ·
                      rfl

theorem cell23_1134855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 1, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 1, 1, 1, 1, 3, 5].length) (baseStart_1134855 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1134855 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1134855 prefixEnd_1134855 := by exact prefixLift 1134855
  have htrace : WordTrace (prefixWord ++ tailWord_1134855) baseStart_1134855 baseEnd_1134855 := by
    simpa [prefixWord, tailWord_1134855, baseEnd_1134855] using wordTrace_append hprefix tailTrace_1134855
  have hstable : (prefixWord ++ tailWord_1134855).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1134855).length < 2 ^ (prefixWord ++ tailWord_1134855).sum := by decide
  have hdescent : baseEnd_1134855 < baseStart_1134855 := by decide
  rcases family_descends (prefixWord ++ tailWord_1134855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1134858 : List Nat := [3, 1, 2, 2, 1, 1, 2, 1, 2, 6, 2]
def baseStart_1134858 : Nat := 118140960795 + 1134858 * 2 ^ 59
def prefixEnd_1134858 : Nat := 4983230072969 + 3 ^ 40 * 1134858 * 2
def baseEnd_1134858 : Nat := 582727628600226096555889

theorem tailTrace_1134858 : CollatzResearch.WordTrace tailWord_1134858 prefixEnd_1134858 582727628600226096555889 := by
  unfold tailWord_1134858
  simp only [CollatzResearch.WordTrace]
  refine ⟨10347917930652689790211307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 27594447815073839440563485 10347917930652689790211307)
  ·
    refine ⟨15521876895979034685316961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10347917930652689790211307 15521876895979034685316961)
    ·
      refine ⟨11641407671984276013987721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15521876895979034685316961 11641407671984276013987721)
      ·
        refine ⟨8731055753988207010490791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11641407671984276013987721 8731055753988207010490791)
        ·
          refine ⟨13096583630982310515736187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8731055753988207010490791 13096583630982310515736187)
          ·
            refine ⟨19644875446473465773604281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13096583630982310515736187 19644875446473465773604281)
            ·
              refine ⟨14733656584855099330203211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19644875446473465773604281 14733656584855099330203211)
              ·
                refine ⟨22100484877282648995304817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14733656584855099330203211 22100484877282648995304817)
                ·
                  refine ⟨16575363657961986746478613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22100484877282648995304817 16575363657961986746478613)
                  ·
                    refine ⟨776970171466968128741185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16575363657961986746478613 776970171466968128741185)
                    ·
                      refine ⟨582727628600226096555889, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 776970171466968128741185 582727628600226096555889)
                      ·
                        rfl

theorem cell23_1134858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 2, 1, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 2, 1, 2, 6, 2].length) (baseStart_1134858 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1134858 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1134858 prefixEnd_1134858 := by exact prefixLift 1134858
  have htrace : WordTrace (prefixWord ++ tailWord_1134858) baseStart_1134858 baseEnd_1134858 := by
    simpa [prefixWord, tailWord_1134858, baseEnd_1134858] using wordTrace_append hprefix tailTrace_1134858
  have hstable : (prefixWord ++ tailWord_1134858).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1134858).length < 2 ^ (prefixWord ++ tailWord_1134858).sum := by decide
  have hdescent : baseEnd_1134858 < baseStart_1134858 := by decide
  rcases family_descends (prefixWord ++ tailWord_1134858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1134891 : List Nat := [1, 1, 1, 1, 2, 1, 2, 1, 1, 9, 3]
def baseStart_1134891 : Nat := 118140960795 + 1134891 * 2 ^ 59
def prefixEnd_1134891 : Nat := 4983230072969 + 3 ^ 40 * 1134891 * 2
def baseEnd_1134891 : Nat := 582744573461824467443237

theorem tailTrace_1134891 : CollatzResearch.WordTrace tailWord_1134891 prefixEnd_1134891 582744573461824467443237 := by
  unfold tailWord_1134891
  simp only [CollatzResearch.WordTrace]
  refine ⟨41392875331491205796796527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27595250220994137197864351 41392875331491205796796527)
  ·
    refine ⟨62089312997236808695194791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41392875331491205796796527 62089312997236808695194791)
    ·
      refine ⟨93133969495855213042792187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62089312997236808695194791 93133969495855213042792187)
      ·
        refine ⟨139700954243782819564188281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 93133969495855213042792187 139700954243782819564188281)
        ·
          refine ⟨104775715682837114673141211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 139700954243782819564188281 104775715682837114673141211)
          ·
            refine ⟨157163573524255672009711817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 104775715682837114673141211 157163573524255672009711817)
            ·
              refine ⟨117872680143191754007283863, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 157163573524255672009711817 117872680143191754007283863)
              ·
                refine ⟨176809020214787631010925795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 117872680143191754007283863 176809020214787631010925795)
                ·
                  refine ⟨265213530322181446516388693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 176809020214787631010925795 265213530322181446516388693)
                  ·
                    refine ⟨1553985529231531913181965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 265213530322181446516388693 1553985529231531913181965)
                    ·
                      refine ⟨582744573461824467443237, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1553985529231531913181965 582744573461824467443237)
                      ·
                        rfl

theorem cell23_1134891_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 1, 1, 9, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 1, 1, 9, 3].length) (baseStart_1134891 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1134891 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1134891 prefixEnd_1134891 := by exact prefixLift 1134891
  have htrace : WordTrace (prefixWord ++ tailWord_1134891) baseStart_1134891 baseEnd_1134891 := by
    simpa [prefixWord, tailWord_1134891, baseEnd_1134891] using wordTrace_append hprefix tailTrace_1134891
  have hstable : (prefixWord ++ tailWord_1134891).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1134891).length < 2 ^ (prefixWord ++ tailWord_1134891).sum := by decide
  have hdescent : baseEnd_1134891 < baseStart_1134891 := by decide
  rcases family_descends (prefixWord ++ tailWord_1134891) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1134905 : List Nat := [1, 2, 1, 6, 1, 2, 2, 1, 1, 2, 4]
def baseStart_1134905 : Nat := 118140960795 + 1134905 * 2 ^ 59
def prefixEnd_1134905 : Nat := 4983230072969 + 3 ^ 40 * 1134905 * 2
def baseEnd_1134905 : Nat := 582751762190987412668173

theorem tailTrace_1134905 : CollatzResearch.WordTrace tailWord_1134905 prefixEnd_1134905 582751762190987412668173 := by
  unfold tailWord_1134905
  simp only [CollatzResearch.WordTrace]
  refine ⟨41393385953440486187806169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27595590635626990791870779 41393385953440486187806169)
  ·
    refine ⟨31045039465080364640854627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41393385953440486187806169 31045039465080364640854627)
    ·
      refine ⟨46567559197620546961281941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31045039465080364640854627 46567559197620546961281941)
      ·
        refine ⟨2182854337388463138810091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 46567559197620546961281941 2182854337388463138810091)
        ·
          refine ⟨3274281506082694708215137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2182854337388463138810091 3274281506082694708215137)
          ·
            refine ⟨2455711129562021031161353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3274281506082694708215137 2455711129562021031161353)
            ·
              refine ⟨1841783347171515773371015, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2455711129562021031161353 1841783347171515773371015)
              ·
                refine ⟨2762675020757273660056523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1841783347171515773371015 2762675020757273660056523)
                ·
                  refine ⟨4144012531135910490084785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2762675020757273660056523 4144012531135910490084785)
                  ·
                    refine ⟨3108009398351932867563589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4144012531135910490084785 3108009398351932867563589)
                    ·
                      refine ⟨582751762190987412668173, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3108009398351932867563589 582751762190987412668173)
                      ·
                        rfl

theorem cell23_1134905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 2, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 2, 2, 1, 1, 2, 4].length) (baseStart_1134905 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1134905 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1134905 prefixEnd_1134905 := by exact prefixLift 1134905
  have htrace : WordTrace (prefixWord ++ tailWord_1134905) baseStart_1134905 baseEnd_1134905 := by
    simpa [prefixWord, tailWord_1134905, baseEnd_1134905] using wordTrace_append hprefix tailTrace_1134905
  have hstable : (prefixWord ++ tailWord_1134905).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1134905).length < 2 ^ (prefixWord ++ tailWord_1134905).sum := by decide
  have hdescent : baseEnd_1134905 < baseStart_1134905 := by decide
  rcases family_descends (prefixWord ++ tailWord_1134905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1134911 : List Nat := [1, 1, 2, 2, 4, 1, 1, 2, 2, 7]
def baseStart_1134911 : Nat := 118140960795 + 1134911 * 2 ^ 59
def prefixEnd_1134911 : Nat := 4983230072969 + 3 ^ 40 * 1134911 * 2
def baseEnd_1134911 : Nat := 194251614358304796397715

theorem tailTrace_1134911 : CollatzResearch.WordTrace tailWord_1134911 prefixEnd_1134911 194251614358304796397715 := by
  unfold tailWord_1134911
  simp only [CollatzResearch.WordTrace]
  refine ⟨41393604791418749212524587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27595736527612499475016391 41393604791418749212524587)
  ·
    refine ⟨62090407187128123818786881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41393604791418749212524587 62090407187128123818786881)
    ·
      refine ⟨46567805390346092864090161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 62090407187128123818786881 46567805390346092864090161)
      ·
        refine ⟨34925854042759569648067621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46567805390346092864090161 34925854042759569648067621)
        ·
          refine ⟨6548597633017419309012679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 34925854042759569648067621 6548597633017419309012679)
          ·
            refine ⟨9822896449526128963519019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6548597633017419309012679 9822896449526128963519019)
            ·
              refine ⟨14734344674289193445278529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9822896449526128963519019 14734344674289193445278529)
              ·
                refine ⟨11050758505716895083958897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14734344674289193445278529 11050758505716895083958897)
                ·
                  refine ⟨8288068879287671312969173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11050758505716895083958897 8288068879287671312969173)
                  ·
                    refine ⟨194251614358304796397715, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 8288068879287671312969173 194251614358304796397715)
                    ·
                      rfl

theorem cell23_1134911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 1, 2, 2, 7].length) (baseStart_1134911 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1134911 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1134911 prefixEnd_1134911 := by exact prefixLift 1134911
  have htrace : WordTrace (prefixWord ++ tailWord_1134911) baseStart_1134911 baseEnd_1134911 := by
    simpa [prefixWord, tailWord_1134911, baseEnd_1134911] using wordTrace_append hprefix tailTrace_1134911
  have hstable : (prefixWord ++ tailWord_1134911).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1134911).length < 2 ^ (prefixWord ++ tailWord_1134911).sum := by decide
  have hdescent : baseEnd_1134911 < baseStart_1134911 := by decide
  rcases family_descends (prefixWord ++ tailWord_1134911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1134921 : List Nat := [1, 2, 1, 1, 2, 3, 1, 3, 2, 2, 5]
def baseStart_1134921 : Nat := 118140960795 + 1134921 * 2 ^ 59
def prefixEnd_1134921 : Nat := 4983230072969 + 3 ^ 40 * 1134921 * 2
def baseEnd_1134921 : Nat := 582759977881459350068099

theorem tailTrace_1134921 : CollatzResearch.WordTrace tailWord_1134921 prefixEnd_1134921 582759977881459350068099 := by
  unfold tailWord_1134921
  simp only [CollatzResearch.WordTrace]
  refine ⟨41393969521382520920388617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27595979680921680613592411 41393969521382520920388617)
  ·
    refine ⟨31045477141036890690291463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41393969521382520920388617 31045477141036890690291463)
    ·
      refine ⟨46568215711555336035437195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31045477141036890690291463 46568215711555336035437195)
      ·
        refine ⟨69852323567333004053155793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46568215711555336035437195 69852323567333004053155793)
        ·
          refine ⟨52389242675499753039866845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 69852323567333004053155793 52389242675499753039866845)
          ·
            refine ⟨19645966003312407389950067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 52389242675499753039866845 19645966003312407389950067)
            ·
              refine ⟨29468949004968611084925101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19645966003312407389950067 29468949004968611084925101)
              ·
                refine ⟨11050855876863229156846913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 29468949004968611084925101 11050855876863229156846913)
                ·
                  refine ⟨8288141907647421867635185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11050855876863229156846913 8288141907647421867635185)
                  ·
                    refine ⟨6216106430735566400726389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8288141907647421867635185 6216106430735566400726389)
                    ·
                      refine ⟨582759977881459350068099, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 6216106430735566400726389 582759977881459350068099)
                      ·
                        rfl

theorem cell23_1134921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 1, 3, 2, 2, 5].length) (baseStart_1134921 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1134921 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1134921 prefixEnd_1134921 := by exact prefixLift 1134921
  have htrace : WordTrace (prefixWord ++ tailWord_1134921) baseStart_1134921 baseEnd_1134921 := by
    simpa [prefixWord, tailWord_1134921, baseEnd_1134921] using wordTrace_append hprefix tailTrace_1134921
  have hstable : (prefixWord ++ tailWord_1134921).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1134921).length < 2 ^ (prefixWord ++ tailWord_1134921).sum := by decide
  have hdescent : baseEnd_1134921 < baseStart_1134921 := by decide
  rcases family_descends (prefixWord ++ tailWord_1134921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1134931 : List Nat := [1, 1, 1, 2, 1, 1, 4, 2, 1, 5, 4]
def baseStart_1134931 : Nat := 118140960795 + 1134931 * 2 ^ 59
def prefixEnd_1134931 : Nat := 4983230072969 + 3 ^ 40 * 1134931 * 2
def baseEnd_1134931 : Nat := 582765112688004310943053

theorem tailTrace_1134931 : CollatzResearch.WordTrace tailWord_1134931 prefixEnd_1134931 582765112688004310943053 := by
  unfold tailWord_1134931
  simp only [CollatzResearch.WordTrace]
  refine ⟨41394334251346292628252647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27596222834230861752168431 41394334251346292628252647)
  ·
    refine ⟨62091501377019438942378971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41394334251346292628252647 62091501377019438942378971)
    ·
      refine ⟨93137252065529158413568457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62091501377019438942378971 93137252065529158413568457)
      ·
        refine ⟨69852939049146868810176343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 93137252065529158413568457 69852939049146868810176343)
        ·
          refine ⟨104779408573720303215264515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 69852939049146868810176343 104779408573720303215264515)
          ·
            refine ⟨157169112860580454822896773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 104779408573720303215264515 157169112860580454822896773)
            ·
              refine ⟨29469208661358835279293145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 157169112860580454822896773 29469208661358835279293145)
              ·
                refine ⟨22101906496019126459469859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29469208661358835279293145 22101906496019126459469859)
                ·
                  refine ⟨33152859744028689689204789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22101906496019126459469859 33152859744028689689204789)
                  ·
                    refine ⟨3108080601002689658362949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 33152859744028689689204789 3108080601002689658362949)
                    ·
                      refine ⟨582765112688004310943053, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3108080601002689658362949 582765112688004310943053)
                      ·
                        rfl

theorem cell23_1134931_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 4, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 4, 2, 1, 5, 4].length) (baseStart_1134931 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1134931 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1134931 prefixEnd_1134931 := by exact prefixLift 1134931
  have htrace : WordTrace (prefixWord ++ tailWord_1134931) baseStart_1134931 baseEnd_1134931 := by
    simpa [prefixWord, tailWord_1134931, baseEnd_1134931] using wordTrace_append hprefix tailTrace_1134931
  have hstable : (prefixWord ++ tailWord_1134931).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1134931).length < 2 ^ (prefixWord ++ tailWord_1134931).sum := by decide
  have hdescent : baseEnd_1134931 < baseStart_1134931 := by decide
  rcases family_descends (prefixWord ++ tailWord_1134931) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1135016 : List Nat := [2, 1, 6, 1, 1, 2, 1, 3, 2, 2, 2]
def baseStart_1135016 : Nat := 118140960795 + 1135016 * 2 ^ 59
def prefixEnd_1135016 : Nat := 4983230072969 + 3 ^ 40 * 1135016 * 2
def baseEnd_1135016 : Nat := 582808758543636478380163

theorem tailTrace_1135016 : CollatzResearch.WordTrace tailWord_1135016 prefixEnd_1135016 582808758543636478380163 := by
  unfold tailWord_1135016
  simp only [CollatzResearch.WordTrace]
  refine ⟨20698717228019176072548451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27598289637358901430064601 20698717228019176072548451)
  ·
    refine ⟨31048075842028764108822677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20698717228019176072548451 31048075842028764108822677)
    ·
      refine ⟨1455378555095098317601063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 31048075842028764108822677 1455378555095098317601063)
      ·
        refine ⟨2183067832642647476401595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1455378555095098317601063 2183067832642647476401595)
        ·
          refine ⟨3274601748963971214602393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2183067832642647476401595 3274601748963971214602393)
          ·
            refine ⟨2455951311722978410951795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3274601748963971214602393 2455951311722978410951795)
            ·
              refine ⟨3683926967584467616427693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2455951311722978410951795 3683926967584467616427693)
              ·
                refine ⟨1381472612844175356160385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3683926967584467616427693 1381472612844175356160385)
                ·
                  refine ⟨1036104459633131517120289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1381472612844175356160385 1036104459633131517120289)
                  ·
                    refine ⟨777078344724848637840217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1036104459633131517120289 777078344724848637840217)
                    ·
                      refine ⟨582808758543636478380163, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 777078344724848637840217 582808758543636478380163)
                      ·
                        rfl

theorem cell23_1135016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 2, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 2, 1, 3, 2, 2, 2].length) (baseStart_1135016 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1135016 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1135016 prefixEnd_1135016 := by exact prefixLift 1135016
  have htrace : WordTrace (prefixWord ++ tailWord_1135016) baseStart_1135016 baseEnd_1135016 := by
    simpa [prefixWord, tailWord_1135016, baseEnd_1135016] using wordTrace_append hprefix tailTrace_1135016
  have hstable : (prefixWord ++ tailWord_1135016).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1135016).length < 2 ^ (prefixWord ++ tailWord_1135016).sum := by decide
  have hdescent : baseEnd_1135016 < baseStart_1135016 := by decide
  rcases family_descends (prefixWord ++ tailWord_1135016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1135055 : List Nat := [1, 1, 2, 1, 1, 4, 1, 4, 2, 4, 2]
def baseStart_1135055 : Nat := 118140960795 + 1135055 * 2 ^ 59
def prefixEnd_1135055 : Nat := 4983230072969 + 3 ^ 40 * 1135055 * 2
def baseEnd_1135055 : Nat := 582828784289161825792483

theorem tailTrace_1135055 : CollatzResearch.WordTrace tailWord_1135055 prefixEnd_1135055 582828784289161825792483 := by
  unfold tailWord_1135055
  simp only [CollatzResearch.WordTrace]
  refine ⟨41398856902897061805766619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27599237935264707870511079 41398856902897061805766619)
  ·
    refine ⟨62098285354345592708649929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41398856902897061805766619 62098285354345592708649929)
    ·
      refine ⟨46573714015759194531487447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 62098285354345592708649929 46573714015759194531487447)
      ·
        refine ⟨69860571023638791797231171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46573714015759194531487447 69860571023638791797231171)
        ·
          refine ⟨104790856535458187695846757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 69860571023638791797231171 104790856535458187695846757)
          ·
            refine ⟨19648285600398410192971267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 104790856535458187695846757 19648285600398410192971267)
            ·
              refine ⟨29472428400597615289456901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19648285600398410192971267 29472428400597615289456901)
              ·
                refine ⟨5526080325112052866773169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 29472428400597615289456901 5526080325112052866773169)
                ·
                  refine ⟨4144560243834039650079877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5526080325112052866773169 4144560243834039650079877)
                  ·
                    refine ⟨777105045718882434389977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4144560243834039650079877 777105045718882434389977)
                    ·
                      refine ⟨582828784289161825792483, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 777105045718882434389977 582828784289161825792483)
                      ·
                        rfl

theorem cell23_1135055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 1, 4, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 1, 4, 2, 4, 2].length) (baseStart_1135055 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1135055 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1135055 prefixEnd_1135055 := by exact prefixLift 1135055
  have htrace : WordTrace (prefixWord ++ tailWord_1135055) baseStart_1135055 baseEnd_1135055 := by
    simpa [prefixWord, tailWord_1135055, baseEnd_1135055] using wordTrace_append hprefix tailTrace_1135055
  have hstable : (prefixWord ++ tailWord_1135055).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1135055).length < 2 ^ (prefixWord ++ tailWord_1135055).sum := by decide
  have hdescent : baseEnd_1135055 < baseStart_1135055 := by decide
  rcases family_descends (prefixWord ++ tailWord_1135055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1135065 : List Nat := [1, 2, 1, 2, 4, 1, 2, 3, 3, 4]
def baseStart_1135065 : Nat := 118140960795 + 1135065 * 2 ^ 59
def prefixEnd_1135065 : Nat := 4983230072969 + 3 ^ 40 * 1135065 * 2
def baseEnd_1135065 : Nat := 194277973031902262222479

theorem tailTrace_1135065 : CollatzResearch.WordTrace tailWord_1135065 prefixEnd_1135065 194277973031902262222479 := by
  unfold tailWord_1135065
  simp only [CollatzResearch.WordTrace]
  refine ⟨41399221632860833513630649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27599481088573889009087099 41399221632860833513630649)
  ·
    refine ⟨31049416224645625135222987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41399221632860833513630649 31049416224645625135222987)
    ·
      refine ⟨46574124336968437702834481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31049416224645625135222987 46574124336968437702834481)
      ·
        refine ⟨34930593252726328277125861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46574124336968437702834481 34930593252726328277125861)
        ·
          refine ⟨6549486234886186551961099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 34930593252726328277125861 6549486234886186551961099)
          ·
            refine ⟨9824229352329279827941649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6549486234886186551961099 9824229352329279827941649)
            ·
              refine ⟨7368172014246959870956237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9824229352329279827941649 7368172014246959870956237)
              ·
                refine ⟨2763064505342609951608589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7368172014246959870956237 2763064505342609951608589)
                ·
                  refine ⟨1036149189503478731853221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2763064505342609951608589 1036149189503478731853221)
                  ·
                    refine ⟨194277973031902262222479, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1036149189503478731853221 194277973031902262222479)
                    ·
                      rfl

theorem cell23_1135065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 2, 3, 3, 4].length) (baseStart_1135065 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1135065 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1135065 prefixEnd_1135065 := by exact prefixLift 1135065
  have htrace : WordTrace (prefixWord ++ tailWord_1135065) baseStart_1135065 baseEnd_1135065 := by
    simpa [prefixWord, tailWord_1135065, baseEnd_1135065] using wordTrace_append hprefix tailTrace_1135065
  have hstable : (prefixWord ++ tailWord_1135065).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1135065).length < 2 ^ (prefixWord ++ tailWord_1135065).sum := by decide
  have hdescent : baseEnd_1135065 < baseStart_1135065 := by decide
  rcases family_descends (prefixWord ++ tailWord_1135065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1135082 : List Nat := [3, 1, 3, 1, 3, 2, 1, 2, 3, 4]
def baseStart_1135082 : Nat := 118140960795 + 1135082 * 2 ^ 59
def prefixEnd_1135082 : Nat := 4983230072969 + 3 ^ 40 * 1135082 * 2
def baseEnd_1135082 : Nat := 194280882755611073384953

theorem tailTrace_1135082 : CollatzResearch.WordTrace tailWord_1135082 prefixEnd_1135082 194280882755611073384953 := by
  unfold tailWord_1135082
  simp only [CollatzResearch.WordTrace]
  refine ⟨10349960418449811354249875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 27599894449199496944666333 10349960418449811354249875)
  ·
    refine ⟨15524940627674717031374813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10349960418449811354249875 15524940627674717031374813)
    ·
      refine ⟨5821852735378018886765555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15524940627674717031374813 5821852735378018886765555)
      ·
        refine ⟨8732779103067028330148333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5821852735378018886765555 8732779103067028330148333)
        ·
          refine ⟨3274792163650135623805625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8732779103067028330148333 3274792163650135623805625)
          ·
            refine ⟨2456094122737601717854219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3274792163650135623805625 2456094122737601717854219)
            ·
              refine ⟨3684141184106402576781329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2456094122737601717854219 3684141184106402576781329)
              ·
                refine ⟨2763105888079801932585997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3684141184106402576781329 2763105888079801932585997)
                ·
                  refine ⟨1036164708029925724719749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2763105888079801932585997 1036164708029925724719749)
                  ·
                    refine ⟨194280882755611073384953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1036164708029925724719749 194280882755611073384953)
                    ·
                      rfl

theorem cell23_1135082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 2, 1, 2, 3, 4].length) (baseStart_1135082 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1135082 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1135082 prefixEnd_1135082 := by exact prefixLift 1135082
  have htrace : WordTrace (prefixWord ++ tailWord_1135082) baseStart_1135082 baseEnd_1135082 := by
    simpa [prefixWord, tailWord_1135082, baseEnd_1135082] using wordTrace_append hprefix tailTrace_1135082
  have hstable : (prefixWord ++ tailWord_1135082).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1135082).length < 2 ^ (prefixWord ++ tailWord_1135082).sum := by decide
  have hdescent : baseEnd_1135082 < baseStart_1135082 := by decide
  rcases family_descends (prefixWord ++ tailWord_1135082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1135132 : List Nat := [2, 2, 3, 1, 2, 2, 1, 2, 1, 5, 2]
def baseStart_1135132 : Nat := 118140960795 + 1135132 * 2 ^ 59
def prefixEnd_1135132 : Nat := 4983230072969 + 3 ^ 40 * 1135132 * 2
def baseEnd_1135132 : Nat := 582868322299558024529629

theorem tailTrace_1135132 : CollatzResearch.WordTrace tailWord_1135132 prefixEnd_1135132 582868322299558024529629 := by
  unfold tailWord_1135132
  simp only [CollatzResearch.WordTrace]
  refine ⟨20700832661809051978159825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27601110215745402637546433 20700832661809051978159825)
  ·
    refine ⟨15525624496356788983619869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20700832661809051978159825 15525624496356788983619869)
    ·
      refine ⟨5822109186133795868857451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15525624496356788983619869 5822109186133795868857451)
      ·
        refine ⟨8733163779200693803286177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5822109186133795868857451 8733163779200693803286177)
        ·
          refine ⟨6549872834400520352464633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8733163779200693803286177 6549872834400520352464633)
          ·
            refine ⟨4912404625800390264348475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6549872834400520352464633 4912404625800390264348475)
            ·
              refine ⟨7368606938700585396522713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4912404625800390264348475 7368606938700585396522713)
              ·
                refine ⟨5526455204025439047392035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7368606938700585396522713 5526455204025439047392035)
                ·
                  refine ⟨8289682806038158571088053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5526455204025439047392035 8289682806038158571088053)
                  ·
                    refine ⟨777157763066077366039505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8289682806038158571088053 777157763066077366039505)
                    ·
                      refine ⟨582868322299558024529629, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 777157763066077366039505 582868322299558024529629)
                      ·
                        rfl

theorem cell23_1135132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 2, 1, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 2, 1, 2, 1, 5, 2].length) (baseStart_1135132 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1135132 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1135132 prefixEnd_1135132 := by exact prefixLift 1135132
  have htrace : WordTrace (prefixWord ++ tailWord_1135132) baseStart_1135132 baseEnd_1135132 := by
    simpa [prefixWord, tailWord_1135132, baseEnd_1135132] using wordTrace_append hprefix tailTrace_1135132
  have hstable : (prefixWord ++ tailWord_1135132).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1135132).length < 2 ^ (prefixWord ++ tailWord_1135132).sum := by decide
  have hdescent : baseEnd_1135132 < baseStart_1135132 := by decide
  rcases family_descends (prefixWord ++ tailWord_1135132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1135155 : List Nat := [1, 1, 1, 2, 4, 2, 1, 1, 6, 4]
def baseStart_1135155 : Nat := 118140960795 + 1135155 * 2 ^ 59
def prefixEnd_1135155 : Nat := 4983230072969 + 3 ^ 40 * 1135155 * 2
def baseEnd_1135155 : Nat := 194293377451537144847341

theorem tailTrace_1135155 : CollatzResearch.WordTrace tailWord_1135155 prefixEnd_1135155 194293377451537144847341 := by
  unfold tailWord_1135155
  simp only [CollatzResearch.WordTrace]
  refine ⟨41402504202534778884406919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27601669468356519256271279 41402504202534778884406919)
  ·
    refine ⟨62103756303802168326610379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41402504202534778884406919 62103756303802168326610379)
    ·
      refine ⟨93155634455703252489915569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62103756303802168326610379 93155634455703252489915569)
      ·
        refine ⟨69866725841777439367436677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 93155634455703252489915569 69866725841777439367436677)
        ·
          refine ⟨13100011095333269881394377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 69866725841777439367436677 13100011095333269881394377)
          ·
            refine ⟨9825008321499952411045783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13100011095333269881394377 9825008321499952411045783)
            ·
              refine ⟨14737512482249928616568675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9825008321499952411045783 14737512482249928616568675)
              ·
                refine ⟨22106268723374892924853013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14737512482249928616568675 22106268723374892924853013)
                ·
                  refine ⟨1036231346408198105852485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 22106268723374892924853013 1036231346408198105852485)
                  ·
                    refine ⟨194293377451537144847341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1036231346408198105852485 194293377451537144847341)
                    ·
                      rfl

theorem cell23_1135155_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 1, 1, 6, 4].length) (baseStart_1135155 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1135155 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1135155 prefixEnd_1135155 := by exact prefixLift 1135155
  have htrace : WordTrace (prefixWord ++ tailWord_1135155) baseStart_1135155 baseEnd_1135155 := by
    simpa [prefixWord, tailWord_1135155, baseEnd_1135155] using wordTrace_append hprefix tailTrace_1135155
  have hstable : (prefixWord ++ tailWord_1135155).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1135155).length < 2 ^ (prefixWord ++ tailWord_1135155).sum := by decide
  have hdescent : baseEnd_1135155 < baseStart_1135155 := by decide
  rcases family_descends (prefixWord ++ tailWord_1135155) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1135162 : List Nat := [3, 1, 1, 1, 3, 3, 2, 3, 1, 1, 4]
def baseStart_1135162 : Nat := 118140960795 + 1135162 * 2 ^ 59
def prefixEnd_1135162 : Nat := 4983230072969 + 3 ^ 40 * 1135162 * 2
def baseEnd_1135162 : Nat := 582883726719192907154491

theorem tailTrace_1135162 : CollatzResearch.WordTrace tailWord_1135162 prefixEnd_1135162 582883726719192907154491 := by
  unfold tailWord_1135162
  simp only [CollatzResearch.WordTrace]
  refine ⟨10350689878377354769977935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 27601839675672946053274493 10350689878377354769977935)
  ·
    refine ⟨15526034817566032154966903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10350689878377354769977935 15526034817566032154966903)
    ·
      refine ⟨23289052226349048232450355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15526034817566032154966903 23289052226349048232450355)
      ·
        refine ⟨34933578339523572348675533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23289052226349048232450355 34933578339523572348675533)
        ·
          refine ⟨13100091877321339630753325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 34933578339523572348675533 13100091877321339630753325)
          ·
            refine ⟨4912534453995502361532497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13100091877321339630753325 4912534453995502361532497)
            ·
              refine ⟨3684400840496626771149373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4912534453995502361532497 3684400840496626771149373)
              ·
                refine ⟨1381650315186235039181015, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3684400840496626771149373 1381650315186235039181015)
                ·
                  refine ⟨2072475472779352558771523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1381650315186235039181015 2072475472779352558771523)
                  ·
                    refine ⟨3108713209169028838157285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2072475472779352558771523 3108713209169028838157285)
                    ·
                      refine ⟨582883726719192907154491, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3108713209169028838157285 582883726719192907154491)
                      ·
                        rfl

theorem cell23_1135162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 3, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 3, 2, 3, 1, 1, 4].length) (baseStart_1135162 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1135162 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1135162 prefixEnd_1135162 := by exact prefixLift 1135162
  have htrace : WordTrace (prefixWord ++ tailWord_1135162) baseStart_1135162 baseEnd_1135162 := by
    simpa [prefixWord, tailWord_1135162, baseEnd_1135162] using wordTrace_append hprefix tailTrace_1135162
  have hstable : (prefixWord ++ tailWord_1135162).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1135162).length < 2 ^ (prefixWord ++ tailWord_1135162).sum := by decide
  have hdescent : baseEnd_1135162 < baseStart_1135162 := by decide
  rcases family_descends (prefixWord ++ tailWord_1135162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1135168 : List Nat := [2, 1, 1, 2, 2, 2, 13]
def baseStart_1135168 : Nat := 118140960795 + 1135168 * 2 ^ 59
def prefixEnd_1135168 : Nat := 4983230072969 + 3 ^ 40 * 1135168 * 2
def baseEnd_1135168 : Nat := 7196133427199010909623

theorem tailTrace_1135168 : CollatzResearch.WordTrace tailWord_1135168 prefixEnd_1135168 7196133427199010909623 := by
  unfold tailWord_1135168
  simp only [CollatzResearch.WordTrace]
  refine ⟨20701489175743841052315079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27601985567658454736420105 20701489175743841052315079)
  ·
    refine ⟨31052233763615761578472619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20701489175743841052315079 31052233763615761578472619)
    ·
      refine ⟨46578350645423642367708929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31052233763615761578472619 46578350645423642367708929)
      ·
        refine ⟨34933762984067731775781697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46578350645423642367708929 34933762984067731775781697)
        ·
          refine ⟨26200322238050798831836273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34933762984067731775781697 26200322238050798831836273)
          ·
            refine ⟨19650241678538099123877205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26200322238050798831836273 19650241678538099123877205)
            ·
              refine ⟨7196133427199010909623, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 13 19650241678538099123877205 7196133427199010909623)
              ·
                rfl

theorem cell23_1135168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 13].length) (baseStart_1135168 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1135168 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1135168 prefixEnd_1135168 := by exact prefixLift 1135168
  have htrace : WordTrace (prefixWord ++ tailWord_1135168) baseStart_1135168 baseEnd_1135168 := by
    simpa [prefixWord, tailWord_1135168, baseEnd_1135168] using wordTrace_append hprefix tailTrace_1135168
  have hstable : (prefixWord ++ tailWord_1135168).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1135168).length < 2 ^ (prefixWord ++ tailWord_1135168).sum := by decide
  have hdescent : baseEnd_1135168 < baseStart_1135168 := by decide
  rcases family_descends (prefixWord ++ tailWord_1135168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1135175 : List Nat := [1, 1, 4, 1, 4, 1, 1, 2, 1, 1, 6]
def baseStart_1135175 : Nat := 118140960795 + 1135175 * 2 ^ 59
def prefixEnd_1135175 : Nat := 4983230072969 + 3 ^ 40 * 1135175 * 2
def baseEnd_1135175 : Nat := 582890401967701356291931

theorem tailTrace_1135175 : CollatzResearch.WordTrace tailWord_1135175 prefixEnd_1135175 582890401967701356291931 := by
  unfold tailWord_1135175
  simp only [CollatzResearch.WordTrace]
  refine ⟨41403233662462322300134979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27602155774974881533423319 41403233662462322300134979)
  ·
    refine ⟨62104850493693483450202469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41403233662462322300134979 62104850493693483450202469)
    ·
      refine ⟨11644659467567528146912963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 62104850493693483450202469 11644659467567528146912963)
      ·
        refine ⟨17466989201351292220369445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11644659467567528146912963 17466989201351292220369445)
        ·
          refine ⟨3275060475253367291319271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 17466989201351292220369445 3275060475253367291319271)
          ·
            refine ⟨4912590712880050936978907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3275060475253367291319271 4912590712880050936978907)
            ·
              refine ⟨7368886069320076405468361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4912590712880050936978907 7368886069320076405468361)
              ·
                refine ⟨5526664551990057304101271, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7368886069320076405468361 5526664551990057304101271)
                ·
                  refine ⟨8289996827985085956151907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5526664551990057304101271 8289996827985085956151907)
                  ·
                    refine ⟨12434995241977628934227861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8289996827985085956151907 12434995241977628934227861)
                    ·
                      refine ⟨582890401967701356291931, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 12434995241977628934227861 582890401967701356291931)
                      ·
                        rfl

theorem cell23_1135175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 1, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 1, 1, 2, 1, 1, 6].length) (baseStart_1135175 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1135175 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1135175 prefixEnd_1135175 := by exact prefixLift 1135175
  have htrace : WordTrace (prefixWord ++ tailWord_1135175) baseStart_1135175 baseEnd_1135175 := by
    simpa [prefixWord, tailWord_1135175, baseEnd_1135175] using wordTrace_append hprefix tailTrace_1135175
  have hstable : (prefixWord ++ tailWord_1135175).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1135175).length < 2 ^ (prefixWord ++ tailWord_1135175).sum := by decide
  have hdescent : baseEnd_1135175 < baseStart_1135175 := by decide
  rcases family_descends (prefixWord ++ tailWord_1135175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1135179 : List Nat := [1, 1, 1, 1, 3, 1, 7, 1, 3, 2, 2]
def baseStart_1135179 : Nat := 118140960795 + 1135179 * 2 ^ 59
def prefixEnd_1135179 : Nat := 4983230072969 + 3 ^ 40 * 1135179 * 2
def baseEnd_1135179 : Nat := 582892455890319340641913

theorem tailTrace_1135179 : CollatzResearch.WordTrace tailWord_1135179 prefixEnd_1135179 582892455890319340641913 := by
  unfold tailWord_1135179
  simp only [CollatzResearch.WordTrace]
  refine ⟨41403379554447830983280591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27602253036298553988853727 41403379554447830983280591)
  ·
    refine ⟨62105069331671746474920887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41403379554447830983280591 62105069331671746474920887)
    ·
      refine ⟨93157603997507619712381331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62105069331671746474920887 93157603997507619712381331)
      ·
        refine ⟨139736405996261429568571997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 93157603997507619712381331 139736405996261429568571997)
        ·
          refine ⟨52401152248598036088214499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 139736405996261429568571997 52401152248598036088214499)
          ·
            refine ⟨78601728372897054132321749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 52401152248598036088214499 78601728372897054132321749)
            ·
              refine ⟨1842228008739774706226291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 78601728372897054132321749 1842228008739774706226291)
              ·
                refine ⟨2763342013109662059339437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1842228008739774706226291 2763342013109662059339437)
                ·
                  refine ⟨1036253254916123272252289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2763342013109662059339437 1036253254916123272252289)
                  ·
                    refine ⟨777189941187092454189217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1036253254916123272252289 777189941187092454189217)
                    ·
                      refine ⟨582892455890319340641913, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 777189941187092454189217 582892455890319340641913)
                      ·
                        rfl

theorem cell23_1135179_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 7, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 7, 1, 3, 2, 2].length) (baseStart_1135179 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1135179 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1135179 prefixEnd_1135179 := by exact prefixLift 1135179
  have htrace : WordTrace (prefixWord ++ tailWord_1135179) baseStart_1135179 baseEnd_1135179 := by
    simpa [prefixWord, tailWord_1135179, baseEnd_1135179] using wordTrace_append hprefix tailTrace_1135179
  have hstable : (prefixWord ++ tailWord_1135179).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1135179).length < 2 ^ (prefixWord ++ tailWord_1135179).sum := by decide
  have hdescent : baseEnd_1135179 < baseStart_1135179 := by decide
  rcases family_descends (prefixWord ++ tailWord_1135179) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1135185 : List Nat := [1, 2, 2, 1, 3, 4, 2, 8]
def baseStart_1135185 : Nat := 118140960795 + 1135185 * 2 ^ 59
def prefixEnd_1135185 : Nat := 4983230072969 + 3 ^ 40 * 1135185 * 2
def baseEnd_1135185 : Nat := 21588723584231345080255

theorem tailTrace_1135185 : CollatzResearch.WordTrace tailWord_1135185 prefixEnd_1135185 21588723584231345080255 := by
  unfold tailWord_1135185
  simp only [CollatzResearch.WordTrace]
  refine ⟨41403598392426094007999009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27602398928284062671999339 41403598392426094007999009)
  ·
    refine ⟨31052698794319570505999257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41403598392426094007999009 31052698794319570505999257)
    ·
      refine ⟨23289524095739677879499443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31052698794319570505999257 23289524095739677879499443)
      ·
        refine ⟨34934286143609516819249165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23289524095739677879499443 34934286143609516819249165)
        ·
          refine ⟨13100357303853568807218437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 34934286143609516819249165 13100357303853568807218437)
          ·
            refine ⟨2456316994472544151353457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 13100357303853568807218437 2456316994472544151353457)
            ·
              refine ⟨1842237745854408113515093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2456316994472544151353457 1842237745854408113515093)
              ·
                refine ⟨21588723584231345080255, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 1842237745854408113515093 21588723584231345080255)
                ·
                  rfl

theorem cell23_1135185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 4, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 4, 2, 8].length) (baseStart_1135185 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1135185 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1135185 prefixEnd_1135185 := by exact prefixLift 1135185
  have htrace : WordTrace (prefixWord ++ tailWord_1135185) baseStart_1135185 baseEnd_1135185 := by
    simpa [prefixWord, tailWord_1135185, baseEnd_1135185] using wordTrace_append hprefix tailTrace_1135185
  have hstable : (prefixWord ++ tailWord_1135185).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1135185).length < 2 ^ (prefixWord ++ tailWord_1135185).sum := by decide
  have hdescent : baseEnd_1135185 < baseStart_1135185 := by decide
  rcases family_descends (prefixWord ++ tailWord_1135185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1135189 : List Nat := [1, 3, 2, 2, 1, 1, 6, 1, 2, 4]
def baseStart_1135189 : Nat := 118140960795 + 1135189 * 2 ^ 59
def prefixEnd_1135189 : Nat := 4983230072969 + 3 ^ 40 * 1135189 * 2
def baseEnd_1135189 : Nat := 194299196898954767172289

theorem tailTrace_1135189 : CollatzResearch.WordTrace tailWord_1135189 prefixEnd_1135189 194299196898954767172289 := by
  unfold tailWord_1135189
  simp only [CollatzResearch.WordTrace]
  refine ⟨41403744284411602691144621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27602496189607735127429747 41403744284411602691144621)
  ·
    refine ⟨15526404106654351009179233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 41403744284411602691144621 15526404106654351009179233)
    ·
      refine ⟨11644803079990763256884425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15526404106654351009179233 11644803079990763256884425)
      ·
        refine ⟨8733602309993072442663319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11644803079990763256884425 8733602309993072442663319)
        ·
          refine ⟨13100403464989608663994979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8733602309993072442663319 13100403464989608663994979)
          ·
            refine ⟨19650605197484412995992469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13100403464989608663994979 19650605197484412995992469)
            ·
              refine ⟨921122118632081859187147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 19650605197484412995992469 921122118632081859187147)
              ·
                refine ⟨1381683177948122788780721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 921122118632081859187147 1381683177948122788780721)
                ·
                  refine ⟨1036262383461092091585541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1381683177948122788780721 1036262383461092091585541)
                  ·
                    refine ⟨194299196898954767172289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1036262383461092091585541 194299196898954767172289)
                    ·
                      rfl

theorem cell23_1135189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 6, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 6, 1, 2, 4].length) (baseStart_1135189 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1135189 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1135189 prefixEnd_1135189 := by exact prefixLift 1135189
  have htrace : WordTrace (prefixWord ++ tailWord_1135189) baseStart_1135189 baseEnd_1135189 := by
    simpa [prefixWord, tailWord_1135189, baseEnd_1135189] using wordTrace_append hprefix tailTrace_1135189
  have hstable : (prefixWord ++ tailWord_1135189).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1135189).length < 2 ^ (prefixWord ++ tailWord_1135189).sum := by decide
  have hdescent : baseEnd_1135189 < baseStart_1135189 := by decide
  rcases family_descends (prefixWord ++ tailWord_1135189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1135196 : List Nat := [2, 2, 4, 1, 3, 2, 1, 2, 1, 1, 4]
def baseStart_1135196 : Nat := 118140960795 + 1135196 * 2 ^ 59
def prefixEnd_1135196 : Nat := 4983230072969 + 3 ^ 40 * 1135196 * 2
def baseEnd_1135196 : Nat := 582901185061445774129335

theorem tailTrace_1135196 : CollatzResearch.WordTrace tailWord_1135196 prefixEnd_1135196 582901185061445774129335 := by
  unfold tailWord_1135196
  simp only [CollatzResearch.WordTrace]
  refine ⟨20701999797693121443324721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27602666396924161924432961 20701999797693121443324721)
  ·
    refine ⟨15526499848269841082493541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20701999797693121443324721 15526499848269841082493541)
    ·
      refine ⟨2911218721550595202967539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 15526499848269841082493541 2911218721550595202967539)
      ·
        refine ⟨4366828082325892804451309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2911218721550595202967539 4366828082325892804451309)
        ·
          refine ⟨1637560530872209801669241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4366828082325892804451309 1637560530872209801669241)
          ·
            refine ⟨1228170398154157351251931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1637560530872209801669241 1228170398154157351251931)
            ·
              refine ⟨1842255597231236026877897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1228170398154157351251931 1842255597231236026877897)
              ·
                refine ⟨1381691697923427020158423, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1842255597231236026877897 1381691697923427020158423)
                ·
                  refine ⟨2072537546885140530237635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1381691697923427020158423 2072537546885140530237635)
                  ·
                    refine ⟨3108806320327710795356453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2072537546885140530237635 3108806320327710795356453)
                    ·
                      refine ⟨582901185061445774129335, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3108806320327710795356453 582901185061445774129335)
                      ·
                        rfl

theorem cell23_1135196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 3, 2, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 3, 2, 1, 2, 1, 1, 4].length) (baseStart_1135196 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1135196 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1135196 prefixEnd_1135196 := by exact prefixLift 1135196
  have htrace : WordTrace (prefixWord ++ tailWord_1135196) baseStart_1135196 baseEnd_1135196 := by
    simpa [prefixWord, tailWord_1135196, baseEnd_1135196] using wordTrace_append hprefix tailTrace_1135196
  have hstable : (prefixWord ++ tailWord_1135196).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1135196).length < 2 ^ (prefixWord ++ tailWord_1135196).sum := by decide
  have hdescent : baseEnd_1135196 < baseStart_1135196 := by decide
  rcases family_descends (prefixWord ++ tailWord_1135196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1135212 : List Nat := [2, 2, 1, 1, 3, 1, 2, 1, 6, 1, 3]
def baseStart_1135212 : Nat := 118140960795 + 1135212 * 2 ^ 59
def prefixEnd_1135212 : Nat := 4983230072969 + 3 ^ 40 * 1135212 * 2
def baseEnd_1135212 : Nat := 582909400751917711529261

theorem tailTrace_1135212 : CollatzResearch.WordTrace tailWord_1135212 prefixEnd_1135212 582909400751917711529261 := by
  unfold tailWord_1135212
  simp only [CollatzResearch.WordTrace]
  refine ⟨20702291581664138809615945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27603055442218851746154593 20702291581664138809615945)
  ·
    refine ⟨15526718686248104107211959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20702291581664138809615945 15526718686248104107211959)
    ·
      refine ⟨23290078029372156160817939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15526718686248104107211959 23290078029372156160817939)
      ·
        refine ⟨34935117044058234241226909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23290078029372156160817939 34935117044058234241226909)
        ·
          refine ⟨13100668891521837840460091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 34935117044058234241226909 13100668891521837840460091)
          ·
            refine ⟨19651003337282756760690137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13100668891521837840460091 19651003337282756760690137)
            ·
              refine ⟨14738252502962067570517603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19651003337282756760690137 14738252502962067570517603)
              ·
                refine ⟨22107378754443101355776405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14738252502962067570517603 22107378754443101355776405)
                ·
                  refine ⟨1036283379114520376052019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 22107378754443101355776405 1036283379114520376052019)
                  ·
                    refine ⟨1554425068671780564078029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1036283379114520376052019 1554425068671780564078029)
                    ·
                      refine ⟨582909400751917711529261, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1554425068671780564078029 582909400751917711529261)
                      ·
                        rfl

theorem cell23_1135212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 6, 1, 3].length) (baseStart_1135212 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1135212 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1135212 prefixEnd_1135212 := by exact prefixLift 1135212
  have htrace : WordTrace (prefixWord ++ tailWord_1135212) baseStart_1135212 baseEnd_1135212 := by
    simpa [prefixWord, tailWord_1135212, baseEnd_1135212] using wordTrace_append hprefix tailTrace_1135212
  have hstable : (prefixWord ++ tailWord_1135212).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1135212).length < 2 ^ (prefixWord ++ tailWord_1135212).sum := by decide
  have hdescent : baseEnd_1135212 < baseStart_1135212 := by decide
  rcases family_descends (prefixWord ++ tailWord_1135212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1135216 : List Nat := [2, 1, 1, 1, 7, 1, 3, 1, 1, 2, 3]
def baseStart_1135216 : Nat := 118140960795 + 1135216 * 2 ^ 59
def prefixEnd_1135216 : Nat := 4983230072969 + 3 ^ 40 * 1135216 * 2
def baseEnd_1135216 : Nat := 582911454674535695879243

theorem tailTrace_1135216 : CollatzResearch.WordTrace tailWord_1135216 prefixEnd_1135216 582911454674535695879243 := by
  unfold tailWord_1135216
  simp only [CollatzResearch.WordTrace]
  refine ⟨20702364527656893151188751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27603152703542524201585001 20702364527656893151188751)
  ·
    refine ⟨31053546791485339726783127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20702364527656893151188751 31053546791485339726783127)
    ·
      refine ⟨46580320187228009590174691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31053546791485339726783127 46580320187228009590174691)
      ·
        refine ⟨69870480280842014385262037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46580320187228009590174691 69870480280842014385262037)
        ·
          refine ⟨1637589381582234712154579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 69870480280842014385262037 1637589381582234712154579)
          ·
            refine ⟨2456384072373352068231869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1637589381582234712154579 2456384072373352068231869)
            ·
              refine ⟨921144027140007025586951, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2456384072373352068231869 921144027140007025586951)
              ·
                refine ⟨1381716040710010538380427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 921144027140007025586951 1381716040710010538380427)
                ·
                  refine ⟨2072574061065015807570641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1381716040710010538380427 2072574061065015807570641)
                  ·
                    refine ⟨1554430545798761855677981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2072574061065015807570641 1554430545798761855677981)
                    ·
                      refine ⟨582911454674535695879243, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1554430545798761855677981 582911454674535695879243)
                      ·
                        rfl

theorem cell23_1135216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 7, 1, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 7, 1, 3, 1, 1, 2, 3].length) (baseStart_1135216 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1135216 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1135216 prefixEnd_1135216 := by exact prefixLift 1135216
  have htrace : WordTrace (prefixWord ++ tailWord_1135216) baseStart_1135216 baseEnd_1135216 := by
    simpa [prefixWord, tailWord_1135216, baseEnd_1135216] using wordTrace_append hprefix tailTrace_1135216
  have hstable : (prefixWord ++ tailWord_1135216).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1135216).length < 2 ^ (prefixWord ++ tailWord_1135216).sum := by decide
  have hdescent : baseEnd_1135216 < baseStart_1135216 := by decide
  rcases family_descends (prefixWord ++ tailWord_1135216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1135235 : List Nat := [1, 1, 1, 3, 3, 1, 3, 1, 2, 3, 4]
def baseStart_1135235 : Nat := 118140960795 + 1135235 * 2 ^ 59
def prefixEnd_1135235 : Nat := 4983230072969 + 3 ^ 40 * 1135235 * 2
def baseEnd_1135235 : Nat := 582921210806971121541655

theorem tailTrace_1135235 : CollatzResearch.WordTrace tailWord_1135235 prefixEnd_1135235 582921210806971121541655 := by
  unfold tailWord_1135235
  simp only [CollatzResearch.WordTrace]
  refine ⟨41405422042244952547319159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27603614694829968364879439 41405422042244952547319159)
  ·
    refine ⟨62108133063367428820978739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41405422042244952547319159 62108133063367428820978739)
    ·
      refine ⟨93162199595051143231468109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62108133063367428820978739 93162199595051143231468109)
      ·
        refine ⟨34935824848144178711800541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 93162199595051143231468109 34935824848144178711800541)
        ·
          refine ⟨13100934318054067016925203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 34935824848144178711800541 13100934318054067016925203)
          ·
            refine ⟨19651401477081100525387805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13100934318054067016925203 19651401477081100525387805)
            ·
              refine ⟨7369275553905412697020427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19651401477081100525387805 7369275553905412697020427)
              ·
                refine ⟨11053913330858119045530641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7369275553905412697020427 11053913330858119045530641)
                ·
                  refine ⟨8290434998143589284147981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11053913330858119045530641 8290434998143589284147981)
                  ·
                    refine ⟨3108913124303845981555493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8290434998143589284147981 3108913124303845981555493)
                    ·
                      refine ⟨582921210806971121541655, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3108913124303845981555493 582921210806971121541655)
                      ·
                        rfl

theorem cell23_1135235_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 3, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 3, 1, 2, 3, 4].length) (baseStart_1135235 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1135235 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1135235 prefixEnd_1135235 := by exact prefixLift 1135235
  have htrace : WordTrace (prefixWord ++ tailWord_1135235) baseStart_1135235 baseEnd_1135235 := by
    simpa [prefixWord, tailWord_1135235, baseEnd_1135235] using wordTrace_append hprefix tailTrace_1135235
  have hstable : (prefixWord ++ tailWord_1135235).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1135235).length < 2 ^ (prefixWord ++ tailWord_1135235).sum := by decide
  have hdescent : baseEnd_1135235 < baseStart_1135235 := by decide
  rcases family_descends (prefixWord ++ tailWord_1135235) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1135262 : List Nat := [4, 3, 1, 1, 1, 1, 1, 2, 1, 8]
def baseStart_1135262 : Nat := 118140960795 + 1135262 * 2 ^ 59
def prefixEnd_1135262 : Nat := 4983230072969 + 3 ^ 40 * 1135262 * 2
def baseEnd_1135262 : Nat := 194311691594880838634677

theorem tailTrace_1135262 : CollatzResearch.WordTrace tailWord_1135262 prefixEnd_1135262 194311691594880838634677 := by
  unfold tailWord_1135262
  simp only [CollatzResearch.WordTrace]
  refine ⟨5175800851643392019819005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 27604271208764757439034693 5175800851643392019819005)
  ·
    refine ⟨1940925319366272007432127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5175800851643392019819005 1940925319366272007432127)
    ·
      refine ⟨2911387979049408011148191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1940925319366272007432127 2911387979049408011148191)
      ·
        refine ⟨4367081968574112016722287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2911387979049408011148191 4367081968574112016722287)
        ·
          refine ⟨6550622952861168025083431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4367081968574112016722287 6550622952861168025083431)
          ·
            refine ⟨9825934429291752037625147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6550622952861168025083431 9825934429291752037625147)
            ·
              refine ⟨14738901643937628056437721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9825934429291752037625147 14738901643937628056437721)
              ·
                refine ⟨11054176232953221042328291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14738901643937628056437721 11054176232953221042328291)
                ·
                  refine ⟨16581264349429831563492437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11054176232953221042328291 16581264349429831563492437)
                  ·
                    refine ⟨194311691594880838634677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 16581264349429831563492437 194311691594880838634677)
                    ·
                      rfl

theorem cell23_1135262_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 1, 2, 1, 8].length) (baseStart_1135262 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1135262 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1135262 prefixEnd_1135262 := by exact prefixLift 1135262
  have htrace : WordTrace (prefixWord ++ tailWord_1135262) baseStart_1135262 baseEnd_1135262 := by
    simpa [prefixWord, tailWord_1135262, baseEnd_1135262] using wordTrace_append hprefix tailTrace_1135262
  have hstable : (prefixWord ++ tailWord_1135262).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1135262).length < 2 ^ (prefixWord ++ tailWord_1135262).sum := by decide
  have hdescent : baseEnd_1135262 < baseStart_1135262 := by decide
  rcases family_descends (prefixWord ++ tailWord_1135262) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1135269 : List Nat := [1, 3, 1, 2, 1, 2, 1, 4, 4, 2, 2]
def baseStart_1135269 : Nat := 118140960795 + 1135269 * 2 ^ 59
def prefixEnd_1135269 : Nat := 4983230072969 + 3 ^ 40 * 1135269 * 2
def baseEnd_1135269 : Nat := 582938669149223988516499

theorem tailTrace_1135269 : CollatzResearch.WordTrace tailWord_1135269 prefixEnd_1135269 582938669149223988516499 := by
  unfold tailWord_1135269
  simp only [CollatzResearch.WordTrace]
  refine ⟨41406662124121776354056861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27604441416081184236037907 41406662124121776354056861)
  ·
    refine ⟨15527498296545666132771323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 41406662124121776354056861 15527498296545666132771323)
    ·
      refine ⟨23291247444818499199156985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15527498296545666132771323 23291247444818499199156985)
      ·
        refine ⟨17468435583613874399367739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23291247444818499199156985 17468435583613874399367739)
        ·
          refine ⟨26202653375420811599051609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17468435583613874399367739 26202653375420811599051609)
          ·
            refine ⟨19651990031565608699288707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26202653375420811599051609 19651990031565608699288707)
            ·
              refine ⟨29477985047348413048933061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19651990031565608699288707 29477985047348413048933061)
              ·
                refine ⟨5527122196377827446674949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 29477985047348413048933061 5527122196377827446674949)
                ·
                  refine ⟨1036335411820842646251553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5527122196377827446674949 1036335411820842646251553)
                  ·
                    refine ⟨777251558865631984688665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1036335411820842646251553 777251558865631984688665)
                    ·
                      refine ⟨582938669149223988516499, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 777251558865631984688665 582938669149223988516499)
                      ·
                        rfl

theorem cell23_1135269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 1, 4, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 1, 4, 4, 2, 2].length) (baseStart_1135269 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1135269 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1135269 prefixEnd_1135269 := by exact prefixLift 1135269
  have htrace : WordTrace (prefixWord ++ tailWord_1135269) baseStart_1135269 baseEnd_1135269 := by
    simpa [prefixWord, tailWord_1135269, baseEnd_1135269] using wordTrace_append hprefix tailTrace_1135269
  have hstable : (prefixWord ++ tailWord_1135269).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1135269).length < 2 ^ (prefixWord ++ tailWord_1135269).sum := by decide
  have hdescent : baseEnd_1135269 < baseStart_1135269 := by decide
  rcases family_descends (prefixWord ++ tailWord_1135269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1135292 : List Nat := [2, 2, 2, 3, 1, 1, 4, 1, 7]
def baseStart_1135292 : Nat := 118140960795 + 1135292 * 2 ^ 59
def prefixEnd_1135292 : Nat := 4983230072969 + 3 ^ 40 * 1135292 * 2
def baseEnd_1135292 : Nat := 64772275467141933169877

theorem tailTrace_1135292 : CollatzResearch.WordTrace tailWord_1135292 prefixEnd_1135292 64772275467141933169877 := by
  unfold tailWord_1135292
  simp only [CollatzResearch.WordTrace]
  refine ⟨20703750501519225641072065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27605000668692300854762753 20703750501519225641072065)
  ·
    refine ⟨15527812876139419230804049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20703750501519225641072065 15527812876139419230804049)
    ·
      refine ⟨11645859657104564423103037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15527812876139419230804049 11645859657104564423103037)
      ·
        refine ⟨4367197371414211658663639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11645859657104564423103037 4367197371414211658663639)
        ·
          refine ⟨6550796057121317487995459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4367197371414211658663639 6550796057121317487995459)
          ·
            refine ⟨9826194085681976231993189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6550796057121317487995459 9826194085681976231993189)
            ·
              refine ⟨1842411391065370543498723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9826194085681976231993189 1842411391065370543498723)
              ·
                refine ⟨2763617086598055815248085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1842411391065370543498723 2763617086598055815248085)
                ·
                  refine ⟨64772275467141933169877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2763617086598055815248085 64772275467141933169877)
                  ·
                    rfl

theorem cell23_1135292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 4, 1, 7].length) (baseStart_1135292 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1135292 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1135292 prefixEnd_1135292 := by exact prefixLift 1135292
  have htrace : WordTrace (prefixWord ++ tailWord_1135292) baseStart_1135292 baseEnd_1135292 := by
    simpa [prefixWord, tailWord_1135292, baseEnd_1135292] using wordTrace_append hprefix tailTrace_1135292
  have hstable : (prefixWord ++ tailWord_1135292).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1135292).length < 2 ^ (prefixWord ++ tailWord_1135292).sum := by decide
  have hdescent : baseEnd_1135292 < baseStart_1135292 := by decide
  rcases family_descends (prefixWord ++ tailWord_1135292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1135312 : List Nat := [2, 1, 1, 1, 1, 2, 1, 2, 3, 7, 2]
def baseStart_1135312 : Nat := 118140960795 + 1135312 * 2 ^ 59
def prefixEnd_1135312 : Nat := 4983230072969 + 3 ^ 40 * 1135312 * 2
def baseEnd_1135312 : Nat := 582960748817367320278801

theorem tailTrace_1135312 : CollatzResearch.WordTrace tailWord_1135312 prefixEnd_1135312 582960748817367320278801 := by
  unfold tailWord_1135312
  simp only [CollatzResearch.WordTrace]
  refine ⟨20704115231482997348936095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27605486975310663131914793 20704115231482997348936095)
  ·
    refine ⟨31056172847224496023404143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20704115231482997348936095 31056172847224496023404143)
    ·
      refine ⟨46584259270836744035106215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31056172847224496023404143 46584259270836744035106215)
      ·
        refine ⟨69876388906255116052659323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46584259270836744035106215 69876388906255116052659323)
        ·
          refine ⟨104814583359382674078988985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 69876388906255116052659323 104814583359382674078988985)
          ·
            refine ⟨78610937519537005559241739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 104814583359382674078988985 78610937519537005559241739)
            ·
              refine ⟨117916406279305508338862609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 78610937519537005559241739 117916406279305508338862609)
              ·
                refine ⟨88437304709479131254146957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 117916406279305508338862609 88437304709479131254146957)
                ·
                  refine ⟨33163989266054674220305109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 88437304709479131254146957 33163989266054674220305109)
                  ·
                    refine ⟨777280998423156427038401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 33163989266054674220305109 777280998423156427038401)
                    ·
                      refine ⟨582960748817367320278801, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 777280998423156427038401 582960748817367320278801)
                      ·
                        rfl

theorem cell23_1135312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 2, 3, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 2, 3, 7, 2].length) (baseStart_1135312 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1135312 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1135312 prefixEnd_1135312 := by exact prefixLift 1135312
  have htrace : WordTrace (prefixWord ++ tailWord_1135312) baseStart_1135312 baseEnd_1135312 := by
    simpa [prefixWord, tailWord_1135312, baseEnd_1135312] using wordTrace_append hprefix tailTrace_1135312
  have hstable : (prefixWord ++ tailWord_1135312).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1135312).length < 2 ^ (prefixWord ++ tailWord_1135312).sum := by decide
  have hdescent : baseEnd_1135312 < baseStart_1135312 := by decide
  rcases family_descends (prefixWord ++ tailWord_1135312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1135322 : List Nat := [3, 1, 1, 2, 2, 2, 2, 3, 2, 5]
def baseStart_1135322 : Nat := 118140960795 + 1135322 * 2 ^ 59
def prefixEnd_1135322 : Nat := 4983230072969 + 3 ^ 40 * 1135322 * 2
def baseEnd_1135322 : Nat := 194321961207970760384585

theorem tailTrace_1135322 : CollatzResearch.WordTrace tailWord_1135322 prefixEnd_1135322 194321961207970760384585 := by
  unfold tailWord_1135322
  simp only [CollatzResearch.WordTrace]
  refine ⟨10352148798232441601434055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 27605730128619844270490813 10352148798232441601434055)
  ·
    refine ⟨15528223197348662402151083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10352148798232441601434055 15528223197348662402151083)
    ·
      refine ⟨23292334796022993603226625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15528223197348662402151083 23292334796022993603226625)
      ·
        refine ⟨17469251097017245202419969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23292334796022993603226625 17469251097017245202419969)
        ·
          refine ⟨13101938322762933901814977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17469251097017245202419969 13101938322762933901814977)
          ·
            refine ⟨9826453742072200426361233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13101938322762933901814977 9826453742072200426361233)
            ·
              refine ⟨7369840306554150319770925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9826453742072200426361233 7369840306554150319770925)
              ·
                refine ⟨2763690114957806369914097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7369840306554150319770925 2763690114957806369914097)
                ·
                  refine ⟨2072767586218354777435573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2763690114957806369914097 2072767586218354777435573)
                  ·
                    refine ⟨194321961207970760384585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2072767586218354777435573 194321961207970760384585)
                    ·
                      rfl

theorem cell23_1135322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 2, 3, 2, 5].length) (baseStart_1135322 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1135322 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1135322 prefixEnd_1135322 := by exact prefixLift 1135322
  have htrace : WordTrace (prefixWord ++ tailWord_1135322) baseStart_1135322 baseEnd_1135322 := by
    simpa [prefixWord, tailWord_1135322, baseEnd_1135322] using wordTrace_append hprefix tailTrace_1135322
  have hstable : (prefixWord ++ tailWord_1135322).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1135322).length < 2 ^ (prefixWord ++ tailWord_1135322).sum := by decide
  have hdescent : baseEnd_1135322 < baseStart_1135322 := by decide
  rcases family_descends (prefixWord ++ tailWord_1135322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1135355 : List Nat := [1, 1, 1, 1, 1, 3, 1, 2, 3, 3, 6]
def baseStart_1135355 : Nat := 118140960795 + 1135355 * 2 ^ 59
def prefixEnd_1135355 : Nat := 4983230072969 + 3 ^ 40 * 1135355 * 2
def baseEnd_1135355 : Nat := 582982828485510652041103

theorem tailTrace_1135355 : CollatzResearch.WordTrace tailWord_1135355 prefixEnd_1135355 582982828485510652041103 := by
  unfold tailWord_1135355
  simp only [CollatzResearch.WordTrace]
  refine ⟨41409798801810213041687519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27606532534540142027791679 41409798801810213041687519)
  ·
    refine ⟨62114698202715319562531279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41409798801810213041687519 62114698202715319562531279)
    ·
      refine ⟨93172047304072979343796919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62114698202715319562531279 93172047304072979343796919)
      ·
        refine ⟨139758070956109469015695379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 93172047304072979343796919 139758070956109469015695379)
        ·
          refine ⟨209637106434164203523543069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 139758070956109469015695379 209637106434164203523543069)
          ·
            refine ⟨78613914912811576321328651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 209637106434164203523543069 78613914912811576321328651)
            ·
              refine ⟨117920872369217364481992977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 78613914912811576321328651 117920872369217364481992977)
              ·
                refine ⟨88440654276913023361494733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 117920872369217364481992977 88440654276913023361494733)
                ·
                  refine ⟨33165245353842383760560525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 88440654276913023361494733 33165245353842383760560525)
                  ·
                    refine ⟨12436967007690893910210197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 33165245353842383760560525 12436967007690893910210197)
                    ·
                      refine ⟨582982828485510652041103, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 12436967007690893910210197 582982828485510652041103)
                      ·
                        rfl

theorem cell23_1135355_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 3, 3, 6].length) (baseStart_1135355 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1135355 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1135355 prefixEnd_1135355 := by exact prefixLift 1135355
  have htrace : WordTrace (prefixWord ++ tailWord_1135355) baseStart_1135355 baseEnd_1135355 := by
    simpa [prefixWord, tailWord_1135355, baseEnd_1135355] using wordTrace_append hprefix tailTrace_1135355
  have hstable : (prefixWord ++ tailWord_1135355).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1135355).length < 2 ^ (prefixWord ++ tailWord_1135355).sum := by decide
  have hdescent : baseEnd_1135355 < baseStart_1135355 := by decide
  rcases family_descends (prefixWord ++ tailWord_1135355) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1135379 : List Nat := [1, 1, 1, 2, 1, 3, 6, 1, 2, 2, 3]
def baseStart_1135379 : Nat := 118140960795 + 1135379 * 2 ^ 59
def prefixEnd_1135379 : Nat := 4983230072969 + 3 ^ 40 * 1135379 * 2
def baseEnd_1135379 : Nat := 582995152021218558140993

theorem tailTrace_1135379 : CollatzResearch.WordTrace tailWord_1135379 prefixEnd_1135379 582995152021218558140993 := by
  unfold tailWord_1135379
  simp only [CollatzResearch.WordTrace]
  refine ⟨41410674153723265140561191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27607116102482176760374127 41410674153723265140561191)
  ·
    refine ⟨62116011230584897710841787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41410674153723265140561191 62116011230584897710841787)
    ·
      refine ⟨93174016845877346566262681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62116011230584897710841787 93174016845877346566262681)
      ·
        refine ⟨69880512634408009924697011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 93174016845877346566262681 69880512634408009924697011)
        ·
          refine ⟨104820768951612014887045517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 69880512634408009924697011 104820768951612014887045517)
          ·
            refine ⟨39307788356854505582642069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 104820768951612014887045517 39307788356854505582642069)
            ·
              refine ⟨1842552579227554949186347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 39307788356854505582642069 1842552579227554949186347)
              ·
                refine ⟨2763828868841332423779521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1842552579227554949186347 2763828868841332423779521)
                ·
                  refine ⟨2072871651630999317834641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2763828868841332423779521 2072871651630999317834641)
                  ·
                    refine ⟨1554653738723249488375981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2072871651630999317834641 1554653738723249488375981)
                    ·
                      refine ⟨582995152021218558140993, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1554653738723249488375981 582995152021218558140993)
                      ·
                        rfl

theorem cell23_1135379_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 6, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 6, 1, 2, 2, 3].length) (baseStart_1135379 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1135379 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1135379 prefixEnd_1135379 := by exact prefixLift 1135379
  have htrace : WordTrace (prefixWord ++ tailWord_1135379) baseStart_1135379 baseEnd_1135379 := by
    simpa [prefixWord, tailWord_1135379, baseEnd_1135379] using wordTrace_append hprefix tailTrace_1135379
  have hstable : (prefixWord ++ tailWord_1135379).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1135379).length < 2 ^ (prefixWord ++ tailWord_1135379).sum := by decide
  have hdescent : baseEnd_1135379 < baseStart_1135379 := by decide
  rcases family_descends (prefixWord ++ tailWord_1135379) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1135386 : List Nat := [3, 1, 1, 3, 2, 1, 2, 5, 1, 4]
def baseStart_1135386 : Nat := 118140960795 + 1135386 * 2 ^ 59
def prefixEnd_1135386 : Nat := 4983230072969 + 3 ^ 40 * 1135386 * 2
def baseEnd_1135386 : Nat := 194332915461933343584487

theorem tailTrace_1135386 : CollatzResearch.WordTrace tailWord_1135386 prefixEnd_1135386 194332915461933343584487 := by
  unfold tailWord_1135386
  simp only [CollatzResearch.WordTrace]
  refine ⟨10352732366174476334016503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 27607286309798603557377341 10352732366174476334016503)
  ·
    refine ⟨15529098549261714501024755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10352732366174476334016503 15529098549261714501024755)
    ·
      refine ⟨23293647823892571751537133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15529098549261714501024755 23293647823892571751537133)
      ·
        refine ⟨8735117933959714406826425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23293647823892571751537133 8735117933959714406826425)
        ·
          refine ⟨6551338450469785805119819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8735117933959714406826425 6551338450469785805119819)
          ·
            refine ⟨9827007675704678707679729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6551338450469785805119819 9827007675704678707679729)
            ·
              refine ⟨7370255756778509030759797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9827007675704678707679729 7370255756778509030759797)
              ·
                refine ⟨690961477197985221633731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 7370255756778509030759797 690961477197985221633731)
                ·
                  refine ⟨1036442215796977832450597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 690961477197985221633731 1036442215796977832450597)
                  ·
                    refine ⟨194332915461933343584487, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1036442215796977832450597 194332915461933343584487)
                    ·
                      rfl

theorem cell23_1135386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 2, 5, 1, 4].length) (baseStart_1135386 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1135386 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1135386 prefixEnd_1135386 := by exact prefixLift 1135386
  have htrace : WordTrace (prefixWord ++ tailWord_1135386) baseStart_1135386 baseEnd_1135386 := by
    simpa [prefixWord, tailWord_1135386, baseEnd_1135386] using wordTrace_append hprefix tailTrace_1135386
  have hstable : (prefixWord ++ tailWord_1135386).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1135386).length < 2 ^ (prefixWord ++ tailWord_1135386).sum := by decide
  have hdescent : baseEnd_1135386 < baseStart_1135386 := by decide
  rcases family_descends (prefixWord ++ tailWord_1135386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1135436 : List Nat := [2, 2, 1, 3, 3, 2, 1, 1, 1, 5, 2]
def baseStart_1135436 : Nat := 118140960795 + 1135436 * 2 ^ 59
def prefixEnd_1135436 : Nat := 4983230072969 + 3 ^ 40 * 1135436 * 2
def baseEnd_1135436 : Nat := 583024420418524835128231

theorem tailTrace_1135436 : CollatzResearch.WordTrace tailWord_1135436 prefixEnd_1135436 583024420418524835128231 := by
  unfold tailWord_1135436
  simp only [CollatzResearch.WordTrace]
  refine ⟨20706376557258381937693081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27608502076344509250257441 20706376557258381937693081)
  ·
    refine ⟨15529782417943786453269811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20706376557258381937693081 15529782417943786453269811)
    ·
      refine ⟨23294673626915679679904717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15529782417943786453269811 23294673626915679679904717)
      ·
        refine ⟨8735502610093379879964269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23294673626915679679904717 8735502610093379879964269)
        ·
          refine ⟨3275813478785017454986601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8735502610093379879964269 3275813478785017454986601)
          ·
            refine ⟨2456860109088763091239951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3275813478785017454986601 2456860109088763091239951)
            ·
              refine ⟨3685290163633144636859927, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2456860109088763091239951 3685290163633144636859927)
              ·
                refine ⟨5527935245449716955289891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3685290163633144636859927 5527935245449716955289891)
                ·
                  refine ⟨8291902868174575432934837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5527935245449716955289891 8291902868174575432934837)
                  ·
                    refine ⟨777365893891366446837641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8291902868174575432934837 777365893891366446837641)
                    ·
                      refine ⟨583024420418524835128231, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 777365893891366446837641 583024420418524835128231)
                      ·
                        rfl

theorem cell23_1135436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 2, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 2, 1, 1, 1, 5, 2].length) (baseStart_1135436 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1135436 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1135436 prefixEnd_1135436 := by exact prefixLift 1135436
  have htrace : WordTrace (prefixWord ++ tailWord_1135436) baseStart_1135436 baseEnd_1135436 := by
    simpa [prefixWord, tailWord_1135436, baseEnd_1135436] using wordTrace_append hprefix tailTrace_1135436
  have hstable : (prefixWord ++ tailWord_1135436).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1135436).length < 2 ^ (prefixWord ++ tailWord_1135436).sum := by decide
  have hdescent : baseEnd_1135436 < baseStart_1135436 := by decide
  rcases family_descends (prefixWord ++ tailWord_1135436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1135499 : List Nat := [1, 1, 1, 1, 4, 2, 2, 4, 1, 3, 3]
def baseStart_1135499 : Nat := 118140960795 + 1135499 * 2 ^ 59
def prefixEnd_1135499 : Nat := 4983230072969 + 3 ^ 40 * 1135499 * 2
def baseEnd_1135499 : Nat := 583056769699758088640441

theorem tailTrace_1135499 : CollatzResearch.WordTrace tailWord_1135499 prefixEnd_1135499 583056769699758088640441 := by
  unfold tailWord_1135499
  simp only [CollatzResearch.WordTrace]
  refine ⟨41415050913288525634929551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27610033942192350423286367 41415050913288525634929551)
  ·
    refine ⟨62122576369932788452394327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41415050913288525634929551 62122576369932788452394327)
    ·
      refine ⟨93183864554899182678591491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62122576369932788452394327 93183864554899182678591491)
      ·
        refine ⟨139775796832348774017887237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 93183864554899182678591491 139775796832348774017887237)
        ·
          refine ⟨26207961906065395128353857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 139775796832348774017887237 26207961906065395128353857)
          ·
            refine ⟨19655971429549046346265393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26207961906065395128353857 19655971429549046346265393)
            ·
              refine ⟨14741978572161784759699045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19655971429549046346265393 14741978572161784759699045)
              ·
                refine ⟨2764120982280334642443571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14741978572161784759699045 2764120982280334642443571)
                ·
                  refine ⟨4146181473420501963665357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2764120982280334642443571 4146181473420501963665357)
                  ·
                    refine ⟨1554818052532688236374509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4146181473420501963665357 1554818052532688236374509)
                    ·
                      refine ⟨583056769699758088640441, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1554818052532688236374509 583056769699758088640441)
                      ·
                        rfl

theorem cell23_1135499_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 2, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 2, 4, 1, 3, 3].length) (baseStart_1135499 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1135499 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1135499 prefixEnd_1135499 := by exact prefixLift 1135499
  have htrace : WordTrace (prefixWord ++ tailWord_1135499) baseStart_1135499 baseEnd_1135499 := by
    simpa [prefixWord, tailWord_1135499, baseEnd_1135499] using wordTrace_append hprefix tailTrace_1135499
  have hstable : (prefixWord ++ tailWord_1135499).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1135499).length < 2 ^ (prefixWord ++ tailWord_1135499).sum := by decide
  have hdescent : baseEnd_1135499 < baseStart_1135499 := by decide
  rcases family_descends (prefixWord ++ tailWord_1135499) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1135500 : List Nat := [2, 2, 1, 2, 1, 2, 5, 3, 1, 2, 2]
def baseStart_1135500 : Nat := 118140960795 + 1135500 * 2 ^ 59
def prefixEnd_1135500 : Nat := 4983230072969 + 3 ^ 40 * 1135500 * 2
def baseEnd_1135500 : Nat := 583057283180412584727937

theorem tailTrace_1135500 : CollatzResearch.WordTrace tailWord_1135500 prefixEnd_1135500 583057283180412584727937 := by
  unfold tailWord_1135500
  simp only [CollatzResearch.WordTrace]
  refine ⟨20707543693142451402857977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27610058257523268537143969 20707543693142451402857977)
  ·
    refine ⟨15530657769856838552143483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20707543693142451402857977 15530657769856838552143483)
    ·
      refine ⟨23295986654785257828215225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15530657769856838552143483 23295986654785257828215225)
      ·
        refine ⟨17471989991088943371161419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23295986654785257828215225 17471989991088943371161419)
        ·
          refine ⟨26207984986633415056742129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17471989991088943371161419 26207984986633415056742129)
          ·
            refine ⟨19655988739975061292556597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26207984986633415056742129 19655988739975061292556597)
            ·
              refine ⟨1842748944372661996177181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 19655988739975061292556597 1842748944372661996177181)
              ·
                refine ⟨691030854139748248566443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1842748944372661996177181 691030854139748248566443)
                ·
                  refine ⟨1036546281209622372849665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 691030854139748248566443 1036546281209622372849665)
                  ·
                    refine ⟨777409710907216779637249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1036546281209622372849665 777409710907216779637249)
                    ·
                      refine ⟨583057283180412584727937, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 777409710907216779637249 583057283180412584727937)
                      ·
                        rfl

theorem cell23_1135500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 5, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 5, 3, 1, 2, 2].length) (baseStart_1135500 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1135500 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1135500 prefixEnd_1135500 := by exact prefixLift 1135500
  have htrace : WordTrace (prefixWord ++ tailWord_1135500) baseStart_1135500 baseEnd_1135500 := by
    simpa [prefixWord, tailWord_1135500, baseEnd_1135500] using wordTrace_append hprefix tailTrace_1135500
  have hstable : (prefixWord ++ tailWord_1135500).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1135500).length < 2 ^ (prefixWord ++ tailWord_1135500).sum := by decide
  have hdescent : baseEnd_1135500 < baseStart_1135500 := by decide
  rcases family_descends (prefixWord ++ tailWord_1135500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1135506 : List Nat := [3, 2, 3, 2, 2, 2, 9]
def baseStart_1135506 : Nat := 118140960795 + 1135506 * 2 ^ 59
def prefixEnd_1135506 : Nat := 4983230072969 + 3 ^ 40 * 1135506 * 2
def baseEnd_1135506 : Nat := 7198276099559747669789

theorem tailTrace_1135506 : CollatzResearch.WordTrace tailWord_1135506 prefixEnd_1135506 7198276099559747669789 := by
  unfold tailWord_1135506
  simp only [CollatzResearch.WordTrace]
  refine ⟨10353826556065791457608593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 27610204149508777220289581 10353826556065791457608593)
  ·
    refine ⟨7765369917049343593206445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10353826556065791457608593 7765369917049343593206445)
    ·
      refine ⟨2912013718893503847452417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7765369917049343593206445 2912013718893503847452417)
      ·
        refine ⟨2184010289170127885589313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2912013718893503847452417 2184010289170127885589313)
        ·
          refine ⟨1638007716877595914191985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2184010289170127885589313 1638007716877595914191985)
          ·
            refine ⟨1228505787658196935643989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1638007716877595914191985 1228505787658196935643989)
            ·
              refine ⟨7198276099559747669789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 1228505787658196935643989 7198276099559747669789)
              ·
                rfl

theorem cell23_1135506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 2, 2, 9].length) (baseStart_1135506 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1135506 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1135506 prefixEnd_1135506 := by exact prefixLift 1135506
  have htrace : WordTrace (prefixWord ++ tailWord_1135506) baseStart_1135506 baseEnd_1135506 := by
    simpa [prefixWord, tailWord_1135506, baseEnd_1135506] using wordTrace_append hprefix tailTrace_1135506
  have hstable : (prefixWord ++ tailWord_1135506).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1135506).length < 2 ^ (prefixWord ++ tailWord_1135506).sum := by decide
  have hdescent : baseEnd_1135506 < baseStart_1135506 := by decide
  rcases family_descends (prefixWord ++ tailWord_1135506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1135510 : List Nat := [5, 3, 1, 1, 1, 1, 2, 1, 4, 4]
def baseStart_1135510 : Nat := 118140960795 + 1135510 * 2 ^ 59
def prefixEnd_1135510 : Nat := 4983230072969 + 3 ^ 40 * 1135510 * 2
def baseEnd_1135510 : Nat := 194354139328985848534297

theorem tailTrace_1135510 : CollatzResearch.WordTrace tailWord_1135510 prefixEnd_1135510 194354139328985848534297 := by
  unfold tailWord_1135510
  simp only [CollatzResearch.WordTrace]
  refine ⟨2588465757265542157098749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 27610301410832449675719989 2588465757265542157098749)
  ·
    refine ⟨970674658974578308912031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2588465757265542157098749 970674658974578308912031)
    ·
      refine ⟨1456011988461867463368047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 970674658974578308912031 1456011988461867463368047)
      ·
        refine ⟨2184017982692801195052071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1456011988461867463368047 2184017982692801195052071)
        ·
          refine ⟨3276026974039201792578107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2184017982692801195052071 3276026974039201792578107)
          ·
            refine ⟨4914040461058802688867161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3276026974039201792578107 4914040461058802688867161)
            ·
              refine ⟨3685530345794102016650371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4914040461058802688867161 3685530345794102016650371)
              ·
                refine ⟨5528295518691153024975557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3685530345794102016650371 5528295518691153024975557)
                ·
                  refine ⟨1036555409754591192182917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5528295518691153024975557 1036555409754591192182917)
                  ·
                    refine ⟨194354139328985848534297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1036555409754591192182917 194354139328985848534297)
                    ·
                      rfl

theorem cell23_1135510_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 1, 2, 1, 4, 4].length) (baseStart_1135510 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1135510 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1135510 prefixEnd_1135510 := by exact prefixLift 1135510
  have htrace : WordTrace (prefixWord ++ tailWord_1135510) baseStart_1135510 baseEnd_1135510 := by
    simpa [prefixWord, tailWord_1135510, baseEnd_1135510] using wordTrace_append hprefix tailTrace_1135510
  have hstable : (prefixWord ++ tailWord_1135510).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1135510).length < 2 ^ (prefixWord ++ tailWord_1135510).sum := by decide
  have hdescent : baseEnd_1135510 < baseStart_1135510 := by decide
  rcases family_descends (prefixWord ++ tailWord_1135510) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1135517 : List Nat := [1, 4, 2, 1, 2, 1, 5, 2, 1, 2, 2]
def baseStart_1135517 : Nat := 118140960795 + 1135517 * 2 ^ 59
def prefixEnd_1135517 : Nat := 4983230072969 + 3 ^ 40 * 1135517 * 2
def baseEnd_1135517 : Nat := 583066012351539018215359

theorem tailTrace_1135517 : CollatzResearch.WordTrace tailWord_1135517 prefixEnd_1135517 583066012351539018215359 := by
  unfold tailWord_1135517
  simp only [CollatzResearch.WordTrace]
  refine ⟨41415707427223314709084805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27610471618148876472723203 41415707427223314709084805)
  ·
    refine ⟨7765445142604371507953401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 41415707427223314709084805 7765445142604371507953401)
    ·
      refine ⟨5824083856953278630965051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7765445142604371507953401 5824083856953278630965051)
      ·
        refine ⟨8736125785429917946447577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5824083856953278630965051 8736125785429917946447577)
        ·
          refine ⟨6552094339072438459835683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8736125785429917946447577 6552094339072438459835683)
          ·
            refine ⟨9828141508608657689753525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6552094339072438459835683 9828141508608657689753525)
            ·
              refine ⟨921388266432061658414393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 9828141508608657689753525 921388266432061658414393)
              ·
                refine ⟨691041199824046243810795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 921388266432061658414393 691041199824046243810795)
                ·
                  refine ⟨1036561799736069365716193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 691041199824046243810795 1036561799736069365716193)
                  ·
                    refine ⟨777421349802052024287145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1036561799736069365716193 777421349802052024287145)
                    ·
                      refine ⟨583066012351539018215359, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 777421349802052024287145 583066012351539018215359)
                      ·
                        rfl

theorem cell23_1135517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 5, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 5, 2, 1, 2, 2].length) (baseStart_1135517 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1135517 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1135517 prefixEnd_1135517 := by exact prefixLift 1135517
  have htrace : WordTrace (prefixWord ++ tailWord_1135517) baseStart_1135517 baseEnd_1135517 := by
    simpa [prefixWord, tailWord_1135517, baseEnd_1135517] using wordTrace_append hprefix tailTrace_1135517
  have hstable : (prefixWord ++ tailWord_1135517).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1135517).length < 2 ^ (prefixWord ++ tailWord_1135517).sum := by decide
  have hdescent : baseEnd_1135517 < baseStart_1135517 := by decide
  rcases family_descends (prefixWord ++ tailWord_1135517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1135527 : List Nat := [1, 1, 6, 1, 4, 1, 2, 1, 2, 4]
def baseStart_1135527 : Nat := 118140960795 + 1135527 * 2 ^ 59
def prefixEnd_1135527 : Nat := 4983230072969 + 3 ^ 40 * 1135527 * 2
def baseEnd_1135527 : Nat := 194357049052694659696771

theorem tailTrace_1135527 : CollatzResearch.WordTrace tailWord_1135527 prefixEnd_1135527 194357049052694659696771 := by
  unfold tailWord_1135527
  simp only [CollatzResearch.WordTrace]
  refine ⟨41416072157187086416948835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27610714771458057611299223 41416072157187086416948835)
  ·
    refine ⟨62124108235780629625423253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41416072157187086416948835 62124108235780629625423253)
    ·
      refine ⟨2912067573552217013691715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 62124108235780629625423253 2912067573552217013691715)
      ·
        refine ⟨4368101360328325520537573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2912067573552217013691715 4368101360328325520537573)
        ·
          refine ⟨819019005061561035100795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4368101360328325520537573 819019005061561035100795)
          ·
            refine ⟨1228528507592341552651193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 819019005061561035100795 1228528507592341552651193)
            ·
              refine ⟨921396380694256164488395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1228528507592341552651193 921396380694256164488395)
              ·
                refine ⟨1382094571041384246732593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 921396380694256164488395 1382094571041384246732593)
                ·
                  refine ⟨1036570928281038185049445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1382094571041384246732593 1036570928281038185049445)
                  ·
                    refine ⟨194357049052694659696771, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1036570928281038185049445 194357049052694659696771)
                    ·
                      rfl

theorem cell23_1135527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 4, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 4, 1, 2, 1, 2, 4].length) (baseStart_1135527 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1135527 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1135527 prefixEnd_1135527 := by exact prefixLift 1135527
  have htrace : WordTrace (prefixWord ++ tailWord_1135527) baseStart_1135527 baseEnd_1135527 := by
    simpa [prefixWord, tailWord_1135527, baseEnd_1135527] using wordTrace_append hprefix tailTrace_1135527
  have hstable : (prefixWord ++ tailWord_1135527).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1135527).length < 2 ^ (prefixWord ++ tailWord_1135527).sum := by decide
  have hdescent : baseEnd_1135527 < baseStart_1135527 := by decide
  rcases family_descends (prefixWord ++ tailWord_1135527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1135543 : List Nat := [1, 1, 3, 1, 3, 1, 5, 2, 1, 3, 2]
def baseStart_1135543 : Nat := 118140960795 + 1135543 * 2 ^ 59
def prefixEnd_1135543 : Nat := 4983230072969 + 3 ^ 40 * 1135543 * 2
def baseEnd_1135543 : Nat := 583079362848555916490239

theorem tailTrace_1135543 : CollatzResearch.WordTrace tailWord_1135543 prefixEnd_1135543 583079362848555916490239 := by
  unfold tailWord_1135543
  simp only [CollatzResearch.WordTrace]
  refine ⟨41416655725129121149531283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27611103816752747433020855 41416655725129121149531283)
  ·
    refine ⟨62124983587693681724296925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41416655725129121149531283 62124983587693681724296925)
    ·
      refine ⟨23296868845385130646611347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 62124983587693681724296925 23296868845385130646611347)
      ·
        refine ⟨34945303268077695969917021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23296868845385130646611347 34945303268077695969917021)
        ·
          refine ⟨13104488725529135988718883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 34945303268077695969917021 13104488725529135988718883)
          ·
            refine ⟨19656733088293703983078325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13104488725529135988718883 19656733088293703983078325)
            ·
              refine ⟨1842818727027534748413593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 19656733088293703983078325 1842818727027534748413593)
              ·
                refine ⟨1382114045270651061310195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1842818727027534748413593 1382114045270651061310195)
                ·
                  refine ⟨2073171067905976591965293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1382114045270651061310195 2073171067905976591965293)
                  ·
                    refine ⟨777439150464741221986985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2073171067905976591965293 777439150464741221986985)
                    ·
                      refine ⟨583079362848555916490239, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 777439150464741221986985 583079362848555916490239)
                      ·
                        rfl

theorem cell23_1135543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 5, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 5, 2, 1, 3, 2].length) (baseStart_1135543 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1135543 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1135543 prefixEnd_1135543 := by exact prefixLift 1135543
  have htrace : WordTrace (prefixWord ++ tailWord_1135543) baseStart_1135543 baseEnd_1135543 := by
    simpa [prefixWord, tailWord_1135543, baseEnd_1135543] using wordTrace_append hprefix tailTrace_1135543
  have hstable : (prefixWord ++ tailWord_1135543).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1135543).length < 2 ^ (prefixWord ++ tailWord_1135543).sum := by decide
  have hdescent : baseEnd_1135543 < baseStart_1135543 := by decide
  rcases family_descends (prefixWord ++ tailWord_1135543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1135559 : List Nat := [1, 1, 4, 1, 1, 2, 4, 1, 2, 1, 5]
def baseStart_1135559 : Nat := 118140960795 + 1135559 * 2 ^ 59
def prefixEnd_1135559 : Nat := 4983230072969 + 3 ^ 40 * 1135559 * 2
def baseEnd_1135559 : Nat := 583087578539027853890165

theorem tailTrace_1135559 : CollatzResearch.WordTrace tailWord_1135559 prefixEnd_1135559 583087578539027853890165 := by
  unfold tailWord_1135559
  simp only [CollatzResearch.WordTrace]
  refine ⟨41417239293071155882113731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27611492862047437254742487 41417239293071155882113731)
  ·
    refine ⟨62125858939606733823170597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41417239293071155882113731 62125858939606733823170597)
    ·
      refine ⟨11648598551176262591844487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 62125858939606733823170597 11648598551176262591844487)
      ·
        refine ⟨17472897826764393887766731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11648598551176262591844487 17472897826764393887766731)
        ·
          refine ⟨26209346740146590831650097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17472897826764393887766731 26209346740146590831650097)
          ·
            refine ⟨19657010055109943123737573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26209346740146590831650097 19657010055109943123737573)
            ·
              refine ⟨3685689385333114335700795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 19657010055109943123737573 3685689385333114335700795)
              ·
                refine ⟨5528534077999671503551193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3685689385333114335700795 5528534077999671503551193)
                ·
                  refine ⟨4146400558499753627663395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5528534077999671503551193 4146400558499753627663395)
                  ·
                    refine ⟨6219600837749630441495093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4146400558499753627663395 6219600837749630441495093)
                    ·
                      refine ⟨583087578539027853890165, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 6219600837749630441495093 583087578539027853890165)
                      ·
                        rfl

theorem cell23_1135559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 4, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 4, 1, 2, 1, 5].length) (baseStart_1135559 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1135559 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1135559 prefixEnd_1135559 := by exact prefixLift 1135559
  have htrace : WordTrace (prefixWord ++ tailWord_1135559) baseStart_1135559 baseEnd_1135559 := by
    simpa [prefixWord, tailWord_1135559, baseEnd_1135559] using wordTrace_append hprefix tailTrace_1135559
  have hstable : (prefixWord ++ tailWord_1135559).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1135559).length < 2 ^ (prefixWord ++ tailWord_1135559).sum := by decide
  have hdescent : baseEnd_1135559 < baseStart_1135559 := by decide
  rcases family_descends (prefixWord ++ tailWord_1135559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1135569 : List Nat := [1, 2, 2, 1, 2, 1, 4, 2, 2, 2, 4]
def baseStart_1135569 : Nat := 118140960795 + 1135569 * 2 ^ 59
def prefixEnd_1135569 : Nat := 4983230072969 + 3 ^ 40 * 1135569 * 2
def baseEnd_1135569 : Nat := 583092713345572814765119

theorem tailTrace_1135569 : CollatzResearch.WordTrace tailWord_1135569 prefixEnd_1135569 583092713345572814765119 := by
  unfold tailWord_1135569
  simp only [CollatzResearch.WordTrace]
  refine ⟨41417604023034927589977761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27611736015356618393318507 41417604023034927589977761)
  ·
    refine ⟨31063203017276195692483321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41417604023034927589977761 31063203017276195692483321)
    ·
      refine ⟨23297402262957146769362491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31063203017276195692483321 23297402262957146769362491)
      ·
        refine ⟨34946103394435720154043737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23297402262957146769362491 34946103394435720154043737)
        ·
          refine ⟨26209577545826790115532803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34946103394435720154043737 26209577545826790115532803)
          ·
            refine ⟨39314366318740185173299205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26209577545826790115532803 39314366318740185173299205)
            ·
              refine ⟨7371443684763784719993601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 39314366318740185173299205 7371443684763784719993601)
              ·
                refine ⟨5528582763572838539995201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7371443684763784719993601 5528582763572838539995201)
                ·
                  refine ⟨4146437072679628904996401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5528582763572838539995201 4146437072679628904996401)
                  ·
                    refine ⟨3109827804509721678747301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4146437072679628904996401 3109827804509721678747301)
                    ·
                      refine ⟨583092713345572814765119, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3109827804509721678747301 583092713345572814765119)
                      ·
                        rfl

theorem cell23_1135569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 4, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 4, 2, 2, 2, 4].length) (baseStart_1135569 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1135569 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1135569 prefixEnd_1135569 := by exact prefixLift 1135569
  have htrace : WordTrace (prefixWord ++ tailWord_1135569) baseStart_1135569 baseEnd_1135569 := by
    simpa [prefixWord, tailWord_1135569, baseEnd_1135569] using wordTrace_append hprefix tailTrace_1135569
  have hstable : (prefixWord ++ tailWord_1135569).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1135569).length < 2 ^ (prefixWord ++ tailWord_1135569).sum := by decide
  have hdescent : baseEnd_1135569 < baseStart_1135569 := by decide
  rcases family_descends (prefixWord ++ tailWord_1135569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1135609 : List Nat := [1, 2, 1, 3, 1, 3, 3, 1, 1, 7]
def baseStart_1135609 : Nat := 118140960795 + 1135609 * 2 ^ 59
def prefixEnd_1135609 : Nat := 4983230072969 + 3 ^ 40 * 1135609 * 2
def baseEnd_1135609 : Nat := 194371084190584219421645

theorem tailTrace_1135609 : CollatzResearch.WordTrace tailWord_1135609 prefixEnd_1135609 194371084190584219421645 := by
  unfold tailWord_1135609
  simp only [CollatzResearch.WordTrace]
  refine ⟨41419062942890014421433881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27612708628593342947622587 41419062942890014421433881)
  ·
    refine ⟨31064297207167510816075411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41419062942890014421433881 31064297207167510816075411)
    ·
      refine ⟨46596445810751266224113117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31064297207167510816075411 46596445810751266224113117)
      ·
        refine ⟨17473667179031724834042419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 46596445810751266224113117 17473667179031724834042419)
        ·
          refine ⟨26210500768547587251063629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17473667179031724834042419 26210500768547587251063629)
          ·
            refine ⟨9828937788205345219148861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 26210500768547587251063629 9828937788205345219148861)
            ·
              refine ⟨3685851670577004457180823, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9828937788205345219148861 3685851670577004457180823)
              ·
                refine ⟨5528777505865506685771235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3685851670577004457180823 5528777505865506685771235)
                ·
                  refine ⟨8293166258798260028656853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5528777505865506685771235 8293166258798260028656853)
                  ·
                    refine ⟨194371084190584219421645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 8293166258798260028656853 194371084190584219421645)
                    ·
                      rfl

theorem cell23_1135609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 3, 1, 1, 7].length) (baseStart_1135609 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1135609 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1135609 prefixEnd_1135609 := by exact prefixLift 1135609
  have htrace : WordTrace (prefixWord ++ tailWord_1135609) baseStart_1135609 baseEnd_1135609 := by
    simpa [prefixWord, tailWord_1135609, baseEnd_1135609] using wordTrace_append hprefix tailTrace_1135609
  have hstable : (prefixWord ++ tailWord_1135609).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1135609).length < 2 ^ (prefixWord ++ tailWord_1135609).sum := by decide
  have hdescent : baseEnd_1135609 < baseStart_1135609 := by decide
  rcases family_descends (prefixWord ++ tailWord_1135609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1135659 : List Nat := [1, 1, 1, 1, 2, 1, 5, 1, 2, 4, 4]
def baseStart_1135659 : Nat := 118140960795 + 1135659 * 2 ^ 59
def prefixEnd_1135659 : Nat := 4983230072969 + 3 ^ 40 * 1135659 * 2
def baseEnd_1135659 : Nat := 583138926604477462639705

theorem tailTrace_1135659 : CollatzResearch.WordTrace tailWord_1135659 prefixEnd_1135659 583138926604477462639705 := by
  unfold tailWord_1135659
  simp only [CollatzResearch.WordTrace]
  refine ⟨41420886592708872960754031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27613924395139248640502687 41420886592708872960754031)
  ·
    refine ⟨62131329889063309441131047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41420886592708872960754031 62131329889063309441131047)
    ·
      refine ⟨93196994833594964161696571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62131329889063309441131047 93196994833594964161696571)
      ·
        refine ⟨139795492250392446242544857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 93196994833594964161696571 139795492250392446242544857)
        ·
          refine ⟨104846619187794334681908643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 139795492250392446242544857 104846619187794334681908643)
          ·
            refine ⟨157269928781691502022862965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 104846619187794334681908643 157269928781691502022862965)
            ·
              refine ⟨14744055823283578314643403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 157269928781691502022862965 14744055823283578314643403)
              ·
                refine ⟨22116083734925367471965105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14744055823283578314643403 22116083734925367471965105)
                ·
                  refine ⟨16587062801194025603973829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22116083734925367471965105 16587062801194025603973829)
                  ·
                    refine ⟨3110074275223879800745093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16587062801194025603973829 3110074275223879800745093)
                    ·
                      refine ⟨583138926604477462639705, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3110074275223879800745093 583138926604477462639705)
                      ·
                        rfl

theorem cell23_1135659_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 5, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 5, 1, 2, 4, 4].length) (baseStart_1135659 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1135659 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1135659 prefixEnd_1135659 := by exact prefixLift 1135659
  have htrace : WordTrace (prefixWord ++ tailWord_1135659) baseStart_1135659 baseEnd_1135659 := by
    simpa [prefixWord, tailWord_1135659, baseEnd_1135659] using wordTrace_append hprefix tailTrace_1135659
  have hstable : (prefixWord ++ tailWord_1135659).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1135659).length < 2 ^ (prefixWord ++ tailWord_1135659).sum := by decide
  have hdescent : baseEnd_1135659 < baseStart_1135659 := by decide
  rcases family_descends (prefixWord ++ tailWord_1135659) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1135666 : List Nat := [3, 2, 1, 1, 2, 2, 1, 3, 1, 4, 3]
def baseStart_1135666 : Nat := 118140960795 + 1135666 * 2 ^ 59
def prefixEnd_1135666 : Nat := 4983230072969 + 3 ^ 40 * 1135666 * 2
def baseEnd_1135666 : Nat := 583142520969058935252173

theorem tailTrace_1135666 : CollatzResearch.WordTrace tailWord_1135666 prefixEnd_1135666 583142520969058935252173 := by
  unfold tailWord_1135666
  simp only [CollatzResearch.WordTrace]
  refine ⟨10355285475920878289064713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 27614094602455675437505901 10355285475920878289064713)
  ·
    refine ⟨7766464106940658716798535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10355285475920878289064713 7766464106940658716798535)
    ·
      refine ⟨11649696160410988075197803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7766464106940658716798535 11649696160410988075197803)
      ·
        refine ⟨17474544240616482112796705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11649696160410988075197803 17474544240616482112796705)
        ·
          refine ⟨13105908180462361584597529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17474544240616482112796705 13105908180462361584597529)
          ·
            refine ⟨9829431135346771188448147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13105908180462361584597529 9829431135346771188448147)
            ·
              refine ⟨14744146703020156782672221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9829431135346771188448147 14744146703020156782672221)
              ·
                refine ⟨5529055013632558793502083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14744146703020156782672221 5529055013632558793502083)
                ·
                  refine ⟨8293582520448838190253125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5529055013632558793502083 8293582520448838190253125)
                  ·
                    refine ⟨1555046722584157160672461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 8293582520448838190253125 1555046722584157160672461)
                    ·
                      refine ⟨583142520969058935252173, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1555046722584157160672461 583142520969058935252173)
                      ·
                        rfl

theorem cell23_1135666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 1, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 1, 3, 1, 4, 3].length) (baseStart_1135666 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1135666 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1135666 prefixEnd_1135666 := by exact prefixLift 1135666
  have htrace : WordTrace (prefixWord ++ tailWord_1135666) baseStart_1135666 baseEnd_1135666 := by
    simpa [prefixWord, tailWord_1135666, baseEnd_1135666] using wordTrace_append hprefix tailTrace_1135666
  have hstable : (prefixWord ++ tailWord_1135666).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1135666).length < 2 ^ (prefixWord ++ tailWord_1135666).sum := by decide
  have hdescent : baseEnd_1135666 < baseStart_1135666 := by decide
  rcases family_descends (prefixWord ++ tailWord_1135666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1135689 : List Nat := [1, 2, 1, 1, 2, 2, 2, 3, 1, 2, 6]
def baseStart_1135689 : Nat := 118140960795 + 1135689 * 2 ^ 59
def prefixEnd_1135689 : Nat := 4983230072969 + 3 ^ 40 * 1135689 * 2
def baseEnd_1135689 : Nat := 583154331024112345264567

theorem tailTrace_1135689 : CollatzResearch.WordTrace tailWord_1135689 prefixEnd_1135689 583154331024112345264567 := by
  unfold tailWord_1135689
  simp only [CollatzResearch.WordTrace]
  refine ⟨41421980782600188084346121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27614653855066792056230747 41421980782600188084346121)
  ·
    refine ⟨31066485586950141063259591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41421980782600188084346121 31066485586950141063259591)
    ·
      refine ⟨46599728380425211594889387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31066485586950141063259591 46599728380425211594889387)
      ·
        refine ⟨69899592570637817392334081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46599728380425211594889387 69899592570637817392334081)
        ·
          refine ⟨52424694427978363044250561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 69899592570637817392334081 52424694427978363044250561)
          ·
            refine ⟨39318520820983772283187921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 52424694427978363044250561 39318520820983772283187921)
            ·
              refine ⟨29488890615737829212390941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 39318520820983772283187921 29488890615737829212390941)
              ·
                refine ⟨11058333980901685954646603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 29488890615737829212390941 11058333980901685954646603)
                ·
                  refine ⟨16587500971352528931969905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11058333980901685954646603 16587500971352528931969905)
                  ·
                    refine ⟨12440625728514396698977429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 16587500971352528931969905 12440625728514396698977429)
                    ·
                      refine ⟨583154331024112345264567, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 12440625728514396698977429 583154331024112345264567)
                      ·
                        rfl

theorem cell23_1135689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 2, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 2, 3, 1, 2, 6].length) (baseStart_1135689 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1135689 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1135689 prefixEnd_1135689 := by exact prefixLift 1135689
  have htrace : WordTrace (prefixWord ++ tailWord_1135689) baseStart_1135689 baseEnd_1135689 := by
    simpa [prefixWord, tailWord_1135689, baseEnd_1135689] using wordTrace_append hprefix tailTrace_1135689
  have hstable : (prefixWord ++ tailWord_1135689).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1135689).length < 2 ^ (prefixWord ++ tailWord_1135689).sum := by decide
  have hdescent : baseEnd_1135689 < baseStart_1135689 := by decide
  rcases family_descends (prefixWord ++ tailWord_1135689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1135713 : List Nat := [1, 2, 3, 1, 1, 2, 2, 4, 3, 1, 3]
def baseStart_1135713 : Nat := 118140960795 + 1135713 * 2 ^ 59
def prefixEnd_1135713 : Nat := 4983230072969 + 3 ^ 40 * 1135713 * 2
def baseEnd_1135713 : Nat := 583166654559820251364457

theorem tailTrace_1135713 : CollatzResearch.WordTrace tailWord_1135713 prefixEnd_1135713 583166654559820251364457 := by
  unfold tailWord_1135713
  simp only [CollatzResearch.WordTrace]
  refine ⟨41422856134513240183219793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27615237423008826788813195 41422856134513240183219793)
  ·
    refine ⟨31067142100884930137414845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41422856134513240183219793 31067142100884930137414845)
    ·
      refine ⟨11650178287831848801530567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 31067142100884930137414845 11650178287831848801530567)
      ·
        refine ⟨17475267431747773202295851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11650178287831848801530567 17475267431747773202295851)
        ·
          refine ⟨26212901147621659803443777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17475267431747773202295851 26212901147621659803443777)
          ·
            refine ⟨19659675860716244852582833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26212901147621659803443777 19659675860716244852582833)
            ·
              refine ⟨14744756895537183639437125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19659675860716244852582833 14744756895537183639437125)
              ·
                refine ⟨2764641917913221932394461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14744756895537183639437125 2764641917913221932394461)
                ·
                  refine ⟨1036740719217458224647923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2764641917913221932394461 1036740719217458224647923)
                  ·
                    refine ⟨1555111078826187336971885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1036740719217458224647923 1555111078826187336971885)
                    ·
                      refine ⟨583166654559820251364457, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1555111078826187336971885 583166654559820251364457)
                      ·
                        rfl

theorem cell23_1135713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 2, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 2, 4, 3, 1, 3].length) (baseStart_1135713 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1135713 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1135713 prefixEnd_1135713 := by exact prefixLift 1135713
  have htrace : WordTrace (prefixWord ++ tailWord_1135713) baseStart_1135713 baseEnd_1135713 := by
    simpa [prefixWord, tailWord_1135713, baseEnd_1135713] using wordTrace_append hprefix tailTrace_1135713
  have hstable : (prefixWord ++ tailWord_1135713).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1135713).length < 2 ^ (prefixWord ++ tailWord_1135713).sum := by decide
  have hdescent : baseEnd_1135713 < baseStart_1135713 := by decide
  rcases family_descends (prefixWord ++ tailWord_1135713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1135756 : List Nat := [2, 2, 1, 2, 1, 1, 1, 6, 1, 1, 5]
def baseStart_1135756 : Nat := 118140960795 + 1135756 * 2 ^ 59
def prefixEnd_1135756 : Nat := 4983230072969 + 3 ^ 40 * 1135756 * 2
def baseEnd_1135756 : Nat := 583188734227963583126759

theorem tailTrace_1135756 : CollatzResearch.WordTrace tailWord_1135756 prefixEnd_1135756 583188734227963583126759 := by
  unfold tailWord_1135756
  simp only [CollatzResearch.WordTrace]
  refine ⟨20712212236678729263517561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27616282982238305684690081 20712212236678729263517561)
  ·
    refine ⟨15534159177509046947638171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20712212236678729263517561 15534159177509046947638171)
    ·
      refine ⟨23301238766263570421457257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15534159177509046947638171 23301238766263570421457257)
      ·
        refine ⟨17475929074697677816092943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23301238766263570421457257 17475929074697677816092943)
        ·
          refine ⟨26213893612046516724139415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17475929074697677816092943 26213893612046516724139415)
          ·
            refine ⟨39320840418069775086209123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26213893612046516724139415 39320840418069775086209123)
            ·
              refine ⟨58981260627104662629313685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39320840418069775086209123 58981260627104662629313685)
              ·
                refine ⟨2764746591895531060749079, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 58981260627104662629313685 2764746591895531060749079)
                ·
                  refine ⟨4147119887843296591123619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2764746591895531060749079 4147119887843296591123619)
                  ·
                    refine ⟨6220679831764944886685429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4147119887843296591123619 6220679831764944886685429)
                    ·
                      refine ⟨583188734227963583126759, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 6220679831764944886685429 583188734227963583126759)
                      ·
                        rfl

theorem cell23_1135756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 1, 6, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 1, 6, 1, 1, 5].length) (baseStart_1135756 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1135756 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1135756 prefixEnd_1135756 := by exact prefixLift 1135756
  have htrace : WordTrace (prefixWord ++ tailWord_1135756) baseStart_1135756 baseEnd_1135756 := by
    simpa [prefixWord, tailWord_1135756, baseEnd_1135756] using wordTrace_append hprefix tailTrace_1135756
  have hstable : (prefixWord ++ tailWord_1135756).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1135756).length < 2 ^ (prefixWord ++ tailWord_1135756).sum := by decide
  have hdescent : baseEnd_1135756 < baseStart_1135756 := by decide
  rcases family_descends (prefixWord ++ tailWord_1135756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1135763 : List Nat := [1, 1, 1, 2, 1, 2, 6, 3, 2, 4]
def baseStart_1135763 : Nat := 118140960795 + 1135763 * 2 ^ 59
def prefixEnd_1135763 : Nat := 4983230072969 + 3 ^ 40 * 1135763 * 2
def baseEnd_1135763 : Nat := 194397442864181685246409

theorem tailTrace_1135763 : CollatzResearch.WordTrace tailWord_1135763 prefixEnd_1135763 194397442864181685246409 := by
  unfold tailWord_1135763
  simp only [CollatzResearch.WordTrace]
  refine ⟨41424679784332098722539943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27616453189554732481693295 41424679784332098722539943)
  ·
    refine ⟨62137019676498148083809915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41424679784332098722539943 62137019676498148083809915)
    ·
      refine ⟨93205529514747222125714873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62137019676498148083809915 93205529514747222125714873)
      ·
        refine ⟨69904147136060416594286155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 93205529514747222125714873 69904147136060416594286155)
        ·
          refine ⟨104856220704090624891429233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 69904147136060416594286155 104856220704090624891429233)
          ·
            refine ⟨78642165528067968668571925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 104856220704090624891429233 78642165528067968668571925)
            ·
              refine ⟨3686351509128186031339309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 78642165528067968668571925 3686351509128186031339309)
              ·
                refine ⟨1382381815923069761752241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3686351509128186031339309 1382381815923069761752241)
                ·
                  refine ⟨1036786361942302321314181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1382381815923069761752241 1036786361942302321314181)
                  ·
                    refine ⟨194397442864181685246409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1036786361942302321314181 194397442864181685246409)
                    ·
                      rfl

theorem cell23_1135763_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 6, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 6, 3, 2, 4].length) (baseStart_1135763 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1135763 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1135763 prefixEnd_1135763 := by exact prefixLift 1135763
  have htrace : WordTrace (prefixWord ++ tailWord_1135763) baseStart_1135763 baseEnd_1135763 := by
    simpa [prefixWord, tailWord_1135763, baseEnd_1135763] using wordTrace_append hprefix tailTrace_1135763
  have hstable : (prefixWord ++ tailWord_1135763).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1135763).length < 2 ^ (prefixWord ++ tailWord_1135763).sum := by decide
  have hdescent : baseEnd_1135763 < baseStart_1135763 := by decide
  rcases family_descends (prefixWord ++ tailWord_1135763) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1135773 : List Nat := [1, 4, 2, 1, 1, 2, 1, 3, 3, 2, 3]
def baseStart_1135773 : Nat := 118140960795 + 1135773 * 2 ^ 59
def prefixEnd_1135773 : Nat := 4983230072969 + 3 ^ 40 * 1135773 * 2
def baseEnd_1135773 : Nat := 583197463399090016614181

theorem tailTrace_1135773 : CollatzResearch.WordTrace tailWord_1135773 prefixEnd_1135773 583197463399090016614181 := by
  unfold tailWord_1135773
  simp only [CollatzResearch.WordTrace]
  refine ⟨41425044514295870430403973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27616696342863913620269315 41425044514295870430403973)
  ·
    refine ⟨7767195846430475705700745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 41425044514295870430403973 7767195846430475705700745)
    ·
      refine ⟨5825396884822856779275559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7767195846430475705700745 5825396884822856779275559)
      ·
        refine ⟨8738095327234285168913339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5825396884822856779275559 8738095327234285168913339)
        ·
          refine ⟨13107142990851427753370009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8738095327234285168913339 13107142990851427753370009)
          ·
            refine ⟨9830357243138570815027507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13107142990851427753370009 9830357243138570815027507)
            ·
              refine ⟨14745535864707856222541261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9830357243138570815027507 14745535864707856222541261)
              ·
                refine ⟨5529575949265446083452973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14745535864707856222541261 5529575949265446083452973)
                ·
                  refine ⟨2073590980974542281294865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5529575949265446083452973 2073590980974542281294865)
                  ·
                    refine ⟨1555193235730906710971149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2073590980974542281294865 1555193235730906710971149)
                    ·
                      refine ⟨583197463399090016614181, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1555193235730906710971149 583197463399090016614181)
                      ·
                        rfl

theorem cell23_1135773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 1, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 1, 3, 3, 2, 3].length) (baseStart_1135773 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1135773 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1135773 prefixEnd_1135773 := by exact prefixLift 1135773
  have htrace : WordTrace (prefixWord ++ tailWord_1135773) baseStart_1135773 baseEnd_1135773 := by
    simpa [prefixWord, tailWord_1135773, baseEnd_1135773] using wordTrace_append hprefix tailTrace_1135773
  have hstable : (prefixWord ++ tailWord_1135773).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1135773).length < 2 ^ (prefixWord ++ tailWord_1135773).sum := by decide
  have hdescent : baseEnd_1135773 < baseStart_1135773 := by decide
  rcases family_descends (prefixWord ++ tailWord_1135773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1135774 : List Nat := [4, 3, 1, 1, 2, 3, 1, 1, 2, 3, 2]
def baseStart_1135774 : Nat := 118140960795 + 1135774 * 2 ^ 59
def prefixEnd_1135774 : Nat := 4983230072969 + 3 ^ 40 * 1135774 * 2
def baseEnd_1135774 : Nat := 583197976879744512701677

theorem tailTrace_1135774 : CollatzResearch.WordTrace tailWord_1135774 prefixEnd_1135774 583197976879744512701677 := by
  unfold tailWord_1135774
  simp only [CollatzResearch.WordTrace]
  refine ⟨5178135123411530950148797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 27616720658194831734126917 5178135123411530950148797)
  ·
    refine ⟨1941800671279324106305799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5178135123411530950148797 1941800671279324106305799)
    ·
      refine ⟨2912701006918986159458699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1941800671279324106305799 2912701006918986159458699)
      ·
        refine ⟨4369051510378479239188049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2912701006918986159458699 4369051510378479239188049)
        ·
          refine ⟨3276788632783859429391037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4369051510378479239188049 3276788632783859429391037)
          ·
            refine ⟨1228795737293947286021639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3276788632783859429391037 1228795737293947286021639)
            ·
              refine ⟨1843193605940920929032459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1228795737293947286021639 1843193605940920929032459)
              ·
                refine ⟨2764790408911381393548689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1843193605940920929032459 2764790408911381393548689)
                ·
                  refine ⟨2073592806683536045161517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2764790408911381393548689 2073592806683536045161517)
                  ·
                    refine ⟨777597302506326016935569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2073592806683536045161517 777597302506326016935569)
                    ·
                      refine ⟨583197976879744512701677, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 777597302506326016935569 583197976879744512701677)
                      ·
                        rfl

theorem cell23_1135774_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 3, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 3, 1, 1, 2, 3, 2].length) (baseStart_1135774 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1135774 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1135774 prefixEnd_1135774 := by exact prefixLift 1135774
  have htrace : WordTrace (prefixWord ++ tailWord_1135774) baseStart_1135774 baseEnd_1135774 := by
    simpa [prefixWord, tailWord_1135774, baseEnd_1135774] using wordTrace_append hprefix tailTrace_1135774
  have hstable : (prefixWord ++ tailWord_1135774).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1135774).length < 2 ^ (prefixWord ++ tailWord_1135774).sum := by decide
  have hdescent : baseEnd_1135774 < baseStart_1135774 := by decide
  rcases family_descends (prefixWord ++ tailWord_1135774) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1135804 : List Nat := [2, 2, 2, 3, 2, 1, 2, 4, 1, 2, 2]
def baseStart_1135804 : Nat := 118140960795 + 1135804 * 2 ^ 59
def prefixEnd_1135804 : Nat := 4983230072969 + 3 ^ 40 * 1135804 * 2
def baseEnd_1135804 : Nat := 583213381299379395326539

theorem tailTrace_1135804 : CollatzResearch.WordTrace tailWord_1135804 prefixEnd_1135804 583213381299379395326539 := by
  unfold tailWord_1135804
  simp only [CollatzResearch.WordTrace]
  refine ⟨20713087588591781362391233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27617450118122375149854977 20713087588591781362391233)
  ·
    refine ⟨15534815691443836021793425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20713087588591781362391233 15534815691443836021793425)
    ·
      refine ⟨11651111768582877016345069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15534815691443836021793425 11651111768582877016345069)
      ·
        refine ⟨4369166913218578881129401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11651111768582877016345069 4369166913218578881129401)
        ·
          refine ⟨3276875184913934160847051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4369166913218578881129401 3276875184913934160847051)
          ·
            refine ⟨4915312777370901241270577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3276875184913934160847051 4915312777370901241270577)
            ·
              refine ⟨3686484583028175930952933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4915312777370901241270577 3686484583028175930952933)
              ·
                refine ⟨691215859317782987053675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3686484583028175930952933 691215859317782987053675)
                ·
                  refine ⟨1036823788976674480580513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 691215859317782987053675 1036823788976674480580513)
                  ·
                    refine ⟨777617841732505860435385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1036823788976674480580513 777617841732505860435385)
                    ·
                      refine ⟨583213381299379395326539, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 777617841732505860435385 583213381299379395326539)
                      ·
                        rfl

theorem cell23_1135804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 1, 2, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 1, 2, 4, 1, 2, 2].length) (baseStart_1135804 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1135804 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1135804 prefixEnd_1135804 := by exact prefixLift 1135804
  have htrace : WordTrace (prefixWord ++ tailWord_1135804) baseStart_1135804 baseEnd_1135804 := by
    simpa [prefixWord, tailWord_1135804, baseEnd_1135804] using wordTrace_append hprefix tailTrace_1135804
  have hstable : (prefixWord ++ tailWord_1135804).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1135804).length < 2 ^ (prefixWord ++ tailWord_1135804).sum := by decide
  have hdescent : baseEnd_1135804 < baseStart_1135804 := by decide
  rcases family_descends (prefixWord ++ tailWord_1135804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1135877 : List Nat := [1, 3, 1, 1, 2, 1, 5, 3, 2, 2, 2]
def baseStart_1135877 : Nat := 118140960795 + 1135877 * 2 ^ 59
def prefixEnd_1135877 : Nat := 4983230072969 + 3 ^ 40 * 1135877 * 2
def baseEnd_1135877 : Nat := 583250865387157609713703

theorem tailTrace_1135877 : CollatzResearch.WordTrace tailWord_1135877 prefixEnd_1135877 583250865387157609713703 := by
  unfold tailWord_1135877
  simp only [CollatzResearch.WordTrace]
  refine ⟨41428837705919096192189885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27619225137279397461459923 41428837705919096192189885)
  ·
    refine ⟨15535814139719661072071207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 41428837705919096192189885 15535814139719661072071207)
    ·
      refine ⟨23303721209579491608106811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15535814139719661072071207 23303721209579491608106811)
      ·
        refine ⟨34955581814369237412160217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23303721209579491608106811 34955581814369237412160217)
        ·
          refine ⟨26216686360776928059120163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34955581814369237412160217 26216686360776928059120163)
          ·
            refine ⟨39325029541165392088680245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26216686360776928059120163 39325029541165392088680245)
            ·
              refine ⟨3686721519484255508313773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 39325029541165392088680245 3686721519484255508313773)
              ·
                refine ⟨1382520569806595815617665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3686721519484255508313773 1382520569806595815617665)
                ·
                  refine ⟨1036890427354946861713249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1382520569806595815617665 1036890427354946861713249)
                  ·
                    refine ⟨777667820516210146284937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1036890427354946861713249 777667820516210146284937)
                    ·
                      refine ⟨583250865387157609713703, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 777667820516210146284937 583250865387157609713703)
                      ·
                        rfl

theorem cell23_1135877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 5, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 5, 3, 2, 2, 2].length) (baseStart_1135877 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1135877 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1135877 prefixEnd_1135877 := by exact prefixLift 1135877
  have htrace : WordTrace (prefixWord ++ tailWord_1135877) baseStart_1135877 baseEnd_1135877 := by
    simpa [prefixWord, tailWord_1135877, baseEnd_1135877] using wordTrace_append hprefix tailTrace_1135877
  have hstable : (prefixWord ++ tailWord_1135877).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1135877).length < 2 ^ (prefixWord ++ tailWord_1135877).sum := by decide
  have hdescent : baseEnd_1135877 < baseStart_1135877 := by decide
  rcases family_descends (prefixWord ++ tailWord_1135877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1135893 : List Nat := [1, 3, 2, 1, 2, 1, 1, 2, 4, 3, 3]
def baseStart_1135893 : Nat := 118140960795 + 1135893 * 2 ^ 59
def prefixEnd_1135893 : Nat := 4983230072969 + 3 ^ 40 * 1135893 * 2
def baseEnd_1135893 : Nat := 583259081077629547113629

theorem tailTrace_1135893 : CollatzResearch.WordTrace tailWord_1135893 prefixEnd_1135893 583259081077629547113629 := by
  unfold tailWord_1135893
  simp only [CollatzResearch.WordTrace]
  refine ⟨41429421273861130924772333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27619614182574087283181555 41429421273861130924772333)
  ·
    refine ⟨15536032977697924096789625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 41429421273861130924772333 15536032977697924096789625)
    ·
      refine ⟨11652024733273443072592219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15536032977697924096789625 11652024733273443072592219)
      ·
        refine ⟨17478037099910164608888329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11652024733273443072592219 17478037099910164608888329)
        ·
          refine ⟨13108527824932623456666247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17478037099910164608888329 13108527824932623456666247)
          ·
            refine ⟨19662791737398935184999371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13108527824932623456666247 19662791737398935184999371)
            ·
              refine ⟨29494187606098402777499057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19662791737398935184999371 29494187606098402777499057)
              ·
                refine ⟨22120640704573802083124293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29494187606098402777499057 22120640704573802083124293)
                ·
                  refine ⟨4147620132107587890585805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 22120640704573802083124293 4147620132107587890585805)
                  ·
                    refine ⟨1555357549540345458969677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4147620132107587890585805 1555357549540345458969677)
                    ·
                      refine ⟨583259081077629547113629, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1555357549540345458969677 583259081077629547113629)
                      ·
                        rfl

theorem cell23_1135893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 1, 2, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 1, 2, 4, 3, 3].length) (baseStart_1135893 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1135893 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1135893 prefixEnd_1135893 := by exact prefixLift 1135893
  have htrace : WordTrace (prefixWord ++ tailWord_1135893) baseStart_1135893 baseEnd_1135893 := by
    simpa [prefixWord, tailWord_1135893, baseEnd_1135893] using wordTrace_append hprefix tailTrace_1135893
  have hstable : (prefixWord ++ tailWord_1135893).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1135893).length < 2 ^ (prefixWord ++ tailWord_1135893).sum := by decide
  have hdescent : baseEnd_1135893 < baseStart_1135893 := by decide
  rcases family_descends (prefixWord ++ tailWord_1135893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1135923 : List Nat := [1, 1, 1, 2, 5, 2, 2, 1, 1, 2, 5]
def baseStart_1135923 : Nat := 118140960795 + 1135923 * 2 ^ 59
def prefixEnd_1135923 : Nat := 4983230072969 + 3 ^ 40 * 1135923 * 2
def baseEnd_1135923 : Nat := 583274485497264429738491

theorem tailTrace_1135923 : CollatzResearch.WordTrace tailWord_1135923 prefixEnd_1135923 583274485497264429738491 := by
  unfold tailWord_1135923
  simp only [CollatzResearch.WordTrace]
  refine ⟨41430515463752446048364423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27620343642501630698909615 41430515463752446048364423)
  ·
    refine ⟨62145773195628669072546635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41430515463752446048364423 62145773195628669072546635)
    ·
      refine ⟨93218659793443003608819953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62145773195628669072546635 93218659793443003608819953)
      ·
        refine ⟨69913994845082252706614965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 93218659793443003608819953 69913994845082252706614965)
        ·
          refine ⟨6554437016726461191245153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 69913994845082252706614965 6554437016726461191245153)
          ·
            refine ⟨4915827762544845893433865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6554437016726461191245153 4915827762544845893433865)
            ·
              refine ⟨3686870821908634420075399, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4915827762544845893433865 3686870821908634420075399)
              ·
                refine ⟨5530306232862951630113099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3686870821908634420075399 5530306232862951630113099)
                ·
                  refine ⟨8295459349294427445169649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5530306232862951630113099 8295459349294427445169649)
                  ·
                    refine ⟨6221594511970820583877237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8295459349294427445169649 6221594511970820583877237)
                    ·
                      refine ⟨583274485497264429738491, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 6221594511970820583877237 583274485497264429738491)
                      ·
                        rfl

theorem cell23_1135923_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 2, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 2, 2, 1, 1, 2, 5].length) (baseStart_1135923 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1135923 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1135923 prefixEnd_1135923 := by exact prefixLift 1135923
  have htrace : WordTrace (prefixWord ++ tailWord_1135923) baseStart_1135923 baseEnd_1135923 := by
    simpa [prefixWord, tailWord_1135923, baseEnd_1135923] using wordTrace_append hprefix tailTrace_1135923
  have hstable : (prefixWord ++ tailWord_1135923).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1135923).length < 2 ^ (prefixWord ++ tailWord_1135923).sum := by decide
  have hdescent : baseEnd_1135923 < baseStart_1135923 := by decide
  rcases family_descends (prefixWord ++ tailWord_1135923) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1135950 : List Nat := [4, 1, 1, 1, 1, 1, 3, 2, 1, 6, 2]
def baseStart_1135950 : Nat := 118140960795 + 1135950 * 2 ^ 59
def prefixEnd_1135950 : Nat := 4983230072969 + 3 ^ 40 * 1135950 * 2
def baseEnd_1135950 : Nat := 583288349474935824100867

theorem tailTrace_1135950 : CollatzResearch.WordTrace tailWord_1135950 prefixEnd_1135950 583288349474935824100867 := by
  unfold tailWord_1135950
  simp only [CollatzResearch.WordTrace]
  refine ⟨5178937529331828707449663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 27621000156436419773064869 5178937529331828707449663)
  ·
    refine ⟨7768406293997743061174495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5178937529331828707449663 7768406293997743061174495)
    ·
      refine ⟨11652609440996614591761743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7768406293997743061174495 11652609440996614591761743)
      ·
        refine ⟨17478914161494921887642615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11652609440996614591761743 17478914161494921887642615)
        ·
          refine ⟨26218371242242382831463923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17478914161494921887642615 26218371242242382831463923)
          ·
            refine ⟨39327556863363574247195885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26218371242242382831463923 39327556863363574247195885)
            ·
              refine ⟨14747833823761340342698457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 39327556863363574247195885 14747833823761340342698457)
              ·
                refine ⟨11060875367821005257023843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14747833823761340342698457 11060875367821005257023843)
                ·
                  refine ⟨16591313051731507885535765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11060875367821005257023843 16591313051731507885535765)
                  ·
                    refine ⟨777717799299914432134489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16591313051731507885535765 777717799299914432134489)
                    ·
                      refine ⟨583288349474935824100867, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 777717799299914432134489 583288349474935824100867)
                      ·
                        rfl

theorem cell23_1135950_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 3, 2, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 3, 2, 1, 6, 2].length) (baseStart_1135950 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1135950 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1135950 prefixEnd_1135950 := by exact prefixLift 1135950
  have htrace : WordTrace (prefixWord ++ tailWord_1135950) baseStart_1135950 baseEnd_1135950 := by
    simpa [prefixWord, tailWord_1135950, baseEnd_1135950] using wordTrace_append hprefix tailTrace_1135950
  have hstable : (prefixWord ++ tailWord_1135950).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1135950).length < 2 ^ (prefixWord ++ tailWord_1135950).sum := by decide
  have hdescent : baseEnd_1135950 < baseStart_1135950 := by decide
  rcases family_descends (prefixWord ++ tailWord_1135950) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1135973 : List Nat := [1, 3, 1, 3, 1, 2, 3, 1, 8]
def baseStart_1135973 : Nat := 118140960795 + 1135973 * 2 ^ 59
def prefixEnd_1135973 : Nat := 4983230072969 + 3 ^ 40 * 1135973 * 2
def baseEnd_1135973 : Nat := 64811128836665470457029

theorem tailTrace_1135973 : CollatzResearch.WordTrace tailWord_1135973 prefixEnd_1135973 64811128836665470457029 := by
  unfold tailWord_1135973
  simp only [CollatzResearch.WordTrace]
  refine ⟨41432339113571304587684573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27621559409047536391789715 41432339113571304587684573)
  ·
    refine ⟨15537127167589239220381715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 41432339113571304587684573 15537127167589239220381715)
    ·
      refine ⟨23305690751383858830572573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15537127167589239220381715 23305690751383858830572573)
      ·
        refine ⟨8739634031768947061464715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23305690751383858830572573 8739634031768947061464715)
        ·
          refine ⟨13109451047653420592197073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8739634031768947061464715 13109451047653420592197073)
          ·
            refine ⟨9832088285740065444147805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13109451047653420592197073 9832088285740065444147805)
            ·
              refine ⟨3687033107152524541555427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9832088285740065444147805 3687033107152524541555427)
              ·
                refine ⟨5530549660728786812333141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3687033107152524541555427 5530549660728786812333141)
                ·
                  refine ⟨64811128836665470457029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 5530549660728786812333141 64811128836665470457029)
                  ·
                    rfl

theorem cell23_1135973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 3, 1, 8].length) (baseStart_1135973 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1135973 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1135973 prefixEnd_1135973 := by exact prefixLift 1135973
  have htrace : WordTrace (prefixWord ++ tailWord_1135973) baseStart_1135973 baseEnd_1135973 := by
    simpa [prefixWord, tailWord_1135973, baseEnd_1135973] using wordTrace_append hprefix tailTrace_1135973
  have hstable : (prefixWord ++ tailWord_1135973).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1135973).length < 2 ^ (prefixWord ++ tailWord_1135973).sum := by decide
  have hdescent : baseEnd_1135973 < baseStart_1135973 := by decide
  rcases family_descends (prefixWord ++ tailWord_1135973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1136028 : List Nat := [2, 2, 3, 4, 1, 1, 3, 2, 1, 4]
def baseStart_1136028 : Nat := 118140960795 + 1136028 * 2 ^ 59
def prefixEnd_1136028 : Nat := 4983230072969 + 3 ^ 40 * 1136028 * 2
def baseEnd_1136028 : Nat := 194442800321995506308503

theorem tailTrace_1136028 : CollatzResearch.WordTrace tailWord_1136028 prefixEnd_1136028 194442800321995506308503 := by
  unfold tailWord_1136028
  simp only [CollatzResearch.WordTrace]
  refine ⟨20717172564186024490468369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27622896752248032653957825 20717172564186024490468369)
  ·
    refine ⟨15537879423139518367851277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20717172564186024490468369 15537879423139518367851277)
    ·
      refine ⟨5826704783677319387944229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15537879423139518367851277 5826704783677319387944229)
      ·
        refine ⟨1092507146939497385239543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5826704783677319387944229 1092507146939497385239543)
        ·
          refine ⟨1638760720409246077859315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1092507146939497385239543 1638760720409246077859315)
          ·
            refine ⟨2458141080613869116788973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1638760720409246077859315 2458141080613869116788973)
            ·
              refine ⟨921802905230200918795865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2458141080613869116788973 921802905230200918795865)
              ·
                refine ⟨691352178922650689096899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 921802905230200918795865 691352178922650689096899)
                ·
                  refine ⟨1037028268383976033645349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 691352178922650689096899 1037028268383976033645349)
                  ·
                    refine ⟨194442800321995506308503, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1037028268383976033645349 194442800321995506308503)
                    ·
                      rfl

theorem cell23_1136028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 1, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 1, 1, 3, 2, 1, 4].length) (baseStart_1136028 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1136028 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1136028 prefixEnd_1136028 := by exact prefixLift 1136028
  have htrace : WordTrace (prefixWord ++ tailWord_1136028) baseStart_1136028 baseEnd_1136028 := by
    simpa [prefixWord, tailWord_1136028, baseEnd_1136028] using wordTrace_append hprefix tailTrace_1136028
  have hstable : (prefixWord ++ tailWord_1136028).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1136028).length < 2 ^ (prefixWord ++ tailWord_1136028).sum := by decide
  have hdescent : baseEnd_1136028 < baseStart_1136028 := by decide
  rcases family_descends (prefixWord ++ tailWord_1136028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1136034 : List Nat := [3, 3, 1, 2, 1, 2, 3, 1, 3, 1, 3]
def baseStart_1136034 : Nat := 118140960795 + 1136034 * 2 ^ 59
def prefixEnd_1136034 : Nat := 4983230072969 + 3 ^ 40 * 1136034 * 2
def baseEnd_1136034 : Nat := 583331481849913495450481

theorem tailTrace_1136034 : CollatzResearch.WordTrace tailWord_1136034 prefixEnd_1136034 583331481849913495450481 := by
  unfold tailWord_1136034
  simp only [CollatzResearch.WordTrace]
  refine ⟨10358640991587578001413789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 27623042644233541337103437 10358640991587578001413789)
  ·
    refine ⟨3884490371845341750530171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10358640991587578001413789 3884490371845341750530171)
    ·
      refine ⟨5826735557768012625795257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3884490371845341750530171 5826735557768012625795257)
      ·
        refine ⟨4370051668326009469346443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5826735557768012625795257 4370051668326009469346443)
        ·
          refine ⟨6555077502489014204019665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4370051668326009469346443 6555077502489014204019665)
          ·
            refine ⟨4916308126866760653014749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6555077502489014204019665 4916308126866760653014749)
            ·
              refine ⟨1843615547575035244880531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4916308126866760653014749 1843615547575035244880531)
              ·
                refine ⟨2765423321362552867320797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1843615547575035244880531 2765423321362552867320797)
                ·
                  refine ⟨1037033745510957325245299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2765423321362552867320797 1037033745510957325245299)
                  ·
                    refine ⟨1555550618266435987867949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1037033745510957325245299 1555550618266435987867949)
                    ·
                      refine ⟨583331481849913495450481, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1555550618266435987867949 583331481849913495450481)
                      ·
                        rfl

theorem cell23_1136034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 2, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 2, 3, 1, 3, 1, 3].length) (baseStart_1136034 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1136034 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1136034 prefixEnd_1136034 := by exact prefixLift 1136034
  have htrace : WordTrace (prefixWord ++ tailWord_1136034) baseStart_1136034 baseEnd_1136034 := by
    simpa [prefixWord, tailWord_1136034, baseEnd_1136034] using wordTrace_append hprefix tailTrace_1136034
  have hstable : (prefixWord ++ tailWord_1136034).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1136034).length < 2 ^ (prefixWord ++ tailWord_1136034).sum := by decide
  have hdescent : baseEnd_1136034 < baseStart_1136034 := by decide
  rcases family_descends (prefixWord ++ tailWord_1136034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1136043 : List Nat := [1, 1, 1, 1, 2, 1, 1, 2, 7, 1, 5]
def baseStart_1136043 : Nat := 118140960795 + 1136043 * 2 ^ 59
def prefixEnd_1136043 : Nat := 4983230072969 + 3 ^ 40 * 1136043 * 2
def baseEnd_1136043 : Nat := 583336103175803960237939

theorem tailTrace_1136043 : CollatzResearch.WordTrace tailWord_1136043 prefixEnd_1136043 583336103175803960237939 := by
  unfold tailWord_1136043
  simp only [CollatzResearch.WordTrace]
  refine ⟨41434892223317706542732783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27623261482211804361821855 41434892223317706542732783)
  ·
    refine ⟨62152338334976559814099175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41434892223317706542732783 62152338334976559814099175)
    ·
      refine ⟨93228507502464839721148763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62152338334976559814099175 93228507502464839721148763)
      ·
        refine ⟨139842761253697259581723145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 93228507502464839721148763 139842761253697259581723145)
        ·
          refine ⟨104882070940272944686292359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 139842761253697259581723145 104882070940272944686292359)
          ·
            refine ⟨157323106410409417029438539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 104882070940272944686292359 157323106410409417029438539)
            ·
              refine ⟨235984659615614125544157809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 157323106410409417029438539 235984659615614125544157809)
              ·
                refine ⟨176988494711710594158118357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 235984659615614125544157809 176988494711710594158118357)
                ·
                  refine ⟨4148167844805717050580899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 176988494711710594158118357 4148167844805717050580899)
                  ·
                    refine ⟨6222251767208575575871349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4148167844805717050580899 6222251767208575575871349)
                    ·
                      refine ⟨583336103175803960237939, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 6222251767208575575871349 583336103175803960237939)
                      ·
                        rfl

theorem cell23_1136043_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 2, 7, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 2, 7, 1, 5].length) (baseStart_1136043 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1136043 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1136043 prefixEnd_1136043 := by exact prefixLift 1136043
  have htrace : WordTrace (prefixWord ++ tailWord_1136043) baseStart_1136043 baseEnd_1136043 := by
    simpa [prefixWord, tailWord_1136043, baseEnd_1136043] using wordTrace_append hprefix tailTrace_1136043
  have hstable : (prefixWord ++ tailWord_1136043).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1136043).length < 2 ^ (prefixWord ++ tailWord_1136043).sum := by decide
  have hdescent : baseEnd_1136043 < baseStart_1136043 := by decide
  rcases family_descends (prefixWord ++ tailWord_1136043) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1136050 : List Nat := [3, 2, 1, 1, 1, 1, 2, 2, 6, 4]
def baseStart_1136050 : Nat := 118140960795 + 1136050 * 2 ^ 59
def prefixEnd_1136050 : Nat := 4983230072969 + 3 ^ 40 * 1136050 * 2
def baseEnd_1136050 : Nat := 194446565846795144283469

theorem tailTrace_1136050 : CollatzResearch.WordTrace tailWord_1136050 prefixEnd_1136050 194446565846795144283469 := by
  unfold tailWord_1136050
  simp only [CollatzResearch.WordTrace]
  refine ⟨10358786883573086684559401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 27623431689528231158825069 10358786883573086684559401)
  ·
    refine ⟨7769090162679815013419551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10358786883573086684559401 7769090162679815013419551)
    ·
      refine ⟨11653635244019722520129327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7769090162679815013419551 11653635244019722520129327)
      ·
        refine ⟨17480452866029583780193991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11653635244019722520129327 17480452866029583780193991)
        ·
          refine ⟨26220679299044375670290987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17480452866029583780193991 26220679299044375670290987)
          ·
            refine ⟨39331018948566563505436481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26220679299044375670290987 39331018948566563505436481)
            ·
              refine ⟨29498264211424922629077361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 39331018948566563505436481 29498264211424922629077361)
              ·
                refine ⟨22123698158568691971808021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29498264211424922629077361 22123698158568691971808021)
                ·
                  refine ⟨1037048351182907436178501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 22123698158568691971808021 1037048351182907436178501)
                  ·
                    refine ⟨194446565846795144283469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1037048351182907436178501 194446565846795144283469)
                    ·
                      rfl

theorem cell23_1136050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 2, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 2, 2, 6, 4].length) (baseStart_1136050 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1136050 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1136050 prefixEnd_1136050 := by exact prefixLift 1136050
  have htrace : WordTrace (prefixWord ++ tailWord_1136050) baseStart_1136050 baseEnd_1136050 := by
    simpa [prefixWord, tailWord_1136050, baseEnd_1136050] using wordTrace_append hprefix tailTrace_1136050
  have hstable : (prefixWord ++ tailWord_1136050).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1136050).length < 2 ^ (prefixWord ++ tailWord_1136050).sum := by decide
  have hdescent : baseEnd_1136050 < baseStart_1136050 := by decide
  rcases family_descends (prefixWord ++ tailWord_1136050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1136057 : List Nat := [1, 2, 1, 4, 4, 1, 1, 1, 3, 1, 4]
def baseStart_1136057 : Nat := 118140960795 + 1136057 * 2 ^ 59
def prefixEnd_1136057 : Nat := 4983230072969 + 3 ^ 40 * 1136057 * 2
def baseEnd_1136057 : Nat := 583343291904966905462875

theorem tailTrace_1136057 : CollatzResearch.WordTrace tailWord_1136057 prefixEnd_1136057 583343291904966905462875 := by
  unfold tailWord_1136057
  simp only [CollatzResearch.WordTrace]
  refine ⟨41435402845266986933742425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27623601896844657955828283 41435402845266986933742425)
  ·
    refine ⟨31076552133950240200306819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41435402845266986933742425 31076552133950240200306819)
    ·
      refine ⟨46614828200925360300460229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31076552133950240200306819 46614828200925360300460229)
      ·
        refine ⟨8740280287673505056336293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 46614828200925360300460229 8740280287673505056336293)
        ·
          refine ⟨1638802553938782198063055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8740280287673505056336293 1638802553938782198063055)
          ·
            refine ⟨2458203830908173297094583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1638802553938782198063055 2458203830908173297094583)
            ·
              refine ⟨3687305746362259945641875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2458203830908173297094583 3687305746362259945641875)
              ·
                refine ⟨5530958619543389918462813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3687305746362259945641875 5530958619543389918462813)
                ·
                  refine ⟨2074109482328771219423555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5530958619543389918462813 2074109482328771219423555)
                  ·
                    refine ⟨3111164223493156829135333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2074109482328771219423555 3111164223493156829135333)
                    ·
                      refine ⟨583343291904966905462875, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3111164223493156829135333 583343291904966905462875)
                      ·
                        rfl

theorem cell23_1136057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 4, 1, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 4, 1, 1, 1, 3, 1, 4].length) (baseStart_1136057 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1136057 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1136057 prefixEnd_1136057 := by exact prefixLift 1136057
  have htrace : WordTrace (prefixWord ++ tailWord_1136057) baseStart_1136057 baseEnd_1136057 := by
    simpa [prefixWord, tailWord_1136057, baseEnd_1136057] using wordTrace_append hprefix tailTrace_1136057
  have hstable : (prefixWord ++ tailWord_1136057).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1136057).length < 2 ^ (prefixWord ++ tailWord_1136057).sum := by decide
  have hdescent : baseEnd_1136057 < baseStart_1136057 := by decide
  rcases family_descends (prefixWord ++ tailWord_1136057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1136074 : List Nat := [3, 1, 2, 1, 2, 4, 3, 1, 1, 1, 4]
def baseStart_1136074 : Nat := 118140960795 + 1136074 * 2 ^ 59
def prefixEnd_1136074 : Nat := 4983230072969 + 3 ^ 40 * 1136074 * 2
def baseEnd_1136074 : Nat := 583352021076093338950297

theorem tailTrace_1136074 : CollatzResearch.WordTrace tailWord_1136074 prefixEnd_1136074 583352021076093338950297 := by
  unfold tailWord_1136074
  simp only [CollatzResearch.WordTrace]
  refine ⟨10359005721551349709277819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 27624015257470265891407517 10359005721551349709277819)
  ·
    refine ⟨15538508582327024563916729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10359005721551349709277819 15538508582327024563916729)
    ·
      refine ⟨11653881436745268422937547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15538508582327024563916729 11653881436745268422937547)
      ·
        refine ⟨17480822155117902634406321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11653881436745268422937547 17480822155117902634406321)
        ·
          refine ⟨13110616616338426975804741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17480822155117902634406321 13110616616338426975804741)
          ·
            refine ⟨2458240615563455057963389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 13110616616338426975804741 2458240615563455057963389)
            ·
              refine ⟨921840230836295646736271, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2458240615563455057963389 921840230836295646736271)
              ·
                refine ⟨1382760346254443470104407, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 921840230836295646736271 1382760346254443470104407)
                ·
                  refine ⟨2074140519381665205156611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1382760346254443470104407 2074140519381665205156611)
                  ·
                    refine ⟨3111210779072497807734917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2074140519381665205156611 3111210779072497807734917)
                    ·
                      refine ⟨583352021076093338950297, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3111210779072497807734917 583352021076093338950297)
                      ·
                        rfl

theorem cell23_1136074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 4, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 4, 3, 1, 1, 1, 4].length) (baseStart_1136074 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1136074 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1136074 prefixEnd_1136074 := by exact prefixLift 1136074
  have htrace : WordTrace (prefixWord ++ tailWord_1136074) baseStart_1136074 baseEnd_1136074 := by
    simpa [prefixWord, tailWord_1136074, baseEnd_1136074] using wordTrace_append hprefix tailTrace_1136074
  have hstable : (prefixWord ++ tailWord_1136074).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1136074).length < 2 ^ (prefixWord ++ tailWord_1136074).sum := by decide
  have hdescent : baseEnd_1136074 < baseStart_1136074 := by decide
  rcases family_descends (prefixWord ++ tailWord_1136074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1136110 : List Nat := [4, 1, 2, 1, 2, 1, 1, 2, 2, 7]
def baseStart_1136110 : Nat := 118140960795 + 1136110 * 2 ^ 59
def prefixEnd_1136110 : Nat := 4983230072969 + 3 ^ 40 * 1136110 * 2
def baseEnd_1136110 : Nat := 194456835459885066033377

theorem tailTrace_1136110 : CollatzResearch.WordTrace tailWord_1136110 prefixEnd_1136110 194456835459885066033377 := by
  unfold tailWord_1136110
  simp only [CollatzResearch.WordTrace]
  refine ⟨5179666989259372123177723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 27624890609383317990281189 5179666989259372123177723)
  ·
    refine ⟨7769500483889058184766585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5179666989259372123177723 7769500483889058184766585)
    ·
      refine ⟨5827125362916793638574939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7769500483889058184766585 5827125362916793638574939)
      ·
        refine ⟨8740688044375190457862409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5827125362916793638574939 8740688044375190457862409)
        ·
          refine ⟨6555516033281392843396807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8740688044375190457862409 6555516033281392843396807)
          ·
            refine ⟨9833274049922089265095211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6555516033281392843396807 9833274049922089265095211)
            ·
              refine ⟨14749911074883133897642817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9833274049922089265095211 14749911074883133897642817)
              ·
                refine ⟨11062433306162350423232113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14749911074883133897642817 11062433306162350423232113)
                ·
                  refine ⟨8296824979621762817424085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11062433306162350423232113 8296824979621762817424085)
                  ·
                    refine ⟨194456835459885066033377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 8296824979621762817424085 194456835459885066033377)
                    ·
                      rfl

theorem cell23_1136110_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 1, 2, 2, 7].length) (baseStart_1136110 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1136110 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1136110 prefixEnd_1136110 := by exact prefixLift 1136110
  have htrace : WordTrace (prefixWord ++ tailWord_1136110) baseStart_1136110 baseEnd_1136110 := by
    simpa [prefixWord, tailWord_1136110, baseEnd_1136110] using wordTrace_append hprefix tailTrace_1136110
  have hstable : (prefixWord ++ tailWord_1136110).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1136110).length < 2 ^ (prefixWord ++ tailWord_1136110).sum := by decide
  have hdescent : baseEnd_1136110 < baseStart_1136110 := by decide
  rcases family_descends (prefixWord ++ tailWord_1136110) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1136168 : List Nat := [2, 1, 5, 2, 2, 1, 2, 2, 1, 3, 2]
def baseStart_1136168 : Nat := 118140960795 + 1136168 * 2 ^ 59
def prefixEnd_1136168 : Nat := 4983230072969 + 3 ^ 40 * 1136168 * 2
def baseEnd_1136168 : Nat := 583400288257615971174865

theorem tailTrace_1136168 : CollatzResearch.WordTrace tailWord_1136168 prefixEnd_1136168 583400288257615971174865 := by
  unfold tailWord_1136168
  simp only [CollatzResearch.WordTrace]
  refine ⟨20719725673932426445516579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27626300898576568594022105 20719725673932426445516579)
  ·
    refine ⟨31079588510898639668274869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20719725673932426445516579 31079588510898639668274869)
    ·
      refine ⟨2913711422896747468900769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 31079588510898639668274869 2913711422896747468900769)
      ·
        refine ⟨2185283567172560601675577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2913711422896747468900769 2185283567172560601675577)
        ·
          refine ⟨1638962675379420451256683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2185283567172560601675577 1638962675379420451256683)
          ·
            refine ⟨2458444013069130676885025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1638962675379420451256683 2458444013069130676885025)
            ·
              refine ⟨1843833009801848007663769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2458444013069130676885025 1843833009801848007663769)
              ·
                refine ⟨1382874757351386005747827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1843833009801848007663769 1382874757351386005747827)
                ·
                  refine ⟨2074312136027079008621741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1382874757351386005747827 2074312136027079008621741)
                  ·
                    refine ⟨777867051010154628233153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2074312136027079008621741 777867051010154628233153)
                    ·
                      refine ⟨583400288257615971174865, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 777867051010154628233153 583400288257615971174865)
                      ·
                        rfl

theorem cell23_1136168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 2, 1, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 2, 1, 2, 2, 1, 3, 2].length) (baseStart_1136168 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1136168 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1136168 prefixEnd_1136168 := by exact prefixLift 1136168
  have htrace : WordTrace (prefixWord ++ tailWord_1136168) baseStart_1136168 baseEnd_1136168 := by
    simpa [prefixWord, tailWord_1136168, baseEnd_1136168] using wordTrace_append hprefix tailTrace_1136168
  have hstable : (prefixWord ++ tailWord_1136168).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1136168).length < 2 ^ (prefixWord ++ tailWord_1136168).sum := by decide
  have hdescent : baseEnd_1136168 < baseStart_1136168 := by decide
  rcases family_descends (prefixWord ++ tailWord_1136168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1136207 : List Nat := [1, 1, 2, 1, 1, 2, 3, 3, 2, 5, 2]
def baseStart_1136207 : Nat := 118140960795 + 1136207 * 2 ^ 59
def prefixEnd_1136207 : Nat := 4983230072969 + 3 ^ 40 * 1136207 * 2
def baseEnd_1136207 : Nat := 583420314003141318587185

theorem tailTrace_1136207 : CollatzResearch.WordTrace tailWord_1136207 prefixEnd_1136207 583420314003141318587185 := by
  unfold tailWord_1136207
  simp only [CollatzResearch.WordTrace]
  refine ⟨41440873794723562551702875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27627249196482375034468583 41440873794723562551702875)
  ·
    refine ⟨62161310692085343827554313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41440873794723562551702875 62161310692085343827554313)
    ·
      refine ⟨46620983019064007870665735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 62161310692085343827554313 46620983019064007870665735)
      ·
        refine ⟨69931474528596011805998603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46620983019064007870665735 69931474528596011805998603)
        ·
          refine ⟨104897211792894017708997905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 69931474528596011805998603 104897211792894017708997905)
          ·
            refine ⟨78672908844670513281748429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 104897211792894017708997905 78672908844670513281748429)
            ·
              refine ⟨29502340816751442480655661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 78672908844670513281748429 29502340816751442480655661)
              ·
                refine ⟨11063377806281790930245873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 29502340816751442480655661 11063377806281790930245873)
                ·
                  refine ⟨8297533354711343197684405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11063377806281790930245873 8297533354711343197684405)
                  ·
                    refine ⟨777893752004188424782913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8297533354711343197684405 777893752004188424782913)
                    ·
                      refine ⟨583420314003141318587185, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 777893752004188424782913 583420314003141318587185)
                      ·
                        rfl

theorem cell23_1136207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 3, 3, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 3, 3, 2, 5, 2].length) (baseStart_1136207 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1136207 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1136207 prefixEnd_1136207 := by exact prefixLift 1136207
  have htrace : WordTrace (prefixWord ++ tailWord_1136207) baseStart_1136207 baseEnd_1136207 := by
    simpa [prefixWord, tailWord_1136207, baseEnd_1136207] using wordTrace_append hprefix tailTrace_1136207
  have hstable : (prefixWord ++ tailWord_1136207).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1136207).length < 2 ^ (prefixWord ++ tailWord_1136207).sum := by decide
  have hdescent : baseEnd_1136207 < baseStart_1136207 := by decide
  rcases family_descends (prefixWord ++ tailWord_1136207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1136234 : List Nat := [3, 1, 3, 2, 1, 3, 2, 1, 2, 5]
def baseStart_1136234 : Nat := 118140960795 + 1136234 * 2 ^ 59
def prefixEnd_1136234 : Nat := 4983230072969 + 3 ^ 40 * 1136234 * 2
def baseEnd_1136234 : Nat := 194478059326937570983187

theorem tailTrace_1136234 : CollatzResearch.WordTrace tailWord_1136234 prefixEnd_1136234 194478059326937570983187 := by
  unfold tailWord_1136234
  simp only [CollatzResearch.WordTrace]
  refine ⟨10360464641406436540733939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 27627905710417164108623837 10360464641406436540733939)
  ·
    refine ⟨15540696962109654811100909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10360464641406436540733939 15540696962109654811100909)
    ·
      refine ⟨5827761360791120554162841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15540696962109654811100909 5827761360791120554162841)
      ·
        refine ⟨4370821020593340415622131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5827761360791120554162841 4370821020593340415622131)
        ·
          refine ⟨6556231530890010623433197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4370821020593340415622131 6556231530890010623433197)
          ·
            refine ⟨2458586824083753983787449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6556231530890010623433197 2458586824083753983787449)
            ·
              refine ⟨1843940118062815487840587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2458586824083753983787449 1843940118062815487840587)
              ·
                refine ⟨2765910177094223231760881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1843940118062815487840587 2765910177094223231760881)
                ·
                  refine ⟨2074432632820667423820661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2765910177094223231760881 2074432632820667423820661)
                  ·
                    refine ⟨194478059326937570983187, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2074432632820667423820661 194478059326937570983187)
                    ·
                      rfl

theorem cell23_1136234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 3, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 3, 2, 1, 2, 5].length) (baseStart_1136234 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1136234 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1136234 prefixEnd_1136234 := by exact prefixLift 1136234
  have htrace : WordTrace (prefixWord ++ tailWord_1136234) baseStart_1136234 baseEnd_1136234 := by
    simpa [prefixWord, tailWord_1136234, baseEnd_1136234] using wordTrace_append hprefix tailTrace_1136234
  have hstable : (prefixWord ++ tailWord_1136234).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1136234).length < 2 ^ (prefixWord ++ tailWord_1136234).sum := by decide
  have hdescent : baseEnd_1136234 < baseStart_1136234 := by decide
  rcases family_descends (prefixWord ++ tailWord_1136234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1136344 : List Nat := [2, 1, 2, 2, 3, 1, 1, 1, 2, 6, 2]
def baseStart_1136344 : Nat := 118140960795 + 1136344 * 2 ^ 59
def prefixEnd_1136344 : Nat := 4983230072969 + 3 ^ 40 * 1136344 * 2
def baseEnd_1136344 : Nat := 583490660852807282574055

theorem tailTrace_1136344 : CollatzResearch.WordTrace tailWord_1136344 prefixEnd_1136344 583490660852807282574055 := by
  unfold tailWord_1136344
  simp only [CollatzResearch.WordTrace]
  refine ⟨20722935297613617474720043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27630580396818156632960057 20722935297613617474720043)
  ·
    refine ⟨31084402946420426212080065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20722935297613617474720043 31084402946420426212080065)
    ·
      refine ⟨23313302209815319659060049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31084402946420426212080065 23313302209815319659060049)
      ·
        refine ⟨17484976657361489744295037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23313302209815319659060049 17484976657361489744295037)
        ·
          refine ⟨6556866246510558654110639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17484976657361489744295037 6556866246510558654110639)
          ·
            refine ⟨9835299369765837981165959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6556866246510558654110639 9835299369765837981165959)
            ·
              refine ⟨14752949054648756971748939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9835299369765837981165959 14752949054648756971748939)
              ·
                refine ⟨22129423581973135457623409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14752949054648756971748939 22129423581973135457623409)
                ·
                  refine ⟨16597067686479851593217557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22129423581973135457623409 16597067686479851593217557)
                  ·
                    refine ⟨777987547803743043432073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16597067686479851593217557 777987547803743043432073)
                    ·
                      refine ⟨583490660852807282574055, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 777987547803743043432073 583490660852807282574055)
                      ·
                        rfl

theorem cell23_1136344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 1, 1, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 1, 1, 2, 6, 2].length) (baseStart_1136344 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1136344 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1136344 prefixEnd_1136344 := by exact prefixLift 1136344
  have htrace : WordTrace (prefixWord ++ tailWord_1136344) baseStart_1136344 baseEnd_1136344 := by
    simpa [prefixWord, tailWord_1136344, baseEnd_1136344] using wordTrace_append hprefix tailTrace_1136344
  have hstable : (prefixWord ++ tailWord_1136344).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1136344).length < 2 ^ (prefixWord ++ tailWord_1136344).sum := by decide
  have hdescent : baseEnd_1136344 < baseStart_1136344 := by decide
  rcases family_descends (prefixWord ++ tailWord_1136344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1136372 : List Nat := [2, 6, 1, 1, 1, 3, 1, 1, 3, 1, 3]
def baseStart_1136372 : Nat := 118140960795 + 1136372 * 2 ^ 59
def prefixEnd_1136372 : Nat := 4983230072969 + 3 ^ 40 * 1136372 * 2
def baseEnd_1136372 : Nat := 583505038311133173023927

theorem tailTrace_1136372 : CollatzResearch.WordTrace tailWord_1136372 prefixEnd_1136372 583505038311133173023927 := by
  unfold tailWord_1136372
  simp only [CollatzResearch.WordTrace]
  refine ⟨20723445919562897865729685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27631261226083863820972913 20723445919562897865729685)
  ·
    refine ⟨971411527479510837456079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 20723445919562897865729685 971411527479510837456079)
    ·
      refine ⟨1457117291219266256184119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 971411527479510837456079 1457117291219266256184119)
      ·
        refine ⟨2185675936828899384276179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1457117291219266256184119 2185675936828899384276179)
        ·
          refine ⟨3278513905243349076414269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2185675936828899384276179 3278513905243349076414269)
          ·
            refine ⟨1229442714466255903655351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3278513905243349076414269 1229442714466255903655351)
            ·
              refine ⟨1844164071699383855483027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1229442714466255903655351 1844164071699383855483027)
              ·
                refine ⟨2766246107549075783224541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1844164071699383855483027 2766246107549075783224541)
                ·
                  refine ⟨1037342290330903418709203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2766246107549075783224541 1037342290330903418709203)
                  ·
                    refine ⟨1556013435496355128063805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1037342290330903418709203 1556013435496355128063805)
                    ·
                      refine ⟨583505038311133173023927, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1556013435496355128063805 583505038311133173023927)
                      ·
                        rfl

theorem cell23_1136372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 3, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 3, 1, 1, 3, 1, 3].length) (baseStart_1136372 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1136372 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1136372 prefixEnd_1136372 := by exact prefixLift 1136372
  have htrace : WordTrace (prefixWord ++ tailWord_1136372) baseStart_1136372 baseEnd_1136372 := by
    simpa [prefixWord, tailWord_1136372, baseEnd_1136372] using wordTrace_append hprefix tailTrace_1136372
  have hstable : (prefixWord ++ tailWord_1136372).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1136372).length < 2 ^ (prefixWord ++ tailWord_1136372).sum := by decide
  have hdescent : baseEnd_1136372 < baseStart_1136372 := by decide
  rcases family_descends (prefixWord ++ tailWord_1136372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1136374 : List Nat := [5, 1, 1, 1, 1, 3, 1, 2, 1, 1, 6]
def baseStart_1136374 : Nat := 118140960795 + 1136374 * 2 ^ 59
def prefixEnd_1136374 : Nat := 4983230072969 + 3 ^ 40 * 1136374 * 2
def baseEnd_1136374 : Nat := 583506065272442165198917

theorem tailTrace_1136374 : CollatzResearch.WordTrace tailWord_1136374 prefixEnd_1136374 583506065272442165198917 := by
  unfold tailWord_1136374
  simp only [CollatzResearch.WordTrace]
  refine ⟨2590435299069909379564511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 27631309856745700048688117 2590435299069909379564511)
  ·
    refine ⟨3885652948604864069346767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2590435299069909379564511 3885652948604864069346767)
    ·
      refine ⟨5828479422907296104020151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3885652948604864069346767 5828479422907296104020151)
      ·
        refine ⟨8742719134360944156030227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5828479422907296104020151 8742719134360944156030227)
        ·
          refine ⟨13114078701541416234045341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8742719134360944156030227 13114078701541416234045341)
          ·
            refine ⟨4917779513078031087767003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13114078701541416234045341 4917779513078031087767003)
            ·
              refine ⟨7376669269617046631650505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4917779513078031087767003 7376669269617046631650505)
              ·
                refine ⟨5532501952212784973737879, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7376669269617046631650505 5532501952212784973737879)
                ·
                  refine ⟨8298752928319177460606819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5532501952212784973737879 8298752928319177460606819)
                  ·
                    refine ⟨12448129392478766190910229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8298752928319177460606819 12448129392478766190910229)
                    ·
                      refine ⟨583506065272442165198917, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 12448129392478766190910229 583506065272442165198917)
                      ·
                        rfl

theorem cell23_1136374_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 3, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 3, 1, 2, 1, 1, 6].length) (baseStart_1136374 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1136374 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1136374 prefixEnd_1136374 := by exact prefixLift 1136374
  have htrace : WordTrace (prefixWord ++ tailWord_1136374) baseStart_1136374 baseEnd_1136374 := by
    simpa [prefixWord, tailWord_1136374, baseEnd_1136374] using wordTrace_append hprefix tailTrace_1136374
  have hstable : (prefixWord ++ tailWord_1136374).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1136374).length < 2 ^ (prefixWord ++ tailWord_1136374).sum := by decide
  have hdescent : baseEnd_1136374 < baseStart_1136374 := by decide
  rcases family_descends (prefixWord ++ tailWord_1136374) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1136388 : List Nat := [2, 3, 2, 2, 1, 2, 4, 1, 2, 4]
def baseStart_1136388 : Nat := 118140960795 + 1136388 * 2 ^ 59
def prefixEnd_1136388 : Nat := 4983230072969 + 3 ^ 40 * 1136388 * 2
def baseEnd_1136388 : Nat := 194504418000535036807951

theorem tailTrace_1136388 : CollatzResearch.WordTrace tailWord_1136388 prefixEnd_1136388 194504418000535036807951 := by
  unfold tailWord_1136388
  simp only [CollatzResearch.WordTrace]
  refine ⟨20723737703533915232020909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27631650271378553642694545 20723737703533915232020909)
  ·
    refine ⟨7771401638825218212007841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20723737703533915232020909 7771401638825218212007841)
    ·
      refine ⟨5828551229118913659005881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7771401638825218212007841 5828551229118913659005881)
      ·
        refine ⟨4371413421839185244254411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5828551229118913659005881 4371413421839185244254411)
        ·
          refine ⟨6557120132758777866381617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4371413421839185244254411 6557120132758777866381617)
          ·
            refine ⟨4917840099569083399786213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6557120132758777866381617 4917840099569083399786213)
            ·
              refine ⟨922095018669203137459915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4917840099569083399786213 922095018669203137459915)
              ·
                refine ⟨1383142528003804706189873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 922095018669203137459915 1383142528003804706189873)
                ·
                  refine ⟨1037356896002853529642405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1383142528003804706189873 1037356896002853529642405)
                  ·
                    refine ⟨194504418000535036807951, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1037356896002853529642405 194504418000535036807951)
                    ·
                      rfl

theorem cell23_1136388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 2, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 2, 4, 1, 2, 4].length) (baseStart_1136388 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1136388 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1136388 prefixEnd_1136388 := by exact prefixLift 1136388
  have htrace : WordTrace (prefixWord ++ tailWord_1136388) baseStart_1136388 baseEnd_1136388 := by
    simpa [prefixWord, tailWord_1136388, baseEnd_1136388] using wordTrace_append hprefix tailTrace_1136388
  have hstable : (prefixWord ++ tailWord_1136388).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1136388).length < 2 ^ (prefixWord ++ tailWord_1136388).sum := by decide
  have hdescent : baseEnd_1136388 < baseStart_1136388 := by decide
  rcases family_descends (prefixWord ++ tailWord_1136388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1136428 : List Nat := [2, 2, 1, 1, 1, 6, 2, 2, 2, 1, 3]
def baseStart_1136428 : Nat := 118140960795 + 1136428 * 2 ^ 59
def prefixEnd_1136428 : Nat := 4983230072969 + 3 ^ 40 * 1136428 * 2
def baseEnd_1136428 : Nat := 583533793227784953923669

theorem tailTrace_1136428 : CollatzResearch.WordTrace tailWord_1136428 prefixEnd_1136428 583533793227784953923669 := by
  unfold tailWord_1136428
  simp only [CollatzResearch.WordTrace]
  refine ⟨20724467163461458647748969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27632622884615278196998625 20724467163461458647748969)
  ·
    refine ⟨15543350372596093985811727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20724467163461458647748969 15543350372596093985811727)
    ·
      refine ⟨23315025558894140978717591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15543350372596093985811727 23315025558894140978717591)
      ·
        refine ⟨34972538338341211468076387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23315025558894140978717591 34972538338341211468076387)
        ·
          refine ⟨52458807507511817202114581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34972538338341211468076387 52458807507511817202114581)
          ·
            refine ⟨2459006601914616431349121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 52458807507511817202114581 2459006601914616431349121)
            ·
              refine ⟨1844254951435962323511841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2459006601914616431349121 1844254951435962323511841)
              ·
                refine ⟨1383191213576971742633881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1844254951435962323511841 1383191213576971742633881)
                ·
                  refine ⟨1037393410182728806975411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1383191213576971742633881 1037393410182728806975411)
                  ·
                    refine ⟨1556090115274093210463117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1037393410182728806975411 1556090115274093210463117)
                    ·
                      refine ⟨583533793227784953923669, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1556090115274093210463117 583533793227784953923669)
                      ·
                        rfl

theorem cell23_1136428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 2, 1, 3].length) (baseStart_1136428 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1136428 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1136428 prefixEnd_1136428 := by exact prefixLift 1136428
  have htrace : WordTrace (prefixWord ++ tailWord_1136428) baseStart_1136428 baseEnd_1136428 := by
    simpa [prefixWord, tailWord_1136428, baseEnd_1136428] using wordTrace_append hprefix tailTrace_1136428
  have hstable : (prefixWord ++ tailWord_1136428).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1136428).length < 2 ^ (prefixWord ++ tailWord_1136428).sum := by decide
  have hdescent : baseEnd_1136428 < baseStart_1136428 := by decide
  rcases family_descends (prefixWord ++ tailWord_1136428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1136434 : List Nat := [3, 2, 1, 1, 3, 2, 1, 1, 2, 3, 4]
def baseStart_1136434 : Nat := 118140960795 + 1136434 * 2 ^ 59
def prefixEnd_1136434 : Nat := 4983230072969 + 3 ^ 40 * 1136434 * 2
def baseEnd_1136434 : Nat := 583536874111711930448641

theorem tailTrace_1136434 : CollatzResearch.WordTrace tailWord_1136434 prefixEnd_1136434 583536874111711930448641 := by
  unfold tailWord_1136434
  simp only [CollatzResearch.WordTrace]
  refine ⟨10362288291225295080054089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 27632768776600786880144237 10362288291225295080054089)
  ·
    refine ⟨7771716218418971310040567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10362288291225295080054089 7771716218418971310040567)
    ·
      refine ⟨11657574327628456965060851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7771716218418971310040567 11657574327628456965060851)
      ·
        refine ⟨17486361491442685447591277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11657574327628456965060851 17486361491442685447591277)
        ·
          refine ⟨6557385559291007042846729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17486361491442685447591277 6557385559291007042846729)
          ·
            refine ⟨4918039169468255282135047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6557385559291007042846729 4918039169468255282135047)
            ·
              refine ⟨7377058754202382923202571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4918039169468255282135047 7377058754202382923202571)
              ·
                refine ⟨11065588131303574384803857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7377058754202382923202571 11065588131303574384803857)
                ·
                  refine ⟨8299191098477680788602893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11065588131303574384803857 8299191098477680788602893)
                  ·
                    refine ⟨3112196661929130295726085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8299191098477680788602893 3112196661929130295726085)
                    ·
                      refine ⟨583536874111711930448641, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3112196661929130295726085 583536874111711930448641)
                      ·
                        rfl

theorem cell23_1136434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 2, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 2, 1, 1, 2, 3, 4].length) (baseStart_1136434 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1136434 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1136434 prefixEnd_1136434 := by exact prefixLift 1136434
  have htrace : WordTrace (prefixWord ++ tailWord_1136434) baseStart_1136434 baseEnd_1136434 := by
    simpa [prefixWord, tailWord_1136434, baseEnd_1136434] using wordTrace_append hprefix tailTrace_1136434
  have hstable : (prefixWord ++ tailWord_1136434).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1136434).length < 2 ^ (prefixWord ++ tailWord_1136434).sum := by decide
  have hdescent : baseEnd_1136434 < baseStart_1136434 := by decide
  rcases family_descends (prefixWord ++ tailWord_1136434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1136451 : List Nat := [1, 1, 1, 3, 1, 5, 1, 3, 1, 4, 2]
def baseStart_1136451 : Nat := 118140960795 + 1136451 * 2 ^ 59
def prefixEnd_1136451 : Nat := 4983230072969 + 3 ^ 40 * 1136451 * 2
def baseEnd_1136451 : Nat := 583545603282838363936063

theorem tailTrace_1136451 : CollatzResearch.WordTrace tailWord_1136451 prefixEnd_1136451 583545603282838363936063 := by
  unfold tailWord_1136451
  simp only [CollatzResearch.WordTrace]
  refine ⟨41449773205839592223585207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27633182137226394815723471 41449773205839592223585207)
  ·
    refine ⟨62174659808759388335377811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41449773205839592223585207 62174659808759388335377811)
    ·
      refine ⟨93261989713139082503066717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62174659808759388335377811 93261989713139082503066717)
      ·
        refine ⟨34973246142427155938650019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 93261989713139082503066717 34973246142427155938650019)
        ·
          refine ⟨52459869213640733907975029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34973246142427155938650019 52459869213640733907975029)
          ·
            refine ⟨4918112738778818803872659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 52459869213640733907975029 4918112738778818803872659)
            ·
              refine ⟨7377169108168228205808989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4918112738778818803872659 7377169108168228205808989)
              ·
                refine ⟨2766438415563085577178371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7377169108168228205808989 2766438415563085577178371)
                ·
                  refine ⟨4149657623344628365767557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2766438415563085577178371 4149657623344628365767557)
                  ·
                    refine ⟨778060804377117818581417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4149657623344628365767557 778060804377117818581417)
                    ·
                      refine ⟨583545603282838363936063, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 778060804377117818581417 583545603282838363936063)
                      ·
                        rfl

theorem cell23_1136451_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 5, 1, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 5, 1, 3, 1, 4, 2].length) (baseStart_1136451 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1136451 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1136451 prefixEnd_1136451 := by exact prefixLift 1136451
  have htrace : WordTrace (prefixWord ++ tailWord_1136451) baseStart_1136451 baseEnd_1136451 := by
    simpa [prefixWord, tailWord_1136451, baseEnd_1136451] using wordTrace_append hprefix tailTrace_1136451
  have hstable : (prefixWord ++ tailWord_1136451).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1136451).length < 2 ^ (prefixWord ++ tailWord_1136451).sum := by decide
  have hdescent : baseEnd_1136451 < baseStart_1136451 := by decide
  rcases family_descends (prefixWord ++ tailWord_1136451) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1136467 : List Nat := [1, 1, 1, 2, 1, 1, 3, 1, 3, 2, 7]
def baseStart_1136467 : Nat := 118140960795 + 1136467 * 2 ^ 59
def prefixEnd_1136467 : Nat := 4983230072969 + 3 ^ 40 * 1136467 * 2
def baseEnd_1136467 : Nat := 583553818973310301335989

theorem tailTrace_1136467 : CollatzResearch.WordTrace tailWord_1136467 prefixEnd_1136467 583553818973310301335989 := by
  unfold tailWord_1136467
  simp only [CollatzResearch.WordTrace]
  refine ⟨41450356773781626956167655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27633571182521084637445103 41450356773781626956167655)
  ·
    refine ⟨62175535160672440434251483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41450356773781626956167655 62175535160672440434251483)
    ·
      refine ⟨93263302741008660651377225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62175535160672440434251483 93263302741008660651377225)
      ·
        refine ⟨69947477055756495488532919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 93263302741008660651377225 69947477055756495488532919)
        ·
          refine ⟨104921215583634743232799379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 69947477055756495488532919 104921215583634743232799379)
          ·
            refine ⟨157381823375452114849199069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 104921215583634743232799379 157381823375452114849199069)
            ·
              refine ⟨59018183765794543068449651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 157381823375452114849199069 59018183765794543068449651)
              ·
                refine ⟨88527275648691814602674477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 59018183765794543068449651 88527275648691814602674477)
                ·
                  refine ⟨33197728368259430476002929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 88527275648691814602674477 33197728368259430476002929)
                  ·
                    refine ⟨24898296276194572857002197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 33197728368259430476002929 24898296276194572857002197)
                    ·
                      refine ⟨583553818973310301335989, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 24898296276194572857002197 583553818973310301335989)
                      ·
                        rfl

theorem cell23_1136467_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 3, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 3, 1, 3, 2, 7].length) (baseStart_1136467 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1136467 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1136467 prefixEnd_1136467 := by exact prefixLift 1136467
  have htrace : WordTrace (prefixWord ++ tailWord_1136467) baseStart_1136467 baseEnd_1136467 := by
    simpa [prefixWord, tailWord_1136467, baseEnd_1136467] using wordTrace_append hprefix tailTrace_1136467
  have hstable : (prefixWord ++ tailWord_1136467).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1136467).length < 2 ^ (prefixWord ++ tailWord_1136467).sum := by decide
  have hdescent : baseEnd_1136467 < baseStart_1136467 := by decide
  rcases family_descends (prefixWord ++ tailWord_1136467) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1136468 : List Nat := [2, 4, 1, 1, 3, 1, 2, 2, 1, 4, 2]
def baseStart_1136468 : Nat := 118140960795 + 1136468 * 2 ^ 59
def prefixEnd_1136468 : Nat := 4983230072969 + 3 ^ 40 * 1136468 * 2
def baseEnd_1136468 : Nat := 583554332453964797423485

theorem tailTrace_1136468 : CollatzResearch.WordTrace tailWord_1136468 prefixEnd_1136468 583554332453964797423485 := by
  unfold tailWord_1136468
  simp only [CollatzResearch.WordTrace]
  refine ⟨20725196623389002063477029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27633595497852002751302705 20725196623389002063477029)
  ·
    refine ⟨3885974366885437886901943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 20725196623389002063477029 3885974366885437886901943)
    ·
      refine ⟨5828961550328156830352915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3885974366885437886901943 5828961550328156830352915)
      ·
        refine ⟨8743442325492235245529373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5828961550328156830352915 8743442325492235245529373)
        ·
          refine ⟨3278790872059588217073515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8743442325492235245529373 3278790872059588217073515)
          ·
            refine ⟨4918186308089382325610273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3278790872059588217073515 4918186308089382325610273)
            ·
              refine ⟨3688639731067036744207705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4918186308089382325610273 3688639731067036744207705)
              ·
                refine ⟨2766479798300277558155779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3688639731067036744207705 2766479798300277558155779)
                ·
                  refine ⟨4149719697450416337233669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2766479798300277558155779 4149719697450416337233669)
                  ·
                    refine ⟨778072443271953063231313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4149719697450416337233669 778072443271953063231313)
                    ·
                      refine ⟨583554332453964797423485, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 778072443271953063231313 583554332453964797423485)
                      ·
                        rfl

theorem cell23_1136468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 1, 2, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 1, 2, 2, 1, 4, 2].length) (baseStart_1136468 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1136468 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1136468 prefixEnd_1136468 := by exact prefixLift 1136468
  have htrace : WordTrace (prefixWord ++ tailWord_1136468) baseStart_1136468 baseEnd_1136468 := by
    simpa [prefixWord, tailWord_1136468, baseEnd_1136468] using wordTrace_append hprefix tailTrace_1136468
  have hstable : (prefixWord ++ tailWord_1136468).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1136468).length < 2 ^ (prefixWord ++ tailWord_1136468).sum := by decide
  have hdescent : baseEnd_1136468 < baseStart_1136468 := by decide
  rcases family_descends (prefixWord ++ tailWord_1136468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1136501 : List Nat := [1, 3, 4, 1, 1, 1, 1, 3, 2, 3, 3]
def baseStart_1136501 : Nat := 118140960795 + 1136501 * 2 ^ 59
def prefixEnd_1136501 : Nat := 4983230072969 + 3 ^ 40 * 1136501 * 2
def baseEnd_1136501 : Nat := 583571277315563168310833

theorem tailTrace_1136501 : CollatzResearch.WordTrace tailWord_1136501 prefixEnd_1136501 583571277315563168310833 := by
  unfold tailWord_1136501
  simp only [CollatzResearch.WordTrace]
  refine ⟨41451596855658450762905357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27634397903772300508603571 41451596855658450762905357)
  ·
    refine ⟨15544348820871919036089509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 41451596855658450762905357 15544348820871919036089509)
    ·
      refine ⟨2914565403913484819266783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 15544348820871919036089509 2914565403913484819266783)
      ·
        refine ⟨4371848105870227228900175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2914565403913484819266783 4371848105870227228900175)
        ·
          refine ⟨6557772158805340843350263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4371848105870227228900175 6557772158805340843350263)
          ·
            refine ⟨9836658238208011265025395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6557772158805340843350263 9836658238208011265025395)
            ·
              refine ⟨14754987357312016897538093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9836658238208011265025395 14754987357312016897538093)
              ·
                refine ⟨5533120258992006336576785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14754987357312016897538093 5533120258992006336576785)
                ·
                  refine ⟨4149840194244004752432589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5533120258992006336576785 4149840194244004752432589)
                  ·
                    refine ⟨1556190072841501782162221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4149840194244004752432589 1556190072841501782162221)
                    ·
                      refine ⟨583571277315563168310833, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1556190072841501782162221 583571277315563168310833)
                      ·
                        rfl

theorem cell23_1136501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 1, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 1, 3, 2, 3, 3].length) (baseStart_1136501 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1136501 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1136501 prefixEnd_1136501 := by exact prefixLift 1136501
  have htrace : WordTrace (prefixWord ++ tailWord_1136501) baseStart_1136501 baseEnd_1136501 := by
    simpa [prefixWord, tailWord_1136501, baseEnd_1136501] using wordTrace_append hprefix tailTrace_1136501
  have hstable : (prefixWord ++ tailWord_1136501).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1136501).length < 2 ^ (prefixWord ++ tailWord_1136501).sum := by decide
  have hdescent : baseEnd_1136501 < baseStart_1136501 := by decide
  rcases family_descends (prefixWord ++ tailWord_1136501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1136502 : List Nat := [5, 1, 1, 3, 2, 2, 1, 1, 1, 4, 2]
def baseStart_1136502 : Nat := 118140960795 + 1136502 * 2 ^ 59
def prefixEnd_1136502 : Nat := 4983230072969 + 3 ^ 40 * 1136502 * 2
def baseEnd_1136502 : Nat := 583571790796217664398329

theorem tailTrace_1136502 : CollatzResearch.WordTrace tailWord_1136502 prefixEnd_1136502 583571790796217664398329 := by
  unfold tailWord_1136502
  simp only [CollatzResearch.WordTrace]
  refine ⟨2590727083040926745855735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 27634422219103218622461173 2590727083040926745855735)
  ·
    refine ⟨3886090624561390118783603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2590727083040926745855735 3886090624561390118783603)
    ·
      refine ⟨5829135936842085178175405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3886090624561390118783603 5829135936842085178175405)
      ·
        refine ⟨2185925976315781941815777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5829135936842085178175405 2185925976315781941815777)
        ·
          refine ⟨1639444482236836456361833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2185925976315781941815777 1639444482236836456361833)
          ·
            refine ⟨1229583361677627342271375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1639444482236836456361833 1229583361677627342271375)
            ·
              refine ⟨1844375042516441013407063, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1229583361677627342271375 1844375042516441013407063)
              ·
                refine ⟨2766562563774661520110595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1844375042516441013407063 2766562563774661520110595)
                ·
                  refine ⟨4149843845661992280165893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2766562563774661520110595 4149843845661992280165893)
                  ·
                    refine ⟨778095721061623552531105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4149843845661992280165893 778095721061623552531105)
                    ·
                      refine ⟨583571790796217664398329, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 778095721061623552531105 583571790796217664398329)
                      ·
                        rfl

theorem cell23_1136502_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 2, 2, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 2, 2, 1, 1, 1, 4, 2].length) (baseStart_1136502 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1136502 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1136502 prefixEnd_1136502 := by exact prefixLift 1136502
  have htrace : WordTrace (prefixWord ++ tailWord_1136502) baseStart_1136502 baseEnd_1136502 := by
    simpa [prefixWord, tailWord_1136502, baseEnd_1136502] using wordTrace_append hprefix tailTrace_1136502
  have hstable : (prefixWord ++ tailWord_1136502).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1136502).length < 2 ^ (prefixWord ++ tailWord_1136502).sum := by decide
  have hdescent : baseEnd_1136502 < baseStart_1136502 := by decide
  rcases family_descends (prefixWord ++ tailWord_1136502) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1136541 : List Nat := [1, 4, 2, 1, 2, 2, 1, 1, 4, 1, 4]
def baseStart_1136541 : Nat := 118140960795 + 1136541 * 2 ^ 59
def prefixEnd_1136541 : Nat := 4983230072969 + 3 ^ 40 * 1136541 * 2
def baseEnd_1136541 : Nat := 583591816541743011810649

theorem tailTrace_1136541 : CollatzResearch.WordTrace tailWord_1136541 prefixEnd_1136541 583591816541743011810649 := by
  unfold tailWord_1136541
  simp only [CollatzResearch.WordTrace]
  refine ⟨41453055775513537594361477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27635370517009025062907651 41453055775513537594361477)
  ·
    refine ⟨7772447957908788298942777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 41453055775513537594361477 7772447957908788298942777)
    ·
      refine ⟨5829335968431591224207083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7772447957908788298942777 5829335968431591224207083)
      ·
        refine ⟨8744003952647386836310625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5829335968431591224207083 8744003952647386836310625)
        ·
          refine ⟨6558002964485540127232969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8744003952647386836310625 6558002964485540127232969)
          ·
            refine ⟨4918502223364155095424727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6558002964485540127232969 4918502223364155095424727)
            ·
              refine ⟨7377753335046232643137091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4918502223364155095424727 7377753335046232643137091)
              ·
                refine ⟨11066630002569348964705637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7377753335046232643137091 11066630002569348964705637)
                ·
                  refine ⟨2074993125481752930882307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11066630002569348964705637 2074993125481752930882307)
                  ·
                    refine ⟨3112489688222629396323461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2074993125481752930882307 3112489688222629396323461)
                    ·
                      refine ⟨583591816541743011810649, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3112489688222629396323461 583591816541743011810649)
                      ·
                        rfl

theorem cell23_1136541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 2, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 2, 1, 1, 4, 1, 4].length) (baseStart_1136541 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1136541 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1136541 prefixEnd_1136541 := by exact prefixLift 1136541
  have htrace : WordTrace (prefixWord ++ tailWord_1136541) baseStart_1136541 baseEnd_1136541 := by
    simpa [prefixWord, tailWord_1136541, baseEnd_1136541] using wordTrace_append hprefix tailTrace_1136541
  have hstable : (prefixWord ++ tailWord_1136541).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1136541).length < 2 ^ (prefixWord ++ tailWord_1136541).sum := by decide
  have hdescent : baseEnd_1136541 < baseStart_1136541 := by decide
  rcases family_descends (prefixWord ++ tailWord_1136541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1136542 : List Nat := [4, 3, 1, 3, 2, 1, 1, 1, 7]
def baseStart_1136542 : Nat := 118140960795 + 1136542 * 2 ^ 59
def prefixEnd_1136542 : Nat := 4983230072969 + 3 ^ 40 * 1136542 * 2
def baseEnd_1136542 : Nat := 64843592224710834210905

theorem tailTrace_1136542 : CollatzResearch.WordTrace tailWord_1136542 prefixEnd_1136542 64843592224710834210905 := by
  unfold tailWord_1136542
  simp only [CollatzResearch.WordTrace]
  refine ⟨5181636531063739345643485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 27635394832339943176765253 5181636531063739345643485)
  ·
    refine ⟨1943113699148902254616307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5181636531063739345643485 1943113699148902254616307)
    ·
      refine ⟨2914670548723353381924461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1943113699148902254616307 2914670548723353381924461)
      ·
        refine ⟨1093001455771257518221673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2914670548723353381924461 1093001455771257518221673)
        ·
          refine ⟨819751091828443138666255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1093001455771257518221673 819751091828443138666255)
          ·
            refine ⟨1229626637742664707999383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 819751091828443138666255 1229626637742664707999383)
            ·
              refine ⟨1844439956613997061999075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1229626637742664707999383 1844439956613997061999075)
              ·
                refine ⟨2766659934920995592998613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1844439956613997061999075 2766659934920995592998613)
                ·
                  refine ⟨64843592224710834210905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2766659934920995592998613 64843592224710834210905)
                  ·
                    rfl

theorem cell23_1136542_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 2, 1, 1, 1, 7].length) (baseStart_1136542 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1136542 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1136542 prefixEnd_1136542 := by exact prefixLift 1136542
  have htrace : WordTrace (prefixWord ++ tailWord_1136542) baseStart_1136542 baseEnd_1136542 := by
    simpa [prefixWord, tailWord_1136542, baseEnd_1136542] using wordTrace_append hprefix tailTrace_1136542
  have hstable : (prefixWord ++ tailWord_1136542).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1136542).length < 2 ^ (prefixWord ++ tailWord_1136542).sum := by decide
  have hdescent : baseEnd_1136542 < baseStart_1136542 := by decide
  rcases family_descends (prefixWord ++ tailWord_1136542) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1136611 : List Nat := [1, 1, 1, 6, 1, 2, 1, 2, 3, 5]
def baseStart_1136611 : Nat := 118140960795 + 1136611 * 2 ^ 59
def prefixEnd_1136611 : Nat := 4983230072969 + 3 ^ 40 * 1136611 * 2
def baseEnd_1136611 : Nat := 194542586729185912645109

theorem tailTrace_1136611 : CollatzResearch.WordTrace tailWord_1136611 prefixEnd_1136611 194542586729185912645109 := by
  unfold tailWord_1136611
  simp only [CollatzResearch.WordTrace]
  refine ⟨41455608885259939549409687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27637072590173293032939791 41455608885259939549409687)
  ·
    refine ⟨62183413327889909324114531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41455608885259939549409687 62183413327889909324114531)
    ·
      refine ⟨93275119991834863986171797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62183413327889909324114531 93275119991834863986171797)
      ·
        refine ⟨4372271249617259249351803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 93275119991834863986171797 4372271249617259249351803)
        ·
          refine ⟨6558406874425888874027705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4372271249617259249351803 6558406874425888874027705)
          ·
            refine ⟨4918805155819416655520779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6558406874425888874027705 4918805155819416655520779)
            ·
              refine ⟨7378207733729124983281169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4918805155819416655520779 7378207733729124983281169)
              ·
                refine ⟨5533655800296843737460877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7378207733729124983281169 5533655800296843737460877)
                ·
                  refine ⟨2075120925111316401547829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5533655800296843737460877 2075120925111316401547829)
                  ·
                    refine ⟨194542586729185912645109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2075120925111316401547829 194542586729185912645109)
                    ·
                      rfl

theorem cell23_1136611_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 2, 1, 2, 3, 5].length) (baseStart_1136611 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1136611 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1136611 prefixEnd_1136611 := by exact prefixLift 1136611
  have htrace : WordTrace (prefixWord ++ tailWord_1136611) baseStart_1136611 baseEnd_1136611 := by
    simpa [prefixWord, tailWord_1136611, baseEnd_1136611] using wordTrace_append hprefix tailTrace_1136611
  have hstable : (prefixWord ++ tailWord_1136611).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1136611).length < 2 ^ (prefixWord ++ tailWord_1136611).sum := by decide
  have hdescent : baseEnd_1136611 < baseStart_1136611 := by decide
  rcases family_descends (prefixWord ++ tailWord_1136611) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1136618 : List Nat := [3, 1, 3, 1, 2, 1, 2, 2, 1, 5, 2]
def baseStart_1136618 : Nat := 118140960795 + 1136618 * 2 ^ 59
def prefixEnd_1136618 : Nat := 4983230072969 + 3 ^ 40 * 1136618 * 2
def baseEnd_1136618 : Nat := 583631354552139210547795

theorem tailTrace_1136618 : CollatzResearch.WordTrace tailWord_1136618 prefixEnd_1136618 583631354552139210547795 := by
  unfold tailWord_1136618
  simp only [CollatzResearch.WordTrace]
  refine ⟨10363966049058644936228627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 27637242797489719829943005 10363966049058644936228627)
  ·
    refine ⟨15545949073587967404342941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10363966049058644936228627 15545949073587967404342941)
    ·
      refine ⟨5829730902595487776628603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15545949073587967404342941 5829730902595487776628603)
      ·
        refine ⟨8744596353893231664942905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5829730902595487776628603 8744596353893231664942905)
        ·
          refine ⟨6558447265419923748707179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8744596353893231664942905 6558447265419923748707179)
          ·
            refine ⟨9837670898129885623060769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6558447265419923748707179 9837670898129885623060769)
            ·
              refine ⟨7378253173597414217295577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9837670898129885623060769 7378253173597414217295577)
              ·
                refine ⟨5533689880198060662971683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7378253173597414217295577 5533689880198060662971683)
                ·
                  refine ⟨8300534820297090994457525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5533689880198060662971683 8300534820297090994457525)
                  ·
                    refine ⟨778175139402852280730393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8300534820297090994457525 778175139402852280730393)
                    ·
                      refine ⟨583631354552139210547795, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 778175139402852280730393 583631354552139210547795)
                      ·
                        rfl

theorem cell23_1136618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 2, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 2, 2, 1, 5, 2].length) (baseStart_1136618 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1136618 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1136618 prefixEnd_1136618 := by exact prefixLift 1136618
  have htrace : WordTrace (prefixWord ++ tailWord_1136618) baseStart_1136618 baseEnd_1136618 := by
    simpa [prefixWord, tailWord_1136618, baseEnd_1136618] using wordTrace_append hprefix tailTrace_1136618
  have hstable : (prefixWord ++ tailWord_1136618).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1136618).length < 2 ^ (prefixWord ++ tailWord_1136618).sum := by decide
  have hdescent : baseEnd_1136618 < baseStart_1136618 := by decide
  rcases family_descends (prefixWord ++ tailWord_1136618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1136625 : List Nat := [1, 2, 2, 2, 5, 1, 1, 2, 3, 1, 3]
def baseStart_1136625 : Nat := 118140960795 + 1136625 * 2 ^ 59
def prefixEnd_1136625 : Nat := 4983230072969 + 3 ^ 40 * 1136625 * 2
def baseEnd_1136625 : Nat := 583634948916720683160263

theorem tailTrace_1136625 : CollatzResearch.WordTrace tailWord_1136625 prefixEnd_1136625 583634948916720683160263 := by
  unfold tailWord_1136625
  simp only [CollatzResearch.WordTrace]
  refine ⟨41456119507209219940419329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27637413004806146626946219 41456119507209219940419329)
  ·
    refine ⟨31092089630406914955314497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41456119507209219940419329 31092089630406914955314497)
    ·
      refine ⟨23319067222805186216485873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31092089630406914955314497 23319067222805186216485873)
      ·
        refine ⟨17489300417103889662364405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23319067222805186216485873 17489300417103889662364405)
        ·
          refine ⟨1639621914103489655846663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 17489300417103889662364405 1639621914103489655846663)
          ·
            refine ⟨2459432871155234483769995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1639621914103489655846663 2459432871155234483769995)
            ·
              refine ⟨3689149306732851725654993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2459432871155234483769995 3689149306732851725654993)
              ·
                refine ⟨2766861980049638794241245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3689149306732851725654993 2766861980049638794241245)
                ·
                  refine ⟨1037573242518614547840467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2766861980049638794241245 1037573242518614547840467)
                  ·
                    refine ⟨1556359863777921821760701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1037573242518614547840467 1556359863777921821760701)
                    ·
                      refine ⟨583634948916720683160263, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1556359863777921821760701 583634948916720683160263)
                      ·
                        rfl

theorem cell23_1136625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 5, 1, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 5, 1, 1, 2, 3, 1, 3].length) (baseStart_1136625 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1136625 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1136625 prefixEnd_1136625 := by exact prefixLift 1136625
  have htrace : WordTrace (prefixWord ++ tailWord_1136625) baseStart_1136625 baseEnd_1136625 := by
    simpa [prefixWord, tailWord_1136625, baseEnd_1136625] using wordTrace_append hprefix tailTrace_1136625
  have hstable : (prefixWord ++ tailWord_1136625).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1136625).length < 2 ^ (prefixWord ++ tailWord_1136625).sum := by decide
  have hdescent : baseEnd_1136625 < baseStart_1136625 := by decide
  rcases family_descends (prefixWord ++ tailWord_1136625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1136641 : List Nat := [1, 2, 4, 1, 2, 1, 1, 4, 1, 6]
def baseStart_1136641 : Nat := 118140960795 + 1136641 * 2 ^ 59
def prefixEnd_1136641 : Nat := 4983230072969 + 3 ^ 40 * 1136641 * 2
def baseEnd_1136641 : Nat := 194547721535730873520063

theorem tailTrace_1136641 : CollatzResearch.WordTrace tailWord_1136641 prefixEnd_1136641 194547721535730873520063 := by
  unfold tailWord_1136641
  simp only [CollatzResearch.WordTrace]
  refine ⟨41456703075151254673001777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27637802050100836448667851 41456703075151254673001777)
  ·
    refine ⟨31092527306363441004751333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41456703075151254673001777 31092527306363441004751333)
    ·
      refine ⟨5829848869943145188390875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 31092527306363441004751333 5829848869943145188390875)
      ·
        refine ⟨8744773304914717782586313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5829848869943145188390875 8744773304914717782586313)
        ·
          refine ⟨6558579978686038336939735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8744773304914717782586313 6558579978686038336939735)
          ·
            refine ⟨9837869968029057505409603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6558579978686038336939735 9837869968029057505409603)
            ·
              refine ⟨14756804952043586258114405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9837869968029057505409603 14756804952043586258114405)
              ·
                refine ⟨2766900928508172423396451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14756804952043586258114405 2766900928508172423396451)
                ·
                  refine ⟨4150351392762258635094677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2766900928508172423396451 4150351392762258635094677)
                  ·
                    refine ⟨194547721535730873520063, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4150351392762258635094677 194547721535730873520063)
                    ·
                      rfl

theorem cell23_1136641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 1, 4, 1, 6].length) (baseStart_1136641 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1136641 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1136641 prefixEnd_1136641 := by exact prefixLift 1136641
  have htrace : WordTrace (prefixWord ++ tailWord_1136641) baseStart_1136641 baseEnd_1136641 := by
    simpa [prefixWord, tailWord_1136641, baseEnd_1136641] using wordTrace_append hprefix tailTrace_1136641
  have hstable : (prefixWord ++ tailWord_1136641).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1136641).length < 2 ^ (prefixWord ++ tailWord_1136641).sum := by decide
  have hdescent : baseEnd_1136641 < baseStart_1136641 := by decide
  rcases family_descends (prefixWord ++ tailWord_1136641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1136645 : List Nat := [1, 3, 1, 1, 2, 6, 2, 1, 1, 5]
def baseStart_1136645 : Nat := 118140960795 + 1136645 * 2 ^ 59
def prefixEnd_1136645 : Nat := 4983230072969 + 3 ^ 40 * 1136645 * 2
def baseEnd_1136645 : Nat := 194548406176603534970057

theorem tailTrace_1136645 : CollatzResearch.WordTrace tailWord_1136645 prefixEnd_1136645 194548406176603534970057 := by
  unfold tailWord_1136645
  simp only [CollatzResearch.WordTrace]
  refine ⟨41456848967136763356147389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27637899311424508904098259 41456848967136763356147389)
  ·
    refine ⟨15546318362676286258555271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 41456848967136763356147389 15546318362676286258555271)
    ·
      refine ⟨23319477544014429387832907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15546318362676286258555271 23319477544014429387832907)
      ·
        refine ⟨34979216316021644081749361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23319477544014429387832907 34979216316021644081749361)
        ·
          refine ⟨26234412237016233061312021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34979216316021644081749361 26234412237016233061312021)
          ·
            refine ⟨1229738073610135924749001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 26234412237016233061312021 1229738073610135924749001)
            ·
              refine ⟨922303555207601943561751, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1229738073610135924749001 922303555207601943561751)
              ·
                refine ⟨1383455332811402915342627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 922303555207601943561751 1383455332811402915342627)
                ·
                  refine ⟨2075182999217104373013941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1383455332811402915342627 2075182999217104373013941)
                  ·
                    refine ⟨194548406176603534970057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2075182999217104373013941 194548406176603534970057)
                    ·
                      rfl

theorem cell23_1136645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 6, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 6, 2, 1, 1, 5].length) (baseStart_1136645 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1136645 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1136645 prefixEnd_1136645 := by exact prefixLift 1136645
  have htrace : WordTrace (prefixWord ++ tailWord_1136645) baseStart_1136645 baseEnd_1136645 := by
    simpa [prefixWord, tailWord_1136645, baseEnd_1136645] using wordTrace_append hprefix tailTrace_1136645
  have hstable : (prefixWord ++ tailWord_1136645).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1136645).length < 2 ^ (prefixWord ++ tailWord_1136645).sum := by decide
  have hdescent : baseEnd_1136645 < baseStart_1136645 := by decide
  rcases family_descends (prefixWord ++ tailWord_1136645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1136648 : List Nat := [2, 1, 3, 2, 1, 2, 3, 3, 1, 1, 4]
def baseStart_1136648 : Nat := 118140960795 + 1136648 * 2 ^ 59
def prefixEnd_1136648 : Nat := 4983230072969 + 3 ^ 40 * 1136648 * 2
def baseEnd_1136648 : Nat := 583646758971774093172657

theorem tailTrace_1136648 : CollatzResearch.WordTrace tailWord_1136648 prefixEnd_1136648 583646758971774093172657 := by
  unfold tailWord_1136648
  simp only [CollatzResearch.WordTrace]
  refine ⟨20728479193062947434253299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27637972257417263245671065 20728479193062947434253299)
  ·
    refine ⟨31092718789594421151379949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20728479193062947434253299 31092718789594421151379949)
    ·
      refine ⟨11659769546097907931767481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 31092718789594421151379949 11659769546097907931767481)
      ·
        refine ⟨8744827159573430948825611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11659769546097907931767481 8744827159573430948825611)
        ·
          refine ⟨13117240739360146423238417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8744827159573430948825611 13117240739360146423238417)
          ·
            refine ⟨9837930554520109817428813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13117240739360146423238417 9837930554520109817428813)
            ·
              refine ⟨3689223957945041181535805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9837930554520109817428813 3689223957945041181535805)
              ·
                refine ⟨1383458984229390443075927, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3689223957945041181535805 1383458984229390443075927)
                ·
                  refine ⟨2075188476344085664613891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1383458984229390443075927 2075188476344085664613891)
                  ·
                    refine ⟨3112782714516128496920837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2075188476344085664613891 3112782714516128496920837)
                    ·
                      refine ⟨583646758971774093172657, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3112782714516128496920837 583646758971774093172657)
                      ·
                        rfl

theorem cell23_1136648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 3, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 3, 3, 1, 1, 4].length) (baseStart_1136648 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1136648 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1136648 prefixEnd_1136648 := by exact prefixLift 1136648
  have htrace : WordTrace (prefixWord ++ tailWord_1136648) baseStart_1136648 baseEnd_1136648 := by
    simpa [prefixWord, tailWord_1136648, baseEnd_1136648] using wordTrace_append hprefix tailTrace_1136648
  have hstable : (prefixWord ++ tailWord_1136648).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1136648).length < 2 ^ (prefixWord ++ tailWord_1136648).sum := by decide
  have hdescent : baseEnd_1136648 < baseStart_1136648 := by decide
  rcases family_descends (prefixWord ++ tailWord_1136648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1136651 : List Nat := [1, 1, 1, 1, 6, 1, 2, 3, 1, 1, 5]
def baseStart_1136651 : Nat := 118140960795 + 1136651 * 2 ^ 59
def prefixEnd_1136651 : Nat := 4983230072969 + 3 ^ 40 * 1136651 * 2
def baseEnd_1136651 : Nat := 583648299413737581435143

theorem tailTrace_1136651 : CollatzResearch.WordTrace tailWord_1136651 prefixEnd_1136651 583648299413737581435143 := by
  unfold tailWord_1136651
  simp only [CollatzResearch.WordTrace]
  refine ⟨41457067805115026380865807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27638045203410017587243871 41457067805115026380865807)
  ·
    refine ⟨62185601707672539571298711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41457067805115026380865807 62185601707672539571298711)
    ·
      refine ⟨93278402561508809356948067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62185601707672539571298711 93278402561508809356948067)
      ·
        refine ⟨139917603842263214035422101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 93278402561508809356948067 139917603842263214035422101)
        ·
          refine ⟨6558637680106088157910411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 139917603842263214035422101 6558637680106088157910411)
          ·
            refine ⟨9837956520159132236865617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6558637680106088157910411 9837956520159132236865617)
            ·
              refine ⟨7378467390119349177649213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9837956520159132236865617 7378467390119349177649213)
              ·
                refine ⟨2766925271294755941618455, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7378467390119349177649213 2766925271294755941618455)
                ·
                  refine ⟨4150387906942133912427683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2766925271294755941618455 4150387906942133912427683)
                  ·
                    refine ⟨6225581860413200868641525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4150387906942133912427683 6225581860413200868641525)
                    ·
                      refine ⟨583648299413737581435143, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 6225581860413200868641525 583648299413737581435143)
                      ·
                        rfl

theorem cell23_1136651_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 2, 3, 1, 1, 5].length) (baseStart_1136651 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1136651 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1136651 prefixEnd_1136651 := by exact prefixLift 1136651
  have htrace : WordTrace (prefixWord ++ tailWord_1136651) baseStart_1136651 baseEnd_1136651 := by
    simpa [prefixWord, tailWord_1136651, baseEnd_1136651] using wordTrace_append hprefix tailTrace_1136651
  have hstable : (prefixWord ++ tailWord_1136651).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1136651).length < 2 ^ (prefixWord ++ tailWord_1136651).sum := by decide
  have hdescent : baseEnd_1136651 < baseStart_1136651 := by decide
  rcases family_descends (prefixWord ++ tailWord_1136651) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1136668 : List Nat := [2, 2, 3, 1, 3, 2, 1, 2, 1, 1, 5]
def baseStart_1136668 : Nat := 118140960795 + 1136668 * 2 ^ 59
def prefixEnd_1136668 : Nat := 4983230072969 + 3 ^ 40 * 1136668 * 2
def baseEnd_1136668 : Nat := 583657028584864014922565

theorem tailTrace_1136668 : CollatzResearch.WordTrace tailWord_1136668 prefixEnd_1136668 583657028584864014922565 := by
  unfold tailWord_1136668
  simp only [CollatzResearch.WordTrace]
  refine ⟨20728843923026719142117329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27638458564035625522823105 20728843923026719142117329)
  ·
    refine ⟨15546632942270039356587997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20728843923026719142117329 15546632942270039356587997)
    ·
      refine ⟨5829987353351264758720499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15546632942270039356587997 5829987353351264758720499)
      ·
        refine ⟨8744981030026897138080749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5829987353351264758720499 8744981030026897138080749)
        ·
          refine ⟨3279367886260086426780281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8744981030026897138080749 3279367886260086426780281)
          ·
            refine ⟨2459525914695064820085211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3279367886260086426780281 2459525914695064820085211)
            ·
              refine ⟨3689288872042597230127817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2459525914695064820085211 3689288872042597230127817)
              ·
                refine ⟨2766966654031947922595863, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3689288872042597230127817 2766966654031947922595863)
                ·
                  refine ⟨4150449981047921883893795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2766966654031947922595863 4150449981047921883893795)
                  ·
                    refine ⟨6225674971571882825840693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4150449981047921883893795 6225674971571882825840693)
                    ·
                      refine ⟨583657028584864014922565, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 6225674971571882825840693 583657028584864014922565)
                      ·
                        rfl

theorem cell23_1136668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 2, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 2, 1, 2, 1, 1, 5].length) (baseStart_1136668 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1136668 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1136668 prefixEnd_1136668 := by exact prefixLift 1136668
  have htrace : WordTrace (prefixWord ++ tailWord_1136668) baseStart_1136668 baseEnd_1136668 := by
    simpa [prefixWord, tailWord_1136668, baseEnd_1136668] using wordTrace_append hprefix tailTrace_1136668
  have hstable : (prefixWord ++ tailWord_1136668).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1136668).length < 2 ^ (prefixWord ++ tailWord_1136668).sum := by decide
  have hdescent : baseEnd_1136668 < baseStart_1136668 := by decide
  rcases family_descends (prefixWord ++ tailWord_1136668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1136675 : List Nat := [1, 1, 1, 4, 3, 1, 5, 1, 2, 4]
def baseStart_1136675 : Nat := 118140960795 + 1136675 * 2 ^ 59
def prefixEnd_1136675 : Nat := 4983230072969 + 3 ^ 40 * 1136675 * 2
def baseEnd_1136675 : Nat := 194553540983148495845011

theorem tailTrace_1136675 : CollatzResearch.WordTrace tailWord_1136675 prefixEnd_1136675 194553540983148495845011 := by
  unfold tailWord_1136675
  simp only [CollatzResearch.WordTrace]
  refine ⟨41457943157028078479739479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27638628771352052319826319 41457943157028078479739479)
  ·
    refine ⟨62186914735542117719609219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41457943157028078479739479 62186914735542117719609219)
    ·
      refine ⟨93280372103313176579413829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62186914735542117719609219 93280372103313176579413829)
      ·
        refine ⟨17490069769371220608640093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 93280372103313176579413829 17490069769371220608640093)
        ·
          refine ⟨6558776163514207728240035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17490069769371220608640093 6558776163514207728240035)
          ·
            refine ⟨9838164245271311592360053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6558776163514207728240035 9838164245271311592360053)
            ·
              refine ⟨922327897994185461783755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 9838164245271311592360053 922327897994185461783755)
              ·
                refine ⟨1383491846991278192675633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 922327897994185461783755 1383491846991278192675633)
                ·
                  refine ⟨1037618885243458644506725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1383491846991278192675633 1037618885243458644506725)
                  ·
                    refine ⟨194553540983148495845011, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1037618885243458644506725 194553540983148495845011)
                    ·
                      rfl

theorem cell23_1136675_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 5, 1, 2, 4].length) (baseStart_1136675 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1136675 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1136675 prefixEnd_1136675 := by exact prefixLift 1136675
  have htrace : WordTrace (prefixWord ++ tailWord_1136675) baseStart_1136675 baseEnd_1136675 := by
    simpa [prefixWord, tailWord_1136675, baseEnd_1136675] using wordTrace_append hprefix tailTrace_1136675
  have hstable : (prefixWord ++ tailWord_1136675).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1136675).length < 2 ^ (prefixWord ++ tailWord_1136675).sum := by decide
  have hdescent : baseEnd_1136675 < baseStart_1136675 := by decide
  rcases family_descends (prefixWord ++ tailWord_1136675) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1136682 : List Nat := [3, 1, 4, 1, 2, 1, 2, 2, 3, 2, 2]
def baseStart_1136682 : Nat := 118140960795 + 1136682 * 2 ^ 59
def prefixEnd_1136682 : Nat := 4983230072969 + 3 ^ 40 * 1136682 * 2
def baseEnd_1136682 : Nat := 583664217314026960147501

theorem tailTrace_1136682 : CollatzResearch.WordTrace tailWord_1136682 prefixEnd_1136682 583664217314026960147501 := by
  unfold tailWord_1136682
  simp only [CollatzResearch.WordTrace]
  refine ⟨10364549617000679668811075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 27638798978668479116829533 10364549617000679668811075)
  ·
    refine ⟨15546824425501019503216613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10364549617000679668811075 15546824425501019503216613)
    ·
      refine ⟨2915029579781441156853115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 15546824425501019503216613 2915029579781441156853115)
      ·
        refine ⟨4372544369672161735279673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2915029579781441156853115 4372544369672161735279673)
        ·
          refine ⟨3279408277254121301459755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4372544369672161735279673 3279408277254121301459755)
          ·
            refine ⟨4919112415881181952189633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3279408277254121301459755 4919112415881181952189633)
            ·
              refine ⟨3689334311910886464142225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4919112415881181952189633 3689334311910886464142225)
              ·
                refine ⟨2767000733933164848106669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3689334311910886464142225 2767000733933164848106669)
                ·
                  refine ⟨1037625275224936818040001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2767000733933164848106669 1037625275224936818040001)
                  ·
                    refine ⟨778218956418702613530001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1037625275224936818040001 778218956418702613530001)
                    ·
                      refine ⟨583664217314026960147501, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 778218956418702613530001 583664217314026960147501)
                      ·
                        rfl

theorem cell23_1136682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 1, 2, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 1, 2, 2, 3, 2, 2].length) (baseStart_1136682 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1136682 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1136682 prefixEnd_1136682 := by exact prefixLift 1136682
  have htrace : WordTrace (prefixWord ++ tailWord_1136682) baseStart_1136682 baseEnd_1136682 := by
    simpa [prefixWord, tailWord_1136682, baseEnd_1136682] using wordTrace_append hprefix tailTrace_1136682
  have hstable : (prefixWord ++ tailWord_1136682).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1136682).length < 2 ^ (prefixWord ++ tailWord_1136682).sum := by decide
  have hdescent : baseEnd_1136682 < baseStart_1136682 := by decide
  rcases family_descends (prefixWord ++ tailWord_1136682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1136688 : List Nat := [2, 1, 1, 1, 2, 7, 2, 7]
def baseStart_1136688 : Nat := 118140960795 + 1136688 * 2 ^ 59
def prefixEnd_1136688 : Nat := 4983230072969 + 3 ^ 40 * 1136688 * 2
def baseEnd_1136688 : Nat := 21617307340664960617499

theorem tailTrace_1136688 : CollatzResearch.WordTrace tailWord_1136688 prefixEnd_1136688 21617307340664960617499 := by
  unfold tailWord_1136688
  simp only [CollatzResearch.WordTrace]
  refine ⟨20729208652990490849981359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27638944870653987799975145 20729208652990490849981359)
  ·
    refine ⟨31093812979485736274972039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20729208652990490849981359 31093812979485736274972039)
    ·
      refine ⟨46640719469228604412458059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31093812979485736274972039 46640719469228604412458059)
      ·
        refine ⟨69961079203842906618687089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46640719469228604412458059 69961079203842906618687089)
        ·
          refine ⟨52470809402882179964015317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 69961079203842906618687089 52470809402882179964015317)
          ·
            refine ⟨1229784595380051092906609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 52470809402882179964015317 1229784595380051092906609)
            ·
              refine ⟨922338446535038319679957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1229784595380051092906609 922338446535038319679957)
              ·
                refine ⟨21617307340664960617499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 922338446535038319679957 21617307340664960617499)
                ·
                  rfl

theorem cell23_1136688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 7, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 7, 2, 7].length) (baseStart_1136688 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1136688 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1136688 prefixEnd_1136688 := by exact prefixLift 1136688
  have htrace : WordTrace (prefixWord ++ tailWord_1136688) baseStart_1136688 baseEnd_1136688 := by
    simpa [prefixWord, tailWord_1136688, baseEnd_1136688] using wordTrace_append hprefix tailTrace_1136688
  have hstable : (prefixWord ++ tailWord_1136688).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1136688).length < 2 ^ (prefixWord ++ tailWord_1136688).sum := by decide
  have hdescent : baseEnd_1136688 < baseStart_1136688 := by decide
  rcases family_descends (prefixWord ++ tailWord_1136688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1136711 : List Nat := [1, 1, 4, 1, 3, 1, 1, 2, 2, 2, 5]
def baseStart_1136711 : Nat := 118140960795 + 1136711 * 2 ^ 59
def prefixEnd_1136711 : Nat := 4983230072969 + 3 ^ 40 * 1136711 * 2
def baseEnd_1136711 : Nat := 583679108253007346684867

theorem tailTrace_1136711 : CollatzResearch.WordTrace tailWord_1136711 prefixEnd_1136711 583679108253007346684867 := by
  unfold tailWord_1136711
  simp only [CollatzResearch.WordTrace]
  refine ⟨41459256184897656628049987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27639504123265104418699991 41459256184897656628049987)
  ·
    refine ⟨62188884277346484942074981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41459256184897656628049987 62188884277346484942074981)
    ·
      refine ⟨11660415802002465926639059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 62188884277346484942074981 11660415802002465926639059)
      ·
        refine ⟨17490623703003698889958589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11660415802002465926639059 17490623703003698889958589)
        ·
          refine ⟨6558983888626387083734471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17490623703003698889958589 6558983888626387083734471)
          ·
            refine ⟨9838475832939580625601707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6558983888626387083734471 9838475832939580625601707)
            ·
              refine ⟨14757713749409370938402561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9838475832939580625601707 14757713749409370938402561)
              ·
                refine ⟨11068285312057028203801921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14757713749409370938402561 11068285312057028203801921)
                ·
                  refine ⟨8301213984042771152851441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11068285312057028203801921 8301213984042771152851441)
                  ·
                    refine ⟨6225910488032078364638581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8301213984042771152851441 6225910488032078364638581)
                    ·
                      refine ⟨583679108253007346684867, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 6225910488032078364638581 583679108253007346684867)
                      ·
                        rfl

theorem cell23_1136711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 1, 2, 2, 2, 5].length) (baseStart_1136711 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1136711 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1136711 prefixEnd_1136711 := by exact prefixLift 1136711
  have htrace : WordTrace (prefixWord ++ tailWord_1136711) baseStart_1136711 baseEnd_1136711 := by
    simpa [prefixWord, tailWord_1136711, baseEnd_1136711] using wordTrace_append hprefix tailTrace_1136711
  have hstable : (prefixWord ++ tailWord_1136711).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1136711).length < 2 ^ (prefixWord ++ tailWord_1136711).sum := by decide
  have hdescent : baseEnd_1136711 < baseStart_1136711 := by decide
  rcases family_descends (prefixWord ++ tailWord_1136711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1136721 : List Nat := [1, 2, 2, 1, 3, 1, 1, 3, 2, 3, 4]
def baseStart_1136721 : Nat := 118140960795 + 1136721 * 2 ^ 59
def prefixEnd_1136721 : Nat := 4983230072969 + 3 ^ 40 * 1136721 * 2
def baseEnd_1136721 : Nat := 583684243059552307559821

theorem tailTrace_1136721 : CollatzResearch.WordTrace tailWord_1136721 prefixEnd_1136721 583684243059552307559821 := by
  unfold tailWord_1136721
  simp only [CollatzResearch.WordTrace]
  refine ⟨41459620914861428335914017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27639747276574285557276011 41459620914861428335914017)
  ·
    refine ⟨31094715686146071251935513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41459620914861428335914017 31094715686146071251935513)
    ·
      refine ⟨23321036764609553438951635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31094715686146071251935513 23321036764609553438951635)
      ·
        refine ⟨34981555146914330158427453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23321036764609553438951635 34981555146914330158427453)
        ·
          refine ⟨13118083180092873809410295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 34981555146914330158427453 13118083180092873809410295)
          ·
            refine ⟨19677124770139310714115443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13118083180092873809410295 19677124770139310714115443)
            ·
              refine ⟨29515687155208966071173165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19677124770139310714115443 29515687155208966071173165)
              ·
                refine ⟨11068382683203362276689937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 29515687155208966071173165 11068382683203362276689937)
                ·
                  refine ⟨8301287012402521707517453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11068382683203362276689937 8301287012402521707517453)
                  ·
                    refine ⟨3112982629650945640319045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8301287012402521707517453 3112982629650945640319045)
                    ·
                      refine ⟨583684243059552307559821, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3112982629650945640319045 583684243059552307559821)
                      ·
                        rfl

theorem cell23_1136721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 1, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 1, 3, 2, 3, 4].length) (baseStart_1136721 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1136721 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1136721 prefixEnd_1136721 := by exact prefixLift 1136721
  have htrace : WordTrace (prefixWord ++ tailWord_1136721) baseStart_1136721 baseEnd_1136721 := by
    simpa [prefixWord, tailWord_1136721, baseEnd_1136721] using wordTrace_append hprefix tailTrace_1136721
  have hstable : (prefixWord ++ tailWord_1136721).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1136721).length < 2 ^ (prefixWord ++ tailWord_1136721).sum := by decide
  have hdescent : baseEnd_1136721 < baseStart_1136721 := by decide
  rcases family_descends (prefixWord ++ tailWord_1136721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1136726 : List Nat := [5, 2, 2, 1, 1, 3, 2, 1, 2, 4]
def baseStart_1136726 : Nat := 118140960795 + 1136726 * 2 ^ 59
def prefixEnd_1136726 : Nat := 4983230072969 + 3 ^ 40 * 1136726 * 2
def baseEnd_1136726 : Nat := 194562270154274929332433

theorem tailTrace_1136726 : CollatzResearch.WordTrace tailWord_1136726 prefixEnd_1136726 194562270154274929332433 := by
  unfold tailWord_1136726
  simp only [CollatzResearch.WordTrace]
  refine ⟨2591237704990207136865377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 27639868853228876126564021 2591237704990207136865377)
  ·
    refine ⟨1943428278742655352649033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2591237704990207136865377 1943428278742655352649033)
    ·
      refine ⟨1457571209056991514486775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1943428278742655352649033 1457571209056991514486775)
      ·
        refine ⟨2186356813585487271730163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1457571209056991514486775 2186356813585487271730163)
        ·
          refine ⟨3279535220378230907595245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2186356813585487271730163 3279535220378230907595245)
          ·
            refine ⟨1229825707641836590348217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3279535220378230907595245 1229825707641836590348217)
            ·
              refine ⟨922369280731377442761163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1229825707641836590348217 922369280731377442761163)
              ·
                refine ⟨1383553921097066164141745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 922369280731377442761163 1383553921097066164141745)
                ·
                  refine ⟨1037665440822799623106309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1383553921097066164141745 1037665440822799623106309)
                  ·
                    refine ⟨194562270154274929332433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1037665440822799623106309 194562270154274929332433)
                    ·
                      rfl

theorem cell23_1136726_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 3, 2, 1, 2, 4].length) (baseStart_1136726 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1136726 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1136726 prefixEnd_1136726 := by exact prefixLift 1136726
  have htrace : WordTrace (prefixWord ++ tailWord_1136726) baseStart_1136726 baseEnd_1136726 := by
    simpa [prefixWord, tailWord_1136726, baseEnd_1136726] using wordTrace_append hprefix tailTrace_1136726
  have hstable : (prefixWord ++ tailWord_1136726).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1136726).length < 2 ^ (prefixWord ++ tailWord_1136726).sum := by decide
  have hdescent : baseEnd_1136726 < baseStart_1136726 := by decide
  rcases family_descends (prefixWord ++ tailWord_1136726) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1136732 : List Nat := [2, 2, 4, 1, 1, 3, 1, 3, 2, 1, 3]
def baseStart_1136732 : Nat := 118140960795 + 1136732 * 2 ^ 59
def prefixEnd_1136732 : Nat := 4983230072969 + 3 ^ 40 * 1136732 * 2
def baseEnd_1136732 : Nat := 583689891346751764522271

theorem tailTrace_1136732 : CollatzResearch.WordTrace tailWord_1136732 prefixEnd_1136732 583689891346751764522271 := by
  unfold tailWord_1136732
  simp only [CollatzResearch.WordTrace]
  refine ⟨20730011058910788607282225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27640014745214384809709633 20730011058910788607282225)
  ·
    refine ⟨15547508294183091455461669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20730011058910788607282225 15547508294183091455461669)
    ·
      refine ⟨2915157805159329647899063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 15547508294183091455461669 2915157805159329647899063)
      ·
        refine ⟨4372736707738994471848595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2915157805159329647899063 4372736707738994471848595)
        ·
          refine ⟨6559105061608491707772893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4372736707738994471848595 6559105061608491707772893)
          ·
            refine ⟨2459664398103184390414835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6559105061608491707772893 2459664398103184390414835)
            ·
              refine ⟨3689496597154776585622253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2459664398103184390414835 3689496597154776585622253)
              ·
                refine ⟨1383561223933041219608345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3689496597154776585622253 1383561223933041219608345)
                ·
                  refine ⟨1037670917949780914706259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1383561223933041219608345 1037670917949780914706259)
                  ·
                    refine ⟨1556506376924671372059389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1037670917949780914706259 1556506376924671372059389)
                    ·
                      refine ⟨583689891346751764522271, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1556506376924671372059389 583689891346751764522271)
                      ·
                        rfl

theorem cell23_1136732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 3, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 3, 1, 3, 2, 1, 3].length) (baseStart_1136732 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1136732 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1136732 prefixEnd_1136732 := by exact prefixLift 1136732
  have htrace : WordTrace (prefixWord ++ tailWord_1136732) baseStart_1136732 baseEnd_1136732 := by
    simpa [prefixWord, tailWord_1136732, baseEnd_1136732] using wordTrace_append hprefix tailTrace_1136732
  have hstable : (prefixWord ++ tailWord_1136732).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1136732).length < 2 ^ (prefixWord ++ tailWord_1136732).sum := by decide
  have hdescent : baseEnd_1136732 < baseStart_1136732 := by decide
  rcases family_descends (prefixWord ++ tailWord_1136732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1136851 : List Nat := [1, 1, 1, 2, 1, 1, 1, 3, 12]
def baseStart_1136851 : Nat := 118140960795 + 1136851 * 2 ^ 59
def prefixEnd_1136851 : Nat := 4983230072969 + 3 ^ 40 * 1136851 * 2
def baseEnd_1136851 : Nat := 64861221727181866548247

theorem tailTrace_1136851 : CollatzResearch.WordTrace tailWord_1136851 prefixEnd_1136851 64861221727181866548247 := by
  unfold tailWord_1136851
  simp only [CollatzResearch.WordTrace]
  refine ⟨41464362404390460538146407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27642908269593640358764271 41464362404390460538146407)
  ·
    refine ⟨62196543606585690807219611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41464362404390460538146407 62196543606585690807219611)
    ·
      refine ⟨93294815409878536210829417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62196543606585690807219611 93294815409878536210829417)
      ·
        refine ⟨69971111557408902158122063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 93294815409878536210829417 69971111557408902158122063)
        ·
          refine ⟨104956667336113353237183095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 69971111557408902158122063 104956667336113353237183095)
          ·
            refine ⟨157435001004170029855774643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 104956667336113353237183095 157435001004170029855774643)
            ·
              refine ⟨236152501506255044783661965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 157435001004170029855774643 236152501506255044783661965)
              ·
                refine ⟨88557188064845641793873237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 236152501506255044783661965 88557188064845641793873237)
                ·
                  refine ⟨64861221727181866548247, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 12 88557188064845641793873237 64861221727181866548247)
                  ·
                    rfl

theorem cell23_1136851_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 3, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 3, 12].length) (baseStart_1136851 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1136851 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1136851 prefixEnd_1136851 := by exact prefixLift 1136851
  have htrace : WordTrace (prefixWord ++ tailWord_1136851) baseStart_1136851 baseEnd_1136851 := by
    simpa [prefixWord, tailWord_1136851, baseEnd_1136851] using wordTrace_append hprefix tailTrace_1136851
  have hstable : (prefixWord ++ tailWord_1136851).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1136851).length < 2 ^ (prefixWord ++ tailWord_1136851).sum := by decide
  have hdescent : baseEnd_1136851 < baseStart_1136851 := by decide
  rcases family_descends (prefixWord ++ tailWord_1136851) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1136865 : List Nat := [1, 2, 3, 1, 3, 1, 2, 3, 2, 2, 3]
def baseStart_1136865 : Nat := 118140960795 + 1136865 * 2 ^ 59
def prefixEnd_1136865 : Nat := 4983230072969 + 3 ^ 40 * 1136865 * 2
def baseEnd_1136865 : Nat := 583758184273799744159159

theorem tailTrace_1136865 : CollatzResearch.WordTrace tailWord_1136865 prefixEnd_1136865 583758184273799744159159 := by
  unfold tailWord_1136865
  simp only [CollatzResearch.WordTrace]
  refine ⟨41464873026339740929156049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27643248684226493952770699 41464873026339740929156049)
  ·
    refine ⟨31098654769754805696867037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41464873026339740929156049 31098654769754805696867037)
    ·
      refine ⟨11661995538658052136325139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 31098654769754805696867037 11661995538658052136325139)
      ·
        refine ⟨17492993307987078204487709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11661995538658052136325139 17492993307987078204487709)
        ·
          refine ⟨6559872490495154326682891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17492993307987078204487709 6559872490495154326682891)
          ·
            refine ⟨9839808735742731490024337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6559872490495154326682891 9839808735742731490024337)
            ·
              refine ⟨7379856551807048617518253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9839808735742731490024337 7379856551807048617518253)
              ·
                refine ⟨2767446206927643231569345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7379856551807048617518253 2767446206927643231569345)
                ·
                  refine ⟨2075584655195732423677009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2767446206927643231569345 2075584655195732423677009)
                  ·
                    refine ⟨1556688491396799317757757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2075584655195732423677009 1556688491396799317757757)
                    ·
                      refine ⟨583758184273799744159159, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1556688491396799317757757 583758184273799744159159)
                      ·
                        rfl

theorem cell23_1136865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 2, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 2, 3, 2, 2, 3].length) (baseStart_1136865 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1136865 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1136865 prefixEnd_1136865 := by exact prefixLift 1136865
  have htrace : WordTrace (prefixWord ++ tailWord_1136865) baseStart_1136865 baseEnd_1136865 := by
    simpa [prefixWord, tailWord_1136865, baseEnd_1136865] using wordTrace_append hprefix tailTrace_1136865
  have hstable : (prefixWord ++ tailWord_1136865).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1136865).length < 2 ^ (prefixWord ++ tailWord_1136865).sum := by decide
  have hdescent : baseEnd_1136865 < baseStart_1136865 := by decide
  rcases family_descends (prefixWord ++ tailWord_1136865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1136882 : List Nat := [3, 2, 1, 3, 2, 2, 1, 2, 2, 2, 3]
def baseStart_1136882 : Nat := 118140960795 + 1136882 * 2 ^ 59
def prefixEnd_1136882 : Nat := 4983230072969 + 3 ^ 40 * 1136882 * 2
def baseEnd_1136882 : Nat := 583766913444926177646581

theorem tailTrace_1136882 : CollatzResearch.WordTrace tailWord_1136882 prefixEnd_1136882 583766913444926177646581 := by
  unfold tailWord_1136882
  simp only [CollatzResearch.WordTrace]
  refine ⟨10366373266819538208131225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 27643662044852101888349933 10366373266819538208131225)
  ·
    refine ⟨7774779950114653656098419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10366373266819538208131225 7774779950114653656098419)
    ·
      refine ⟨11662169925171980484147629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7774779950114653656098419 11662169925171980484147629)
      ·
        refine ⟨4373313721939492681555361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11662169925171980484147629 4373313721939492681555361)
        ·
          refine ⟨3279985291454619511166521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4373313721939492681555361 3279985291454619511166521)
          ·
            refine ⟨2459988968590964633374891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3279985291454619511166521 2459988968590964633374891)
            ·
              refine ⟨3689983452886446950062337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2459988968590964633374891 3689983452886446950062337)
              ·
                refine ⟨2767487589664835212546753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3689983452886446950062337 2767487589664835212546753)
                ·
                  refine ⟨2075615692248626409410065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2767487589664835212546753 2075615692248626409410065)
                  ·
                    refine ⟨1556711769186469807057549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2075615692248626409410065 1556711769186469807057549)
                    ·
                      refine ⟨583766913444926177646581, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1556711769186469807057549 583766913444926177646581)
                      ·
                        rfl

theorem cell23_1136882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 2, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 2, 1, 2, 2, 2, 3].length) (baseStart_1136882 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1136882 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1136882 prefixEnd_1136882 := by exact prefixLift 1136882
  have htrace : WordTrace (prefixWord ++ tailWord_1136882) baseStart_1136882 baseEnd_1136882 := by
    simpa [prefixWord, tailWord_1136882, baseEnd_1136882] using wordTrace_append hprefix tailTrace_1136882
  have hstable : (prefixWord ++ tailWord_1136882).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1136882).length < 2 ^ (prefixWord ++ tailWord_1136882).sum := by decide
  have hdescent : baseEnd_1136882 < baseStart_1136882 := by decide
  rcases family_descends (prefixWord ++ tailWord_1136882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1136946 : List Nat := [3, 2, 1, 1, 5, 1, 1, 4, 1, 1, 3]
def baseStart_1136946 : Nat := 118140960795 + 1136946 * 2 ^ 59
def prefixEnd_1136946 : Nat := 4983230072969 + 3 ^ 40 * 1136946 * 2
def baseEnd_1136946 : Nat := 583799776206813927246287

theorem tailTrace_1136946 : CollatzResearch.WordTrace tailWord_1136946 prefixEnd_1136946 583799776206813927246287 := by
  unfold tailWord_1136946
  simp only [CollatzResearch.WordTrace]
  refine ⟨10366956834761572940713673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 27645218226030861175236461 10366956834761572940713673)
  ·
    refine ⟨7775217626071179705535255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10366956834761572940713673 7775217626071179705535255)
    ·
      refine ⟨11662826439106769558302883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7775217626071179705535255 11662826439106769558302883)
      ·
        refine ⟨17494239658660154337454325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11662826439106769558302883 17494239658660154337454325)
        ·
          refine ⟨1640084967999389469136343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 17494239658660154337454325 1640084967999389469136343)
          ·
            refine ⟨2460127451999084203704515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1640084967999389469136343 2460127451999084203704515)
            ·
              refine ⟨3690191177998626305556773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2460127451999084203704515 3690191177998626305556773)
              ·
                refine ⟨691910845874742432291895, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3690191177998626305556773 691910845874742432291895)
                ·
                  refine ⟨1037866268812113648437843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 691910845874742432291895 1037866268812113648437843)
                  ·
                    refine ⟨1556799403218170472656765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1037866268812113648437843 1556799403218170472656765)
                    ·
                      refine ⟨583799776206813927246287, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1556799403218170472656765 583799776206813927246287)
                      ·
                        rfl

theorem cell23_1136946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 5, 1, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 5, 1, 1, 4, 1, 1, 3].length) (baseStart_1136946 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1136946 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1136946 prefixEnd_1136946 := by exact prefixLift 1136946
  have htrace : WordTrace (prefixWord ++ tailWord_1136946) baseStart_1136946 baseEnd_1136946 := by
    simpa [prefixWord, tailWord_1136946, baseEnd_1136946] using wordTrace_append hprefix tailTrace_1136946
  have hstable : (prefixWord ++ tailWord_1136946).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1136946).length < 2 ^ (prefixWord ++ tailWord_1136946).sum := by decide
  have hdescent : baseEnd_1136946 < baseStart_1136946 := by decide
  rcases family_descends (prefixWord ++ tailWord_1136946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1136972 : List Nat := [2, 2, 1, 3, 2, 1, 2, 4, 1, 2, 3]
def baseStart_1136972 : Nat := 118140960795 + 1136972 * 2 ^ 59
def prefixEnd_1136972 : Nat := 4983230072969 + 3 ^ 40 * 1136972 * 2
def baseEnd_1136972 : Nat := 583813126703830825521167

theorem tailTrace_1136972 : CollatzResearch.WordTrace tailWord_1136972 prefixEnd_1136972 583813126703830825521167 := by
  unfold tailWord_1136972
  simp only [CollatzResearch.WordTrace]
  refine ⟨20734387818476049101650585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27645850424634732135534113 20734387818476049101650585)
  ·
    refine ⟨15550790863857036826237939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20734387818476049101650585 15550790863857036826237939)
    ·
      refine ⟨23326186295785555239356909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15550790863857036826237939 23326186295785555239356909)
      ·
        refine ⟨8747319860919583214758841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23326186295785555239356909 8747319860919583214758841)
        ·
          refine ⟨6560489895689687411069131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8747319860919583214758841 6560489895689687411069131)
          ·
            refine ⟨9840734843534531116603697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6560489895689687411069131 9840734843534531116603697)
            ·
              refine ⟨7380551132650898337452773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9840734843534531116603697 7380551132650898337452773)
              ·
                refine ⟨1383853337372043438272395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7380551132650898337452773 1383853337372043438272395)
                ·
                  refine ⟨2075780006058065157408593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1383853337372043438272395 2075780006058065157408593)
                  ·
                    refine ⟨1556835004543548868056445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2075780006058065157408593 1556835004543548868056445)
                    ·
                      refine ⟨583813126703830825521167, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1556835004543548868056445 583813126703830825521167)
                      ·
                        rfl

theorem cell23_1136972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 2, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 2, 4, 1, 2, 3].length) (baseStart_1136972 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1136972 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1136972 prefixEnd_1136972 := by exact prefixLift 1136972
  have htrace : WordTrace (prefixWord ++ tailWord_1136972) baseStart_1136972 baseEnd_1136972 := by
    simpa [prefixWord, tailWord_1136972, baseEnd_1136972] using wordTrace_append hprefix tailTrace_1136972
  have hstable : (prefixWord ++ tailWord_1136972).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1136972).length < 2 ^ (prefixWord ++ tailWord_1136972).sum := by decide
  have hdescent : baseEnd_1136972 < baseStart_1136972 := by decide
  rcases family_descends (prefixWord ++ tailWord_1136972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1137026 : List Nat := [3, 4, 2, 1, 2, 2, 2, 7]
def baseStart_1137026 : Nat := 118140960795 + 1137026 * 2 ^ 59
def prefixEnd_1137026 : Nat := 4983230072969 + 3 ^ 40 * 1137026 * 2
def baseEnd_1137026 : Nat := 21623735357747170897997

theorem tailTrace_1137026 : CollatzResearch.WordTrace tailWord_1137026 prefixEnd_1137026 21623735357747170897997 := by
  unfold tailWord_1137026
  simp only [CollatzResearch.WordTrace]
  refine ⟨10367686294689116356441733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 27647163452504310283844621 10367686294689116356441733)
  ·
    refine ⟨1943941180254209316832825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 10367686294689116356441733 1943941180254209316832825)
    ·
      refine ⟨1457955885190656987624619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1943941180254209316832825 1457955885190656987624619)
      ·
        refine ⟨2186933827785985481436929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1457955885190656987624619 2186933827785985481436929)
        ·
          refine ⟨1640200370839489111077697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2186933827785985481436929 1640200370839489111077697)
          ·
            refine ⟨1230150278129616833308273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1640200370839489111077697 1230150278129616833308273)
            ·
              refine ⟨922612708597212624981205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1230150278129616833308273 922612708597212624981205)
              ·
                refine ⟨21623735357747170897997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 922612708597212624981205 21623735357747170897997)
                ·
                  rfl

theorem cell23_1137026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 2, 2, 2, 7].length) (baseStart_1137026 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1137026 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1137026 prefixEnd_1137026 := by exact prefixLift 1137026
  have htrace : WordTrace (prefixWord ++ tailWord_1137026) baseStart_1137026 baseEnd_1137026 := by
    simpa [prefixWord, tailWord_1137026, baseEnd_1137026] using wordTrace_append hprefix tailTrace_1137026
  have hstable : (prefixWord ++ tailWord_1137026).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1137026).length < 2 ^ (prefixWord ++ tailWord_1137026).sum := by decide
  have hdescent : baseEnd_1137026 < baseStart_1137026 := by decide
  rcases family_descends (prefixWord ++ tailWord_1137026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
