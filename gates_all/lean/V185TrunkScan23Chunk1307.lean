import V185TrunkScan23Chunk1306

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_7741438 : List Nat := [4, 2, 2, 2, 1, 2, 2, 1, 2, 2, 3]
def baseStart_7741438 : Nat := 118140960795 + 7741438 * 2 ^ 59
def prefixEnd_7741438 : Nat := 4983230072969 + 3 ^ 40 * 7741438 * 2
def baseEnd_7741438 : Nat := 3975078650980987821922781

theorem tailTrace_7741438 : CollatzResearch.WordTrace tailWord_7741438 prefixEnd_7741438 3975078650980987821922781 := by
  unfold tailWord_7741438
  simp only [CollatzResearch.WordTrace]
  refine ⟨35294180016012466649397121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 188235626752066488796784645 35294180016012466649397121)
  ·
    refine ⟨26470635012009349987047841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35294180016012466649397121 26470635012009349987047841)
    ·
      refine ⟨19852976259007012490285881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26470635012009349987047841 19852976259007012490285881)
      ·
        refine ⟨14889732194255259367714411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19852976259007012490285881 14889732194255259367714411)
        ·
          refine ⟨22334598291382889051571617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14889732194255259367714411 22334598291382889051571617)
          ·
            refine ⟨16750948718537166788678713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22334598291382889051571617 16750948718537166788678713)
            ·
              refine ⟨12563211538902875091509035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16750948718537166788678713 12563211538902875091509035)
              ·
                refine ⟨18844817308354312637263553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12563211538902875091509035 18844817308354312637263553)
                ·
                  refine ⟨14133612981265734477947665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18844817308354312637263553 14133612981265734477947665)
                  ·
                    refine ⟨10600209735949300858460749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14133612981265734477947665 10600209735949300858460749)
                    ·
                      refine ⟨3975078650980987821922781, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10600209735949300858460749 3975078650980987821922781)
                      ·
                        rfl

theorem cell23_7741438_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 2, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 2, 2, 1, 2, 2, 3].length) (baseStart_7741438 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7741438 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7741438 prefixEnd_7741438 := by exact prefixLift 7741438
  have htrace : WordTrace (prefixWord ++ tailWord_7741438) baseStart_7741438 baseEnd_7741438 := by
    simpa [prefixWord, tailWord_7741438, baseEnd_7741438] using wordTrace_append hprefix tailTrace_7741438
  have hstable : (prefixWord ++ tailWord_7741438).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7741438).length < 2 ^ (prefixWord ++ tailWord_7741438).sum := by decide
  have hdescent : baseEnd_7741438 < baseStart_7741438 := by decide
  rcases family_descends (prefixWord ++ tailWord_7741438) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7741474 : List Nat := [3, 3, 1, 1, 1, 2, 1, 1, 5, 1, 4]
def baseStart_7741474 : Nat := 118140960795 + 7741474 * 2 ^ 59
def prefixEnd_7741474 : Nat := 4983230072969 + 3 ^ 40 * 7741474 * 2
def baseEnd_7741474 : Nat := 3975097136284549681072615

theorem tailTrace_7741474 : CollatzResearch.WordTrace tailWord_7741474 prefixEnd_7741474 3975097136284549681072615 := by
  unfold tailWord_7741474
  simp only [CollatzResearch.WordTrace]
  refine ⟨70588688288992327835871869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 188236502103979540895658317 70588688288992327835871869)
  ·
    refine ⟨26470758108372122938451951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 70588688288992327835871869 26470758108372122938451951)
    ·
      refine ⟨39706137162558184407677927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26470758108372122938451951 39706137162558184407677927)
      ·
        refine ⟨59559205743837276611516891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39706137162558184407677927 59559205743837276611516891)
        ·
          refine ⟨89338808615755914917275337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59559205743837276611516891 89338808615755914917275337)
          ·
            refine ⟨67004106461816936187956503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 89338808615755914917275337 67004106461816936187956503)
            ·
              refine ⟨100506159692725404281934755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67004106461816936187956503 100506159692725404281934755)
              ·
                refine ⟨150759239539088106422902133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 100506159692725404281934755 150759239539088106422902133)
                ·
                  refine ⟨14133678706789509977147075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 150759239539088106422902133 14133678706789509977147075)
                  ·
                    refine ⟨21200518060184264965720613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14133678706789509977147075 21200518060184264965720613)
                    ·
                      refine ⟨3975097136284549681072615, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21200518060184264965720613 3975097136284549681072615)
                      ·
                        rfl

theorem cell23_7741474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 1, 1, 5, 1, 4].length) (baseStart_7741474 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7741474 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7741474 prefixEnd_7741474 := by exact prefixLift 7741474
  have htrace : WordTrace (prefixWord ++ tailWord_7741474) baseStart_7741474 baseEnd_7741474 := by
    simpa [prefixWord, tailWord_7741474, baseEnd_7741474] using wordTrace_append hprefix tailTrace_7741474
  have hstable : (prefixWord ++ tailWord_7741474).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7741474).length < 2 ^ (prefixWord ++ tailWord_7741474).sum := by decide
  have hdescent : baseEnd_7741474 < baseStart_7741474 := by decide
  rcases family_descends (prefixWord ++ tailWord_7741474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7741491 : List Nat := [1, 1, 1, 2, 4, 1, 3, 1, 5, 2, 2]
def baseStart_7741491 : Nat := 118140960795 + 7741491 * 2 ^ 59
def prefixEnd_7741491 : Nat := 4983230072969 + 3 ^ 40 * 7741491 * 2
def baseEnd_7741491 : Nat := 3975105865455676114560037

theorem tailTrace_7741491 : CollatzResearch.WordTrace tailWord_7741491 prefixEnd_7741491 3975105865455676114560037 := by
  unfold tailWord_7741491
  simp only [CollatzResearch.WordTrace]
  refine ⟨282355373196907723246856327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188236915464605148831237551 282355373196907723246856327)
  ·
    refine ⟨423533059795361584870284491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 282355373196907723246856327 423533059795361584870284491)
    ·
      refine ⟨635299589693042377305426737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 423533059795361584870284491 635299589693042377305426737)
      ·
        refine ⟨476474692269781782979070053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 635299589693042377305426737 476474692269781782979070053)
        ·
          refine ⟨89339004800584084308575635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 476474692269781782979070053 89339004800584084308575635)
          ·
            refine ⟨134008507200876126462863453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89339004800584084308575635 134008507200876126462863453)
            ·
              refine ⟨50253190200328547423573795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 134008507200876126462863453 50253190200328547423573795)
              ·
                refine ⟨75379785300492821135360693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50253190200328547423573795 75379785300492821135360693)
                ·
                  refine ⟨7066854871921201981440065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 75379785300492821135360693 7066854871921201981440065)
                  ·
                    refine ⟨5300141153940901486080049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7066854871921201981440065 5300141153940901486080049)
                    ·
                      refine ⟨3975105865455676114560037, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5300141153940901486080049 3975105865455676114560037)
                      ·
                        rfl

theorem cell23_7741491_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 3, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 3, 1, 5, 2, 2].length) (baseStart_7741491 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7741491 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7741491 prefixEnd_7741491 := by exact prefixLift 7741491
  have htrace : WordTrace (prefixWord ++ tailWord_7741491) baseStart_7741491 baseEnd_7741491 := by
    simpa [prefixWord, tailWord_7741491, baseEnd_7741491] using wordTrace_append hprefix tailTrace_7741491
  have hstable : (prefixWord ++ tailWord_7741491).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7741491).length < 2 ^ (prefixWord ++ tailWord_7741491).sum := by decide
  have hdescent : baseEnd_7741491 < baseStart_7741491 := by decide
  rcases family_descends (prefixWord ++ tailWord_7741491) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7741502 : List Nat := [4, 2, 1, 3, 2, 1, 2, 3, 1, 1, 3]
def baseStart_7741502 : Nat := 118140960795 + 7741502 * 2 ^ 59
def prefixEnd_7741502 : Nat := 4983230072969 + 3 ^ 40 * 7741502 * 2
def baseEnd_7741502 : Nat := 3975111513742875571522487

theorem tailTrace_7741502 : CollatzResearch.WordTrace tailWord_7741502 prefixEnd_7741502 3975111513742875571522487 := by
  unfold tailWord_7741502
  simp only [CollatzResearch.WordTrace]
  refine ⟨35294471799983484015688345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 188237182933245248083671173 35294471799983484015688345)
  ·
    refine ⟨26470853849987613011766259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35294471799983484015688345 26470853849987613011766259)
    ·
      refine ⟨39706280774981419517649389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26470853849987613011766259 39706280774981419517649389)
      ·
        refine ⟨14889855290618032319118521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39706280774981419517649389 14889855290618032319118521)
        ·
          refine ⟨11167391467963524239338891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14889855290618032319118521 11167391467963524239338891)
          ·
            refine ⟨16751087201945286359008337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11167391467963524239338891 16751087201945286359008337)
            ·
              refine ⟨12563315401458964769256253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16751087201945286359008337 12563315401458964769256253)
              ·
                refine ⟨4711243275547111788471095, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12563315401458964769256253 4711243275547111788471095)
                ·
                  refine ⟨7066864913320667682706643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4711243275547111788471095 7066864913320667682706643)
                  ·
                    refine ⟨10600297369981001524059965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7066864913320667682706643 10600297369981001524059965)
                    ·
                      refine ⟨3975111513742875571522487, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10600297369981001524059965 3975111513742875571522487)
                      ·
                        rfl

theorem cell23_7741502_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 2, 1, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 2, 1, 2, 3, 1, 1, 3].length) (baseStart_7741502 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7741502 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7741502 prefixEnd_7741502 := by exact prefixLift 7741502
  have htrace : WordTrace (prefixWord ++ tailWord_7741502) baseStart_7741502 baseEnd_7741502 := by
    simpa [prefixWord, tailWord_7741502, baseEnd_7741502] using wordTrace_append hprefix tailTrace_7741502
  have hstable : (prefixWord ++ tailWord_7741502).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7741502).length < 2 ^ (prefixWord ++ tailWord_7741502).sum := by decide
  have hdescent : baseEnd_7741502 < baseStart_7741502 := by decide
  rcases family_descends (prefixWord ++ tailWord_7741502) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7741504 : List Nat := [2, 1, 1, 2, 2, 4, 2, 2, 1, 2, 4]
def baseStart_7741504 : Nat := 118140960795 + 7741504 * 2 ^ 59
def prefixEnd_7741504 : Nat := 4983230072969 + 3 ^ 40 * 7741504 * 2
def baseEnd_7741504 : Nat := 3975112540704184563697477

theorem tailTrace_7741504 : CollatzResearch.WordTrace tailWord_7741504 prefixEnd_7741504 3975112540704184563697477 := by
  unfold tailWord_7741504
  simp only [CollatzResearch.WordTrace]
  refine ⟨141177923672930313233539783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 188237231563907084311386377 141177923672930313233539783)
  ·
    refine ⟨211766885509395469850309675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141177923672930313233539783 211766885509395469850309675)
    ·
      refine ⟨317650328264093204775464513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 211766885509395469850309675 317650328264093204775464513)
      ·
        refine ⟨238237746198069903581598385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 317650328264093204775464513 238237746198069903581598385)
        ·
          refine ⟨178678309648552427686198789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 238237746198069903581598385 178678309648552427686198789)
          ·
            refine ⟨33502183059103580191162273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 178678309648552427686198789 33502183059103580191162273)
            ·
              refine ⟨25126637294327685143371705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33502183059103580191162273 25126637294327685143371705)
              ·
                refine ⟨18844977970745763857528779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25126637294327685143371705 18844977970745763857528779)
                ·
                  refine ⟨28267466956118645786293169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18844977970745763857528779 28267466956118645786293169)
                  ·
                    refine ⟨21200600217088984339719877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 28267466956118645786293169 21200600217088984339719877)
                    ·
                      refine ⟨3975112540704184563697477, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21200600217088984339719877 3975112540704184563697477)
                      ·
                        rfl

theorem cell23_7741504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 4, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 4, 2, 2, 1, 2, 4].length) (baseStart_7741504 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7741504 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7741504 prefixEnd_7741504 := by exact prefixLift 7741504
  have htrace : WordTrace (prefixWord ++ tailWord_7741504) baseStart_7741504 baseEnd_7741504 := by
    simpa [prefixWord, tailWord_7741504, baseEnd_7741504] using wordTrace_append hprefix tailTrace_7741504
  have hstable : (prefixWord ++ tailWord_7741504).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7741504).length < 2 ^ (prefixWord ++ tailWord_7741504).sum := by decide
  have hdescent : baseEnd_7741504 < baseStart_7741504 := by decide
  rcases family_descends (prefixWord ++ tailWord_7741504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7741511 : List Nat := [1, 1, 4, 1, 3, 1, 3, 3, 1, 2, 3]
def baseStart_7741511 : Nat := 118140960795 + 7741511 * 2 ^ 59
def prefixEnd_7741511 : Nat := 4983230072969 + 3 ^ 40 * 7741511 * 2
def baseEnd_7741511 : Nat := 3975116135068766036309945

theorem tailTrace_7741511 : CollatzResearch.WordTrace tailWord_7741511 prefixEnd_7741511 3975116135068766036309945 := by
  unfold tailWord_7741511
  simp only [CollatzResearch.WordTrace]
  refine ⟨282356102656835266662584387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188237401771223511108389591 282356102656835266662584387)
  ·
    refine ⟨423534153985252899993876581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 282356102656835266662584387 423534153985252899993876581)
    ·
      refine ⟨79412653872234918748851859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 423534153985252899993876581 79412653872234918748851859)
      ·
        refine ⟨119118980808352378123277789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79412653872234918748851859 119118980808352378123277789)
        ·
          refine ⟨44669617803132141796229171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 119118980808352378123277789 44669617803132141796229171)
          ·
            refine ⟨67004426704698212694343757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44669617803132141796229171 67004426704698212694343757)
            ·
              refine ⟨25126660014261829760378909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 67004426704698212694343757 25126660014261829760378909)
              ·
                refine ⟨9422497505348186160142091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25126660014261829760378909 9422497505348186160142091)
                ·
                  refine ⟨14133746258022279240213137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9422497505348186160142091 14133746258022279240213137)
                  ·
                    refine ⟨10600309693516709430159853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14133746258022279240213137 10600309693516709430159853)
                    ·
                      refine ⟨3975116135068766036309945, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10600309693516709430159853 3975116135068766036309945)
                      ·
                        rfl

theorem cell23_7741511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 3, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 3, 3, 1, 2, 3].length) (baseStart_7741511 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7741511 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7741511 prefixEnd_7741511 := by exact prefixLift 7741511
  have htrace : WordTrace (prefixWord ++ tailWord_7741511) baseStart_7741511 baseEnd_7741511 := by
    simpa [prefixWord, tailWord_7741511, baseEnd_7741511] using wordTrace_append hprefix tailTrace_7741511
  have hstable : (prefixWord ++ tailWord_7741511).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7741511).length < 2 ^ (prefixWord ++ tailWord_7741511).sum := by decide
  have hdescent : baseEnd_7741511 < baseStart_7741511 := by decide
  rcases family_descends (prefixWord ++ tailWord_7741511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7741518 : List Nat := [4, 1, 1, 1, 1, 6, 1, 2, 2, 4]
def baseStart_7741518 : Nat := 118140960795 + 7741518 * 2 ^ 59
def prefixEnd_7741518 : Nat := 4983230072969 + 3 ^ 40 * 7741518 * 2
def baseEnd_7741518 : Nat := 1325039909811115836307471

theorem tailTrace_7741518 : CollatzResearch.WordTrace tailWord_7741518 prefixEnd_7741518 1325039909811115836307471 := by
  unfold tailWord_7741518
  simp only [CollatzResearch.WordTrace]
  refine ⟨35294544745976238357261151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 188237571978539937905392805 35294544745976238357261151)
  ·
    refine ⟨52941817118964357535891727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35294544745976238357261151 52941817118964357535891727)
    ·
      refine ⟨79412725678446536303837591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52941817118964357535891727 79412725678446536303837591)
      ·
        refine ⟨119119088517669804455756387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79412725678446536303837591 119119088517669804455756387)
        ·
          refine ⟨178678632776504706683634581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 119119088517669804455756387 178678632776504706683634581)
          ·
            refine ⟨8375560911398658125795371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 178678632776504706683634581 8375560911398658125795371)
            ·
              refine ⟨12563341367097987188693057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8375560911398658125795371 12563341367097987188693057)
              ·
                refine ⟨9422506025323490391519793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12563341367097987188693057 9422506025323490391519793)
                ·
                  refine ⟨7066879518992617793639845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9422506025323490391519793 7066879518992617793639845)
                  ·
                    refine ⟨1325039909811115836307471, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7066879518992617793639845 1325039909811115836307471)
                    ·
                      rfl

theorem cell23_7741518_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 6, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 6, 1, 2, 2, 4].length) (baseStart_7741518 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7741518 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7741518 prefixEnd_7741518 := by exact prefixLift 7741518
  have htrace : WordTrace (prefixWord ++ tailWord_7741518) baseStart_7741518 baseEnd_7741518 := by
    simpa [prefixWord, tailWord_7741518, baseEnd_7741518] using wordTrace_append hprefix tailTrace_7741518
  have hstable : (prefixWord ++ tailWord_7741518).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7741518).length < 2 ^ (prefixWord ++ tailWord_7741518).sum := by decide
  have hdescent : baseEnd_7741518 < baseStart_7741518 := by decide
  rcases family_descends (prefixWord ++ tailWord_7741518) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7741525 : List Nat := [1, 3, 2, 2, 1, 3, 2, 4, 1, 2, 2]
def baseStart_7741525 : Nat := 118140960795 + 7741525 * 2 ^ 59
def prefixEnd_7741525 : Nat := 4983230072969 + 3 ^ 40 * 7741525 * 2
def baseEnd_7741525 : Nat := 3975123323797928981534881

theorem tailTrace_7741525 : CollatzResearch.WordTrace tailWord_7741525 prefixEnd_7741525 3975123323797928981534881 := by
  unfold tailWord_7741525
  simp only [CollatzResearch.WordTrace]
  refine ⟨282356613278784547053594029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188237742185856364702396019 282356613278784547053594029)
  ·
    refine ⟨105883729979544205145097761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 282356613278784547053594029 105883729979544205145097761)
    ·
      refine ⟨79412797484658153858823321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 105883729979544205145097761 79412797484658153858823321)
      ·
        refine ⟨59559598113493615394117491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79412797484658153858823321 59559598113493615394117491)
        ·
          refine ⟨89339397170240423091176237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59559598113493615394117491 89339397170240423091176237)
          ·
            refine ⟨33502273938840158659191089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 89339397170240423091176237 33502273938840158659191089)
            ·
              refine ⟨25126705454130118994393317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33502273938840158659191089 25126705454130118994393317)
              ·
                refine ⟨4711257272649397311448747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25126705454130118994393317 4711257272649397311448747)
                ·
                  refine ⟨7066885908974095967173121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4711257272649397311448747 7066885908974095967173121)
                  ·
                    refine ⟨5300164431730571975379841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7066885908974095967173121 5300164431730571975379841)
                    ·
                      refine ⟨3975123323797928981534881, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5300164431730571975379841 3975123323797928981534881)
                      ·
                        rfl

theorem cell23_7741525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 3, 2, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 3, 2, 4, 1, 2, 2].length) (baseStart_7741525 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7741525 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7741525 prefixEnd_7741525 := by exact prefixLift 7741525
  have htrace : WordTrace (prefixWord ++ tailWord_7741525) baseStart_7741525 baseEnd_7741525 := by
    simpa [prefixWord, tailWord_7741525, baseEnd_7741525] using wordTrace_append hprefix tailTrace_7741525
  have hstable : (prefixWord ++ tailWord_7741525).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7741525).length < 2 ^ (prefixWord ++ tailWord_7741525).sum := by decide
  have hdescent : baseEnd_7741525 < baseStart_7741525 := by decide
  rcases family_descends (prefixWord ++ tailWord_7741525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7741527 : List Nat := [1, 1, 3, 2, 2, 1, 2, 1, 1, 9]
def baseStart_7741527 : Nat := 118140960795 + 7741527 * 2 ^ 59
def prefixEnd_7741527 : Nat := 4983230072969 + 3 ^ 40 * 7741527 * 2
def baseEnd_7741527 : Nat := 1325041450253079324569957

theorem tailTrace_7741527 : CollatzResearch.WordTrace tailWord_7741527 prefixEnd_7741527 1325041450253079324569957 := by
  unfold tailWord_7741527
  simp only [CollatzResearch.WordTrace]
  refine ⟨282356686224777301395166835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188237790816518200930111223 282356686224777301395166835)
  ·
    refine ⟨423535029337165952092750253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 282356686224777301395166835 423535029337165952092750253)
    ·
      refine ⟨158825636001437232034781345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 423535029337165952092750253 158825636001437232034781345)
      ·
        refine ⟨119119227001077924026086009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 158825636001437232034781345 119119227001077924026086009)
        ·
          refine ⟨89339420250808443019564507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 119119227001077924026086009 89339420250808443019564507)
          ·
            refine ⟨134009130376212664529346761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89339420250808443019564507 134009130376212664529346761)
            ·
              refine ⟨100506847782159498397010071, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 134009130376212664529346761 100506847782159498397010071)
              ·
                refine ⟨150760271673239247595515107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 100506847782159498397010071 150760271673239247595515107)
                ·
                  refine ⟨226140407509858871393272661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 150760271673239247595515107 226140407509858871393272661)
                  ·
                    refine ⟨1325041450253079324569957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 226140407509858871393272661 1325041450253079324569957)
                    ·
                      rfl

theorem cell23_7741527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 2, 1, 1, 9].length) (baseStart_7741527 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7741527 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7741527 prefixEnd_7741527 := by exact prefixLift 7741527
  have htrace : WordTrace (prefixWord ++ tailWord_7741527) baseStart_7741527 baseEnd_7741527 := by
    simpa [prefixWord, tailWord_7741527, baseEnd_7741527] using wordTrace_append hprefix tailTrace_7741527
  have hstable : (prefixWord ++ tailWord_7741527).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7741527).length < 2 ^ (prefixWord ++ tailWord_7741527).sum := by decide
  have hdescent : baseEnd_7741527 < baseStart_7741527 := by decide
  rcases family_descends (prefixWord ++ tailWord_7741527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7741541 : List Nat := [1, 3, 1, 3, 2, 2, 3, 1, 1, 3, 3]
def baseStart_7741541 : Nat := 118140960795 + 7741541 * 2 ^ 59
def prefixEnd_7741541 : Nat := 4983230072969 + 3 ^ 40 * 7741541 * 2
def baseEnd_7741541 : Nat := 3975131539488400918934807

theorem tailTrace_7741541 : CollatzResearch.WordTrace tailWord_7741541 prefixEnd_7741541 3975131539488400918934807 := by
  unfold tailWord_7741541
  simp only [CollatzResearch.WordTrace]
  refine ⟨282357196846726581786176477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188238131231151054524117651 282357196846726581786176477)
  ·
    refine ⟨105883948817522468169816179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 282357196846726581786176477 105883948817522468169816179)
    ·
      refine ⟨158825923226283702254724269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105883948817522468169816179 158825923226283702254724269)
      ·
        refine ⟨59559721209856388345521601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 158825923226283702254724269 59559721209856388345521601)
        ·
          refine ⟨44669790907392291259141201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59559721209856388345521601 44669790907392291259141201)
          ·
            refine ⟨33502343180544218444355901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44669790907392291259141201 33502343180544218444355901)
            ·
              refine ⟨12563378692704081916633463, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33502343180544218444355901 12563378692704081916633463)
              ·
                refine ⟨18845068039056122874950195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12563378692704081916633463 18845068039056122874950195)
                ·
                  refine ⟨28267602058584184312425293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18845068039056122874950195 28267602058584184312425293)
                  ·
                    refine ⟨10600350771969069117159485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 28267602058584184312425293 10600350771969069117159485)
                    ·
                      refine ⟨3975131539488400918934807, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10600350771969069117159485 3975131539488400918934807)
                      ·
                        rfl

theorem cell23_7741541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 2, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 2, 3, 1, 1, 3, 3].length) (baseStart_7741541 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7741541 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7741541 prefixEnd_7741541 := by exact prefixLift 7741541
  have htrace : WordTrace (prefixWord ++ tailWord_7741541) baseStart_7741541 baseEnd_7741541 := by
    simpa [prefixWord, tailWord_7741541, baseEnd_7741541] using wordTrace_append hprefix tailTrace_7741541
  have hstable : (prefixWord ++ tailWord_7741541).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7741541).length < 2 ^ (prefixWord ++ tailWord_7741541).sum := by decide
  have hdescent : baseEnd_7741541 < baseStart_7741541 := by decide
  rcases family_descends (prefixWord ++ tailWord_7741541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7741554 : List Nat := [3, 2, 1, 2, 2, 2, 1, 1, 2, 2, 5]
def baseStart_7741554 : Nat := 118140960795 + 7741554 * 2 ^ 59
def prefixEnd_7741554 : Nat := 4983230072969 + 3 ^ 40 * 7741554 * 2
def baseEnd_7741554 : Nat := 3975138214736909368072247

theorem tailTrace_7741554 : CollatzResearch.WordTrace tailWord_7741554 prefixEnd_7741554 3975138214736909368072247 := by
  unfold tailWord_7741554
  simp only [CollatzResearch.WordTrace]
  refine ⟨70589417748919871251599929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 188238447330452990004266477 70589417748919871251599929)
  ·
    refine ⟨52942063311689903438699947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70589417748919871251599929 52942063311689903438699947)
    ·
      refine ⟨79413094967534855158049921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52942063311689903438699947 79413094967534855158049921)
      ·
        refine ⟨59559821225651141368537441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79413094967534855158049921 59559821225651141368537441)
        ·
          refine ⟨44669865919238356026403081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59559821225651141368537441 44669865919238356026403081)
          ·
            refine ⟨33502399439428767019802311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44669865919238356026403081 33502399439428767019802311)
            ·
              refine ⟨50253599159143150529703467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33502399439428767019802311 50253599159143150529703467)
              ·
                refine ⟨75380398738714725794555201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50253599159143150529703467 75380398738714725794555201)
                ·
                  refine ⟨56535299054036044345916401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 75380398738714725794555201 56535299054036044345916401)
                  ·
                    refine ⟨42401474290527033259437301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 56535299054036044345916401 42401474290527033259437301)
                    ·
                      refine ⟨3975138214736909368072247, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 42401474290527033259437301 3975138214736909368072247)
                      ·
                        rfl

theorem cell23_7741554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 2, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 2, 1, 1, 2, 2, 5].length) (baseStart_7741554 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7741554 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7741554 prefixEnd_7741554 := by exact prefixLift 7741554
  have htrace : WordTrace (prefixWord ++ tailWord_7741554) baseStart_7741554 baseEnd_7741554 := by
    simpa [prefixWord, tailWord_7741554, baseEnd_7741554] using wordTrace_append hprefix tailTrace_7741554
  have hstable : (prefixWord ++ tailWord_7741554).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7741554).length < 2 ^ (prefixWord ++ tailWord_7741554).sum := by decide
  have hdescent : baseEnd_7741554 < baseStart_7741554 := by decide
  rcases family_descends (prefixWord ++ tailWord_7741554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7741558 : List Nat := [5, 1, 1, 2, 1, 2, 1, 2, 4, 1, 3]
def baseStart_7741558 : Nat := 118140960795 + 7741558 * 2 ^ 59
def prefixEnd_7741558 : Nat := 4983230072969 + 3 ^ 40 * 7741558 * 2
def baseEnd_7741558 : Nat := 3975140268659527352422229

theorem tailTrace_7741558 : CollatzResearch.WordTrace tailWord_7741558 prefixEnd_7741558 3975140268659527352422229 := by
  unfold tailWord_7741558
  simp only [CollatzResearch.WordTrace]
  refine ⟨17647363555479062105596583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 188238544591776662459696885 17647363555479062105596583)
  ·
    refine ⟨26471045333218593158394875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17647363555479062105596583 26471045333218593158394875)
    ·
      refine ⟨39706567999827889737592313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26471045333218593158394875 39706567999827889737592313)
      ·
        refine ⟨29779925999870917303194235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39706567999827889737592313 29779925999870917303194235)
        ·
          refine ⟨44669888999806375954791353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29779925999870917303194235 44669888999806375954791353)
          ·
            refine ⟨33502416749854781966093515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44669888999806375954791353 33502416749854781966093515)
            ·
              refine ⟨50253625124782172949140273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33502416749854781966093515 50253625124782172949140273)
              ·
                refine ⟨37690218843586629711855205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50253625124782172949140273 37690218843586629711855205)
                ·
                  refine ⟨7066916033172493070972851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 37690218843586629711855205 7066916033172493070972851)
                  ·
                    refine ⟨10600374049758739606459277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7066916033172493070972851 10600374049758739606459277)
                    ·
                      refine ⟨3975140268659527352422229, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10600374049758739606459277 3975140268659527352422229)
                      ·
                        rfl

theorem cell23_7741558_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 2, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 2, 1, 2, 4, 1, 3].length) (baseStart_7741558 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7741558 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7741558 prefixEnd_7741558 := by exact prefixLift 7741558
  have htrace : WordTrace (prefixWord ++ tailWord_7741558) baseStart_7741558 baseEnd_7741558 := by
    simpa [prefixWord, tailWord_7741558, baseEnd_7741558] using wordTrace_append hprefix tailTrace_7741558
  have hstable : (prefixWord ++ tailWord_7741558).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7741558).length < 2 ^ (prefixWord ++ tailWord_7741558).sum := by decide
  have hdescent : baseEnd_7741558 < baseStart_7741558 := by decide
  rcases family_descends (prefixWord ++ tailWord_7741558) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7741584 : List Nat := [2, 1, 1, 1, 1, 1, 6, 1, 2, 4, 3]
def baseStart_7741584 : Nat := 118140960795 + 7741584 * 2 ^ 59
def prefixEnd_7741584 : Nat := 4983230072969 + 3 ^ 40 * 7741584 * 2
def baseEnd_7741584 : Nat := 3975153619156544250697109

theorem tailTrace_7741584 : CollatzResearch.WordTrace tailWord_7741584 prefixEnd_7741584 3975153619156544250697109 := by
  unfold tailWord_7741584
  simp only [CollatzResearch.WordTrace]
  refine ⟨141179382592785400064995903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 188239176790380533419994537 141179382592785400064995903)
  ·
    refine ⟨211769073889178100097493855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141179382592785400064995903 211769073889178100097493855)
    ·
      refine ⟨317653610833767150146240783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 211769073889178100097493855 317653610833767150146240783)
      ·
        refine ⟨476480416250650725219361175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 317653610833767150146240783 476480416250650725219361175)
        ·
          refine ⟨714720624375976087829041763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 476480416250650725219361175 714720624375976087829041763)
          ·
            refine ⟨1072080936563964131743562645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 714720624375976087829041763 1072080936563964131743562645)
            ·
              refine ⟨50253793901435818675479499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 1072080936563964131743562645 50253793901435818675479499)
              ·
                refine ⟨75380690852153728013219249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50253793901435818675479499 75380690852153728013219249)
                ·
                  refine ⟨56535518139115296009914437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 75380690852153728013219249 56535518139115296009914437)
                  ·
                    refine ⟨10600409651084118001858957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 56535518139115296009914437 10600409651084118001858957)
                    ·
                      refine ⟨3975153619156544250697109, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10600409651084118001858957 3975153619156544250697109)
                      ·
                        rfl

theorem cell23_7741584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 6, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 6, 1, 2, 4, 3].length) (baseStart_7741584 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7741584 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7741584 prefixEnd_7741584 := by exact prefixLift 7741584
  have htrace : WordTrace (prefixWord ++ tailWord_7741584) baseStart_7741584 baseEnd_7741584 := by
    simpa [prefixWord, tailWord_7741584, baseEnd_7741584] using wordTrace_append hprefix tailTrace_7741584
  have hstable : (prefixWord ++ tailWord_7741584).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7741584).length < 2 ^ (prefixWord ++ tailWord_7741584).sum := by decide
  have hdescent : baseEnd_7741584 < baseStart_7741584 := by decide
  rcases family_descends (prefixWord ++ tailWord_7741584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7741592 : List Nat := [2, 1, 2, 4, 3, 2, 2, 1, 2, 1, 3]
def baseStart_7741592 : Nat := 118140960795 + 7741592 * 2 ^ 59
def prefixEnd_7741592 : Nat := 4983230072969 + 3 ^ 40 * 7741592 * 2
def baseEnd_7741592 : Nat := 3975157727001780219397073

theorem tailTrace_7741592 : CollatzResearch.WordTrace tailWord_7741592 prefixEnd_7741592 3975157727001780219397073 := by
  unfold tailWord_7741592
  simp only [CollatzResearch.WordTrace]
  refine ⟨141179528484770908748141515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 188239371313027878330855353 141179528484770908748141515)
  ·
    refine ⟨211769292727156363122212273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141179528484770908748141515 211769292727156363122212273)
    ·
      refine ⟨158826969545367272341659205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 211769292727156363122212273 158826969545367272341659205)
      ·
        refine ⟨29780056789756363564061101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 158826969545367272341659205 29780056789756363564061101)
        ·
          refine ⟨11167521296158636336522913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29780056789756363564061101 11167521296158636336522913)
          ·
            refine ⟨8375640972118977252392185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11167521296158636336522913 8375640972118977252392185)
            ·
              refine ⟨6281730729089232939294139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8375640972118977252392185 6281730729089232939294139)
              ·
                refine ⟨9422596093633849408941209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6281730729089232939294139 9422596093633849408941209)
                ·
                  refine ⟨7066947070225387056705907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9422596093633849408941209 7066947070225387056705907)
                  ·
                    refine ⟨10600420605338080585058861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7066947070225387056705907 10600420605338080585058861)
                    ·
                      refine ⟨3975157727001780219397073, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10600420605338080585058861 3975157727001780219397073)
                      ·
                        rfl

theorem cell23_7741592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 3, 2, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 3, 2, 2, 1, 2, 1, 3].length) (baseStart_7741592 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7741592 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7741592 prefixEnd_7741592 := by exact prefixLift 7741592
  have htrace : WordTrace (prefixWord ++ tailWord_7741592) baseStart_7741592 baseEnd_7741592 := by
    simpa [prefixWord, tailWord_7741592, baseEnd_7741592] using wordTrace_append hprefix tailTrace_7741592
  have hstable : (prefixWord ++ tailWord_7741592).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7741592).length < 2 ^ (prefixWord ++ tailWord_7741592).sum := by decide
  have hdescent : baseEnd_7741592 < baseStart_7741592 := by decide
  rcases family_descends (prefixWord ++ tailWord_7741592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7741602 : List Nat := [3, 3, 1, 3, 1, 3, 1, 2, 1, 3, 2]
def baseStart_7741602 : Nat := 118140960795 + 7741602 * 2 ^ 59
def prefixEnd_7741602 : Nat := 4983230072969 + 3 ^ 40 * 7741602 * 2
def baseEnd_7741602 : Nat := 3975162861808325180272027

theorem tailTrace_7741602 : CollatzResearch.WordTrace tailWord_7741602 prefixEnd_7741602 3975162861808325180272027 := by
  unfold tailWord_7741602
  simp only [CollatzResearch.WordTrace]
  refine ⟨70589855424876397301036765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 188239614466337059469431373 70589855424876397301036765)
  ·
    refine ⟨26471195784328648987888787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 70589855424876397301036765 26471195784328648987888787)
    ·
      refine ⟨39706793676492973481833181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26471195784328648987888787 39706793676492973481833181)
      ·
        refine ⟨14890047628684865055687443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39706793676492973481833181 14890047628684865055687443)
        ·
          refine ⟨22335071443027297583531165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14890047628684865055687443 22335071443027297583531165)
          ·
            refine ⟨8375651791135236593824187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22335071443027297583531165 8375651791135236593824187)
            ·
              refine ⟨12563477686702854890736281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8375651791135236593824187 12563477686702854890736281)
              ·
                refine ⟨9422608265027141168052211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12563477686702854890736281 9422608265027141168052211)
                ·
                  refine ⟨14133912397540711752078317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9422608265027141168052211 14133912397540711752078317)
                  ·
                    refine ⟨5300217149077766907029369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14133912397540711752078317 5300217149077766907029369)
                    ·
                      refine ⟨3975162861808325180272027, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5300217149077766907029369 3975162861808325180272027)
                      ·
                        rfl

theorem cell23_7741602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 3, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 3, 1, 2, 1, 3, 2].length) (baseStart_7741602 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7741602 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7741602 prefixEnd_7741602 := by exact prefixLift 7741602
  have htrace : WordTrace (prefixWord ++ tailWord_7741602) baseStart_7741602 baseEnd_7741602 := by
    simpa [prefixWord, tailWord_7741602, baseEnd_7741602] using wordTrace_append hprefix tailTrace_7741602
  have hstable : (prefixWord ++ tailWord_7741602).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7741602).length < 2 ^ (prefixWord ++ tailWord_7741602).sum := by decide
  have hdescent : baseEnd_7741602 < baseStart_7741602 := by decide
  rcases family_descends (prefixWord ++ tailWord_7741602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7741732 : List Nat := [2, 3, 1, 3, 1, 4, 1, 3, 1, 4]
def baseStart_7741732 : Nat := 118140960795 + 7741732 * 2 ^ 59
def prefixEnd_7741732 : Nat := 4983230072969 + 3 ^ 40 * 7741732 * 2
def baseEnd_7741732 : Nat := 1325076538097803223882143

theorem tailTrace_7741732 : CollatzResearch.WordTrace tailWord_7741732 prefixEnd_7741732 1325076538097803223882143 := by
  unfold tailWord_7741732
  simp only [CollatzResearch.WordTrace]
  refine ⟨141182081594517310703189725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 188242775459356414270919633 141182081594517310703189725)
  ·
    refine ⟨52943280597943991513696147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 141182081594517310703189725 52943280597943991513696147)
    ·
      refine ⟨79414920896915987270544221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52943280597943991513696147 79414920896915987270544221)
      ·
        refine ⟨29780595336343495226454083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 79414920896915987270544221 29780595336343495226454083)
        ·
          refine ⟨44670893004515242839681125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29780595336343495226454083 44670893004515242839681125)
          ·
            refine ⟨8375792438346608032440211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 44670893004515242839681125 8375792438346608032440211)
            ·
              refine ⟨12563688657519912048660317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8375792438346608032440211 12563688657519912048660317)
              ·
                refine ⟨4711383246569967018247619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12563688657519912048660317 4711383246569967018247619)
                ·
                  refine ⟨7067074869854950527371429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4711383246569967018247619 7067074869854950527371429)
                  ·
                    refine ⟨1325076538097803223882143, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7067074869854950527371429 1325076538097803223882143)
                    ·
                      rfl

theorem cell23_7741732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 4, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 4, 1, 3, 1, 4].length) (baseStart_7741732 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7741732 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7741732 prefixEnd_7741732 := by exact prefixLift 7741732
  have htrace : WordTrace (prefixWord ++ tailWord_7741732) baseStart_7741732 baseEnd_7741732 := by
    simpa [prefixWord, tailWord_7741732, baseEnd_7741732] using wordTrace_append hprefix tailTrace_7741732
  have hstable : (prefixWord ++ tailWord_7741732).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7741732).length < 2 ^ (prefixWord ++ tailWord_7741732).sum := by decide
  have hdescent : baseEnd_7741732 < baseStart_7741732 := by decide
  rcases family_descends (prefixWord ++ tailWord_7741732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7741742 : List Nat := [4, 1, 3, 3, 1, 1, 1, 2, 2, 2, 3]
def baseStart_7741742 : Nat := 118140960795 + 7741742 * 2 ^ 59
def prefixEnd_7741742 : Nat := 4983230072969 + 3 ^ 40 * 7741742 * 2
def baseEnd_7741742 : Nat := 3975234749099954632521383

theorem tailTrace_7741742 : CollatzResearch.WordTrace tailWord_7741742 prefixEnd_7741742 3975234749099954632521383 := by
  unfold tailWord_7741742
  simp only [CollatzResearch.WordTrace]
  refine ⟨35295565989874799139280435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 188243018612665595409495653 35295565989874799139280435)
  ·
    refine ⟨52943348984812198708920653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35295565989874799139280435 52943348984812198708920653)
    ·
      refine ⟨19853755869304574515845245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 52943348984812198708920653 19853755869304574515845245)
      ·
        refine ⟨7445158450989215443441967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19853755869304574515845245 7445158450989215443441967)
        ·
          refine ⟨11167737676483823165162951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7445158450989215443441967 11167737676483823165162951)
          ·
            refine ⟨16751606514725734747744427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11167737676483823165162951 16751606514725734747744427)
            ·
              refine ⟨25127409772088602121616641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16751606514725734747744427 25127409772088602121616641)
              ·
                refine ⟨18845557329066451591212481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25127409772088602121616641 18845557329066451591212481)
                ·
                  refine ⟨14134167996799838693409361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18845557329066451591212481 14134167996799838693409361)
                  ·
                    refine ⟨10600625997599879020057021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14134167996799838693409361 10600625997599879020057021)
                    ·
                      refine ⟨3975234749099954632521383, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10600625997599879020057021 3975234749099954632521383)
                      ·
                        rfl

theorem cell23_7741742_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 1, 1, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 1, 1, 1, 2, 2, 2, 3].length) (baseStart_7741742 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7741742 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7741742 prefixEnd_7741742 := by exact prefixLift 7741742
  have htrace : WordTrace (prefixWord ++ tailWord_7741742) baseStart_7741742 baseEnd_7741742 := by
    simpa [prefixWord, tailWord_7741742, baseEnd_7741742] using wordTrace_append hprefix tailTrace_7741742
  have hstable : (prefixWord ++ tailWord_7741742).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7741742).length < 2 ^ (prefixWord ++ tailWord_7741742).sum := by decide
  have hdescent : baseEnd_7741742 < baseStart_7741742 := by decide
  rcases family_descends (prefixWord ++ tailWord_7741742) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7741771 : List Nat := [1, 1, 1, 1, 3, 1, 1, 4, 6, 4]
def baseStart_7741771 : Nat := 118140960795 + 7741771 * 2 ^ 59
def prefixEnd_7741771 : Nat := 4983230072969 + 3 ^ 40 * 7741771 * 2
def baseEnd_7741771 : Nat := 1325083213346311673019583

theorem tailTrace_7741771 : CollatzResearch.WordTrace tailWord_7741771 prefixEnd_7741771 1325083213346311673019583 := by
  unfold tailWord_7741771
  simp only [CollatzResearch.WordTrace]
  refine ⟨282365585635893331067049167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188243723757262220711366111 282365585635893331067049167)
  ·
    refine ⟨423548378453839996600573751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 282365585635893331067049167 423548378453839996600573751)
    ·
      refine ⟨635322567680759994900860627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 423548378453839996600573751 635322567680759994900860627)
      ·
        refine ⟨952983851521139992351290941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 635322567680759994900860627 952983851521139992351290941)
        ·
          refine ⟨357368944320427497131734103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 952983851521139992351290941 357368944320427497131734103)
          ·
            refine ⟨536053416480641245697601155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 357368944320427497131734103 536053416480641245697601155)
            ·
              refine ⟨804080124720961868546401733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 536053416480641245697601155 804080124720961868546401733)
              ·
                refine ⟨150765023385180350352450325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 804080124720961868546401733 150765023385180350352450325)
                ·
                  refine ⟨7067110471180328922771109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 150765023385180350352450325 7067110471180328922771109)
                  ·
                    refine ⟨1325083213346311673019583, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7067110471180328922771109 1325083213346311673019583)
                    ·
                      rfl

theorem cell23_7741771_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 4, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 4, 6, 4].length) (baseStart_7741771 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7741771 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7741771 prefixEnd_7741771 := by exact prefixLift 7741771
  have htrace : WordTrace (prefixWord ++ tailWord_7741771) baseStart_7741771 baseEnd_7741771 := by
    simpa [prefixWord, tailWord_7741771, baseEnd_7741771] using wordTrace_append hprefix tailTrace_7741771
  have hstable : (prefixWord ++ tailWord_7741771).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7741771).length < 2 ^ (prefixWord ++ tailWord_7741771).sum := by decide
  have hdescent : baseEnd_7741771 < baseStart_7741771 := by decide
  rcases family_descends (prefixWord ++ tailWord_7741771) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7741778 : List Nat := [3, 2, 2, 1, 1, 1, 2, 1, 2, 6, 2]
def baseStart_7741778 : Nat := 118140960795 + 7741778 * 2 ^ 59
def prefixEnd_7741778 : Nat := 4983230072969 + 3 ^ 40 * 7741778 * 2
def baseEnd_7741778 : Nat := 3975253234403516491671217

theorem tailTrace_7741778 : CollatzResearch.WordTrace tailWord_7741778 prefixEnd_7741778 3975253234403516491671217 := by
  unfold tailWord_7741778
  simp only [CollatzResearch.WordTrace]
  refine ⟨70591460236716992815638497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 188243893964578647508369325 70591460236716992815638497)
  ·
    refine ⟨52943595177537744611728873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70591460236716992815638497 52943595177537744611728873)
    ·
      refine ⟨39707696383153308458796655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52943595177537744611728873 39707696383153308458796655)
      ·
        refine ⟨59561544574729962688194983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39707696383153308458796655 59561544574729962688194983)
        ·
          refine ⟨89342316862094944032292475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59561544574729962688194983 89342316862094944032292475)
          ·
            refine ⟨134013475293142416048438713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89342316862094944032292475 134013475293142416048438713)
            ·
              refine ⟨100510106469856812036329035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 134013475293142416048438713 100510106469856812036329035)
              ·
                refine ⟨150765159704785218054493553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 100510106469856812036329035 150765159704785218054493553)
                ·
                  refine ⟨113073869778588913540870165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 150765159704785218054493553 113073869778588913540870165)
                  ·
                    refine ⟨5300337645871355322228289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 113073869778588913540870165 5300337645871355322228289)
                    ·
                      refine ⟨3975253234403516491671217, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5300337645871355322228289 3975253234403516491671217)
                      ·
                        rfl

theorem cell23_7741778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 2, 1, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 2, 1, 2, 6, 2].length) (baseStart_7741778 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7741778 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7741778 prefixEnd_7741778 := by exact prefixLift 7741778
  have htrace : WordTrace (prefixWord ++ tailWord_7741778) baseStart_7741778 baseEnd_7741778 := by
    simpa [prefixWord, tailWord_7741778, baseEnd_7741778] using wordTrace_append hprefix tailTrace_7741778
  have hstable : (prefixWord ++ tailWord_7741778).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7741778).length < 2 ^ (prefixWord ++ tailWord_7741778).sum := by decide
  have hdescent : baseEnd_7741778 < baseStart_7741778 := by decide
  rcases family_descends (prefixWord ++ tailWord_7741778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7741791 : List Nat := [1, 1, 2, 3, 1, 2, 3, 1, 3, 2, 4]
def baseStart_7741791 : Nat := 118140960795 + 7741791 * 2 ^ 59
def prefixEnd_7741791 : Nat := 4983230072969 + 3 ^ 40 * 7741791 * 2
def baseEnd_7741791 : Nat := 3975259909652024940808657

theorem tailTrace_7741791 : CollatzResearch.WordTrace tailWord_7741791 prefixEnd_7741791 3975259909652024940808657 := by
  unfold tailWord_7741791
  simp only [CollatzResearch.WordTrace]
  refine ⟨282366315095820874482777227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188244210063880582988518151 282366315095820874482777227)
  ·
    refine ⟨423549472643731311724165841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 282366315095820874482777227 423549472643731311724165841)
    ·
      refine ⟨317662104482798483793124381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 423549472643731311724165841 317662104482798483793124381)
      ·
        refine ⟨119123289181049431422421643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 317662104482798483793124381 119123289181049431422421643)
        ·
          refine ⟨178684933771574147133632465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 119123289181049431422421643 178684933771574147133632465)
          ·
            refine ⟨134013700328680610350224349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 178684933771574147133632465 134013700328680610350224349)
            ·
              refine ⟨50255137623255228881334131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 134013700328680610350224349 50255137623255228881334131)
              ·
                refine ⟨75382706434882843322001197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50255137623255228881334131 75382706434882843322001197)
                ·
                  refine ⟨28268514913081066245750449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 75382706434882843322001197 28268514913081066245750449)
                  ·
                    refine ⟨21201386184810799684312837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 28268514913081066245750449 21201386184810799684312837)
                    ·
                      refine ⟨3975259909652024940808657, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21201386184810799684312837 3975259909652024940808657)
                      ·
                        rfl

theorem cell23_7741791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 3, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 3, 1, 3, 2, 4].length) (baseStart_7741791 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7741791 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7741791 prefixEnd_7741791 := by exact prefixLift 7741791
  have htrace : WordTrace (prefixWord ++ tailWord_7741791) baseStart_7741791 baseEnd_7741791 := by
    simpa [prefixWord, tailWord_7741791, baseEnd_7741791] using wordTrace_append hprefix tailTrace_7741791
  have hstable : (prefixWord ++ tailWord_7741791).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7741791).length < 2 ^ (prefixWord ++ tailWord_7741791).sum := by decide
  have hdescent : baseEnd_7741791 < baseStart_7741791 := by decide
  rcases family_descends (prefixWord ++ tailWord_7741791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7741795 : List Nat := [1, 1, 1, 5, 2, 1, 5, 1, 1, 1, 4]
def baseStart_7741795 : Nat := 118140960795 + 7741795 * 2 ^ 59
def prefixEnd_7741795 : Nat := 4983230072969 + 3 ^ 40 * 7741795 * 2
def baseEnd_7741795 : Nat := 3975261963574642925158639

theorem tailTrace_7741795 : CollatzResearch.WordTrace tailWord_7741795 prefixEnd_7741795 3975261963574642925158639 := by
  unfold tailWord_7741795
  simp only [CollatzResearch.WordTrace]
  refine ⟨282366460987806383165922839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188244307325204255443948559 282366460987806383165922839)
  ·
    refine ⟨423549691481709574748884259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 282366460987806383165922839 423549691481709574748884259)
    ·
      refine ⟨635324537222564362123326389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 423549691481709574748884259 635324537222564362123326389)
      ·
        refine ⟨59561675364615408949061849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 635324537222564362123326389 59561675364615408949061849)
        ·
          refine ⟨44671256523461556711796387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59561675364615408949061849 44671256523461556711796387)
          ·
            refine ⟨67006884785192335067694581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44671256523461556711796387 67006884785192335067694581)
            ·
              refine ⟨6281895448611781412596367, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 67006884785192335067694581 6281895448611781412596367)
              ·
                refine ⟨9422843172917672118894551, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6281895448611781412596367 9422843172917672118894551)
                ·
                  refine ⟨14134264759376508178341827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9422843172917672118894551 14134264759376508178341827)
                  ·
                    refine ⟨21201397139064762267512741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14134264759376508178341827 21201397139064762267512741)
                    ·
                      refine ⟨3975261963574642925158639, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21201397139064762267512741 3975261963574642925158639)
                      ·
                        rfl

theorem cell23_7741795_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 5, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 5, 1, 1, 1, 4].length) (baseStart_7741795 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7741795 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7741795 prefixEnd_7741795 := by exact prefixLift 7741795
  have htrace : WordTrace (prefixWord ++ tailWord_7741795) baseStart_7741795 baseEnd_7741795 := by
    simpa [prefixWord, tailWord_7741795, baseEnd_7741795] using wordTrace_append hprefix tailTrace_7741795
  have hstable : (prefixWord ++ tailWord_7741795).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7741795).length < 2 ^ (prefixWord ++ tailWord_7741795).sum := by decide
  have hdescent : baseEnd_7741795 < baseStart_7741795 := by decide
  rcases family_descends (prefixWord ++ tailWord_7741795) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7741805 : List Nat := [1, 5, 1, 1, 1, 2, 4, 2, 2, 4]
def baseStart_7741805 : Nat := 118140960795 + 7741805 * 2 ^ 59
def prefixEnd_7741805 : Nat := 4983230072969 + 3 ^ 40 * 7741805 * 2
def baseEnd_7741805 : Nat := 1325089032793729295344531

theorem tailTrace_7741805 : CollatzResearch.WordTrace tailWord_7741805 prefixEnd_7741805 1325089032793729295344531 := by
  unfold tailWord_7741805
  simp only [CollatzResearch.WordTrace]
  refine ⟨282366825717770154873786869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188244550478513436582524579 282366825717770154873786869)
  ·
    refine ⟨26471889911040952019417519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 282366825717770154873786869 26471889911040952019417519)
    ·
      refine ⟨39707834866561428029126279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26471889911040952019417519 39707834866561428029126279)
      ·
        refine ⟨59561752299842142043689419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39707834866561428029126279 59561752299842142043689419)
        ·
          refine ⟨89342628449763213065534129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59561752299842142043689419 89342628449763213065534129)
          ·
            refine ⟨67006971337322409799150597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 89342628449763213065534129 67006971337322409799150597)
            ·
              refine ⟨12563807125747951837340737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 67006971337322409799150597 12563807125747951837340737)
              ·
                refine ⟨9422855344310963878005553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12563807125747951837340737 9422855344310963878005553)
                ·
                  refine ⟨7067141508233222908504165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9422855344310963878005553 7067141508233222908504165)
                  ·
                    refine ⟨1325089032793729295344531, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7067141508233222908504165 1325089032793729295344531)
                    ·
                      rfl

theorem cell23_7741805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 4, 2, 2, 4].length) (baseStart_7741805 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7741805 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7741805 prefixEnd_7741805 := by exact prefixLift 7741805
  have htrace : WordTrace (prefixWord ++ tailWord_7741805) baseStart_7741805 baseEnd_7741805 := by
    simpa [prefixWord, tailWord_7741805, baseEnd_7741805] using wordTrace_append hprefix tailTrace_7741805
  have hstable : (prefixWord ++ tailWord_7741805).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7741805).length < 2 ^ (prefixWord ++ tailWord_7741805).sum := by decide
  have hdescent : baseEnd_7741805 < baseStart_7741805 := by decide
  rcases family_descends (prefixWord ++ tailWord_7741805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7741825 : List Nat := [1, 2, 4, 3, 1, 2, 2, 1, 1, 2, 4]
def baseStart_7741825 : Nat := 118140960795 + 7741825 * 2 ^ 59
def prefixEnd_7741825 : Nat := 4983230072969 + 3 ^ 40 * 7741825 * 2
def baseEnd_7741825 : Nat := 3975277367994277807783501

theorem tailTrace_7741825 : CollatzResearch.WordTrace tailWord_7741825 prefixEnd_7741825 3975277367994277807783501 := by
  unfold tailWord_7741825
  simp only [CollatzResearch.WordTrace]
  refine ⟨282367555177697698289514929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188245036785131798859676619 282367555177697698289514929)
  ·
    refine ⟨211775666383273273717136197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 282367555177697698289514929 211775666383273273717136197)
    ·
      refine ⟨39707937446863738821963037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 211775666383273273717136197 39707937446863738821963037)
      ·
        refine ⟨14890476542573902058236139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39707937446863738821963037 14890476542573902058236139)
        ·
          refine ⟨22335714813860853087354209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14890476542573902058236139 22335714813860853087354209)
          ·
            refine ⟨16751786110395639815515657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22335714813860853087354209 16751786110395639815515657)
            ·
              refine ⟨12563839582796729861636743, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16751786110395639815515657 12563839582796729861636743)
              ·
                refine ⟨18845759374195094792455115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12563839582796729861636743 18845759374195094792455115)
                ·
                  refine ⟨28268639061292642188682673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18845759374195094792455115 28268639061292642188682673)
                  ·
                    refine ⟨21201479295969481641512005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 28268639061292642188682673 21201479295969481641512005)
                    ·
                      refine ⟨3975277367994277807783501, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21201479295969481641512005 3975277367994277807783501)
                      ·
                        rfl

theorem cell23_7741825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 2, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 2, 2, 1, 1, 2, 4].length) (baseStart_7741825 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7741825 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7741825 prefixEnd_7741825 := by exact prefixLift 7741825
  have htrace : WordTrace (prefixWord ++ tailWord_7741825) baseStart_7741825 baseEnd_7741825 := by
    simpa [prefixWord, tailWord_7741825, baseEnd_7741825] using wordTrace_append hprefix tailTrace_7741825
  have hstable : (prefixWord ++ tailWord_7741825).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7741825).length < 2 ^ (prefixWord ++ tailWord_7741825).sum := by decide
  have hdescent : baseEnd_7741825 < baseStart_7741825 := by decide
  rcases family_descends (prefixWord ++ tailWord_7741825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7741831 : List Nat := [1, 1, 4, 2, 2, 1, 1, 2, 2, 7]
def baseStart_7741831 : Nat := 118140960795 + 7741831 * 2 ^ 59
def prefixEnd_7741831 : Nat := 4983230072969 + 3 ^ 40 * 7741831 * 2
def baseEnd_7741831 : Nat := 1325093482959401594769491

theorem tailTrace_7741831 : CollatzResearch.WordTrace tailWord_7741831 prefixEnd_7741831 1325093482959401594769491 := by
  unfold tailWord_7741831
  simp only [CollatzResearch.WordTrace]
  refine ⟨282367774015675961314233347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188245182677117307542822231 282367774015675961314233347)
  ·
    refine ⟨423551661023513941971350021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 282367774015675961314233347 423551661023513941971350021)
    ·
      refine ⟨79415936441908864119628129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 423551661023513941971350021 79415936441908864119628129)
      ·
        refine ⟨59561952331431648089721097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79415936441908864119628129 59561952331431648089721097)
        ·
          refine ⟨44671464248573736067290823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59561952331431648089721097 44671464248573736067290823)
          ·
            refine ⟨67007196372860604100936235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44671464248573736067290823 67007196372860604100936235)
            ·
              refine ⟨100510794559290906151404353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67007196372860604100936235 100510794559290906151404353)
              ·
                refine ⟨75383095919468179613553265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 100510794559290906151404353 75383095919468179613553265)
                ·
                  refine ⟨56537321939601134710164949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 75383095919468179613553265 56537321939601134710164949)
                  ·
                    refine ⟨1325093482959401594769491, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 56537321939601134710164949 1325093482959401594769491)
                    ·
                      rfl

theorem cell23_7741831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 1, 2, 2, 7].length) (baseStart_7741831 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7741831 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7741831 prefixEnd_7741831 := by exact prefixLift 7741831
  have htrace : WordTrace (prefixWord ++ tailWord_7741831) baseStart_7741831 baseEnd_7741831 := by
    simpa [prefixWord, tailWord_7741831, baseEnd_7741831] using wordTrace_append hprefix tailTrace_7741831
  have hstable : (prefixWord ++ tailWord_7741831).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7741831).length < 2 ^ (prefixWord ++ tailWord_7741831).sum := by decide
  have hdescent : baseEnd_7741831 < baseStart_7741831 := by decide
  rcases family_descends (prefixWord ++ tailWord_7741831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7741846 : List Nat := [5, 3, 1, 2, 1, 1, 1, 3, 1, 1, 4]
def baseStart_7741846 : Nat := 118140960795 + 7741846 * 2 ^ 59
def prefixEnd_7741846 : Nat := 4983230072969 + 3 ^ 40 * 7741846 * 2
def baseEnd_7741846 : Nat := 3975288151088022225620905

theorem tailTrace_7741846 : CollatzResearch.WordTrace tailWord_7741846 prefixEnd_7741846 3975288151088022225620905 := by
  unfold tailWord_7741846
  simp only [CollatzResearch.WordTrace]
  refine ⟨17648020069413851179751837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 188245547407081079250686261 17648020069413851179751837)
  ·
    refine ⟨6618007526030194192406939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17648020069413851179751837 6618007526030194192406939)
    ·
      refine ⟨9927011289045291288610409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6618007526030194192406939 9927011289045291288610409)
      ·
        refine ⟨7445258466783968466457807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9927011289045291288610409 7445258466783968466457807)
        ·
          refine ⟨11167887700175952699686711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7445258466783968466457807 11167887700175952699686711)
          ·
            refine ⟨16751831550263929049530067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11167887700175952699686711 16751831550263929049530067)
            ·
              refine ⟨25127747325395893574295101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16751831550263929049530067 25127747325395893574295101)
              ·
                refine ⟨9422905247023460090360663, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25127747325395893574295101 9422905247023460090360663)
                ·
                  refine ⟨14134357870535190135540995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9422905247023460090360663 14134357870535190135540995)
                  ·
                    refine ⟨21201536805802785203311493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14134357870535190135540995 21201536805802785203311493)
                    ·
                      refine ⟨3975288151088022225620905, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21201536805802785203311493 3975288151088022225620905)
                      ·
                        rfl

theorem cell23_7741846_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 1, 1, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 1, 1, 1, 3, 1, 1, 4].length) (baseStart_7741846 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7741846 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7741846 prefixEnd_7741846 := by exact prefixLift 7741846
  have htrace : WordTrace (prefixWord ++ tailWord_7741846) baseStart_7741846 baseEnd_7741846 := by
    simpa [prefixWord, tailWord_7741846, baseEnd_7741846] using wordTrace_append hprefix tailTrace_7741846
  have hstable : (prefixWord ++ tailWord_7741846).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7741846).length < 2 ^ (prefixWord ++ tailWord_7741846).sum := by decide
  have hdescent : baseEnd_7741846 < baseStart_7741846 := by decide
  rcases family_descends (prefixWord ++ tailWord_7741846) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7741861 : List Nat := [1, 3, 1, 2, 1, 1, 3, 1, 4, 6]
def baseStart_7741861 : Nat := 118140960795 + 7741861 * 2 ^ 59
def prefixEnd_7741861 : Nat := 4983230072969 + 3 ^ 40 * 7741861 * 2
def baseEnd_7741861 : Nat := 1325098617765946555644445

theorem tailTrace_7741861 : CollatzResearch.WordTrace tailWord_7741861 prefixEnd_7741861 1325098617765946555644445 := by
  unfold tailWord_7741861
  simp only [CollatzResearch.WordTrace]
  refine ⟨282368868205567276437825437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188245912137044850958550291 282368868205567276437825437)
  ·
    refine ⟨105888325577087728664184539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 282368868205567276437825437 105888325577087728664184539)
    ·
      refine ⟨158832488365631592996276809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105888325577087728664184539 158832488365631592996276809)
      ·
        refine ⟨119124366274223694747207607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 158832488365631592996276809 119124366274223694747207607)
        ·
          refine ⟨178686549411335542120811411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 119124366274223694747207607 178686549411335542120811411)
          ·
            refine ⟨268029824117003313181217117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 178686549411335542120811411 268029824117003313181217117)
            ·
              refine ⟨100511184043876242442956419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 268029824117003313181217117 100511184043876242442956419)
              ·
                refine ⟨150766776065814363664434629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 100511184043876242442956419 150766776065814363664434629)
                ·
                  refine ⟨28268770512340193187081493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 150766776065814363664434629 28268770512340193187081493)
                  ·
                    refine ⟨1325098617765946555644445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28268770512340193187081493 1325098617765946555644445)
                    ·
                      rfl

theorem cell23_7741861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 3, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 3, 1, 4, 6].length) (baseStart_7741861 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7741861 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7741861 prefixEnd_7741861 := by exact prefixLift 7741861
  have htrace : WordTrace (prefixWord ++ tailWord_7741861) baseStart_7741861 baseEnd_7741861 := by
    simpa [prefixWord, tailWord_7741861, baseEnd_7741861] using wordTrace_append hprefix tailTrace_7741861
  have hstable : (prefixWord ++ tailWord_7741861).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7741861).length < 2 ^ (prefixWord ++ tailWord_7741861).sum := by decide
  have hdescent : baseEnd_7741861 < baseStart_7741861 := by decide
  rcases family_descends (prefixWord ++ tailWord_7741861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7741871 : List Nat := [1, 1, 2, 1, 2, 2, 1, 1, 6, 1, 5]
def baseStart_7741871 : Nat := 118140960795 + 7741871 * 2 ^ 59
def prefixEnd_7741871 : Nat := 4983230072969 + 3 ^ 40 * 7741871 * 2
def baseEnd_7741871 : Nat := 3975300988104384627808289

theorem tailTrace_7741871 : CollatzResearch.WordTrace tailWord_7741871 prefixEnd_7741871 3975300988104384627808289 := by
  unfold tailWord_7741871
  simp only [CollatzResearch.WordTrace]
  refine ⟨282369232935531048145689467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188246155290354032097126311 282369232935531048145689467)
  ·
    refine ⟨423553849403296572218534201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 282369232935531048145689467 423553849403296572218534201)
    ·
      refine ⟨317665387052472429163900651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 423553849403296572218534201 317665387052472429163900651)
      ·
        refine ⟨476498080578708643745850977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 317665387052472429163900651 476498080578708643745850977)
        ·
          refine ⟨357373560434031482809388233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 476498080578708643745850977 357373560434031482809388233)
          ·
            refine ⟨268030170325523612107041175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 357373560434031482809388233 268030170325523612107041175)
            ·
              refine ⟨402045255488285418160561763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 268030170325523612107041175 402045255488285418160561763)
              ·
                refine ⟨603067883232428127240842645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 402045255488285418160561763 603067883232428127240842645)
                ·
                  refine ⟨28268807026520068464414499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 603067883232428127240842645 28268807026520068464414499)
                  ·
                    refine ⟨42403210539780102696621749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 28268807026520068464414499 42403210539780102696621749)
                    ·
                      refine ⟨3975300988104384627808289, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 42403210539780102696621749 3975300988104384627808289)
                      ·
                        rfl

theorem cell23_7741871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 1, 1, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 1, 1, 6, 1, 5].length) (baseStart_7741871 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7741871 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7741871 prefixEnd_7741871 := by exact prefixLift 7741871
  have htrace : WordTrace (prefixWord ++ tailWord_7741871) baseStart_7741871 baseEnd_7741871 := by
    simpa [prefixWord, tailWord_7741871, baseEnd_7741871] using wordTrace_append hprefix tailTrace_7741871
  have hstable : (prefixWord ++ tailWord_7741871).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7741871).length < 2 ^ (prefixWord ++ tailWord_7741871).sum := by decide
  have hdescent : baseEnd_7741871 < baseStart_7741871 := by decide
  rcases family_descends (prefixWord ++ tailWord_7741871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7741876 : List Nat := [2, 5, 2, 2, 2, 1, 1, 1, 1, 2, 4]
def baseStart_7741876 : Nat := 118140960795 + 7741876 * 2 ^ 59
def prefixEnd_7741876 : Nat := 4983230072969 + 3 ^ 40 * 7741876 * 2
def baseEnd_7741876 : Nat := 3975303555507657108245767

theorem tailTrace_7741876 : CollatzResearch.WordTrace tailWord_7741876 prefixEnd_7741876 3975303555507657108245767 := by
  unfold tailWord_7741876
  simp only [CollatzResearch.WordTrace]
  refine ⟨141184707650256466999810741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 188246276867008622666414321 141184707650256466999810741)
  ·
    refine ⟨13236066342211543781232257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 141184707650256466999810741 13236066342211543781232257)
    ·
      refine ⟨9927049756658657835924193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13236066342211543781232257 9927049756658657835924193)
      ·
        refine ⟨7445287317493993376943145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9927049756658657835924193 7445287317493993376943145)
        ·
          refine ⟨5583965488120495032707359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7445287317493993376943145 5583965488120495032707359)
          ·
            refine ⟨8375948232180742549061039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5583965488120495032707359 8375948232180742549061039)
            ·
              refine ⟨12563922348271113823591559, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8375948232180742549061039 12563922348271113823591559)
              ·
                refine ⟨18845883522406670735387339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12563922348271113823591559 18845883522406670735387339)
                ·
                  refine ⟨28268825283610006103081009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18845883522406670735387339 28268825283610006103081009)
                  ·
                    refine ⟨21201618962707504577310757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 28268825283610006103081009 21201618962707504577310757)
                    ·
                      refine ⟨3975303555507657108245767, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21201618962707504577310757 3975303555507657108245767)
                      ·
                        rfl

theorem cell23_7741876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 2, 1, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 2, 1, 1, 1, 1, 2, 4].length) (baseStart_7741876 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7741876 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7741876 prefixEnd_7741876 := by exact prefixLift 7741876
  have htrace : WordTrace (prefixWord ++ tailWord_7741876) baseStart_7741876 baseEnd_7741876 := by
    simpa [prefixWord, tailWord_7741876, baseEnd_7741876] using wordTrace_append hprefix tailTrace_7741876
  have hstable : (prefixWord ++ tailWord_7741876).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7741876).length < 2 ^ (prefixWord ++ tailWord_7741876).sum := by decide
  have hdescent : baseEnd_7741876 < baseStart_7741876 := by decide
  rcases family_descends (prefixWord ++ tailWord_7741876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7741911 : List Nat := [1, 1, 3, 2, 1, 1, 1, 1, 2, 4, 6]
def baseStart_7741911 : Nat := 118140960795 + 7741911 * 2 ^ 59
def prefixEnd_7741911 : Nat := 4983230072969 + 3 ^ 40 * 7741911 * 2
def baseEnd_7741911 : Nat := 3975321527330564471308105

theorem tailTrace_7741911 : CollatzResearch.WordTrace tailWord_7741911 prefixEnd_7741911 3975321527330564471308105 := by
  unfold tailWord_7741911
  simp only [CollatzResearch.WordTrace]
  refine ⟨282370691855386134977145587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188247127903590756651430391 282370691855386134977145587)
  ·
    refine ⟨423556037783079202465718381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 282370691855386134977145587 423556037783079202465718381)
    ·
      refine ⟨158833514168654700924644393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 423556037783079202465718381 158833514168654700924644393)
      ·
        refine ⟨119125135626491025693483295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 158833514168654700924644393 119125135626491025693483295)
        ·
          refine ⟨178687703439736538540224943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 119125135626491025693483295 178687703439736538540224943)
          ·
            refine ⟨268031555159604807810337415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 178687703439736538540224943 268031555159604807810337415)
            ·
              refine ⟨402047332739407211715506123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 268031555159604807810337415 402047332739407211715506123)
              ·
                refine ⟨603070999109110817573259185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 402047332739407211715506123 603070999109110817573259185)
                ·
                  refine ⟨452303249331833113179944389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 603070999109110817573259185 452303249331833113179944389)
                  ·
                    refine ⟨84806859249718708721239573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 452303249331833113179944389 84806859249718708721239573)
                    ·
                      refine ⟨3975321527330564471308105, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 84806859249718708721239573 3975321527330564471308105)
                      ·
                        rfl

theorem cell23_7741911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 1, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 1, 1, 2, 4, 6].length) (baseStart_7741911 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7741911 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7741911 prefixEnd_7741911 := by exact prefixLift 7741911
  have htrace : WordTrace (prefixWord ++ tailWord_7741911) baseStart_7741911 baseEnd_7741911 := by
    simpa [prefixWord, tailWord_7741911, baseEnd_7741911] using wordTrace_append hprefix tailTrace_7741911
  have hstable : (prefixWord ++ tailWord_7741911).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7741911).length < 2 ^ (prefixWord ++ tailWord_7741911).sum := by decide
  have hdescent : baseEnd_7741911 < baseStart_7741911 := by decide
  rcases family_descends (prefixWord ++ tailWord_7741911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7741972 : List Nat := [2, 4, 3, 1, 1, 1, 2, 2, 2, 5]
def baseStart_7741972 : Nat := 118140960795 + 7741972 * 2 ^ 59
def prefixEnd_7741972 : Nat := 4983230072969 + 3 ^ 40 * 7741972 * 2
def baseEnd_7741972 : Nat := 1325117616550162910881775

theorem tailTrace_7741972 : CollatzResearch.WordTrace tailWord_7741972 prefixEnd_7741972 1325117616550162910881775 := by
  unfold tailWord_7741972
  simp only [CollatzResearch.WordTrace]
  refine ⟨141186458354082571197558085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 188248611138776761596744113 141186458354082571197558085)
  ·
    refine ⟨26472460941390482099542141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 141186458354082571197558085 26472460941390482099542141)
    ·
      refine ⟨9927172853021430787328303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26472460941390482099542141 9927172853021430787328303)
      ·
        refine ⟨14890759279532146180992455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9927172853021430787328303 14890759279532146180992455)
        ·
          refine ⟨22336138919298219271488683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14890759279532146180992455 22336138919298219271488683)
          ·
            refine ⟨33504208378947328907233025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22336138919298219271488683 33504208378947328907233025)
            ·
              refine ⟨25128156284210496680424769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33504208378947328907233025 25128156284210496680424769)
              ·
                refine ⟨18846117213157872510318577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25128156284210496680424769 18846117213157872510318577)
                ·
                  refine ⟨14134587909868404382738933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18846117213157872510318577 14134587909868404382738933)
                  ·
                    refine ⟨1325117616550162910881775, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14134587909868404382738933 1325117616550162910881775)
                    ·
                      rfl

theorem cell23_7741972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 1, 2, 2, 2, 5].length) (baseStart_7741972 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7741972 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7741972 prefixEnd_7741972 := by exact prefixLift 7741972
  have htrace : WordTrace (prefixWord ++ tailWord_7741972) baseStart_7741972 baseEnd_7741972 := by
    simpa [prefixWord, tailWord_7741972, baseEnd_7741972] using wordTrace_append hprefix tailTrace_7741972
  have hstable : (prefixWord ++ tailWord_7741972).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7741972).length < 2 ^ (prefixWord ++ tailWord_7741972).sum := by decide
  have hdescent : baseEnd_7741972 < baseStart_7741972 := by decide
  rcases family_descends (prefixWord ++ tailWord_7741972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7741985 : List Nat := [1, 2, 3, 2, 2, 1, 2, 3, 3, 4]
def baseStart_7741985 : Nat := 118140960795 + 7741985 * 2 ^ 59
def prefixEnd_7741985 : Nat := 4983230072969 + 3 ^ 40 * 7741985 * 2
def baseEnd_7741985 : Nat := 1325119841632999060594255

theorem tailTrace_7741985 : CollatzResearch.WordTrace tailWord_7741985 prefixEnd_7741985 1325119841632999060594255 := by
  unfold tailWord_7741985
  simp only [CollatzResearch.WordTrace]
  refine ⟨282373390857118045615339409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188248927238078697076892939 282373390857118045615339409)
  ·
    refine ⟨211780043142838534211504557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 282373390857118045615339409 211780043142838534211504557)
    ·
      refine ⟨79417516178564450329314209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 211780043142838534211504557 79417516178564450329314209)
      ·
        refine ⟨59563137133923337746985657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79417516178564450329314209 59563137133923337746985657)
        ·
          refine ⟨44672352850442503310239243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59563137133923337746985657 44672352850442503310239243)
          ·
            refine ⟨67008529275663754965358865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44672352850442503310239243 67008529275663754965358865)
            ·
              refine ⟨50256396956747816224019149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 67008529275663754965358865 50256396956747816224019149)
              ·
                refine ⟨18846148858780431084007181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 50256396956747816224019149 18846148858780431084007181)
                ·
                  refine ⟨7067305822042661656502693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18846148858780431084007181 7067305822042661656502693)
                  ·
                    refine ⟨1325119841632999060594255, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7067305822042661656502693 1325119841632999060594255)
                    ·
                      rfl

theorem cell23_7741985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 2, 3, 3, 4].length) (baseStart_7741985 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7741985 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7741985 prefixEnd_7741985 := by exact prefixLift 7741985
  have htrace : WordTrace (prefixWord ++ tailWord_7741985) baseStart_7741985 baseEnd_7741985 := by
    simpa [prefixWord, tailWord_7741985, baseEnd_7741985] using wordTrace_append hprefix tailTrace_7741985
  have hstable : (prefixWord ++ tailWord_7741985).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7741985).length < 2 ^ (prefixWord ++ tailWord_7741985).sum := by decide
  have hdescent : baseEnd_7741985 < baseStart_7741985 := by decide
  rcases family_descends (prefixWord ++ tailWord_7741985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7741992 : List Nat := [2, 1, 5, 2, 1, 1, 1, 1, 1, 6, 2]
def baseStart_7741992 : Nat := 118140960795 + 7741992 * 2 ^ 59
def prefixEnd_7741992 : Nat := 4983230072969 + 3 ^ 40 * 7741992 * 2
def baseEnd_7741992 : Nat := 3975363119263578654395233

theorem tailTrace_7741992 : CollatzResearch.WordTrace tailWord_7741992 prefixEnd_7741992 3975363119263578654395233 := by
  unfold tailWord_7741992
  simp only [CollatzResearch.WordTrace]
  refine ⟨141186823084046342905422115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 188249097445395123873896153 141186823084046342905422115)
  ·
    refine ⟨211780234626069514358133173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141186823084046342905422115 211780234626069514358133173)
    ·
      refine ⟨19854396996194016971074985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 211780234626069514358133173 19854396996194016971074985)
      ·
        refine ⟨14890797747145512728306239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19854396996194016971074985 14890797747145512728306239)
        ·
          refine ⟨22336196620718269092459359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14890797747145512728306239 22336196620718269092459359)
          ·
            refine ⟨33504294931077403638689039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22336196620718269092459359 33504294931077403638689039)
            ·
              refine ⟨50256442396616105458033559, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33504294931077403638689039 50256442396616105458033559)
              ·
                refine ⟨75384663594924158187050339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50256442396616105458033559 75384663594924158187050339)
                ·
                  refine ⟨113076995392386237280575509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 75384663594924158187050339 113076995392386237280575509)
                  ·
                    refine ⟨5300484159018104872526977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 113076995392386237280575509 5300484159018104872526977)
                    ·
                      refine ⟨3975363119263578654395233, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5300484159018104872526977 3975363119263578654395233)
                      ·
                        rfl

theorem cell23_7741992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 1, 1, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 1, 1, 1, 1, 6, 2].length) (baseStart_7741992 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7741992 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7741992 prefixEnd_7741992 := by exact prefixLift 7741992
  have htrace : WordTrace (prefixWord ++ tailWord_7741992) baseStart_7741992 baseEnd_7741992 := by
    simpa [prefixWord, tailWord_7741992, baseEnd_7741992] using wordTrace_append hprefix tailTrace_7741992
  have hstable : (prefixWord ++ tailWord_7741992).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7741992).length < 2 ^ (prefixWord ++ tailWord_7741992).sum := by decide
  have hdescent : baseEnd_7741992 < baseStart_7741992 := by decide
  rcases family_descends (prefixWord ++ tailWord_7741992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7742012 : List Nat := [2, 2, 2, 2, 3, 1, 3, 1, 2, 2, 3]
def baseStart_7742012 : Nat := 118140960795 + 7742012 * 2 ^ 59
def prefixEnd_7742012 : Nat := 4983230072969 + 3 ^ 40 * 7742012 * 2
def baseEnd_7742012 : Nat := 3975373388876668576145141

theorem tailTrace_7742012 : CollatzResearch.WordTrace tailWord_7742012 prefixEnd_7742012 3975373388876668576145141 := by
  unfold tailWord_7742012
  simp only [CollatzResearch.WordTrace]
  refine ⟨141187187814010114613286145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 188249583752013486151048193 141187187814010114613286145)
  ·
    refine ⟨105890390860507585959964609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 141187187814010114613286145 105890390860507585959964609)
    ·
      refine ⟨79417793145380689469973457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 105890390860507585959964609 79417793145380689469973457)
      ·
        refine ⟨59563344859035517102480093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79417793145380689469973457 59563344859035517102480093)
        ·
          refine ⟨22336254322138318913430035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 59563344859035517102480093 22336254322138318913430035)
          ·
            refine ⟨33504381483207478370145053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22336254322138318913430035 33504381483207478370145053)
            ·
              refine ⟨12564143056202804388804395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33504381483207478370145053 12564143056202804388804395)
              ·
                refine ⟨18846214584304206583206593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12564143056202804388804395 18846214584304206583206593)
                ·
                  refine ⟨14134660938228154937404945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18846214584304206583206593 14134660938228154937404945)
                  ·
                    refine ⟨10600995703671116203053709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14134660938228154937404945 10600995703671116203053709)
                    ·
                      refine ⟨3975373388876668576145141, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10600995703671116203053709 3975373388876668576145141)
                      ·
                        rfl

theorem cell23_7742012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 1, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 1, 3, 1, 2, 2, 3].length) (baseStart_7742012 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7742012 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7742012 prefixEnd_7742012 := by exact prefixLift 7742012
  have htrace : WordTrace (prefixWord ++ tailWord_7742012) baseStart_7742012 baseEnd_7742012 := by
    simpa [prefixWord, tailWord_7742012, baseEnd_7742012] using wordTrace_append hprefix tailTrace_7742012
  have hstable : (prefixWord ++ tailWord_7742012).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7742012).length < 2 ^ (prefixWord ++ tailWord_7742012).sum := by decide
  have hdescent : baseEnd_7742012 < baseStart_7742012 := by decide
  rcases family_descends (prefixWord ++ tailWord_7742012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7742022 : List Nat := [6, 1, 1, 1, 2, 1, 1, 1, 2, 1, 6]
def baseStart_7742022 : Nat := 118140960795 + 7742022 * 2 ^ 59
def prefixEnd_7742022 : Nat := 4983230072969 + 3 ^ 40 * 7742022 * 2
def baseEnd_7742022 : Nat := 3975378523683213537020095

theorem tailTrace_7742022 : CollatzResearch.WordTrace tailWord_7742022 prefixEnd_7742022 3975378523683213537020095 := by
  unfold tailWord_7742022
  simp only [CollatzResearch.WordTrace]
  refine ⟨8824210636187000029201135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 188249826905322667289624213 8824210636187000029201135)
  ·
    refine ⟨13236315954280500043801703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8824210636187000029201135 13236315954280500043801703)
    ·
      refine ⟨19854473931420750065702555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13236315954280500043801703 19854473931420750065702555)
      ·
        refine ⟨29781710897131125098553833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19854473931420750065702555 29781710897131125098553833)
        ·
          refine ⟨22336283172848343823915375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29781710897131125098553833 22336283172848343823915375)
          ·
            refine ⟨33504424759272515735873063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22336283172848343823915375 33504424759272515735873063)
            ·
              refine ⟨50256637138908773603809595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33504424759272515735873063 50256637138908773603809595)
              ·
                refine ⟨75384955708363160405714393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50256637138908773603809595 75384955708363160405714393)
                ·
                  refine ⟨56538716781272370304285795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 75384955708363160405714393 56538716781272370304285795)
                  ·
                    refine ⟨84808075171908555456428693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 56538716781272370304285795 84808075171908555456428693)
                    ·
                      refine ⟨3975378523683213537020095, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 84808075171908555456428693 3975378523683213537020095)
                      ·
                        rfl

theorem cell23_7742022_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 1, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 1, 1, 1, 2, 1, 6].length) (baseStart_7742022 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7742022 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7742022 prefixEnd_7742022 := by exact prefixLift 7742022
  have htrace : WordTrace (prefixWord ++ tailWord_7742022) baseStart_7742022 baseEnd_7742022 := by
    simpa [prefixWord, tailWord_7742022, baseEnd_7742022] using wordTrace_append hprefix tailTrace_7742022
  have hstable : (prefixWord ++ tailWord_7742022).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7742022).length < 2 ^ (prefixWord ++ tailWord_7742022).sum := by decide
  have hdescent : baseEnd_7742022 < baseStart_7742022 := by decide
  rcases family_descends (prefixWord ++ tailWord_7742022) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7742062 : List Nat := [4, 1, 2, 2, 2, 1, 1, 4, 1, 5]
def baseStart_7742062 : Nat := 118140960795 + 7742062 * 2 ^ 59
def prefixEnd_7742062 : Nat := 4983230072969 + 3 ^ 40 * 7742062 * 2
def baseEnd_7742062 : Nat := 1325133020969797793506637

theorem tailTrace_7742062 : CollatzResearch.WordTrace tailWord_7742062 prefixEnd_7742062 1325133020969797793506637 := by
  unfold tailWord_7742062
  simp only [CollatzResearch.WordTrace]
  refine ⟨35297024909729885970736555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 188250799518559391843928293 35297024909729885970736555)
  ·
    refine ⟨52945537364594828956104833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35297024909729885970736555 52945537364594828956104833)
    ·
      refine ⟨39709153023446121717078625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52945537364594828956104833 39709153023446121717078625)
      ·
        refine ⟨29781864767584591287808969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39709153023446121717078625 29781864767584591287808969)
        ·
          refine ⟨22336398575688443465856727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29781864767584591287808969 22336398575688443465856727)
          ·
            refine ⟨33504597863532665198785091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22336398575688443465856727 33504597863532665198785091)
            ·
              refine ⟨50256896795298997798177637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33504597863532665198785091 50256896795298997798177637)
              ·
                refine ⟨9423168149118562087158307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 50256896795298997798177637 9423168149118562087158307)
                ·
                  refine ⟨14134752223677843130737461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9423168149118562087158307 14134752223677843130737461)
                  ·
                    refine ⟨1325133020969797793506637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14134752223677843130737461 1325133020969797793506637)
                    ·
                      rfl

theorem cell23_7742062_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 1, 1, 4, 1, 5].length) (baseStart_7742062 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7742062 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7742062 prefixEnd_7742062 := by exact prefixLift 7742062
  have htrace : WordTrace (prefixWord ++ tailWord_7742062) baseStart_7742062 baseEnd_7742062 := by
    simpa [prefixWord, tailWord_7742062, baseEnd_7742062] using wordTrace_append hprefix tailTrace_7742062
  have hstable : (prefixWord ++ tailWord_7742062).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7742062).length < 2 ^ (prefixWord ++ tailWord_7742062).sum := by decide
  have hdescent : baseEnd_7742062 < baseStart_7742062 := by decide
  rcases family_descends (prefixWord ++ tailWord_7742062) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7742085 : List Nat := [1, 3, 1, 1, 4, 2, 1, 3, 1, 1, 5]
def baseStart_7742085 : Nat := 118140960795 + 7742085 * 2 ^ 59
def prefixEnd_7742085 : Nat := 4983230072969 + 3 ^ 40 * 7742085 * 2
def baseEnd_7742085 : Nat := 3975410872964446790532305

theorem tailTrace_7742085 : CollatzResearch.WordTrace tailWord_7742085 prefixEnd_7742085 3975410872964446790532305 := by
  unfold tailWord_7742085
  simp only [CollatzResearch.WordTrace]
  refine ⟨282377038156755762693979709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188251358771170508462653139 282377038156755762693979709)
  ·
    refine ⟨105891389308783411010242391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 282377038156755762693979709 105891389308783411010242391)
    ·
      refine ⟨158837083963175116515363587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105891389308783411010242391 158837083963175116515363587)
      ·
        refine ⟨238255625944762674773045381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 158837083963175116515363587 238255625944762674773045381)
        ·
          refine ⟨44672929864643001519946009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 238255625944762674773045381 44672929864643001519946009)
          ·
            refine ⟨33504697398482251139959507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44672929864643001519946009 33504697398482251139959507)
            ·
              refine ⟨50257046097723376709939261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33504697398482251139959507 50257046097723376709939261)
              ·
                refine ⟨18846392286646266266227223, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 50257046097723376709939261 18846392286646266266227223)
                ·
                  refine ⟨28269588429969399399340835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18846392286646266266227223 28269588429969399399340835)
                  ·
                    refine ⟨42404382644954099099011253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 28269588429969399399340835 42404382644954099099011253)
                    ·
                      refine ⟨3975410872964446790532305, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 42404382644954099099011253 3975410872964446790532305)
                      ·
                        rfl

theorem cell23_7742085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 2, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 2, 1, 3, 1, 1, 5].length) (baseStart_7742085 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7742085 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7742085 prefixEnd_7742085 := by exact prefixLift 7742085
  have htrace : WordTrace (prefixWord ++ tailWord_7742085) baseStart_7742085 baseEnd_7742085 := by
    simpa [prefixWord, tailWord_7742085, baseEnd_7742085] using wordTrace_append hprefix tailTrace_7742085
  have hstable : (prefixWord ++ tailWord_7742085).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7742085).length < 2 ^ (prefixWord ++ tailWord_7742085).sum := by decide
  have hdescent : baseEnd_7742085 < baseStart_7742085 := by decide
  rcases family_descends (prefixWord ++ tailWord_7742085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7742109 : List Nat := [1, 4, 2, 1, 1, 1, 6, 1, 2, 4]
def baseStart_7742109 : Nat := 118140960795 + 7742109 * 2 ^ 59
def prefixEnd_7742109 : Nat := 4983230072969 + 3 ^ 40 * 7742109 * 2
def baseEnd_7742109 : Nat := 1325141065500051565544065

theorem tailTrace_7742109 : CollatzResearch.WordTrace tailWord_7742109 prefixEnd_7742109 1325141065500051565544065 := by
  unfold tailWord_7742109
  simp only [CollatzResearch.WordTrace]
  refine ⟨282377913508668814792853381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188251942339112543195235587 282377913508668814792853381)
  ·
    refine ⟨52945858782875402773660009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 282377913508668814792853381 52945858782875402773660009)
    ·
      refine ⟨39709394087156552080245007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52945858782875402773660009 39709394087156552080245007)
      ·
        refine ⟨59564091130734828120367511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39709394087156552080245007 59564091130734828120367511)
        ·
          refine ⟨89346136696102242180551267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59564091130734828120367511 89346136696102242180551267)
          ·
            refine ⟨134019205044153363270826901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89346136696102242180551267 134019205044153363270826901)
            ·
              refine ⟨6282150236444688903320011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 134019205044153363270826901 6282150236444688903320011)
              ·
                refine ⟨9423225354667033354980017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6282150236444688903320011 9423225354667033354980017)
                ·
                  refine ⟨7067419016000275016235013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9423225354667033354980017 7067419016000275016235013)
                  ·
                    refine ⟨1325141065500051565544065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7067419016000275016235013 1325141065500051565544065)
                    ·
                      rfl

theorem cell23_7742109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 6, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 6, 1, 2, 4].length) (baseStart_7742109 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7742109 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7742109 prefixEnd_7742109 := by exact prefixLift 7742109
  have htrace : WordTrace (prefixWord ++ tailWord_7742109) baseStart_7742109 baseEnd_7742109 := by
    simpa [prefixWord, tailWord_7742109, baseEnd_7742109] using wordTrace_append hprefix tailTrace_7742109
  have hstable : (prefixWord ++ tailWord_7742109).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7742109).length < 2 ^ (prefixWord ++ tailWord_7742109).sum := by decide
  have hdescent : baseEnd_7742109 < baseStart_7742109 := by decide
  rcases family_descends (prefixWord ++ tailWord_7742109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7742129 : List Nat := [1, 2, 2, 6, 1, 1, 1, 2, 1, 2, 4]
def baseStart_7742129 : Nat := 118140960795 + 7742129 * 2 ^ 59
def prefixEnd_7742129 : Nat := 4983230072969 + 3 ^ 40 * 7742129 * 2
def baseEnd_7742129 : Nat := 3975433466113244618382103

theorem tailTrace_7742129 : CollatzResearch.WordTrace tailWord_7742129 prefixEnd_7742129 3975433466113244618382103 := by
  unfold tailWord_7742129
  simp only [CollatzResearch.WordTrace]
  refine ⟨282378642968596358208581441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188252428645730905472387627 282378642968596358208581441)
  ·
    refine ⟨211783982226447268656436081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 282378642968596358208581441 211783982226447268656436081)
    ·
      refine ⟨158837986669835451492327061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 211783982226447268656436081 158837986669835451492327061)
      ·
        refine ⟨7445530625148536788702831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 158837986669835451492327061 7445530625148536788702831)
        ·
          refine ⟨11168295937722805183054247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7445530625148536788702831 11168295937722805183054247)
          ·
            refine ⟨16752443906584207774581371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11168295937722805183054247 16752443906584207774581371)
            ·
              refine ⟨25128665859876311661872057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16752443906584207774581371 25128665859876311661872057)
              ·
                refine ⟨18846499394907233746404043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25128665859876311661872057 18846499394907233746404043)
                ·
                  refine ⟨28269749092360850619606065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18846499394907233746404043 28269749092360850619606065)
                  ·
                    refine ⟨21202311819270637964704549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 28269749092360850619606065 21202311819270637964704549)
                    ·
                      refine ⟨3975433466113244618382103, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21202311819270637964704549 3975433466113244618382103)
                      ·
                        rfl

theorem cell23_7742129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 1, 1, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 1, 1, 1, 2, 1, 2, 4].length) (baseStart_7742129 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7742129 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7742129 prefixEnd_7742129 := by exact prefixLift 7742129
  have htrace : WordTrace (prefixWord ++ tailWord_7742129) baseStart_7742129 baseEnd_7742129 := by
    simpa [prefixWord, tailWord_7742129, baseEnd_7742129] using wordTrace_append hprefix tailTrace_7742129
  have hstable : (prefixWord ++ tailWord_7742129).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7742129).length < 2 ^ (prefixWord ++ tailWord_7742129).sum := by decide
  have hdescent : baseEnd_7742129 < baseStart_7742129 := by decide
  rcases family_descends (prefixWord ++ tailWord_7742129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7742189 : List Nat := [1, 5, 1, 2, 1, 1, 1, 4, 1, 4, 2]
def baseStart_7742189 : Nat := 118140960795 + 7742189 * 2 ^ 59
def prefixEnd_7742189 : Nat := 4983230072969 + 3 ^ 40 * 7742189 * 2
def baseEnd_7742189 : Nat := 3975464274952514383631827

theorem tailTrace_7742189 : CollatzResearch.WordTrace tailWord_7742189 prefixEnd_7742189 3975464274952514383631827 := by
  unfold tailWord_7742189
  simp only [CollatzResearch.WordTrace]
  refine ⟨282380831348378988455765621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188253887565585992303843747 282380831348378988455765621)
  ·
    refine ⟨26473202938910530167728027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 282380831348378988455765621 26473202938910530167728027)
    ·
      refine ⟨39709804408365795251592041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26473202938910530167728027 39709804408365795251592041)
      ·
        refine ⟨29782353306274346438694031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39709804408365795251592041 29782353306274346438694031)
        ·
          refine ⟨44673529959411519658041047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29782353306274346438694031 44673529959411519658041047)
          ·
            refine ⟨67010294939117279487061571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44673529959411519658041047 67010294939117279487061571)
            ·
              refine ⟨100515442408675919230592357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67010294939117279487061571 100515442408675919230592357)
              ·
                refine ⟨18846645451626734855736067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 100515442408675919230592357 18846645451626734855736067)
                ·
                  refine ⟨28269968177440102283604101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18846645451626734855736067 28269968177440102283604101)
                  ·
                    refine ⟨5300619033270019178175769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28269968177440102283604101 5300619033270019178175769)
                    ·
                      refine ⟨3975464274952514383631827, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5300619033270019178175769 3975464274952514383631827)
                      ·
                        rfl

theorem cell23_7742189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 1, 4, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 1, 4, 1, 4, 2].length) (baseStart_7742189 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7742189 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7742189 prefixEnd_7742189 := by exact prefixLift 7742189
  have htrace : WordTrace (prefixWord ++ tailWord_7742189) baseStart_7742189 baseEnd_7742189 := by
    simpa [prefixWord, tailWord_7742189, baseEnd_7742189] using wordTrace_append hprefix tailTrace_7742189
  have hstable : (prefixWord ++ tailWord_7742189).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7742189).length < 2 ^ (prefixWord ++ tailWord_7742189).sum := by decide
  have hdescent : baseEnd_7742189 < baseStart_7742189 := by decide
  rcases family_descends (prefixWord ++ tailWord_7742189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7742212 : List Nat := [2, 3, 2, 2, 1, 1, 4, 1, 7]
def baseStart_7742212 : Nat := 118140960795 + 7742212 * 2 ^ 59
def prefixEnd_7742212 : Nat := 4983230072969 + 3 ^ 40 * 7742212 * 2
def baseEnd_7742212 : Nat := 441719565000840865960469

theorem tailTrace_7742212 : CollatzResearch.WordTrace tailWord_7742212 prefixEnd_7742212 441719565000840865960469 := by
  unfold tailWord_7742212
  simp only [CollatzResearch.WordTrace]
  refine ⟨141190835113647831691926445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 188254446818197108922568593 141190835113647831691926445)
  ·
    refine ⟨52946563167617936884472417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 141190835113647831691926445 52946563167617936884472417)
    ·
      refine ⟨39709922375713452663354313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52946563167617936884472417 39709922375713452663354313)
      ·
        refine ⟨29782441781785089497515735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39709922375713452663354313 29782441781785089497515735)
        ·
          refine ⟨44673662672677634246273603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29782441781785089497515735 44673662672677634246273603)
          ·
            refine ⟨67010494009016451369410405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44673662672677634246273603 67010494009016451369410405)
            ·
              refine ⟨12564467626690584631764451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 67010494009016451369410405 12564467626690584631764451)
              ·
                refine ⟨18846701440035876947646677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12564467626690584631764451 18846701440035876947646677)
                ·
                  refine ⟨441719565000840865960469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18846701440035876947646677 441719565000840865960469)
                  ·
                    rfl

theorem cell23_7742212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 4, 1, 7].length) (baseStart_7742212 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7742212 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7742212 prefixEnd_7742212 := by exact prefixLift 7742212
  have htrace : WordTrace (prefixWord ++ tailWord_7742212) baseStart_7742212 baseEnd_7742212 := by
    simpa [prefixWord, tailWord_7742212, baseEnd_7742212] using wordTrace_append hprefix tailTrace_7742212
  have hstable : (prefixWord ++ tailWord_7742212).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7742212).length < 2 ^ (prefixWord ++ tailWord_7742212).sum := by decide
  have hdescent : baseEnd_7742212 < baseStart_7742212 := by decide
  rcases family_descends (prefixWord ++ tailWord_7742212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7742225 : List Nat := [1, 2, 2, 1, 1, 3, 3, 2, 1, 7]
def baseStart_7742225 : Nat := 118140960795 + 7742225 * 2 ^ 59
def prefixEnd_7742225 : Nat := 4983230072969 + 3 ^ 40 * 7742225 * 2
def baseEnd_7742225 : Nat := 1325160920085358747593887

theorem tailTrace_7742225 : CollatzResearch.WordTrace tailWord_7742225 prefixEnd_7742225 1325160920085358747593887 := by
  unfold tailWord_7742225
  simp only [CollatzResearch.WordTrace]
  refine ⟨282382144376248566604076129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188254762917499044402717419 282382144376248566604076129)
  ·
    refine ⟨211786608282186424953057097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 282382144376248566604076129 211786608282186424953057097)
    ·
      refine ⟨158839956211639818714792823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 211786608282186424953057097 158839956211639818714792823)
      ·
        refine ⟨238259934317459728072189235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 158839956211639818714792823 238259934317459728072189235)
        ·
          refine ⟨357389901476189592108283853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 238259934317459728072189235 357389901476189592108283853)
          ·
            refine ⟨134021213053571097040606445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 357389901476189592108283853 134021213053571097040606445)
            ·
              refine ⟨50257954895089161390227417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 134021213053571097040606445 50257954895089161390227417)
              ·
                refine ⟨37693466171316871042670563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50257954895089161390227417 37693466171316871042670563)
                ·
                  refine ⟨56540199256975306564005845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37693466171316871042670563 56540199256975306564005845)
                  ·
                    refine ⟨1325160920085358747593887, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 56540199256975306564005845 1325160920085358747593887)
                    ·
                      rfl

theorem cell23_7742225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 7].length) (baseStart_7742225 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7742225 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7742225 prefixEnd_7742225 := by exact prefixLift 7742225
  have htrace : WordTrace (prefixWord ++ tailWord_7742225) baseStart_7742225 baseEnd_7742225 := by
    simpa [prefixWord, tailWord_7742225, baseEnd_7742225] using wordTrace_append hprefix tailTrace_7742225
  have hstable : (prefixWord ++ tailWord_7742225).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7742225).length < 2 ^ (prefixWord ++ tailWord_7742225).sum := by decide
  have hdescent : baseEnd_7742225 < baseStart_7742225 := by decide
  rcases family_descends (prefixWord ++ tailWord_7742225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7742242 : List Nat := [3, 3, 1, 1, 2, 2, 2, 1, 1, 7]
def baseStart_7742242 : Nat := 118140960795 + 7742242 * 2 ^ 59
def prefixEnd_7742242 : Nat := 4983230072969 + 3 ^ 40 * 7742242 * 2
def baseEnd_7742242 : Nat := 1325163829809067558756361

theorem tailTrace_7742242 : CollatzResearch.WordTrace tailWord_7742242 prefixEnd_7742242 1325163829809067558756361 := by
  unfold tailWord_7742242
  simp only [CollatzResearch.WordTrace]
  refine ⟨70595691104296744626861245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 188255176278124652338296653 70595691104296744626861245)
  ·
    refine ⟨26473384164111279235072967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 70595691104296744626861245 26473384164111279235072967)
    ·
      refine ⟨39710076246166918852609451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26473384164111279235072967 39710076246166918852609451)
      ·
        refine ⟨59565114369250378278914177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39710076246166918852609451 59565114369250378278914177)
        ·
          refine ⟨44673835776937783709185633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59565114369250378278914177 44673835776937783709185633)
          ·
            refine ⟨33505376832703337781889225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44673835776937783709185633 33505376832703337781889225)
            ·
              refine ⟨25129032624527503336416919, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33505376832703337781889225 25129032624527503336416919)
              ·
                refine ⟨37693548936791255004625379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25129032624527503336416919 37693548936791255004625379)
                ·
                  refine ⟨56540323405186882506938069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37693548936791255004625379 56540323405186882506938069)
                  ·
                    refine ⟨1325163829809067558756361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 56540323405186882506938069 1325163829809067558756361)
                    ·
                      rfl

theorem cell23_7742242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 2, 2, 1, 1, 7].length) (baseStart_7742242 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7742242 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7742242 prefixEnd_7742242 := by exact prefixLift 7742242
  have htrace : WordTrace (prefixWord ++ tailWord_7742242) baseStart_7742242 baseEnd_7742242 := by
    simpa [prefixWord, tailWord_7742242, baseEnd_7742242] using wordTrace_append hprefix tailTrace_7742242
  have hstable : (prefixWord ++ tailWord_7742242).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7742242).length < 2 ^ (prefixWord ++ tailWord_7742242).sum := by decide
  have hdescent : baseEnd_7742242 < baseStart_7742242 := by decide
  rcases family_descends (prefixWord ++ tailWord_7742242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7742269 : List Nat := [1, 4, 1, 4, 2, 1, 1, 1, 1, 2, 5]
def baseStart_7742269 : Nat := 118140960795 + 7742269 * 2 ^ 59
def prefixEnd_7742269 : Nat := 4983230072969 + 3 ^ 40 * 7742269 * 2
def baseEnd_7742269 : Nat := 3975505353404874070631459

theorem tailTrace_7742269 : CollatzResearch.WordTrace tailWord_7742269 prefixEnd_7742269 3975505353404874070631459 := by
  unfold tailWord_7742269
  simp only [CollatzResearch.WordTrace]
  refine ⟨282383749188089162118677861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188255832792059441412451907 282383749188089162118677861)
  ·
    refine ⟨52946952972766717897252099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 282383749188089162118677861 52946952972766717897252099)
    ·
      refine ⟨79420429459150076845878149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52946952972766717897252099 79420429459150076845878149)
      ·
        refine ⟨14891330523590639408602153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 79420429459150076845878149 14891330523590639408602153)
        ·
          refine ⟨11168497892692979556451615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14891330523590639408602153 11168497892692979556451615)
          ·
            refine ⟨16752746839039469334677423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11168497892692979556451615 16752746839039469334677423)
            ·
              refine ⟨25129120258559204002016135, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16752746839039469334677423 25129120258559204002016135)
              ·
                refine ⟨37693680387838806003024203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25129120258559204002016135 37693680387838806003024203)
                ·
                  refine ⟨56540520581758209004536305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37693680387838806003024203 56540520581758209004536305)
                  ·
                    refine ⟨42405390436318656753402229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 56540520581758209004536305 42405390436318656753402229)
                    ·
                      refine ⟨3975505353404874070631459, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 42405390436318656753402229 3975505353404874070631459)
                      ·
                        rfl

theorem cell23_7742269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 2, 1, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 2, 1, 1, 1, 1, 2, 5].length) (baseStart_7742269 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7742269 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7742269 prefixEnd_7742269 := by exact prefixLift 7742269
  have htrace : WordTrace (prefixWord ++ tailWord_7742269) baseStart_7742269 baseEnd_7742269 := by
    simpa [prefixWord, tailWord_7742269, baseEnd_7742269] using wordTrace_append hprefix tailTrace_7742269
  have hstable : (prefixWord ++ tailWord_7742269).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7742269).length < 2 ^ (prefixWord ++ tailWord_7742269).sum := by decide
  have hdescent : baseEnd_7742269 < baseStart_7742269 := by decide
  rcases family_descends (prefixWord ++ tailWord_7742269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7742282 : List Nat := [3, 1, 2, 1, 1, 1, 2, 4, 1, 4, 3]
def baseStart_7742282 : Nat := 118140960795 + 7742282 * 2 ^ 59
def prefixEnd_7742282 : Nat := 4983230072969 + 3 ^ 40 * 7742282 * 2
def baseEnd_7742282 : Nat := 3975512028653382519768899

theorem tailTrace_7742282 : CollatzResearch.WordTrace tailWord_7742282 prefixEnd_7742282 3975512028653382519768899 := by
  unfold tailWord_7742282
  simp only [CollatzResearch.WordTrace]
  refine ⟨70596055834260516334725275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 188256148891361376892600733 70596055834260516334725275)
  ·
    refine ⟨105894083751390774502087913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70596055834260516334725275 105894083751390774502087913)
    ·
      refine ⟨79420562813543080876565935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 105894083751390774502087913 79420562813543080876565935)
      ·
        refine ⟨119130844220314621314848903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79420562813543080876565935 119130844220314621314848903)
        ·
          refine ⟨178696266330471931972273355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 119130844220314621314848903 178696266330471931972273355)
          ·
            refine ⟨268044399495707897958410033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 178696266330471931972273355 268044399495707897958410033)
            ·
              refine ⟨201033299621780923468807525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 268044399495707897958410033 201033299621780923468807525)
              ·
                refine ⟨37693743679083923150401411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 201033299621780923468807525 37693743679083923150401411)
                ·
                  refine ⟨56540615518625884725602117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37693743679083923150401411 56540615518625884725602117)
                  ·
                    refine ⟨10601365409742353386050397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 56540615518625884725602117 10601365409742353386050397)
                    ·
                      refine ⟨3975512028653382519768899, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10601365409742353386050397 3975512028653382519768899)
                      ·
                        rfl

theorem cell23_7742282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 2, 4, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 2, 4, 1, 4, 3].length) (baseStart_7742282 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7742282 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7742282 prefixEnd_7742282 := by exact prefixLift 7742282
  have htrace : WordTrace (prefixWord ++ tailWord_7742282) baseStart_7742282 baseEnd_7742282 := by
    simpa [prefixWord, tailWord_7742282, baseEnd_7742282] using wordTrace_append hprefix tailTrace_7742282
  have hstable : (prefixWord ++ tailWord_7742282).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7742282).length < 2 ^ (prefixWord ++ tailWord_7742282).sum := by decide
  have hdescent : baseEnd_7742282 < baseStart_7742282 := by decide
  rcases family_descends (prefixWord ++ tailWord_7742282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7742339 : List Nat := [1, 1, 1, 3, 4, 1, 2, 2, 1, 5, 2]
def baseStart_7742339 : Nat := 118140960795 + 7742339 * 2 ^ 59
def prefixEnd_7742339 : Nat := 4983230072969 + 3 ^ 40 * 7742339 * 2
def baseEnd_7742339 : Nat := 3975541297050688796756137

theorem tailTrace_7742339 : CollatzResearch.WordTrace tailWord_7742339 prefixEnd_7742339 3975541297050688796756137 := by
  unfold tailWord_7742339
  simp only [CollatzResearch.WordTrace]
  refine ⟨282386302297835564073726071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188257534865223709382484047 282386302297835564073726071)
  ·
    refine ⟨423579453446753346110589107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 282386302297835564073726071 423579453446753346110589107)
    ·
      refine ⟨635369180170130019165883661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 423579453446753346110589107 635369180170130019165883661)
      ·
        refine ⟨238263442563798757187206373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 635369180170130019165883661 238263442563798757187206373)
        ·
          refine ⟨44674395480712266972601195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 238263442563798757187206373 44674395480712266972601195)
          ·
            refine ⟨67011593221068400458901793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44674395480712266972601195 67011593221068400458901793)
            ·
              refine ⟨50258694915801300344176345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 67011593221068400458901793 50258694915801300344176345)
              ·
                refine ⟨37694021186850975258132259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50258694915801300344176345 37694021186850975258132259)
                ·
                  refine ⟨56541031780276462887198389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37694021186850975258132259 56541031780276462887198389)
                  ·
                    refine ⟨5300721729400918395674849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 56541031780276462887198389 5300721729400918395674849)
                    ·
                      refine ⟨3975541297050688796756137, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5300721729400918395674849 3975541297050688796756137)
                      ·
                        rfl

theorem cell23_7742339_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 2, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 2, 2, 1, 5, 2].length) (baseStart_7742339 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7742339 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7742339 prefixEnd_7742339 := by exact prefixLift 7742339
  have htrace : WordTrace (prefixWord ++ tailWord_7742339) baseStart_7742339 baseEnd_7742339 := by
    simpa [prefixWord, tailWord_7742339, baseEnd_7742339] using wordTrace_append hprefix tailTrace_7742339
  have hstable : (prefixWord ++ tailWord_7742339).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7742339).length < 2 ^ (prefixWord ++ tailWord_7742339).sum := by decide
  have hdescent : baseEnd_7742339 < baseStart_7742339 := by decide
  rcases family_descends (prefixWord ++ tailWord_7742339) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7742346 : List Nat := [3, 1, 2, 4, 1, 1, 1, 1, 5, 1, 3]
def baseStart_7742346 : Nat := 118140960795 + 7742346 * 2 ^ 59
def prefixEnd_7742346 : Nat := 4983230072969 + 3 ^ 40 * 7742346 * 2
def baseEnd_7742346 : Nat := 3975544891415270269368605

theorem tailTrace_7742346 : CollatzResearch.WordTrace tailWord_7742346 prefixEnd_7742346 3975544891415270269368605 := by
  unfold tailWord_7742346
  simp only [CollatzResearch.WordTrace]
  refine ⟨70596639402202551067307723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 188257705072540136179487261 70596639402202551067307723)
  ·
    refine ⟨105894959103303826600961585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70596639402202551067307723 105894959103303826600961585)
    ·
      refine ⟨79421219327477869950721189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 105894959103303826600961585 79421219327477869950721189)
      ·
        refine ⟨14891478623902100615760223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 79421219327477869950721189 14891478623902100615760223)
        ·
          refine ⟨22337217935853150923640335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14891478623902100615760223 22337217935853150923640335)
          ·
            refine ⟨33505826903779726385460503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22337217935853150923640335 33505826903779726385460503)
            ·
              refine ⟨50258740355669589578190755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33505826903779726385460503 50258740355669589578190755)
              ·
                refine ⟨75388110533504384367286133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50258740355669589578190755 75388110533504384367286133)
                ·
                  refine ⟨7067635362516036034433075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 75388110533504384367286133 7067635362516036034433075)
                  ·
                    refine ⟨10601453043774054051649613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7067635362516036034433075 10601453043774054051649613)
                    ·
                      refine ⟨3975544891415270269368605, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10601453043774054051649613 3975544891415270269368605)
                      ·
                        rfl

theorem cell23_7742346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 1, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 1, 1, 1, 5, 1, 3].length) (baseStart_7742346 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7742346 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7742346 prefixEnd_7742346 := by exact prefixLift 7742346
  have htrace : WordTrace (prefixWord ++ tailWord_7742346) baseStart_7742346 baseEnd_7742346 := by
    simpa [prefixWord, tailWord_7742346, baseEnd_7742346] using wordTrace_append hprefix tailTrace_7742346
  have hstable : (prefixWord ++ tailWord_7742346).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7742346).length < 2 ^ (prefixWord ++ tailWord_7742346).sum := by decide
  have hdescent : baseEnd_7742346 < baseStart_7742346 := by decide
  rcases family_descends (prefixWord ++ tailWord_7742346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7742352 : List Nat := [2, 1, 1, 1, 1, 1, 2, 2, 7, 1, 4]
def baseStart_7742352 : Nat := 118140960795 + 7742352 * 2 ^ 59
def prefixEnd_7742352 : Nat := 4983230072969 + 3 ^ 40 * 7742352 * 2
def baseEnd_7742352 : Nat := 3975547972299197245893577

theorem tailTrace_7742352 : CollatzResearch.WordTrace tailWord_7742352 prefixEnd_7742352 3975547972299197245893577 := by
  unfold tailWord_7742352
  simp only [CollatzResearch.WordTrace]
  refine ⟨141193388223394233646974655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 188257850964525644862632873 141193388223394233646974655)
  ·
    refine ⟨211790082335091350470461983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141193388223394233646974655 211790082335091350470461983)
    ·
      refine ⟨317685123502637025705692975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 211790082335091350470461983 317685123502637025705692975)
      ·
        refine ⟨476527685253955538558539463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 317685123502637025705692975 476527685253955538558539463)
        ·
          refine ⟨714791527880933307837809195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 476527685253955538558539463 714791527880933307837809195)
          ·
            refine ⟨1072187291821399961756713793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 714791527880933307837809195 1072187291821399961756713793)
            ·
              refine ⟨804140468866049971317535345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1072187291821399961756713793 804140468866049971317535345)
              ·
                refine ⟨603105351649537478488151509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 804140468866049971317535345 603105351649537478488151509)
                ·
                  refine ⟨14135281679286034652066051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 603105351649537478488151509 14135281679286034652066051)
                  ·
                    refine ⟨21202922518929051978099077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14135281679286034652066051 21202922518929051978099077)
                    ·
                      refine ⟨3975547972299197245893577, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21202922518929051978099077 3975547972299197245893577)
                      ·
                        rfl

theorem cell23_7742352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 2, 7, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 2, 7, 1, 4].length) (baseStart_7742352 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7742352 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7742352 prefixEnd_7742352 := by exact prefixLift 7742352
  have htrace : WordTrace (prefixWord ++ tailWord_7742352) baseStart_7742352 baseEnd_7742352 := by
    simpa [prefixWord, tailWord_7742352, baseEnd_7742352] using wordTrace_append hprefix tailTrace_7742352
  have hstable : (prefixWord ++ tailWord_7742352).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7742352).length < 2 ^ (prefixWord ++ tailWord_7742352).sum := by decide
  have hdescent : baseEnd_7742352 < baseStart_7742352 := by decide
  rcases family_descends (prefixWord ++ tailWord_7742352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7742356 : List Nat := [2, 4, 2, 1, 1, 1, 3, 1, 1, 5, 2]
def baseStart_7742356 : Nat := 118140960795 + 7742356 * 2 ^ 59
def prefixEnd_7742356 : Nat := 4983230072969 + 3 ^ 40 * 7742356 * 2
def baseEnd_7742356 : Nat := 3975550026221815230243559

theorem tailTrace_7742356 : CollatzResearch.WordTrace tailWord_7742356 prefixEnd_7742356 3975550026221815230243559 := by
  unfold tailWord_7742356
  simp only [CollatzResearch.WordTrace]
  refine ⟨141193461169386987988547461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 188257948225849317318063281 141193461169386987988547461)
  ·
    refine ⟨26473773969260060247852649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 141193461169386987988547461 26473773969260060247852649)
    ·
      refine ⟨19855330476945045185889487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26473773969260060247852649 19855330476945045185889487)
      ·
        refine ⟨29782995715417567778834231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19855330476945045185889487 29782995715417567778834231)
        ·
          refine ⟨44674493573126351668251347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29782995715417567778834231 44674493573126351668251347)
          ·
            refine ⟨67011740359689527502377021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44674493573126351668251347 67011740359689527502377021)
            ·
              refine ⟨25129402634883572813391383, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 67011740359689527502377021 25129402634883572813391383)
              ·
                refine ⟨37694103952325359220087075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25129402634883572813391383 37694103952325359220087075)
                ·
                  refine ⟨56541155928488038830130613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37694103952325359220087075 56541155928488038830130613)
                  ·
                    refine ⟨5300733368295753640324745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 56541155928488038830130613 5300733368295753640324745)
                    ·
                      refine ⟨3975550026221815230243559, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5300733368295753640324745 3975550026221815230243559)
                      ·
                        rfl

theorem cell23_7742356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 3, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 3, 1, 1, 5, 2].length) (baseStart_7742356 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7742356 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7742356 prefixEnd_7742356 := by exact prefixLift 7742356
  have htrace : WordTrace (prefixWord ++ tailWord_7742356) baseStart_7742356 baseEnd_7742356 := by
    simpa [prefixWord, tailWord_7742356, baseEnd_7742356] using wordTrace_append hprefix tailTrace_7742356
  have hstable : (prefixWord ++ tailWord_7742356).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7742356).length < 2 ^ (prefixWord ++ tailWord_7742356).sum := by decide
  have hdescent : baseEnd_7742356 < baseStart_7742356 := by decide
  rcases family_descends (prefixWord ++ tailWord_7742356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7742389 : List Nat := [1, 3, 3, 2, 1, 1, 3, 2, 1, 1, 5]
def baseStart_7742389 : Nat := 118140960795 + 7742389 * 2 ^ 59
def prefixEnd_7742389 : Nat := 4983230072969 + 3 ^ 40 * 7742389 * 2
def baseEnd_7742389 : Nat := 3975566971083413601130907

theorem tailTrace_7742389 : CollatzResearch.WordTrace tailWord_7742389 prefixEnd_7742389 3975566971083413601130907 := by
  unfold tailWord_7742389
  simp only [CollatzResearch.WordTrace]
  refine ⟨282388125947654422613046221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188258750631769615075364147 282388125947654422613046221)
  ·
    refine ⟨105895547230370408479892333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 282388125947654422613046221 105895547230370408479892333)
    ·
      refine ⟨39710830211388903179959625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 105895547230370408479892333 39710830211388903179959625)
      ·
        refine ⟨29783122658541677384969719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39710830211388903179959625 29783122658541677384969719)
        ·
          refine ⟨44674683987812516077454579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29783122658541677384969719 44674683987812516077454579)
          ·
            refine ⟨67012025981718774116181869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44674683987812516077454579 67012025981718774116181869)
            ·
              refine ⟨25129509743144540293568201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 67012025981718774116181869 25129509743144540293568201)
              ·
                refine ⟨18847132307358405220176151, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25129509743144540293568201 18847132307358405220176151)
                ·
                  refine ⟨28270698461037607830264227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18847132307358405220176151 28270698461037607830264227)
                  ·
                    refine ⟨42406047691556411745396341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 28270698461037607830264227 42406047691556411745396341)
                    ·
                      refine ⟨3975566971083413601130907, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 42406047691556411745396341 3975566971083413601130907)
                      ·
                        rfl

theorem cell23_7742389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 3, 2, 1, 1, 5].length) (baseStart_7742389 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7742389 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7742389 prefixEnd_7742389 := by exact prefixLift 7742389
  have htrace : WordTrace (prefixWord ++ tailWord_7742389) baseStart_7742389 baseEnd_7742389 := by
    simpa [prefixWord, tailWord_7742389, baseEnd_7742389] using wordTrace_append hprefix tailTrace_7742389
  have hstable : (prefixWord ++ tailWord_7742389).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7742389).length < 2 ^ (prefixWord ++ tailWord_7742389).sum := by decide
  have hdescent : baseEnd_7742389 < baseStart_7742389 := by decide
  rcases family_descends (prefixWord ++ tailWord_7742389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7742437 : List Nat := [1, 3, 1, 6, 1, 2, 1, 1, 3, 2, 2]
def baseStart_7742437 : Nat := 118140960795 + 7742437 * 2 ^ 59
def prefixEnd_7742437 : Nat := 4983230072969 + 3 ^ 40 * 7742437 * 2
def baseEnd_7742437 : Nat := 3975591618154829413330687

theorem tailTrace_7742437 : CollatzResearch.WordTrace tailWord_7742437 prefixEnd_7742437 3975591618154829413330687 := by
  unfold tailWord_7742437
  simp only [CollatzResearch.WordTrace]
  refine ⟨282389876651480526810793565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188259917767653684540529043 282389876651480526810793565)
  ·
    refine ⟨105896203744305197554047587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 282389876651480526810793565 105896203744305197554047587)
    ·
      refine ⟨158844305616457796331071381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105896203744305197554047587 158844305616457796331071381)
      ·
        refine ⟨7445826825771459203018971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 158844305616457796331071381 7445826825771459203018971)
        ·
          refine ⟨11168740238657188804528457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7445826825771459203018971 11168740238657188804528457)
          ·
            refine ⟨8376555178992891603396343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11168740238657188804528457 8376555178992891603396343)
            ·
              refine ⟨12564832768489337405094515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8376555178992891603396343 12564832768489337405094515)
              ·
                refine ⟨18847249152734006107641773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12564832768489337405094515 18847249152734006107641773)
                ·
                  refine ⟨7067718432275252290365665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18847249152734006107641773 7067718432275252290365665)
                  ·
                    refine ⟨5300788824206439217774249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7067718432275252290365665 5300788824206439217774249)
                    ·
                      refine ⟨3975591618154829413330687, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5300788824206439217774249 3975591618154829413330687)
                      ·
                        rfl

theorem cell23_7742437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 1, 2, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 1, 2, 1, 1, 3, 2, 2].length) (baseStart_7742437 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7742437 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7742437 prefixEnd_7742437 := by exact prefixLift 7742437
  have htrace : WordTrace (prefixWord ++ tailWord_7742437) baseStart_7742437 baseEnd_7742437 := by
    simpa [prefixWord, tailWord_7742437, baseEnd_7742437] using wordTrace_append hprefix tailTrace_7742437
  have hstable : (prefixWord ++ tailWord_7742437).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7742437).length < 2 ^ (prefixWord ++ tailWord_7742437).sum := by decide
  have hdescent : baseEnd_7742437 < baseStart_7742437 := by decide
  rcases family_descends (prefixWord ++ tailWord_7742437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7742476 : List Nat := [2, 2, 1, 2, 3, 2, 1, 1, 3, 4, 2]
def baseStart_7742476 : Nat := 118140960795 + 7742476 * 2 ^ 59
def prefixEnd_7742476 : Nat := 4983230072969 + 3 ^ 40 * 7742476 * 2
def baseEnd_7742476 : Nat := 3975611643900354760743007

theorem tailTrace_7742476 : CollatzResearch.WordTrace tailWord_7742476 prefixEnd_7742476 3975611643900354760743007 := by
  unfold tailWord_7742476
  simp only [CollatzResearch.WordTrace]
  refine ⟨141195649549169618235731641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 188260866065559490980975521 141195649549169618235731641)
  ·
    refine ⟨105896737161877213676798731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 141195649549169618235731641 105896737161877213676798731)
    ·
      refine ⟨158845105742815820515198097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105896737161877213676798731 158845105742815820515198097)
      ·
        refine ⟨119133829307111865386398573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 158845105742815820515198097 119133829307111865386398573)
        ·
          refine ⟨44675185990166949519899465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 119133829307111865386398573 44675185990166949519899465)
          ·
            refine ⟨33506389492625212139924599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44675185990166949519899465 33506389492625212139924599)
            ·
              refine ⟨50259584238937818209886899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33506389492625212139924599 50259584238937818209886899)
              ·
                refine ⟨75389376358406727314830349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50259584238937818209886899 75389376358406727314830349)
                ·
                  refine ⟨28271016134402522743061381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 75389376358406727314830349 28271016134402522743061381)
                  ·
                    refine ⟨5300815525200473014324009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28271016134402522743061381 5300815525200473014324009)
                    ·
                      refine ⟨3975611643900354760743007, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5300815525200473014324009 3975611643900354760743007)
                      ·
                        rfl

theorem cell23_7742476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 2, 1, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 2, 1, 1, 3, 4, 2].length) (baseStart_7742476 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7742476 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7742476 prefixEnd_7742476 := by exact prefixLift 7742476
  have htrace : WordTrace (prefixWord ++ tailWord_7742476) baseStart_7742476 baseEnd_7742476 := by
    simpa [prefixWord, tailWord_7742476, baseEnd_7742476] using wordTrace_append hprefix tailTrace_7742476
  have hstable : (prefixWord ++ tailWord_7742476).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7742476).length < 2 ^ (prefixWord ++ tailWord_7742476).sum := by decide
  have hdescent : baseEnd_7742476 < baseStart_7742476 := by decide
  rcases family_descends (prefixWord ++ tailWord_7742476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7742510 : List Nat := [4, 1, 3, 1, 1, 1, 1, 5, 2, 2, 2]
def baseStart_7742510 : Nat := 118140960795 + 7742510 * 2 ^ 59
def prefixEnd_7742510 : Nat := 4983230072969 + 3 ^ 40 * 7742510 * 2
def baseEnd_7742510 : Nat := 3975629102242607627717851

theorem tailTrace_7742510 : CollatzResearch.WordTrace tailWord_7742510 prefixEnd_7742510 3975629102242607627717851 := by
  unfold tailWord_7742510
  simp only [CollatzResearch.WordTrace]
  refine ⟨35299067397527007534775123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 188261692786810706852133989 35299067397527007534775123)
  ·
    refine ⟨52948601096290511302162685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35299067397527007534775123 52948601096290511302162685)
    ·
      refine ⟨19855725411108941738311007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 52948601096290511302162685 19855725411108941738311007)
      ·
        refine ⟨29783588116663412607466511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19855725411108941738311007 29783588116663412607466511)
        ·
          refine ⟨44675382174995118911199767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29783588116663412607466511 44675382174995118911199767)
          ·
            refine ⟨67013073262492678366799651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44675382174995118911199767 67013073262492678366799651)
            ·
              refine ⟨100519609893739017550199477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67013073262492678366799651 100519609893739017550199477)
              ·
                refine ⟨9423713427538032895331201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 100519609893739017550199477 9423713427538032895331201)
                ·
                  refine ⟨7067785070653524671498401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9423713427538032895331201 7067785070653524671498401)
                  ·
                    refine ⟨5300838802990143503623801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7067785070653524671498401 5300838802990143503623801)
                    ·
                      refine ⟨3975629102242607627717851, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5300838802990143503623801 3975629102242607627717851)
                      ·
                        rfl

theorem cell23_7742510_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 1, 5, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 1, 5, 2, 2, 2].length) (baseStart_7742510 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7742510 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7742510 prefixEnd_7742510 := by exact prefixLift 7742510
  have htrace : WordTrace (prefixWord ++ tailWord_7742510) baseStart_7742510 baseEnd_7742510 := by
    simpa [prefixWord, tailWord_7742510, baseEnd_7742510] using wordTrace_append hprefix tailTrace_7742510
  have hstable : (prefixWord ++ tailWord_7742510).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7742510).length < 2 ^ (prefixWord ++ tailWord_7742510).sum := by decide
  have hdescent : baseEnd_7742510 < baseStart_7742510 := by decide
  rcases family_descends (prefixWord ++ tailWord_7742510) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7742516 : List Nat := [2, 5, 1, 2, 1, 1, 1, 1, 9]
def baseStart_7742516 : Nat := 118140960795 + 7742516 * 2 ^ 59
def prefixEnd_7742516 : Nat := 4983230072969 + 3 ^ 40 * 7742516 * 2
def baseEnd_7742516 : Nat := 441736909236281622693647

theorem tailTrace_7742516 : CollatzResearch.WordTrace tailWord_7742516 prefixEnd_7742516 441736909236281622693647 := by
  unfold tailWord_7742516
  simp only [CollatzResearch.WordTrace]
  refine ⟨141196379009097161651459701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 188261838678796215535279601 141196379009097161651459701)
  ·
    refine ⟨13237160532102858904824347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 141196379009097161651459701 13237160532102858904824347)
    ·
      refine ⟨19855740798154288357236521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13237160532102858904824347 19855740798154288357236521)
      ·
        refine ⟨14891805598615716267927391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19855740798154288357236521 14891805598615716267927391)
        ·
          refine ⟨22337708397923574401891087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14891805598615716267927391 22337708397923574401891087)
          ·
            refine ⟨33506562596885361602836631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22337708397923574401891087 33506562596885361602836631)
            ·
              refine ⟨50259843895328042404254947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33506562596885361602836631 50259843895328042404254947)
              ·
                refine ⟨75389765842992063606382421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50259843895328042404254947 75389765842992063606382421)
                ·
                  refine ⟨441736909236281622693647, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 75389765842992063606382421 441736909236281622693647)
                  ·
                    rfl

theorem cell23_7742516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 1, 1, 1, 9].length) (baseStart_7742516 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7742516 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7742516 prefixEnd_7742516 := by exact prefixLift 7742516
  have htrace : WordTrace (prefixWord ++ tailWord_7742516) baseStart_7742516 baseEnd_7742516 := by
    simpa [prefixWord, tailWord_7742516, baseEnd_7742516] using wordTrace_append hprefix tailTrace_7742516
  have hstable : (prefixWord ++ tailWord_7742516).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7742516).length < 2 ^ (prefixWord ++ tailWord_7742516).sum := by decide
  have hdescent : baseEnd_7742516 < baseStart_7742516 := by decide
  rcases family_descends (prefixWord ++ tailWord_7742516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7742550 : List Nat := [5, 2, 2, 1, 2, 1, 2, 1, 7]
def baseStart_7742550 : Nat := 118140960795 + 7742550 * 2 ^ 59
def prefixEnd_7742550 : Nat := 4983230072969 + 3 ^ 40 * 7742550 * 2
def baseEnd_7742550 : Nat := 441738849052087496801963

theorem tailTrace_7742550 : CollatzResearch.WordTrace tailWord_7742550 prefixEnd_7742550 441738849052087496801963 := by
  unfold tailWord_7742550
  simp only [CollatzResearch.WordTrace]
  refine ⟨17649624881254446694353569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 188262665400047431406438069 17649624881254446694353569)
  ·
    refine ⟨13237218660940835020765177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17649624881254446694353569 13237218660940835020765177)
    ·
      refine ⟨9927913995705626265573883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13237218660940835020765177 9927913995705626265573883)
      ·
        refine ⟨14891870993558439398360825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9927913995705626265573883 14891870993558439398360825)
        ·
          refine ⟨11168903245168829548770619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14891870993558439398360825 11168903245168829548770619)
          ·
            refine ⟨16753354867753244323155929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11168903245168829548770619 16753354867753244323155929)
            ·
              refine ⟨12565016150814933242366947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16753354867753244323155929 12565016150814933242366947)
              ·
                refine ⟨18847524226222399863550421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12565016150814933242366947 18847524226222399863550421)
                ·
                  refine ⟨441738849052087496801963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18847524226222399863550421 441738849052087496801963)
                  ·
                    rfl

theorem cell23_7742550_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 2, 1, 2, 1, 7].length) (baseStart_7742550 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7742550 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7742550 prefixEnd_7742550 := by exact prefixLift 7742550
  have htrace : WordTrace (prefixWord ++ tailWord_7742550) baseStart_7742550 baseEnd_7742550 := by
    simpa [prefixWord, tailWord_7742550, baseEnd_7742550] using wordTrace_append hprefix tailTrace_7742550
  have hstable : (prefixWord ++ tailWord_7742550).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7742550).length < 2 ^ (prefixWord ++ tailWord_7742550).sum := by decide
  have hdescent : baseEnd_7742550 < baseStart_7742550 := by decide
  rcases family_descends (prefixWord ++ tailWord_7742550) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7742576 : List Nat := [2, 1, 1, 1, 5, 1, 1, 4, 3, 4]
def baseStart_7742576 : Nat := 118140960795 + 7742576 * 2 ^ 59
def prefixEnd_7742576 : Nat := 4983230072969 + 3 ^ 40 * 7742576 * 2
def baseEnd_7742576 : Nat := 1325220997321934789830849

theorem tailTrace_7742576 : CollatzResearch.WordTrace tailWord_7742576 prefixEnd_7742576 1325220997321934789830849 := by
  unfold tailWord_7742576
  simp only [CollatzResearch.WordTrace]
  refine ⟨141197473198988476775051791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 188263297598651302366735721 141197473198988476775051791)
  ·
    refine ⟨211796209798482715162577687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141197473198988476775051791 211796209798482715162577687)
    ·
      refine ⟨317694314697724072743866531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 211796209798482715162577687 317694314697724072743866531)
      ·
        refine ⟨476541472046586109115799797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 317694314697724072743866531 476541472046586109115799797)
        ·
          refine ⟨44675763004367447729606231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 476541472046586109115799797 44675763004367447729606231)
          ·
            refine ⟨67013644506551171594409347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44675763004367447729606231 67013644506551171594409347)
            ·
              refine ⟨100520466759826757391614021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67013644506551171594409347 100520466759826757391614021)
              ·
                refine ⟨18847587517467517010927629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 100520466759826757391614021 18847587517467517010927629)
                ·
                  refine ⟨7067845319050318879097861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18847587517467517010927629 7067845319050318879097861)
                  ·
                    refine ⟨1325220997321934789830849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7067845319050318879097861 1325220997321934789830849)
                    ·
                      rfl

theorem cell23_7742576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 1, 4, 3, 4].length) (baseStart_7742576 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7742576 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7742576 prefixEnd_7742576 := by exact prefixLift 7742576
  have htrace : WordTrace (prefixWord ++ tailWord_7742576) baseStart_7742576 baseEnd_7742576 := by
    simpa [prefixWord, tailWord_7742576, baseEnd_7742576] using wordTrace_append hprefix tailTrace_7742576
  have hstable : (prefixWord ++ tailWord_7742576).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7742576).length < 2 ^ (prefixWord ++ tailWord_7742576).sum := by decide
  have hdescent : baseEnd_7742576 < baseStart_7742576 := by decide
  rcases family_descends (prefixWord ++ tailWord_7742576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7742589 : List Nat := [1, 4, 1, 1, 3, 1, 1, 1, 10]
def baseStart_7742589 : Nat := 118140960795 + 7742589 * 2 ^ 59
def prefixEnd_7742589 : Nat := 4983230072969 + 3 ^ 40 * 7742589 * 2
def baseEnd_7742589 : Nat := 441741074134923646514443

theorem tailTrace_7742589 : CollatzResearch.WordTrace tailWord_7742589 prefixEnd_7742589 441741074134923646514443 := by
  unfold tailWord_7742589
  simp only [CollatzResearch.WordTrace]
  refine ⟨282395420546929856770326821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188263613697953237846884547 282395420546929856770326821)
  ·
    refine ⟨52949141352549348144436279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 282395420546929856770326821 52949141352549348144436279)
    ·
      refine ⟨79423712028824022216654419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52949141352549348144436279 79423712028824022216654419)
      ·
        refine ⟨119135568043236033324981629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79423712028824022216654419 119135568043236033324981629)
        ·
          refine ⟨44675838016213512496868111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 119135568043236033324981629 44675838016213512496868111)
          ·
            refine ⟨67013757024320268745302167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44675838016213512496868111 67013757024320268745302167)
            ·
              refine ⟨100520635536480403117953251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67013757024320268745302167 100520635536480403117953251)
              ·
                refine ⟨150780953304720604676929877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 100520635536480403117953251 150780953304720604676929877)
                ·
                  refine ⟨441741074134923646514443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 150780953304720604676929877 441741074134923646514443)
                  ·
                    rfl

theorem cell23_7742589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 1, 1, 10].length) (baseStart_7742589 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7742589 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7742589 prefixEnd_7742589 := by exact prefixLift 7742589
  have htrace : WordTrace (prefixWord ++ tailWord_7742589) baseStart_7742589 baseEnd_7742589 := by
    simpa [prefixWord, tailWord_7742589, baseEnd_7742589] using wordTrace_append hprefix tailTrace_7742589
  have hstable : (prefixWord ++ tailWord_7742589).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7742589).length < 2 ^ (prefixWord ++ tailWord_7742589).sum := by decide
  have hdescent : baseEnd_7742589 < baseStart_7742589 := by decide
  rcases family_descends (prefixWord ++ tailWord_7742589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7742606 : List Nat := [4, 1, 1, 3, 2, 1, 2, 1, 8]
def baseStart_7742606 : Nat := 118140960795 + 7742606 * 2 ^ 59
def prefixEnd_7742606 : Nat := 4983230072969 + 3 ^ 40 * 7742606 * 2
def baseEnd_7742606 : Nat := 441742044042826583568601

theorem tailTrace_7742606 : CollatzResearch.WordTrace tailWord_7742606 prefixEnd_7742606 441742044042826583568601 := by
  unfold tailWord_7742606
  simp only [CollatzResearch.WordTrace]
  refine ⟨35299505073483533584211959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 188264027058578845782463781 35299505073483533584211959)
  ·
    refine ⟨52949257610225300376317939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35299505073483533584211959 52949257610225300376317939)
    ·
      refine ⟨79423886415337950564476909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52949257610225300376317939 79423886415337950564476909)
      ·
        refine ⟨29783957405751731461678841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 79423886415337950564476909 29783957405751731461678841)
        ·
          refine ⟨22337968054313798596259131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29783957405751731461678841 22337968054313798596259131)
          ·
            refine ⟨33506952081470697894388697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22337968054313798596259131 33506952081470697894388697)
            ·
              refine ⟨25130214061103023420791523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33506952081470697894388697 25130214061103023420791523)
              ·
                refine ⟨37695321091654535131187285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25130214061103023420791523 37695321091654535131187285)
                ·
                  refine ⟨441742044042826583568601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 37695321091654535131187285 441742044042826583568601)
                  ·
                    rfl

theorem cell23_7742606_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 1, 2, 1, 8].length) (baseStart_7742606 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7742606 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7742606 prefixEnd_7742606 := by exact prefixLift 7742606
  have htrace : WordTrace (prefixWord ++ tailWord_7742606) baseStart_7742606 baseEnd_7742606 := by
    simpa [prefixWord, tailWord_7742606, baseEnd_7742606] using wordTrace_append hprefix tailTrace_7742606
  have hstable : (prefixWord ++ tailWord_7742606).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7742606).length < 2 ^ (prefixWord ++ tailWord_7742606).sum := by decide
  have hdescent : baseEnd_7742606 < baseStart_7742606 := by decide
  rcases family_descends (prefixWord ++ tailWord_7742606) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7742610 : List Nat := [3, 2, 3, 1, 1, 4, 1, 1, 3, 4]
def baseStart_7742610 : Nat := 118140960795 + 7742610 * 2 ^ 59
def prefixEnd_7742610 : Nat := 4983230072969 + 3 ^ 40 * 7742610 * 2
def baseEnd_7742610 : Nat := 1325226816769352412155797

theorem tailTrace_7742610 : CollatzResearch.WordTrace tailWord_7742610 prefixEnd_7742610 1325226816769352412155797 := by
  unfold tailWord_7742610
  simp only [CollatzResearch.WordTrace]
  refine ⟨70599046619963444339210321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 188264124319902518237894189 70599046619963444339210321)
  ·
    refine ⟨52949284964972583254407741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70599046619963444339210321 52949284964972583254407741)
    ·
      refine ⟨19855981861864718720402903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 52949284964972583254407741 19855981861864718720402903)
      ·
        refine ⟨29783972792797078080604355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19855981861864718720402903 29783972792797078080604355)
        ·
          refine ⟨44675959189195617120906533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29783972792797078080604355 44675959189195617120906533)
          ·
            refine ⟨8376742347974178210169975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 44675959189195617120906533 8376742347974178210169975)
            ·
              refine ⟨12565113521961267315254963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8376742347974178210169975 12565113521961267315254963)
              ·
                refine ⟨18847670282941900972882445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12565113521961267315254963 18847670282941900972882445)
                ·
                  refine ⟨7067876356103212864830917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18847670282941900972882445 7067876356103212864830917)
                  ·
                    refine ⟨1325226816769352412155797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7067876356103212864830917 1325226816769352412155797)
                    ·
                      rfl

theorem cell23_7742610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 4, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 4, 1, 1, 3, 4].length) (baseStart_7742610 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7742610 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7742610 prefixEnd_7742610 := by exact prefixLift 7742610
  have htrace : WordTrace (prefixWord ++ tailWord_7742610) baseStart_7742610 baseEnd_7742610 := by
    simpa [prefixWord, tailWord_7742610, baseEnd_7742610] using wordTrace_append hprefix tailTrace_7742610
  have hstable : (prefixWord ++ tailWord_7742610).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7742610).length < 2 ^ (prefixWord ++ tailWord_7742610).sum := by decide
  have hdescent : baseEnd_7742610 < baseStart_7742610 := by decide
  rcases family_descends (prefixWord ++ tailWord_7742610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7742623 : List Nat := [1, 1, 2, 6, 2, 1, 1, 3, 6]
def baseStart_7742623 : Nat := 118140960795 + 7742623 * 2 ^ 59
def prefixEnd_7742623 : Nat := 4983230072969 + 3 ^ 40 * 7742623 * 2
def baseEnd_7742623 : Nat := 441743013950729520622759

theorem tailTrace_7742623 : CollatzResearch.WordTrace tailWord_7742623 prefixEnd_7742623 441743013950729520622759 := by
  unfold tailWord_7742623
  simp only [CollatzResearch.WordTrace]
  refine ⟨282396660628806680577064523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188264440419204453718043015 282396660628806680577064523)
  ·
    refine ⟨423594990943210020865596785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 282396660628806680577064523 423594990943210020865596785)
    ·
      refine ⟨317696243207407515649197589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 423594990943210020865596785 317696243207407515649197589)
      ·
        refine ⟨14892011400347227296056137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 317696243207407515649197589 14892011400347227296056137)
        ·
          refine ⟨11169008550260420472042103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14892011400347227296056137 11169008550260420472042103)
          ·
            refine ⟨16753512825390630708063155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11169008550260420472042103 16753512825390630708063155)
            ·
              refine ⟨25130269238085946062094733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16753512825390630708063155 25130269238085946062094733)
              ·
                refine ⟨9423850964282229773285525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25130269238085946062094733 9423850964282229773285525)
                ·
                  refine ⟨441743013950729520622759, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9423850964282229773285525 441743013950729520622759)
                  ·
                    rfl

theorem cell23_7742623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 2, 1, 1, 3, 6].length) (baseStart_7742623 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7742623 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7742623 prefixEnd_7742623 := by exact prefixLift 7742623
  have htrace : WordTrace (prefixWord ++ tailWord_7742623) baseStart_7742623 baseEnd_7742623 := by
    simpa [prefixWord, tailWord_7742623, baseEnd_7742623] using wordTrace_append hprefix tailTrace_7742623
  have hstable : (prefixWord ++ tailWord_7742623).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7742623).length < 2 ^ (prefixWord ++ tailWord_7742623).sum := by decide
  have hdescent : baseEnd_7742623 < baseStart_7742623 := by decide
  rcases family_descends (prefixWord ++ tailWord_7742623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7742636 : List Nat := [2, 2, 1, 1, 1, 1, 1, 8, 1, 5]
def baseStart_7742636 : Nat := 118140960795 + 7742636 * 2 ^ 59
def prefixEnd_7742636 : Nat := 4983230072969 + 3 ^ 40 * 7742636 * 2
def baseEnd_7742636 : Nat := 1325231266935024711580757

theorem tailTrace_7742636 : CollatzResearch.WordTrace tailWord_7742636 prefixEnd_7742636 1325231266935024711580757 := by
  unfold tailWord_7742636
  simp only [CollatzResearch.WordTrace]
  refine ⟨141198567388879791898643881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 188264756518506389198191841 141198567388879791898643881)
  ·
    refine ⟨105898925541659843923982911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 141198567388879791898643881 105898925541659843923982911)
    ·
      refine ⟨158848388312489765885974367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105898925541659843923982911 158848388312489765885974367)
      ·
        refine ⟨238272582468734648828961551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 158848388312489765885974367 238272582468734648828961551)
        ·
          refine ⟨357408873703101973243442327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 238272582468734648828961551 357408873703101973243442327)
          ·
            refine ⟨536113310554652959865163491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 357408873703101973243442327 536113310554652959865163491)
            ·
              refine ⟨804169965831979439797745237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 536113310554652959865163491 804169965831979439797745237)
              ·
                refine ⟨9423866787093509060129827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 804169965831979439797745237 9423866787093509060129827)
                ·
                  refine ⟨14135800180640263590194741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9423866787093509060129827 14135800180640263590194741)
                  ·
                    refine ⟨1325231266935024711580757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14135800180640263590194741 1325231266935024711580757)
                    ·
                      rfl

theorem cell23_7742636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 1, 5].length) (baseStart_7742636 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7742636 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7742636 prefixEnd_7742636 := by exact prefixLift 7742636
  have htrace : WordTrace (prefixWord ++ tailWord_7742636) baseStart_7742636 baseEnd_7742636 := by
    simpa [prefixWord, tailWord_7742636, baseEnd_7742636] using wordTrace_append hprefix tailTrace_7742636
  have hstable : (prefixWord ++ tailWord_7742636).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7742636).length < 2 ^ (prefixWord ++ tailWord_7742636).sum := by decide
  have hdescent : baseEnd_7742636 < baseStart_7742636 := by decide
  rcases family_descends (prefixWord ++ tailWord_7742636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7742643 : List Nat := [1, 1, 1, 2, 3, 2, 3, 3, 2, 3, 2]
def baseStart_7742643 : Nat := 118140960795 + 7742643 * 2 ^ 59
def prefixEnd_7742643 : Nat := 4983230072969 + 3 ^ 40 * 7742643 * 2
def baseEnd_7742643 : Nat := 3975697395169655607354739

theorem tailTrace_7742643 : CollatzResearch.WordTrace tailWord_7742643 prefixEnd_7742643 3975697395169655607354739 := by
  unfold tailWord_7742643
  simp only [CollatzResearch.WordTrace]
  refine ⟨282397390088734223992792583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188264926725822815995195055 282397390088734223992792583)
  ·
    refine ⟨423596085133101335989188875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 282397390088734223992792583 423596085133101335989188875)
    ·
      refine ⟨635394127699652003983783313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 423596085133101335989188875 635394127699652003983783313)
      ·
        refine ⟨476545595774739002987837485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 635394127699652003983783313 476545595774739002987837485)
        ·
          refine ⟨178704598415527126120439057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 476545595774739002987837485 178704598415527126120439057)
          ·
            refine ⟨134028448811645344590329293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 178704598415527126120439057 134028448811645344590329293)
            ·
              refine ⟨50260668304367004221373485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 134028448811645344590329293 50260668304367004221373485)
              ·
                refine ⟨18847750614137626583015057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 50260668304367004221373485 18847750614137626583015057)
                ·
                  refine ⟨14135812960603219937261293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18847750614137626583015057 14135812960603219937261293)
                  ·
                    refine ⟨5300929860226207476472985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14135812960603219937261293 5300929860226207476472985)
                    ·
                      refine ⟨3975697395169655607354739, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5300929860226207476472985 3975697395169655607354739)
                      ·
                        rfl

theorem cell23_7742643_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 3, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 3, 3, 2, 3, 2].length) (baseStart_7742643 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7742643 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7742643 prefixEnd_7742643 := by exact prefixLift 7742643
  have htrace : WordTrace (prefixWord ++ tailWord_7742643) baseStart_7742643 baseEnd_7742643 := by
    simpa [prefixWord, tailWord_7742643, baseEnd_7742643] using wordTrace_append hprefix tailTrace_7742643
  have hstable : (prefixWord ++ tailWord_7742643).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7742643).length < 2 ^ (prefixWord ++ tailWord_7742643).sum := by decide
  have hdescent : baseEnd_7742643 < baseStart_7742643 := by decide
  rcases family_descends (prefixWord ++ tailWord_7742643) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7742650 : List Nat := [3, 1, 1, 1, 2, 2, 1, 7, 1, 1, 3]
def baseStart_7742650 : Nat := 118140960795 + 7742650 * 2 ^ 59
def prefixEnd_7742650 : Nat := 4983230072969 + 3 ^ 40 * 7742650 * 2
def baseEnd_7742650 : Nat := 3975700989534237079967207

theorem tailTrace_7742650 : CollatzResearch.WordTrace tailWord_7742650 prefixEnd_7742650 3975700989534237079967207 := by
  unfold tailWord_7742650
  simp only [CollatzResearch.WordTrace]
  refine ⟨70599411349927216047074351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 188265096933139242792198269 70599411349927216047074351)
  ·
    refine ⟨105899117024890824070611527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70599411349927216047074351 105899117024890824070611527)
    ·
      refine ⟨158848675537336236105917291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105899117024890824070611527 158848675537336236105917291)
      ·
        refine ⟨238273013306004354158875937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 158848675537336236105917291 238273013306004354158875937)
        ·
          refine ⟨178704759979503265619156953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 238273013306004354158875937 178704759979503265619156953)
          ·
            refine ⟨134028569984627449214367715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 178704759979503265619156953 134028569984627449214367715)
            ·
              refine ⟨201042854976941173821551573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 134028569984627449214367715 201042854976941173821551573)
              ·
                refine ⟨4711941913522058761442615, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 201042854976941173821551573 4711941913522058761442615)
                ·
                  refine ⟨7067912870283088142163923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4711941913522058761442615 7067912870283088142163923)
                  ·
                    refine ⟨10601869305424632213245885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7067912870283088142163923 10601869305424632213245885)
                    ·
                      refine ⟨3975700989534237079967207, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10601869305424632213245885 3975700989534237079967207)
                      ·
                        rfl

theorem cell23_7742650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 1, 7, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 1, 7, 1, 1, 3].length) (baseStart_7742650 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7742650 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7742650 prefixEnd_7742650 := by exact prefixLift 7742650
  have htrace : WordTrace (prefixWord ++ tailWord_7742650) baseStart_7742650 baseEnd_7742650 := by
    simpa [prefixWord, tailWord_7742650, baseEnd_7742650] using wordTrace_append hprefix tailTrace_7742650
  have hstable : (prefixWord ++ tailWord_7742650).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7742650).length < 2 ^ (prefixWord ++ tailWord_7742650).sum := by decide
  have hdescent : baseEnd_7742650 < baseStart_7742650 := by decide
  rcases family_descends (prefixWord ++ tailWord_7742650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7742707 : List Nat := [1, 1, 1, 2, 2, 5, 1, 5, 1, 2, 2]
def baseStart_7742707 : Nat := 118140960795 + 7742707 * 2 ^ 59
def prefixEnd_7742707 : Nat := 4983230072969 + 3 ^ 40 * 7742707 * 2
def baseEnd_7742707 : Nat := 3975730257931543356954445

theorem tailTrace_7742707 : CollatzResearch.WordTrace tailWord_7742707 prefixEnd_7742707 3975730257931543356954445 := by
  unfold tailWord_7742707
  simp only [CollatzResearch.WordTrace]
  refine ⟨282399724360502362923122375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188266482907001575282081583 282399724360502362923122375)
  ·
    refine ⟨423599586540753544384683563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 282399724360502362923122375 423599586540753544384683563)
    ·
      refine ⟨635399379811130316577025345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 423599586540753544384683563 635399379811130316577025345)
      ·
        refine ⟨476549534858347737432769009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 635399379811130316577025345 476549534858347737432769009)
        ·
          refine ⟨357412151143760803074576757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 476549534858347737432769009 357412151143760803074576757)
          ·
            refine ⟨33507389169727575288241571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 357412151143760803074576757 33507389169727575288241571)
            ·
              refine ⟨50261083754591362932362357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33507389169727575288241571 50261083754591362932362357)
              ·
                refine ⟨4711976601992940274908971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 50261083754591362932362357 4711976601992940274908971)
                ·
                  refine ⟨7067964902989410412363457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4711976601992940274908971 7067964902989410412363457)
                  ·
                    refine ⟨5300973677242057809272593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7067964902989410412363457 5300973677242057809272593)
                    ·
                      refine ⟨3975730257931543356954445, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5300973677242057809272593 3975730257931543356954445)
                      ·
                        rfl

theorem cell23_7742707_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 5, 1, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 5, 1, 5, 1, 2, 2].length) (baseStart_7742707 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7742707 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7742707 prefixEnd_7742707 := by exact prefixLift 7742707
  have htrace : WordTrace (prefixWord ++ tailWord_7742707) baseStart_7742707 baseEnd_7742707 := by
    simpa [prefixWord, tailWord_7742707, baseEnd_7742707] using wordTrace_append hprefix tailTrace_7742707
  have hstable : (prefixWord ++ tailWord_7742707).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7742707).length < 2 ^ (prefixWord ++ tailWord_7742707).sum := by decide
  have hdescent : baseEnd_7742707 < baseStart_7742707 := by decide
  rcases family_descends (prefixWord ++ tailWord_7742707) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7742724 : List Nat := [2, 3, 2, 2, 2, 1, 2, 4, 1, 2, 2]
def baseStart_7742724 : Nat := 118140960795 + 7742724 * 2 ^ 59
def prefixEnd_7742724 : Nat := 4983230072969 + 3 ^ 40 * 7742724 * 2
def baseEnd_7742724 : Nat := 3975738987102669790441867

theorem tailTrace_7742724 : CollatzResearch.WordTrace tailWord_7742724 prefixEnd_7742724 3975738987102669790441867 := by
  unfold tailWord_7742724
  simp only [CollatzResearch.WordTrace]
  refine ⟨141200172200720387413245613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 188266896267627183217660817 141200172200720387413245613)
  ·
    refine ⟨52950064575270145279967105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 141200172200720387413245613 52950064575270145279967105)
    ·
      refine ⟨39712548431452608959975329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52950064575270145279967105 39712548431452608959975329)
      ·
        refine ⟨29784411323589456719981497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39712548431452608959975329 29784411323589456719981497)
        ·
          refine ⟨22338308492692092539986123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29784411323589456719981497 22338308492692092539986123)
          ·
            refine ⟨33507462739038138809979185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22338308492692092539986123 33507462739038138809979185)
            ·
              refine ⟨25130597054278604107484389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33507462739038138809979185 25130597054278604107484389)
              ·
                refine ⟨4711986947677238270153323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25130597054278604107484389 4711986947677238270153323)
                ·
                  refine ⟨7067980421515857405229985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4711986947677238270153323 7067980421515857405229985)
                  ·
                    refine ⟨5300985316136893053922489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7067980421515857405229985 5300985316136893053922489)
                    ·
                      refine ⟨3975738987102669790441867, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5300985316136893053922489 3975738987102669790441867)
                      ·
                        rfl

theorem cell23_7742724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 1, 2, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 1, 2, 4, 1, 2, 2].length) (baseStart_7742724 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7742724 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7742724 prefixEnd_7742724 := by exact prefixLift 7742724
  have htrace : WordTrace (prefixWord ++ tailWord_7742724) baseStart_7742724 baseEnd_7742724 := by
    simpa [prefixWord, tailWord_7742724, baseEnd_7742724] using wordTrace_append hprefix tailTrace_7742724
  have hstable : (prefixWord ++ tailWord_7742724).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7742724).length < 2 ^ (prefixWord ++ tailWord_7742724).sum := by decide
  have hdescent : baseEnd_7742724 < baseStart_7742724 := by decide
  rcases family_descends (prefixWord ++ tailWord_7742724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7742833 : List Nat := [1, 2, 2, 2, 1, 2, 4, 2, 2, 5]
def baseStart_7742833 : Nat := 118140960795 + 7742833 * 2 ^ 59
def prefixEnd_7742833 : Nat := 4983230072969 + 3 ^ 40 * 7742833 * 2
def baseEnd_7742833 : Nat := 1325264985498003287992955

theorem tailTrace_7742833 : CollatzResearch.WordTrace tailWord_7742833 prefixEnd_7742833 1325264985498003287992955 := by
  unfold tailWord_7742833
  simp only [CollatzResearch.WordTrace]
  refine ⟨282404319958045886442209153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188269546638697257628139435 282404319958045886442209153)
  ·
    refine ⟨211803239968534414831656865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 282404319958045886442209153 211803239968534414831656865)
    ·
      refine ⟨158852429976400811123742649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 211803239968534414831656865 158852429976400811123742649)
      ·
        refine ⟨119139322482300608342806987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 158852429976400811123742649 119139322482300608342806987)
        ·
          refine ⟨178708983723450912514210481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 119139322482300608342806987 178708983723450912514210481)
          ·
            refine ⟨134031737792588184385657861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 178708983723450912514210481 134031737792588184385657861)
            ·
              refine ⟨25130950836110284572310849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 134031737792588184385657861 25130950836110284572310849)
              ·
                refine ⟨18848213127082713429233137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25130950836110284572310849 18848213127082713429233137)
                ·
                  refine ⟨14136159845312035071924853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18848213127082713429233137 14136159845312035071924853)
                  ·
                    refine ⟨1325264985498003287992955, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14136159845312035071924853 1325264985498003287992955)
                    ·
                      rfl

theorem cell23_7742833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 4, 2, 2, 5].length) (baseStart_7742833 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7742833 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7742833 prefixEnd_7742833 := by exact prefixLift 7742833
  have htrace : WordTrace (prefixWord ++ tailWord_7742833) baseStart_7742833 baseEnd_7742833 := by
    simpa [prefixWord, tailWord_7742833, baseEnd_7742833] using wordTrace_append hprefix tailTrace_7742833
  have hstable : (prefixWord ++ tailWord_7742833).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7742833).length < 2 ^ (prefixWord ++ tailWord_7742833).sum := by decide
  have hdescent : baseEnd_7742833 < baseStart_7742833 := by decide
  rcases family_descends (prefixWord ++ tailWord_7742833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7742837 : List Nat := [1, 3, 4, 1, 3, 1, 1, 4, 5]
def baseStart_7742837 : Nat := 118140960795 + 7742837 * 2 ^ 59
def prefixEnd_7742837 : Nat := 4983230072969 + 3 ^ 40 * 7742837 * 2
def baseEnd_7742837 : Nat := 441755223379625316480983

theorem tailTrace_7742837 : CollatzResearch.WordTrace tailWord_7742837 prefixEnd_7742837 441755223379625316480983 := by
  unfold tailWord_7742837
  simp only [CollatzResearch.WordTrace]
  refine ⟨282404465850031395125354765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188269643900020930083569843 282404465850031395125354765)
  ·
    refine ⟨105901674693761773172008037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 282404465850031395125354765 105901674693761773172008037)
    ·
      refine ⟨19856564005080332469751507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 105901674693761773172008037 19856564005080332469751507)
      ·
        refine ⟨29784846007620498704627261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19856564005080332469751507 29784846007620498704627261)
        ·
          refine ⟨11169317252857687014235223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29784846007620498704627261 11169317252857687014235223)
          ·
            refine ⟨16753975879286530521352835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11169317252857687014235223 16753975879286530521352835)
            ·
              refine ⟨25130963818929795782029253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16753975879286530521352835 25130963818929795782029253)
              ·
                refine ⟨4712055716049336709130485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25130963818929795782029253 4712055716049336709130485)
                ·
                  refine ⟨441755223379625316480983, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4712055716049336709130485 441755223379625316480983)
                  ·
                    rfl

theorem cell23_7742837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 3, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 3, 1, 1, 4, 5].length) (baseStart_7742837 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7742837 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7742837 prefixEnd_7742837 := by exact prefixLift 7742837
  have htrace : WordTrace (prefixWord ++ tailWord_7742837) baseStart_7742837 baseEnd_7742837 := by
    simpa [prefixWord, tailWord_7742837, baseEnd_7742837] using wordTrace_append hprefix tailTrace_7742837
  have hstable : (prefixWord ++ tailWord_7742837).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7742837).length < 2 ^ (prefixWord ++ tailWord_7742837).sum := by decide
  have hdescent : baseEnd_7742837 < baseStart_7742837 := by decide
  rcases family_descends (prefixWord ++ tailWord_7742837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7742853 : List Nat := [1, 3, 1, 1, 3, 1, 2, 2, 4, 1, 4]
def baseStart_7742853 : Nat := 118140960795 + 7742853 * 2 ^ 59
def prefixEnd_7742853 : Nat := 4983230072969 + 3 ^ 40 * 7742853 * 2
def baseEnd_7742853 : Nat := 3975805226107099785728773

theorem tailTrace_7742853 : CollatzResearch.WordTrace tailWord_7742853 prefixEnd_7742853 3975805226107099785728773 := by
  unfold tailWord_7742853
  simp only [CollatzResearch.WordTrace]
  refine ⟨282405049417973429857937213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188270032945315619905291475 282405049417973429857937213)
  ·
    refine ⟨105901893531740036196726455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 282405049417973429857937213 105901893531740036196726455)
    ·
      refine ⟨158852840297610054295089683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105901893531740036196726455 158852840297610054295089683)
      ·
        refine ⟨238279260446415081442634525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 158852840297610054295089683 238279260446415081442634525)
        ·
          refine ⟨89354722667405655540987947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 238279260446415081442634525 89354722667405655540987947)
          ·
            refine ⟨134032084001108483311481921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89354722667405655540987947 134032084001108483311481921)
            ·
              refine ⟨100524063000831362483611441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 134032084001108483311481921 100524063000831362483611441)
              ·
                refine ⟨75393047250623521862708581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 100524063000831362483611441 75393047250623521862708581)
                ·
                  refine ⟨14136196359491910349257859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 75393047250623521862708581 14136196359491910349257859)
                  ·
                    refine ⟨21204294539237865523886789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14136196359491910349257859 21204294539237865523886789)
                    ·
                      refine ⟨3975805226107099785728773, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21204294539237865523886789 3975805226107099785728773)
                      ·
                        rfl

theorem cell23_7742853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 2, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 2, 2, 4, 1, 4].length) (baseStart_7742853 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7742853 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7742853 prefixEnd_7742853 := by exact prefixLift 7742853
  have htrace : WordTrace (prefixWord ++ tailWord_7742853) baseStart_7742853 baseEnd_7742853 := by
    simpa [prefixWord, tailWord_7742853, baseEnd_7742853] using wordTrace_append hprefix tailTrace_7742853
  have hstable : (prefixWord ++ tailWord_7742853).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7742853).length < 2 ^ (prefixWord ++ tailWord_7742853).sum := by decide
  have hdescent : baseEnd_7742853 < baseStart_7742853 := by decide
  rcases family_descends (prefixWord ++ tailWord_7742853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7742897 : List Nat := [1, 2, 2, 4, 1, 1, 1, 6, 1, 4]
def baseStart_7742897 : Nat := 118140960795 + 7742897 * 2 ^ 59
def prefixEnd_7742897 : Nat := 4983230072969 + 3 ^ 40 * 7742897 * 2
def baseEnd_7742897 : Nat := 1325275939751965871192857

theorem tailTrace_7742897 : CollatzResearch.WordTrace tailWord_7742897 prefixEnd_7742897 1325275939751965871192857 := by
  unfold tailWord_7742897
  simp only [CollatzResearch.WordTrace]
  refine ⟨282406654229814025372538945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188271102819876016915025963 282406654229814025372538945)
  ·
    refine ⟨211804990672360519029404209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 282406654229814025372538945 211804990672360519029404209)
    ·
      refine ⟨158853743004270389272053157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 211804990672360519029404209 158853743004270389272053157)
      ·
        refine ⟨29785076813300697988509967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 158853743004270389272053157 29785076813300697988509967)
        ·
          refine ⟨44677615219951046982764951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29785076813300697988509967 44677615219951046982764951)
          ·
            refine ⟨67016422829926570474147427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44677615219951046982764951 67016422829926570474147427)
            ·
              refine ⟨100524634244889855711221141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67016422829926570474147427 100524634244889855711221141)
              ·
                refine ⟨4712092230229211986463491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 100524634244889855711221141 4712092230229211986463491)
                ·
                  refine ⟨7068138345343817979695237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4712092230229211986463491 7068138345343817979695237)
                  ·
                    refine ⟨1325275939751965871192857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7068138345343817979695237 1325275939751965871192857)
                    ·
                      rfl

theorem cell23_7742897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 1, 6, 1, 4].length) (baseStart_7742897 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7742897 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7742897 prefixEnd_7742897 := by exact prefixLift 7742897
  have htrace : WordTrace (prefixWord ++ tailWord_7742897) baseStart_7742897 baseEnd_7742897 := by
    simpa [prefixWord, tailWord_7742897, baseEnd_7742897] using wordTrace_append hprefix tailTrace_7742897
  have hstable : (prefixWord ++ tailWord_7742897).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7742897).length < 2 ^ (prefixWord ++ tailWord_7742897).sum := by decide
  have hdescent : baseEnd_7742897 < baseStart_7742897 := by decide
  rcases family_descends (prefixWord ++ tailWord_7742897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7742923 : List Nat := [1, 1, 1, 1, 3, 3, 2, 3, 3, 5]
def baseStart_7742923 : Nat := 118140960795 + 7742923 * 2 ^ 59
def prefixEnd_7742923 : Nat := 4983230072969 + 3 ^ 40 * 7742923 * 2
def baseEnd_7742923 : Nat := 1325280389917638170617817

theorem tailTrace_7742923 : CollatzResearch.WordTrace tailWord_7742923 prefixEnd_7742923 1325280389917638170617817 := by
  unfold tailWord_7742923
  simp only [CollatzResearch.WordTrace]
  refine ⟨282407602527719831812985423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188271735018479887875323615 282407602527719831812985423)
  ·
    refine ⟨423611403791579747719478135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 282407602527719831812985423 423611403791579747719478135)
    ·
      refine ⟨635417105687369621579217203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 423611403791579747719478135 635417105687369621579217203)
      ·
        refine ⟨953125658531054432368825805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 635417105687369621579217203 953125658531054432368825805)
        ·
          refine ⟨357422121949145412138309677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 953125658531054432368825805 357422121949145412138309677)
          ·
            refine ⟨134033295730929529551866129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 357422121949145412138309677 134033295730929529551866129)
            ·
              refine ⟨100524971798197147163899597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 134033295730929529551866129 100524971798197147163899597)
              ·
                refine ⟨37696864424323930186462349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 100524971798197147163899597 37696864424323930186462349)
                ·
                  refine ⟨14136324159121473819923381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 37696864424323930186462349 14136324159121473819923381)
                  ·
                    refine ⟨1325280389917638170617817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14136324159121473819923381 1325280389917638170617817)
                    ·
                      rfl

theorem cell23_7742923_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 2, 3, 3, 5].length) (baseStart_7742923 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7742923 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7742923 prefixEnd_7742923 := by exact prefixLift 7742923
  have htrace : WordTrace (prefixWord ++ tailWord_7742923) baseStart_7742923 baseEnd_7742923 := by
    simpa [prefixWord, tailWord_7742923, baseEnd_7742923] using wordTrace_append hprefix tailTrace_7742923
  have hstable : (prefixWord ++ tailWord_7742923).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7742923).length < 2 ^ (prefixWord ++ tailWord_7742923).sum := by decide
  have hdescent : baseEnd_7742923 < baseStart_7742923 := by decide
  rcases family_descends (prefixWord ++ tailWord_7742923) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7742947 : List Nat := [1, 1, 1, 6, 2, 1, 1, 1, 4, 3, 2]
def baseStart_7742947 : Nat := 118140960795 + 7742947 * 2 ^ 59
def prefixEnd_7742947 : Nat := 4983230072969 + 3 ^ 40 * 7742947 * 2
def baseEnd_7742947 : Nat := 3975853493288622417953341

theorem tailTrace_7742947 : CollatzResearch.WordTrace tailWord_7742947 prefixEnd_7742947 3975853493288622417953341 := by
  unfold tailWord_7742947
  simp only [CollatzResearch.WordTrace]
  refine ⟨282408477879632883911859095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188272318586421922607906063 282408477879632883911859095)
  ·
    refine ⟨423612716819449325867788643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 282408477879632883911859095 423612716819449325867788643)
    ·
      refine ⟨635419075229173988801682965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 423612716819449325867788643 635419075229173988801682965)
      ·
        refine ⟨29785269151367530725078889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 635419075229173988801682965 29785269151367530725078889)
        ·
          refine ⟨22338951863525648043809167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29785269151367530725078889 22338951863525648043809167)
          ·
            refine ⟨33508427795288472065713751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22338951863525648043809167 33508427795288472065713751)
            ·
              refine ⟨50262641692932708098570627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33508427795288472065713751 50262641692932708098570627)
              ·
                refine ⟨75393962539399062147855941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50262641692932708098570627 75393962539399062147855941)
                ·
                  refine ⟨14136367976137324152722989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 75393962539399062147855941 14136367976137324152722989)
                  ·
                    refine ⟨5301137991051496557271121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14136367976137324152722989 5301137991051496557271121)
                    ·
                      refine ⟨3975853493288622417953341, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5301137991051496557271121 3975853493288622417953341)
                      ·
                        rfl

theorem cell23_7742947_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 1, 1, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 1, 1, 1, 4, 3, 2].length) (baseStart_7742947 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7742947 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7742947 prefixEnd_7742947 := by exact prefixLift 7742947
  have htrace : WordTrace (prefixWord ++ tailWord_7742947) baseStart_7742947 baseEnd_7742947 := by
    simpa [prefixWord, tailWord_7742947, baseEnd_7742947] using wordTrace_append hprefix tailTrace_7742947
  have hstable : (prefixWord ++ tailWord_7742947).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7742947).length < 2 ^ (prefixWord ++ tailWord_7742947).sum := by decide
  have hdescent : baseEnd_7742947 < baseStart_7742947 := by decide
  rcases family_descends (prefixWord ++ tailWord_7742947) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7742963 : List Nat := [1, 1, 1, 2, 2, 2, 2, 3, 3, 1, 5]
def baseStart_7742963 : Nat := 118140960795 + 7742963 * 2 ^ 59
def prefixEnd_7742963 : Nat := 4983230072969 + 3 ^ 40 * 7742963 * 2
def baseEnd_7742963 : Nat := 3975861708979094355353267

theorem tailTrace_7742963 : CollatzResearch.WordTrace tailWord_7742963 prefixEnd_7742963 3975861708979094355353267 := by
  unfold tailWord_7742963
  simp only [CollatzResearch.WordTrace]
  refine ⟨282409061447574918644441543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188272707631716612429627695 282409061447574918644441543)
  ·
    refine ⟨423613592171362377966662315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 282409061447574918644441543 423613592171362377966662315)
    ·
      refine ⟨635420388257043566949993473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 423613592171362377966662315 635420388257043566949993473)
      ·
        refine ⟨476565291192782675212495105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 635420388257043566949993473 476565291192782675212495105)
        ·
          refine ⟨357423968394587006409371329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 476565291192782675212495105 357423968394587006409371329)
          ·
            refine ⟨268067976295940254807028497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 357423968394587006409371329 268067976295940254807028497)
            ·
              refine ⟨201050982221955191105271373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 268067976295940254807028497 201050982221955191105271373)
              ·
                refine ⟨75394118333233196664476765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 201050982221955191105271373 75394118333233196664476765)
                ·
                  refine ⟨28272794374962448749178787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 75394118333233196664476765 28272794374962448749178787)
                  ·
                    refine ⟨42409191562443673123768181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 28272794374962448749178787 42409191562443673123768181)
                    ·
                      refine ⟨3975861708979094355353267, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 42409191562443673123768181 3975861708979094355353267)
                      ·
                        rfl

theorem cell23_7742963_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 2, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 2, 3, 3, 1, 5].length) (baseStart_7742963 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7742963 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7742963 prefixEnd_7742963 := by exact prefixLift 7742963
  have htrace : WordTrace (prefixWord ++ tailWord_7742963) baseStart_7742963 baseEnd_7742963 := by
    simpa [prefixWord, tailWord_7742963, baseEnd_7742963] using wordTrace_append hprefix tailTrace_7742963
  have hstable : (prefixWord ++ tailWord_7742963).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7742963).length < 2 ^ (prefixWord ++ tailWord_7742963).sum := by decide
  have hdescent : baseEnd_7742963 < baseStart_7742963 := by decide
  rcases family_descends (prefixWord ++ tailWord_7742963) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7742974 : List Nat := [4, 2, 2, 3, 1, 1, 1, 1, 3, 5]
def baseStart_7742974 : Nat := 118140960795 + 7742974 * 2 ^ 59
def prefixEnd_7742974 : Nat := 4983230072969 + 3 ^ 40 * 7742974 * 2
def baseEnd_7742974 : Nat := 1325289119088764604105239

theorem tailTrace_7742974 : CollatzResearch.WordTrace tailWord_7742974 prefixEnd_7742974 1325289119088764604105239 := by
  unfold tailWord_7742974
  simp only [CollatzResearch.WordTrace]
  refine ⟨35301182831316883440386497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 188272975100356711682061317 35301182831316883440386497)
  ·
    refine ⟨26475887123487662580289873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35301182831316883440386497 26475887123487662580289873)
    ·
      refine ⟨19856915342615746935217405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26475887123487662580289873 19856915342615746935217405)
      ·
        refine ⟨7446343253480905100706527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19856915342615746935217405 7446343253480905100706527)
        ·
          refine ⟨11169514880221357651059791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7446343253480905100706527 11169514880221357651059791)
          ·
            refine ⟨16754272320332036476589687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11169514880221357651059791 16754272320332036476589687)
            ·
              refine ⟨25131408480498054714884531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16754272320332036476589687 25131408480498054714884531)
              ·
                refine ⟨37697112720747082072326797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25131408480498054714884531 37697112720747082072326797)
                ·
                  refine ⟨14136417270280155777122549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 37697112720747082072326797 14136417270280155777122549)
                  ·
                    refine ⟨1325289119088764604105239, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14136417270280155777122549 1325289119088764604105239)
                    ·
                      rfl

theorem cell23_7742974_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 1, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 1, 1, 1, 1, 3, 5].length) (baseStart_7742974 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7742974 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7742974 prefixEnd_7742974 := by exact prefixLift 7742974
  have htrace : WordTrace (prefixWord ++ tailWord_7742974) baseStart_7742974 baseEnd_7742974 := by
    simpa [prefixWord, tailWord_7742974, baseEnd_7742974] using wordTrace_append hprefix tailTrace_7742974
  have hstable : (prefixWord ++ tailWord_7742974).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7742974).length < 2 ^ (prefixWord ++ tailWord_7742974).sum := by decide
  have hdescent : baseEnd_7742974 < baseStart_7742974 := by decide
  rcases family_descends (prefixWord ++ tailWord_7742974) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7742977 : List Nat := [1, 2, 4, 1, 4, 1, 1, 1, 3, 1, 4]
def baseStart_7742977 : Nat := 118140960795 + 7742977 * 2 ^ 59
def prefixEnd_7742977 : Nat := 4983230072969 + 3 ^ 40 * 7742977 * 2
def baseEnd_7742977 : Nat := 3975868897708257300578203

theorem tailTrace_7742977 : CollatzResearch.WordTrace tailWord_7742977 prefixEnd_7742977 3975868897708257300578203 := by
  unfold tailWord_7742977
  simp only [CollatzResearch.WordTrace]
  refine ⟨282409572069524199035451185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188273048046349466023634123 282409572069524199035451185)
  ·
    refine ⟨211807179052143149276588389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 282409572069524199035451185 211807179052143149276588389)
    ·
      refine ⟨39713846072276840489360323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 211807179052143149276588389 39713846072276840489360323)
      ·
        refine ⟨59570769108415260734040485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39713846072276840489360323 59570769108415260734040485)
        ·
          refine ⟨11169519207827861387632591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 59570769108415260734040485 11169519207827861387632591)
          ·
            refine ⟨16754278811741792081448887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11169519207827861387632591 16754278811741792081448887)
            ·
              refine ⟨25131418217612688122173331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16754278811741792081448887 25131418217612688122173331)
              ·
                refine ⟨37697127326419032183259997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25131418217612688122173331 37697127326419032183259997)
                ·
                  refine ⟨14136422747407137068722499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 37697127326419032183259997 14136422747407137068722499)
                  ·
                    refine ⟨21204634121110705603083749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14136422747407137068722499 21204634121110705603083749)
                    ·
                      refine ⟨3975868897708257300578203, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21204634121110705603083749 3975868897708257300578203)
                      ·
                        rfl

theorem cell23_7742977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 4, 1, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 4, 1, 1, 1, 3, 1, 4].length) (baseStart_7742977 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7742977 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7742977 prefixEnd_7742977 := by exact prefixLift 7742977
  have htrace : WordTrace (prefixWord ++ tailWord_7742977) baseStart_7742977 baseEnd_7742977 := by
    simpa [prefixWord, tailWord_7742977, baseEnd_7742977] using wordTrace_append hprefix tailTrace_7742977
  have hstable : (prefixWord ++ tailWord_7742977).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7742977).length < 2 ^ (prefixWord ++ tailWord_7742977).sum := by decide
  have hdescent : baseEnd_7742977 < baseStart_7742977 := by decide
  rcases family_descends (prefixWord ++ tailWord_7742977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7742997 : List Nat := [1, 3, 2, 1, 3, 4, 1, 1, 1, 1, 5]
def baseStart_7742997 : Nat := 118140960795 + 7742997 * 2 ^ 59
def prefixEnd_7742997 : Nat := 4983230072969 + 3 ^ 40 * 7742997 * 2
def baseEnd_7742997 : Nat := 3975879167321347222328111

theorem tailTrace_7742997 : CollatzResearch.WordTrace tailWord_7742997 prefixEnd_7742997 3975879167321347222328111 := by
  unfold tailWord_7742997
  simp only [CollatzResearch.WordTrace]
  refine ⟨282410301529451742451179245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188273534352967828300786163 282410301529451742451179245)
  ·
    refine ⟨105903863073544403419192217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 282410301529451742451179245 105903863073544403419192217)
    ·
      refine ⟨79427897305158302564394163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 105903863073544403419192217 79427897305158302564394163)
      ·
        refine ⟨119141845957737453846591245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79427897305158302564394163 119141845957737453846591245)
        ·
          refine ⟨44678192234151545192471717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 119141845957737453846591245 44678192234151545192471717)
          ·
            refine ⟨8377161043903414723588447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 44678192234151545192471717 8377161043903414723588447)
            ·
              refine ⟨12565741565855122085382671, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8377161043903414723588447 12565741565855122085382671)
              ·
                refine ⟨18848612348782683128074007, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12565741565855122085382671 18848612348782683128074007)
                ·
                  refine ⟨28272918523174024692111011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18848612348782683128074007 28272918523174024692111011)
                  ·
                    refine ⟨42409377784761037038166517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 28272918523174024692111011 42409377784761037038166517)
                    ·
                      refine ⟨3975879167321347222328111, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 42409377784761037038166517 3975879167321347222328111)
                      ·
                        rfl

theorem cell23_7742997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 4, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 4, 1, 1, 1, 1, 5].length) (baseStart_7742997 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7742997 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7742997 prefixEnd_7742997 := by exact prefixLift 7742997
  have htrace : WordTrace (prefixWord ++ tailWord_7742997) baseStart_7742997 baseEnd_7742997 := by
    simpa [prefixWord, tailWord_7742997, baseEnd_7742997] using wordTrace_append hprefix tailTrace_7742997
  have hstable : (prefixWord ++ tailWord_7742997).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7742997).length < 2 ^ (prefixWord ++ tailWord_7742997).sum := by decide
  have hdescent : baseEnd_7742997 < baseStart_7742997 := by decide
  rcases family_descends (prefixWord ++ tailWord_7742997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7743000 : List Nat := [2, 1, 2, 3, 5, 10]
def baseStart_7743000 : Nat := 118140960795 + 7743000 * 2 ^ 59
def prefixEnd_7743000 : Nat := 4983230072969 + 3 ^ 40 * 7743000 * 2
def baseEnd_7743000 : Nat := 16361649003141196339879

theorem tailTrace_7743000 : CollatzResearch.WordTrace tailWord_7743000 prefixEnd_7743000 16361649003141196339879 := by
  unfold tailWord_7743000
  simp only [CollatzResearch.WordTrace]
  refine ⟨141205205474220436981769227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 188273607298960582642358969 141205205474220436981769227)
  ·
    refine ⟨211807808211330655472653841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141205205474220436981769227 211807808211330655472653841)
    ·
      refine ⟨158855856158497991604490381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 211807808211330655472653841 158855856158497991604490381)
      ·
        refine ⟨59570946059436746851683893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 158855856158497991604490381 59570946059436746851683893)
        ·
          refine ⟨5584776193072195017345365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 59570946059436746851683893 5584776193072195017345365)
          ·
            refine ⟨16361649003141196339879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 5584776193072195017345365 16361649003141196339879)
            ·
              rfl

theorem cell23_7743000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 5, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 5, 10].length) (baseStart_7743000 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7743000 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7743000 prefixEnd_7743000 := by exact prefixLift 7743000
  have htrace : WordTrace (prefixWord ++ tailWord_7743000) baseStart_7743000 baseEnd_7743000 := by
    simpa [prefixWord, tailWord_7743000, baseEnd_7743000] using wordTrace_append hprefix tailTrace_7743000
  have hstable : (prefixWord ++ tailWord_7743000).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7743000).length < 2 ^ (prefixWord ++ tailWord_7743000).sum := by decide
  have hdescent : baseEnd_7743000 < baseStart_7743000 := by decide
  rcases family_descends (prefixWord ++ tailWord_7743000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7743027 : List Nat := [1, 1, 1, 2, 4, 4, 2, 1, 1, 3, 3]
def baseStart_7743027 : Nat := 118140960795 + 7743027 * 2 ^ 59
def prefixEnd_7743027 : Nat := 4983230072969 + 3 ^ 40 * 7743027 * 2
def baseEnd_7743027 : Nat := 3975894571740982104952973

theorem tailTrace_7743027 : CollatzResearch.WordTrace tailWord_7743027 prefixEnd_7743027 3975894571740982104952973 := by
  unfold tailWord_7743027
  simp only [CollatzResearch.WordTrace]
  refine ⟨282411395719343057574771335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188274263812895371716514223 282411395719343057574771335)
  ·
    refine ⟨423617093579014586362157003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 282411395719343057574771335 423617093579014586362157003)
    ·
      refine ⟨635425640368521879543235505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 423617093579014586362157003 635425640368521879543235505)
      ·
        refine ⟨476569230276391409657426629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 635425640368521879543235505 476569230276391409657426629)
        ·
          refine ⟨89356730676823389310767493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 476569230276391409657426629 89356730676823389310767493)
          ·
            refine ⟨16754387001904385495768905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 89356730676823389310767493 16754387001904385495768905)
            ·
              refine ⟨12565790251428289121826679, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16754387001904385495768905 12565790251428289121826679)
              ·
                refine ⟨18848685377142433682740019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12565790251428289121826679 18848685377142433682740019)
                ·
                  refine ⟨28273028065713650524110029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18848685377142433682740019 28273028065713650524110029)
                  ·
                    refine ⟨10602385524642618946541261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 28273028065713650524110029 10602385524642618946541261)
                    ·
                      refine ⟨3975894571740982104952973, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10602385524642618946541261 3975894571740982104952973)
                      ·
                        rfl

theorem cell23_7743027_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 4, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 4, 2, 1, 1, 3, 3].length) (baseStart_7743027 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7743027 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7743027 prefixEnd_7743027 := by exact prefixLift 7743027
  have htrace : WordTrace (prefixWord ++ tailWord_7743027) baseStart_7743027 baseEnd_7743027 := by
    simpa [prefixWord, tailWord_7743027, baseEnd_7743027] using wordTrace_append hprefix tailTrace_7743027
  have hstable : (prefixWord ++ tailWord_7743027).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7743027).length < 2 ^ (prefixWord ++ tailWord_7743027).sum := by decide
  have hdescent : baseEnd_7743027 < baseStart_7743027 := by decide
  rcases family_descends (prefixWord ++ tailWord_7743027) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7743060 : List Nat := [2, 4, 1, 1, 1, 2, 1, 1, 4, 6]
def baseStart_7743060 : Nat := 118140960795 + 7743060 * 2 ^ 59
def prefixEnd_7743060 : Nat := 4983230072969 + 3 ^ 40 * 7743060 * 2
def baseEnd_7743060 : Nat := 1325303838867526825280107

theorem tailTrace_7743060 : CollatzResearch.WordTrace tailWord_7743060 prefixEnd_7743060 1325303838867526825280107 := by
  unfold tailWord_7743060
  simp only [CollatzResearch.WordTrace]
  refine ⟨141206299664111752105361317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 188275066218815669473815089 141206299664111752105361317)
  ·
    refine ⟨26476181187020953519755247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 141206299664111752105361317 26476181187020953519755247)
    ·
      refine ⟨39714271780531430279632871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26476181187020953519755247 39714271780531430279632871)
      ·
        refine ⟨59571407670797145419449307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39714271780531430279632871 59571407670797145419449307)
        ·
          refine ⟨89357111506195718129173961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59571407670797145419449307 89357111506195718129173961)
          ·
            refine ⟨67017833629646788596880471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 89357111506195718129173961 67017833629646788596880471)
            ·
              refine ⟨100526750444470182895320707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67017833629646788596880471 100526750444470182895320707)
              ·
                refine ⟨150790125666705274342981061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 100526750444470182895320707 150790125666705274342981061)
                ·
                  refine ⟨28273148562507238939308949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 150790125666705274342981061 28273148562507238939308949)
                  ·
                    refine ⟨1325303838867526825280107, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28273148562507238939308949 1325303838867526825280107)
                    ·
                      rfl

theorem cell23_7743060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 1, 1, 4, 6].length) (baseStart_7743060 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7743060 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7743060 prefixEnd_7743060 := by exact prefixLift 7743060
  have htrace : WordTrace (prefixWord ++ tailWord_7743060) baseStart_7743060 baseEnd_7743060 := by
    simpa [prefixWord, tailWord_7743060, baseEnd_7743060] using wordTrace_append hprefix tailTrace_7743060
  have hstable : (prefixWord ++ tailWord_7743060).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7743060).length < 2 ^ (prefixWord ++ tailWord_7743060).sum := by decide
  have hdescent : baseEnd_7743060 < baseStart_7743060 := by decide
  rcases family_descends (prefixWord ++ tailWord_7743060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7743247 : List Nat := [1, 1, 2, 1, 1, 1, 4, 4, 3, 1, 4]
def baseStart_7743247 : Nat := 118140960795 + 7743247 * 2 ^ 59
def prefixEnd_7743247 : Nat := 4983230072969 + 3 ^ 40 * 7743247 * 2
def baseEnd_7743247 : Nat := 3976007537484971244201961

theorem tailTrace_7743247 : CollatzResearch.WordTrace tailWord_7743247 prefixEnd_7743247 3976007537484971244201961 := by
  unfold tailWord_7743247
  simp only [CollatzResearch.WordTrace]
  refine ⟨282419419778546035147779995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188279613185697356765186663 282419419778546035147779995)
  ·
    refine ⟨423629129667819052721669993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 282419419778546035147779995 423629129667819052721669993)
    ·
      refine ⟨317721847250864289541252495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 423629129667819052721669993 317721847250864289541252495)
      ·
        refine ⟨476582770876296434311878743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 317721847250864289541252495 476582770876296434311878743)
        ·
          refine ⟨714874156314444651467818115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 476582770876296434311878743 714874156314444651467818115)
          ·
            refine ⟨1072311234471666977201727173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 714874156314444651467818115 1072311234471666977201727173)
            ·
              refine ⟨201058356463437558225323845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1072311234471666977201727173 201058356463437558225323845)
              ·
                refine ⟨37698441836894542167248221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 201058356463437558225323845 37698441836894542167248221)
                ·
                  refine ⟨14136915688835453312718083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 37698441836894542167248221 14136915688835453312718083)
                  ·
                    refine ⟨21205373533253179969077125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14136915688835453312718083 21205373533253179969077125)
                    ·
                      refine ⟨3976007537484971244201961, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21205373533253179969077125 3976007537484971244201961)
                      ·
                        rfl

theorem cell23_7743247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 4, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 4, 4, 3, 1, 4].length) (baseStart_7743247 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7743247 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7743247 prefixEnd_7743247 := by exact prefixLift 7743247
  have htrace : WordTrace (prefixWord ++ tailWord_7743247) baseStart_7743247 baseEnd_7743247 := by
    simpa [prefixWord, tailWord_7743247, baseEnd_7743247] using wordTrace_append hprefix tailTrace_7743247
  have hstable : (prefixWord ++ tailWord_7743247).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7743247).length < 2 ^ (prefixWord ++ tailWord_7743247).sum := by decide
  have hdescent : baseEnd_7743247 < baseStart_7743247 := by decide
  rcases family_descends (prefixWord ++ tailWord_7743247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7743264 : List Nat := [2, 1, 1, 5, 1, 1, 1, 1, 2, 6, 2]
def baseStart_7743264 : Nat := 118140960795 + 7743264 * 2 ^ 59
def prefixEnd_7743264 : Nat := 4983230072969 + 3 ^ 40 * 7743264 * 2
def baseEnd_7743264 : Nat := 3976016266656097677689383

theorem tailTrace_7743264 : CollatzResearch.WordTrace tailWord_7743264 prefixEnd_7743264 3976016266656097677689383 := by
  unfold tailWord_7743264
  simp only [CollatzResearch.WordTrace]
  refine ⟨141210019909742223525574423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 188280026546322964700765897 141210019909742223525574423)
  ·
    refine ⟨211815029864613335288361635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141210019909742223525574423 211815029864613335288361635)
    ·
      refine ⟨317722544796920002932542453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 211815029864613335288361635 317722544796920002932542453)
      ·
        refine ⟨29786488574711250274925855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 317722544796920002932542453 29786488574711250274925855)
        ·
          refine ⟨44679732862066875412388783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29786488574711250274925855 44679732862066875412388783)
          ·
            refine ⟨67019599293100313118583175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44679732862066875412388783 67019599293100313118583175)
            ·
              refine ⟨100529398939650469677874763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67019599293100313118583175 100529398939650469677874763)
              ·
                refine ⟨150794098409475704516812145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 100529398939650469677874763 150794098409475704516812145)
                ·
                  refine ⟨113095573807106778387609109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 150794098409475704516812145 113095573807106778387609109)
                  ·
                    refine ⟨5301355022208130236919177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 113095573807106778387609109 5301355022208130236919177)
                    ·
                      refine ⟨3976016266656097677689383, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5301355022208130236919177 3976016266656097677689383)
                      ·
                        rfl

theorem cell23_7743264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 1, 1, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 1, 1, 2, 6, 2].length) (baseStart_7743264 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7743264 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7743264 prefixEnd_7743264 := by exact prefixLift 7743264
  have htrace : WordTrace (prefixWord ++ tailWord_7743264) baseStart_7743264 baseEnd_7743264 := by
    simpa [prefixWord, tailWord_7743264, baseEnd_7743264] using wordTrace_append hprefix tailTrace_7743264
  have hstable : (prefixWord ++ tailWord_7743264).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7743264).length < 2 ^ (prefixWord ++ tailWord_7743264).sum := by decide
  have hdescent : baseEnd_7743264 < baseStart_7743264 := by decide
  rcases family_descends (prefixWord ++ tailWord_7743264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7743294 : List Nat := [4, 2, 1, 2, 2, 1, 1, 2, 1, 1, 6]
def baseStart_7743294 : Nat := 118140960795 + 7743294 * 2 ^ 59
def prefixEnd_7743294 : Nat := 4983230072969 + 3 ^ 40 * 7743294 * 2
def baseEnd_7743294 : Nat := 3976031671075732560314245

theorem tailTrace_7743294 : CollatzResearch.WordTrace tailWord_7743294 prefixEnd_7743294 3976031671075732560314245 := by
  unfold tailWord_7743294
  simp only [CollatzResearch.WordTrace]
  refine ⟨35302641751171970271842617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 188280756006250508116493957 35302641751171970271842617)
  ·
    refine ⟨26476981313378977703881963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35302641751171970271842617 26476981313378977703881963)
    ·
      refine ⟨39715471970068466555822945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26476981313378977703881963 39715471970068466555822945)
      ·
        refine ⟨29786603977551349916867209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39715471970068466555822945 29786603977551349916867209)
        ·
          refine ⟨22339952983163512437650407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29786603977551349916867209 22339952983163512437650407)
          ·
            refine ⟨33509929474745268656475611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22339952983163512437650407 33509929474745268656475611)
            ·
              refine ⟨50264894212117902984713417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33509929474745268656475611 50264894212117902984713417)
              ·
                refine ⟨37698670659088427238535063, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50264894212117902984713417 37698670659088427238535063)
                ·
                  refine ⟨56548005988632640857802595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37698670659088427238535063 56548005988632640857802595)
                  ·
                    refine ⟨84822008982948961286703893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 56548005988632640857802595 84822008982948961286703893)
                    ·
                      refine ⟨3976031671075732560314245, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 84822008982948961286703893 3976031671075732560314245)
                      ·
                        rfl

theorem cell23_7743294_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 1, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 1, 1, 2, 1, 1, 6].length) (baseStart_7743294 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7743294 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7743294 prefixEnd_7743294 := by exact prefixLift 7743294
  have htrace : WordTrace (prefixWord ++ tailWord_7743294) baseStart_7743294 baseEnd_7743294 := by
    simpa [prefixWord, tailWord_7743294, baseEnd_7743294] using wordTrace_append hprefix tailTrace_7743294
  have hstable : (prefixWord ++ tailWord_7743294).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7743294).length < 2 ^ (prefixWord ++ tailWord_7743294).sum := by decide
  have hdescent : baseEnd_7743294 < baseStart_7743294 := by decide
  rcases family_descends (prefixWord ++ tailWord_7743294) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7743331 : List Nat := [1, 1, 1, 5, 4, 1, 1, 2, 1, 3, 3]
def baseStart_7743331 : Nat := 118140960795 + 7743331 * 2 ^ 59
def prefixEnd_7743331 : Nat := 4983230072969 + 3 ^ 40 * 7743331 * 2
def baseEnd_7743331 : Nat := 3976050669859948915551575

theorem tailTrace_7743331 : CollatzResearch.WordTrace tailWord_7743331 prefixEnd_7743331 3976050669859948915551575 := by
  unfold tailWord_7743331
  simp only [CollatzResearch.WordTrace]
  refine ⟨282422483510241717493837847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188281655673494478329225231 282422483510241717493837847)
  ·
    refine ⟨423633725265362576240756771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 282422483510241717493837847 423633725265362576240756771)
    ·
      refine ⟨635450587898043864361135157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 423633725265362576240756771 635450587898043864361135157)
      ·
        refine ⟨59573492615441612283856421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 635450587898043864361135157 59573492615441612283856421)
        ·
          refine ⟨11170029865395302303223079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 59573492615441612283856421 11170029865395302303223079)
          ·
            refine ⟨16755044798092953454834619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11170029865395302303223079 16755044798092953454834619)
            ·
              refine ⟨25132567197139430182251929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16755044798092953454834619 25132567197139430182251929)
              ·
                refine ⟨18849425397854572636688947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25132567197139430182251929 18849425397854572636688947)
                ·
                  refine ⟨28274138096781858955033421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18849425397854572636688947 28274138096781858955033421)
                  ·
                    refine ⟨10602801786293197108137533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 28274138096781858955033421 10602801786293197108137533)
                    ·
                      refine ⟨3976050669859948915551575, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10602801786293197108137533 3976050669859948915551575)
                      ·
                        rfl

theorem cell23_7743331_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 4, 1, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 4, 1, 1, 2, 1, 3, 3].length) (baseStart_7743331 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7743331 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7743331 prefixEnd_7743331 := by exact prefixLift 7743331
  have htrace : WordTrace (prefixWord ++ tailWord_7743331) baseStart_7743331 baseEnd_7743331 := by
    simpa [prefixWord, tailWord_7743331, baseEnd_7743331] using wordTrace_append hprefix tailTrace_7743331
  have hstable : (prefixWord ++ tailWord_7743331).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7743331).length < 2 ^ (prefixWord ++ tailWord_7743331).sum := by decide
  have hdescent : baseEnd_7743331 < baseStart_7743331 := by decide
  rcases family_descends (prefixWord ++ tailWord_7743331) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7743337 : List Nat := [1, 2, 1, 1, 1, 3, 1, 2, 4, 3, 4]
def baseStart_7743337 : Nat := 118140960795 + 7743337 * 2 ^ 59
def prefixEnd_7743337 : Nat := 4983230072969 + 3 ^ 40 * 7743337 * 2
def baseEnd_7743337 : Nat := 3976053750743875892076547

theorem tailTrace_7743337 : CollatzResearch.WordTrace tailWord_7743337 prefixEnd_7743337 3976053750743875892076547 := by
  unfold tailWord_7743337
  simp only [CollatzResearch.WordTrace]
  refine ⟨282422702348219980518556265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188281801565479987012370843 282422702348219980518556265)
  ·
    refine ⟨211817026761164985388917199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 282422702348219980518556265 211817026761164985388917199)
    ·
      refine ⟨317725540141747478083375799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 211817026761164985388917199 317725540141747478083375799)
      ·
        refine ⟨476588310212621217125063699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 317725540141747478083375799 476588310212621217125063699)
        ·
          refine ⟨714882465318931825687595549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 476588310212621217125063699 714882465318931825687595549)
          ·
            refine ⟨268080924494599434632848331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 714882465318931825687595549 268080924494599434632848331)
            ·
              refine ⟨402121386741899151949272497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 268080924494599434632848331 402121386741899151949272497)
              ·
                refine ⟨301591040056424363961954373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 402121386741899151949272497 301591040056424363961954373)
                ·
                  refine ⟨56548320010579568242866445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 301591040056424363961954373 56548320010579568242866445)
                  ·
                    refine ⟨21205620003967338091074917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 56548320010579568242866445 21205620003967338091074917)
                    ·
                      refine ⟨3976053750743875892076547, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21205620003967338091074917 3976053750743875892076547)
                      ·
                        rfl

theorem cell23_7743337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 1, 2, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 1, 2, 4, 3, 4].length) (baseStart_7743337 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7743337 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7743337 prefixEnd_7743337 := by exact prefixLift 7743337
  have htrace : WordTrace (prefixWord ++ tailWord_7743337) baseStart_7743337 baseEnd_7743337 := by
    simpa [prefixWord, tailWord_7743337, baseEnd_7743337] using wordTrace_append hprefix tailTrace_7743337
  have hstable : (prefixWord ++ tailWord_7743337).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7743337).length < 2 ^ (prefixWord ++ tailWord_7743337).sum := by decide
  have hdescent : baseEnd_7743337 < baseStart_7743337 := by decide
  rcases family_descends (prefixWord ++ tailWord_7743337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7743347 : List Nat := [1, 1, 1, 2, 2, 1, 3, 4, 2, 6]
def baseStart_7743347 : Nat := 118140960795 + 7743347 * 2 ^ 59
def prefixEnd_7743347 : Nat := 4983230072969 + 3 ^ 40 * 7743347 * 2
def baseEnd_7743347 : Nat := 1325352961850140284317167

theorem tailTrace_7743347 : CollatzResearch.WordTrace tailWord_7743347 prefixEnd_7743347 1325352961850140284317167 := by
  unfold tailWord_7743347
  simp only [CollatzResearch.WordTrace]
  refine ⟨282423067078183752226420295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188282044718789168150946863 282423067078183752226420295)
  ·
    refine ⟨423634600617275628339630443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 282423067078183752226420295 423634600617275628339630443)
    ·
      refine ⟨635451900925913442509445665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 423634600617275628339630443 635451900925913442509445665)
      ·
        refine ⟨476588925694435081882084249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 635451900925913442509445665 476588925694435081882084249)
        ·
          refine ⟨357441694270826311411563187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 476588925694435081882084249 357441694270826311411563187)
          ·
            refine ⟨536162541406239467117344781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 357441694270826311411563187 536162541406239467117344781)
            ·
              refine ⟨201060953027339800169004293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 536162541406239467117344781 201060953027339800169004293)
              ·
                refine ⟨37698928692626212531688305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 201060953027339800169004293 37698928692626212531688305)
                ·
                  refine ⟨28274196519469659398766229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37698928692626212531688305 28274196519469659398766229)
                  ·
                    refine ⟨1325352961850140284317167, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28274196519469659398766229 1325352961850140284317167)
                    ·
                      rfl

theorem cell23_7743347_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 3, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 3, 4, 2, 6].length) (baseStart_7743347 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7743347 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7743347 prefixEnd_7743347 := by exact prefixLift 7743347
  have htrace : WordTrace (prefixWord ++ tailWord_7743347) baseStart_7743347 baseEnd_7743347 := by
    simpa [prefixWord, tailWord_7743347, baseEnd_7743347] using wordTrace_append hprefix tailTrace_7743347
  have hstable : (prefixWord ++ tailWord_7743347).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7743347).length < 2 ^ (prefixWord ++ tailWord_7743347).sum := by decide
  have hdescent : baseEnd_7743347 < baseStart_7743347 := by decide
  rcases family_descends (prefixWord ++ tailWord_7743347) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7743371 : List Nat := [1, 1, 1, 1, 4, 2, 1, 2, 6, 2, 2]
def baseStart_7743371 : Nat := 118140960795 + 7743371 * 2 ^ 59
def prefixEnd_7743371 : Nat := 4983230072969 + 3 ^ 40 * 7743371 * 2
def baseEnd_7743371 : Nat := 3976071209086128759051391

theorem tailTrace_7743371 : CollatzResearch.WordTrace tailWord_7743371 prefixEnd_7743371 3976071209086128759051391 := by
  unfold tailWord_7743371
  simp only [CollatzResearch.WordTrace]
  refine ⟨282423942430096804325293967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188282628286731202883529311 282423942430096804325293967)
  ·
    refine ⟨423635913645145206487940951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 282423942430096804325293967 423635913645145206487940951)
    ·
      refine ⟨635453870467717809731911427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 423635913645145206487940951 635453870467717809731911427)
      ·
        refine ⟨953180805701576714597867141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 635453870467717809731911427 953180805701576714597867141)
        ·
          refine ⟨178721401069045633987100089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 953180805701576714597867141 178721401069045633987100089)
          ·
            refine ⟨134041050801784225490325067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 178721401069045633987100089 134041050801784225490325067)
            ·
              refine ⟨201061576202676338235487601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 134041050801784225490325067 201061576202676338235487601)
              ·
                refine ⟨150796182152007253676615701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 201061576202676338235487601 150796182152007253676615701)
                ·
                  refine ⟨7068571038375340016091361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 150796182152007253676615701 7068571038375340016091361)
                  ·
                    refine ⟨5301428278781505012068521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7068571038375340016091361 5301428278781505012068521)
                    ·
                      refine ⟨3976071209086128759051391, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5301428278781505012068521 3976071209086128759051391)
                      ·
                        rfl

theorem cell23_7743371_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 1, 2, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 1, 2, 6, 2, 2].length) (baseStart_7743371 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7743371 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7743371 prefixEnd_7743371 := by exact prefixLift 7743371
  have htrace : WordTrace (prefixWord ++ tailWord_7743371) baseStart_7743371 baseEnd_7743371 := by
    simpa [prefixWord, tailWord_7743371, baseEnd_7743371] using wordTrace_append hprefix tailTrace_7743371
  have hstable : (prefixWord ++ tailWord_7743371).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7743371).length < 2 ^ (prefixWord ++ tailWord_7743371).sum := by decide
  have hdescent : baseEnd_7743371 < baseStart_7743371 := by decide
  rcases family_descends (prefixWord ++ tailWord_7743371) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7743377 : List Nat := [1, 2, 2, 1, 1, 1, 5, 1, 9]
def baseStart_7743377 : Nat := 118140960795 + 7743377 * 2 ^ 59
def prefixEnd_7743377 : Nat := 4983230072969 + 3 ^ 40 * 7743377 * 2
def baseEnd_7743377 : Nat := 441786032218895081730707

theorem tailTrace_7743377 : CollatzResearch.WordTrace tailWord_7743377 prefixEnd_7743377 441786032218895081730707 := by
  unfold tailWord_7743377
  simp only [CollatzResearch.WordTrace]
  refine ⟨282424161268075067350012385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188282774178716711566674923 282424161268075067350012385)
  ·
    refine ⟨211818120951056300512509289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 282424161268075067350012385 211818120951056300512509289)
    ·
      refine ⟨158863590713292225384381967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 211818120951056300512509289 158863590713292225384381967)
      ·
        refine ⟨238295386069938338076572951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 158863590713292225384381967 238295386069938338076572951)
        ·
          refine ⟨357443079104907507114859427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 238295386069938338076572951 357443079104907507114859427)
          ·
            refine ⟨536164618657361260672289141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 357443079104907507114859427 536164618657361260672289141)
            ·
              refine ⟨50265432999127618188027107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 536164618657361260672289141 50265432999127618188027107)
              ·
                refine ⟨75398149498691427282040661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50265432999127618188027107 75398149498691427282040661)
                ·
                  refine ⟨441786032218895081730707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 75398149498691427282040661 441786032218895081730707)
                  ·
                    rfl

theorem cell23_7743377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 5, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 5, 1, 9].length) (baseStart_7743377 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7743377 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7743377 prefixEnd_7743377 := by exact prefixLift 7743377
  have htrace : WordTrace (prefixWord ++ tailWord_7743377) baseStart_7743377 baseEnd_7743377 := by
    simpa [prefixWord, tailWord_7743377, baseEnd_7743377] using wordTrace_append hprefix tailTrace_7743377
  have hstable : (prefixWord ++ tailWord_7743377).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7743377).length < 2 ^ (prefixWord ++ tailWord_7743377).sum := by decide
  have hdescent : baseEnd_7743377 < baseStart_7743377 := by decide
  rcases family_descends (prefixWord ++ tailWord_7743377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7743388 : List Nat := [2, 2, 3, 3, 1, 1, 2, 2, 1, 4, 2]
def baseStart_7743388 : Nat := 118140960795 + 7743388 * 2 ^ 59
def prefixEnd_7743388 : Nat := 4983230072969 + 3 ^ 40 * 7743388 * 2
def baseEnd_7743388 : Nat := 3976079938257255192538813

theorem tailTrace_7743388 : CollatzResearch.WordTrace tailWord_7743388 prefixEnd_7743388 3976079938257255192538813 := by
  unfold tailWord_7743388
  simp only [CollatzResearch.WordTrace]
  refine ⟨141212281235517608114331409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 188283041647356810819108545 141212281235517608114331409)
  ·
    refine ⟨105909210926638206085748557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 141212281235517608114331409 105909210926638206085748557)
    ·
      refine ⟨39715954097489327282155709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 105909210926638206085748557 39715954097489327282155709)
      ·
        refine ⟨14893482786558497730808391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39715954097489327282155709 14893482786558497730808391)
        ·
          refine ⟨22340224179837746596212587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14893482786558497730808391 22340224179837746596212587)
          ·
            refine ⟨33510336269756619894318881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22340224179837746596212587 33510336269756619894318881)
            ·
              refine ⟨25132752202317464920739161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33510336269756619894318881 25132752202317464920739161)
              ·
                refine ⟨18849564151738098690554371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25132752202317464920739161 18849564151738098690554371)
                ·
                  refine ⟨28274346227607148035831557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18849564151738098690554371 28274346227607148035831557)
                  ·
                    refine ⟨5301439917676340256718417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28274346227607148035831557 5301439917676340256718417)
                    ·
                      refine ⟨3976079938257255192538813, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5301439917676340256718417 3976079938257255192538813)
                      ·
                        rfl

theorem cell23_7743388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 1, 2, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 1, 2, 2, 1, 4, 2].length) (baseStart_7743388 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7743388 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7743388 prefixEnd_7743388 := by exact prefixLift 7743388
  have htrace : WordTrace (prefixWord ++ tailWord_7743388) baseStart_7743388 baseEnd_7743388 := by
    simpa [prefixWord, tailWord_7743388, baseEnd_7743388] using wordTrace_append hprefix tailTrace_7743388
  have hstable : (prefixWord ++ tailWord_7743388).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7743388).length < 2 ^ (prefixWord ++ tailWord_7743388).sum := by decide
  have hdescent : baseEnd_7743388 < baseStart_7743388 := by decide
  rcases family_descends (prefixWord ++ tailWord_7743388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7743421 : List Nat := [1, 4, 1, 2, 3, 1, 2, 1, 2, 3, 3]
def baseStart_7743421 : Nat := 118140960795 + 7743421 * 2 ^ 59
def prefixEnd_7743421 : Nat := 4983230072969 + 3 ^ 40 * 7743421 * 2
def baseEnd_7743421 : Nat := 3976096883118853563426161

theorem tailTrace_7743421 : CollatzResearch.WordTrace tailWord_7743421 prefixEnd_7743421 3976096883118853563426161 := by
  unfold tailWord_7743421
  simp only [CollatzResearch.WordTrace]
  refine ⟨282425766079915662864614117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188283844053277108576409411 282425766079915662864614117)
  ·
    refine ⟨52954831139984186787115147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 282425766079915662864614117 52954831139984186787115147)
    ·
      refine ⟨79432246709976280180672721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52954831139984186787115147 79432246709976280180672721)
      ·
        refine ⟨59574185032482210135504541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79432246709976280180672721 59574185032482210135504541)
        ·
          refine ⟨22340319387180828800814203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 59574185032482210135504541 22340319387180828800814203)
          ·
            refine ⟨33510479080771243201221305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22340319387180828800814203 33510479080771243201221305)
            ·
              refine ⟨25132859310578432400915979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33510479080771243201221305 25132859310578432400915979)
              ·
                refine ⟨37699288965867648601373969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25132859310578432400915979 37699288965867648601373969)
                ·
                  refine ⟨28274466724400736451030477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37699288965867648601373969 28274466724400736451030477)
                  ·
                    refine ⟨10602925021650276169136429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 28274466724400736451030477 10602925021650276169136429)
                    ·
                      refine ⟨3976096883118853563426161, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10602925021650276169136429 3976096883118853563426161)
                      ·
                        rfl

theorem cell23_7743421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 1, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 1, 2, 1, 2, 3, 3].length) (baseStart_7743421 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7743421 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7743421 prefixEnd_7743421 := by exact prefixLift 7743421
  have htrace : WordTrace (prefixWord ++ tailWord_7743421) baseStart_7743421 baseEnd_7743421 := by
    simpa [prefixWord, tailWord_7743421, baseEnd_7743421] using wordTrace_append hprefix tailTrace_7743421
  have hstable : (prefixWord ++ tailWord_7743421).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7743421).length < 2 ^ (prefixWord ++ tailWord_7743421).sum := by decide
  have hdescent : baseEnd_7743421 < baseStart_7743421 := by decide
  rcases family_descends (prefixWord ++ tailWord_7743421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7743422 : List Nat := [4, 2, 1, 1, 1, 4, 3, 1, 2, 2, 2]
def baseStart_7743422 : Nat := 118140960795 + 7743422 * 2 ^ 59
def prefixEnd_7743422 : Nat := 4983230072969 + 3 ^ 40 * 7743422 * 2
def baseEnd_7743422 : Nat := 3976097396599508059513657

theorem tailTrace_7743422 : CollatzResearch.WordTrace tailWord_7743422 prefixEnd_7743422 3976097396599508059513657 := by
  unfold tailWord_7743422
  simp only [CollatzResearch.WordTrace]
  refine ⟨35303225319114005004425065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 188283868368608026690267013 35303225319114005004425065)
  ·
    refine ⟨26477418989335503753318799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35303225319114005004425065 26477418989335503753318799)
    ·
      refine ⟨39716128484003255629978199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26477418989335503753318799 39716128484003255629978199)
      ·
        refine ⟨59574192726004883444967299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39716128484003255629978199 59574192726004883444967299)
        ·
          refine ⟨89361289089007325167450949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59574192726004883444967299 89361289089007325167450949)
          ·
            refine ⟨16755241704188873468897053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 89361289089007325167450949 16755241704188873468897053)
            ·
              refine ⟨6283215639070827550836395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16755241704188873468897053 6283215639070827550836395)
              ·
                refine ⟨9424823458606241326254593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6283215639070827550836395 9424823458606241326254593)
                ·
                  refine ⟨7068617593954680994690945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9424823458606241326254593 7068617593954680994690945)
                  ·
                    refine ⟨5301463195466010746018209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7068617593954680994690945 5301463195466010746018209)
                    ·
                      refine ⟨3976097396599508059513657, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5301463195466010746018209 3976097396599508059513657)
                      ·
                        rfl

theorem cell23_7743422_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 4, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 4, 3, 1, 2, 2, 2].length) (baseStart_7743422 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7743422 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7743422 prefixEnd_7743422 := by exact prefixLift 7743422
  have htrace : WordTrace (prefixWord ++ tailWord_7743422) baseStart_7743422 baseEnd_7743422 := by
    simpa [prefixWord, tailWord_7743422, baseEnd_7743422] using wordTrace_append hprefix tailTrace_7743422
  have hstable : (prefixWord ++ tailWord_7743422).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7743422).length < 2 ^ (prefixWord ++ tailWord_7743422).sum := by decide
  have hdescent : baseEnd_7743422 < baseStart_7743422 := by decide
  rcases family_descends (prefixWord ++ tailWord_7743422) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7743545 : List Nat := [1, 2, 1, 5, 3, 1, 1, 2, 3, 1, 3]
def baseStart_7743545 : Nat := 118140960795 + 7743545 * 2 ^ 59
def prefixEnd_7743545 : Nat := 4983230072969 + 3 ^ 40 * 7743545 * 2
def baseEnd_7743545 : Nat := 3976160554720011078275591

theorem tailTrace_7743545 : CollatzResearch.WordTrace tailWord_7743545 prefixEnd_7743545 3976160554720011078275591 := by
  unfold tailWord_7743545
  simp only [CollatzResearch.WordTrace]
  refine ⟨282430288731466432042128089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188286859154310954694752059 282430288731466432042128089)
  ·
    refine ⟨211822716548599824031596067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 282430288731466432042128089 211822716548599824031596067)
    ·
      refine ⟨317734074822899736047394101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 211822716548599824031596067 317734074822899736047394101)
      ·
        refine ⟨29787569514646850254443197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 317734074822899736047394101 29787569514646850254443197)
        ·
          refine ⟨11170338567992568845416199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29787569514646850254443197 11170338567992568845416199)
          ·
            refine ⟨16755507851988853268124299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11170338567992568845416199 16755507851988853268124299)
            ·
              refine ⟨25133261777983279902186449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16755507851988853268124299 25133261777983279902186449)
              ·
                refine ⟨18849946333487459926639837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25133261777983279902186449 18849946333487459926639837)
                ·
                  refine ⟨7068729875057797472489939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18849946333487459926639837 7068729875057797472489939)
                  ·
                    refine ⟨10603094812586696208734909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7068729875057797472489939 10603094812586696208734909)
                    ·
                      refine ⟨3976160554720011078275591, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10603094812586696208734909 3976160554720011078275591)
                      ·
                        rfl

theorem cell23_7743545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 3, 1, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 3, 1, 1, 2, 3, 1, 3].length) (baseStart_7743545 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7743545 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7743545 prefixEnd_7743545 := by exact prefixLift 7743545
  have htrace : WordTrace (prefixWord ++ tailWord_7743545) baseStart_7743545 baseEnd_7743545 := by
    simpa [prefixWord, tailWord_7743545, baseEnd_7743545] using wordTrace_append hprefix tailTrace_7743545
  have hstable : (prefixWord ++ tailWord_7743545).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7743545).length < 2 ^ (prefixWord ++ tailWord_7743545).sum := by decide
  have hdescent : baseEnd_7743545 < baseStart_7743545 := by decide
  rcases family_descends (prefixWord ++ tailWord_7743545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7743551 : List Nat := [1, 1, 2, 2, 3, 1, 4, 1, 3, 1, 4]
def baseStart_7743551 : Nat := 118140960795 + 7743551 * 2 ^ 59
def prefixEnd_7743551 : Nat := 4983230072969 + 3 ^ 40 * 7743551 * 2
def baseEnd_7743551 : Nat := 3976163635603938054800563

theorem tailTrace_7743551 : CollatzResearch.WordTrace tailWord_7743551 prefixEnd_7743551 3976163635603938054800563 := by
  unfold tailWord_7743551
  simp only [CollatzResearch.WordTrace]
  refine ⟨282430507569444695066846507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188287005046296463377897671 282430507569444695066846507)
  ·
    refine ⟨423645761354167042600269761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 282430507569444695066846507 423645761354167042600269761)
    ·
      refine ⟨317734321015625281950202321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 423645761354167042600269761 317734321015625281950202321)
      ·
        refine ⟨238300740761718961462651741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 317734321015625281950202321 238300740761718961462651741)
        ·
          refine ⟨89362777785644610548494403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 238300740761718961462651741 89362777785644610548494403)
          ·
            refine ⟨134044166678466915822741605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89362777785644610548494403 134044166678466915822741605)
            ·
              refine ⟨25133281252212546716764051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 134044166678466915822741605 25133281252212546716764051)
              ·
                refine ⟨37699921878318820075146077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25133281252212546716764051 37699921878318820075146077)
                ·
                  refine ⟨14137470704369557528179779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 37699921878318820075146077 14137470704369557528179779)
                  ·
                    refine ⟨21206206056554336292269669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14137470704369557528179779 21206206056554336292269669)
                    ·
                      refine ⟨3976163635603938054800563, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21206206056554336292269669 3976163635603938054800563)
                      ·
                        rfl

theorem cell23_7743551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 4, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 4, 1, 3, 1, 4].length) (baseStart_7743551 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7743551 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7743551 prefixEnd_7743551 := by exact prefixLift 7743551
  have htrace : WordTrace (prefixWord ++ tailWord_7743551) baseStart_7743551 baseEnd_7743551 := by
    simpa [prefixWord, tailWord_7743551, baseEnd_7743551] using wordTrace_append hprefix tailTrace_7743551
  have hstable : (prefixWord ++ tailWord_7743551).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7743551).length < 2 ^ (prefixWord ++ tailWord_7743551).sum := by decide
  have hdescent : baseEnd_7743551 < baseStart_7743551 := by decide
  rcases family_descends (prefixWord ++ tailWord_7743551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7743561 : List Nat := [1, 2, 1, 1, 2, 2, 4, 2, 4, 4]
def baseStart_7743561 : Nat := 118140960795 + 7743561 * 2 ^ 59
def prefixEnd_7743561 : Nat := 4983230072969 + 3 ^ 40 * 7743561 * 2
def baseEnd_7743561 : Nat := 1325389590136827671891839

theorem tailTrace_7743561 : CollatzResearch.WordTrace tailWord_7743561 prefixEnd_7743561 1325389590136827671891839 := by
  unfold tailWord_7743561
  simp only [CollatzResearch.WordTrace]
  refine ⟨282430872299408466774710537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188287248199605644516473691 282430872299408466774710537)
  ·
    refine ⟨211823154224556350081032903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 282430872299408466774710537 211823154224556350081032903)
    ·
      refine ⟨317734731336834525121549355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 211823154224556350081032903 317734731336834525121549355)
      ·
        refine ⟨476602097005251787682324033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 317734731336834525121549355 476602097005251787682324033)
        ·
          refine ⟨357451572753938840761743025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 476602097005251787682324033 357451572753938840761743025)
          ·
            refine ⟨268088679565454130571307269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 357451572753938840761743025 268088679565454130571307269)
            ·
              refine ⟨50266627418522649482120113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 268088679565454130571307269 50266627418522649482120113)
              ·
                refine ⟨37699970563891987111590085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50266627418522649482120113 37699970563891987111590085)
                ·
                  refine ⟨7068744480729747583423141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 37699970563891987111590085 7068744480729747583423141)
                  ·
                    refine ⟨1325389590136827671891839, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7068744480729747583423141 1325389590136827671891839)
                    ·
                      rfl

theorem cell23_7743561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 4, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 4, 2, 4, 4].length) (baseStart_7743561 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7743561 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7743561 prefixEnd_7743561 := by exact prefixLift 7743561
  have htrace : WordTrace (prefixWord ++ tailWord_7743561) baseStart_7743561 baseEnd_7743561 := by
    simpa [prefixWord, tailWord_7743561, baseEnd_7743561] using wordTrace_append hprefix tailTrace_7743561
  have hstable : (prefixWord ++ tailWord_7743561).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7743561).length < 2 ^ (prefixWord ++ tailWord_7743561).sum := by decide
  have hdescent : baseEnd_7743561 < baseStart_7743561 := by decide
  rcases family_descends (prefixWord ++ tailWord_7743561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7743619 : List Nat := [1, 1, 1, 3, 3, 5, 1, 3, 1, 2, 2]
def baseStart_7743619 : Nat := 118140960795 + 7743619 * 2 ^ 59
def prefixEnd_7743619 : Nat := 4983230072969 + 3 ^ 40 * 7743619 * 2
def baseEnd_7743619 : Nat := 3976198552288443788750251

theorem tailTrace_7743619 : CollatzResearch.WordTrace tailWord_7743619 prefixEnd_7743619 3976198552288443788750251 := by
  unfold tailWord_7743619
  simp only [CollatzResearch.WordTrace]
  refine ⟨282432987733198342680321911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188288658488798895120214607 282432987733198342680321911)
  ·
    refine ⟨423649481599797514020482867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 282432987733198342680321911 423649481599797514020482867)
    ·
      refine ⟨635474222399696271030724301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 423649481599797514020482867 635474222399696271030724301)
      ·
        refine ⟨238302833399886101636521613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 635474222399696271030724301 238302833399886101636521613)
        ·
          refine ⟨89363562524957288113695605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 238302833399886101636521613 89363562524957288113695605)
          ·
            refine ⟨8377833986714745760658963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 89363562524957288113695605 8377833986714745760658963)
            ·
              refine ⟨12566750980072118640988445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8377833986714745760658963 12566750980072118640988445)
              ·
                refine ⟨4712531617527044490370667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12566750980072118640988445 4712531617527044490370667)
                ·
                  refine ⟨7068797426290566735556001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4712531617527044490370667 7068797426290566735556001)
                  ·
                    refine ⟨5301598069717925051667001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7068797426290566735556001 5301598069717925051667001)
                    ·
                      refine ⟨3976198552288443788750251, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5301598069717925051667001 3976198552288443788750251)
                      ·
                        rfl

theorem cell23_7743619_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 5, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 5, 1, 3, 1, 2, 2].length) (baseStart_7743619 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7743619 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7743619 prefixEnd_7743619 := by exact prefixLift 7743619
  have htrace : WordTrace (prefixWord ++ tailWord_7743619) baseStart_7743619 baseEnd_7743619 := by
    simpa [prefixWord, tailWord_7743619, baseEnd_7743619] using wordTrace_append hprefix tailTrace_7743619
  have hstable : (prefixWord ++ tailWord_7743619).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7743619).length < 2 ^ (prefixWord ++ tailWord_7743619).sum := by decide
  have hdescent : baseEnd_7743619 < baseStart_7743619 := by decide
  rcases family_descends (prefixWord ++ tailWord_7743619) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7743628 : List Nat := [2, 2, 1, 2, 1, 1, 1, 1, 7, 3, 2]
def baseStart_7743628 : Nat := 118140960795 + 7743628 * 2 ^ 59
def prefixEnd_7743628 : Nat := 4983230072969 + 3 ^ 40 * 7743628 * 2
def baseEnd_7743628 : Nat := 3976203173614334253537709

theorem tailTrace_7743628 : CollatzResearch.WordTrace tailWord_7743628 prefixEnd_7743628 3976203173614334253537709 := by
  unfold tailWord_7743628
  simp only [CollatzResearch.WordTrace]
  refine ⟨141216657995082868608699769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 188288877326777158144933025 141216657995082868608699769)
  ·
    refine ⟨105912493496312151456524827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 141216657995082868608699769 105912493496312151456524827)
    ·
      refine ⟨158868740244468227184787241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105912493496312151456524827 158868740244468227184787241)
      ·
        refine ⟨119151555183351170388590431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 158868740244468227184787241 119151555183351170388590431)
        ·
          refine ⟨178727332775026755582885647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 119151555183351170388590431 178727332775026755582885647)
          ·
            refine ⟨268090999162540133374328471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 178727332775026755582885647 268090999162540133374328471)
            ·
              refine ⟨402136498743810200061492707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 268090999162540133374328471 402136498743810200061492707)
              ·
                refine ⟨603204748115715300092239061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 402136498743810200061492707 603204748115715300092239061)
                ·
                  refine ⟨14137611283962077345911853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 603204748115715300092239061 14137611283962077345911853)
                  ·
                    refine ⟨5301604231485779004716945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14137611283962077345911853 5301604231485779004716945)
                    ·
                      refine ⟨3976203173614334253537709, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5301604231485779004716945 3976203173614334253537709)
                      ·
                        rfl

theorem cell23_7743628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 1, 1, 7, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 1, 1, 7, 3, 2].length) (baseStart_7743628 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7743628 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7743628 prefixEnd_7743628 := by exact prefixLift 7743628
  have htrace : WordTrace (prefixWord ++ tailWord_7743628) baseStart_7743628 baseEnd_7743628 := by
    simpa [prefixWord, tailWord_7743628, baseEnd_7743628] using wordTrace_append hprefix tailTrace_7743628
  have hstable : (prefixWord ++ tailWord_7743628).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7743628).length < 2 ^ (prefixWord ++ tailWord_7743628).sum := by decide
  have hdescent : baseEnd_7743628 < baseStart_7743628 := by decide
  rcases family_descends (prefixWord ++ tailWord_7743628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7743636 : List Nat := [2, 4, 2, 3, 1, 2, 1, 1, 3, 2, 2]
def baseStart_7743636 : Nat := 118140960795 + 7743636 * 2 ^ 59
def prefixEnd_7743636 : Nat := 4983230072969 + 3 ^ 40 * 7743636 * 2
def baseEnd_7743636 : Nat := 3976207281459570222237673

theorem tailTrace_7743636 : CollatzResearch.WordTrace tailWord_7743636 prefixEnd_7743636 3976207281459570222237673 := by
  unfold tailWord_7743636
  simp only [CollatzResearch.WordTrace]
  refine ⟨141216803887068377291845381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 188289071849424503055793841 141216803887068377291845381)
  ·
    refine ⟨26478150728825320742221009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 141216803887068377291845381 26478150728825320742221009)
    ·
      refine ⟨19858613046618990556665757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26478150728825320742221009 19858613046618990556665757)
      ·
        refine ⟨7446979892482121458749659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19858613046618990556665757 7446979892482121458749659)
        ·
          refine ⟨11170469838723182188124489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7446979892482121458749659 11170469838723182188124489)
          ·
            refine ⟨8377852379042386641093367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11170469838723182188124489 8377852379042386641093367)
            ·
              refine ⟨12566778568563579961640051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8377852379042386641093367 12566778568563579961640051)
              ·
                refine ⟨18850167852845369942460077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12566778568563579961640051 18850167852845369942460077)
                ·
                  refine ⟨7068812944817013728422529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18850167852845369942460077 7068812944817013728422529)
                  ·
                    refine ⟨5301609708612760296316897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7068812944817013728422529 5301609708612760296316897)
                    ·
                      refine ⟨3976207281459570222237673, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5301609708612760296316897 3976207281459570222237673)
                      ·
                        rfl

theorem cell23_7743636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 1, 2, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 1, 2, 1, 1, 3, 2, 2].length) (baseStart_7743636 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7743636 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7743636 prefixEnd_7743636 := by exact prefixLift 7743636
  have htrace : WordTrace (prefixWord ++ tailWord_7743636) baseStart_7743636 baseEnd_7743636 := by
    simpa [prefixWord, tailWord_7743636, baseEnd_7743636] using wordTrace_append hprefix tailTrace_7743636
  have hstable : (prefixWord ++ tailWord_7743636).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7743636).length < 2 ^ (prefixWord ++ tailWord_7743636).sum := by decide
  have hdescent : baseEnd_7743636 < baseStart_7743636 := by decide
  rcases family_descends (prefixWord ++ tailWord_7743636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7743646 : List Nat := [4, 3, 1, 1, 4, 1, 2, 1, 2, 4]
def baseStart_7743646 : Nat := 118140960795 + 7743646 * 2 ^ 59
def prefixEnd_7743646 : Nat := 4983230072969 + 3 ^ 40 * 7743646 * 2
def baseEnd_7743646 : Nat := 1325404138755371727704209

theorem tailTrace_7743646 : CollatzResearch.WordTrace tailWord_7743646 prefixEnd_7743646 1325404138755371727704209 := by
  unfold tailWord_7743646
  simp only [CollatzResearch.WordTrace]
  refine ⟨35304246563012565786444349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 188289315002733684194369861 35304246563012565786444349)
  ·
    refine ⟨13239092461129712169916631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35304246563012565786444349 13239092461129712169916631)
    ·
      refine ⟨19858638691694568254874947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13239092461129712169916631 19858638691694568254874947)
      ·
        refine ⟨29787958037541852382312421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19858638691694568254874947 29787958037541852382312421)
        ·
          refine ⟨5585242132039097321683579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 29787958037541852382312421 5585242132039097321683579)
          ·
            refine ⟨8377863198058645982525369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5585242132039097321683579 8377863198058645982525369)
            ·
              refine ⟨6283397398543984486894027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8377863198058645982525369 6283397398543984486894027)
              ·
                refine ⟨9425096097815976730341041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6283397398543984486894027 9425096097815976730341041)
                ·
                  refine ⟨7068822073361982547755781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9425096097815976730341041 7068822073361982547755781)
                  ·
                    refine ⟨1325404138755371727704209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7068822073361982547755781 1325404138755371727704209)
                    ·
                      rfl

theorem cell23_7743646_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 4, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 4, 1, 2, 1, 2, 4].length) (baseStart_7743646 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7743646 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7743646 prefixEnd_7743646 := by exact prefixLift 7743646
  have htrace : WordTrace (prefixWord ++ tailWord_7743646) baseStart_7743646 baseEnd_7743646 := by
    simpa [prefixWord, tailWord_7743646, baseEnd_7743646] using wordTrace_append hprefix tailTrace_7743646
  have hstable : (prefixWord ++ tailWord_7743646).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7743646).length < 2 ^ (prefixWord ++ tailWord_7743646).sum := by decide
  have hdescent : baseEnd_7743646 < baseStart_7743646 := by decide
  rcases family_descends (prefixWord ++ tailWord_7743646) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7743652 : List Nat := [2, 3, 1, 2, 4, 1, 1, 3, 2, 1, 3]
def baseStart_7743652 : Nat := 118140960795 + 7743652 * 2 ^ 59
def prefixEnd_7743652 : Nat := 4983230072969 + 3 ^ 40 * 7743652 * 2
def baseEnd_7743652 : Nat := 3976215497150042159637599

theorem tailTrace_7743652 : CollatzResearch.WordTrace tailWord_7743652 prefixEnd_7743652 3976215497150042159637599 := by
  unfold tailWord_7743652
  simp only [CollatzResearch.WordTrace]
  refine ⟨141217095671039394658136605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 188289460894719192877515473 141217095671039394658136605)
  ·
    refine ⟨52956410876639772996801227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 141217095671039394658136605 52956410876639772996801227)
    ·
      refine ⟨79434616314959659495201841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52956410876639772996801227 79434616314959659495201841)
      ·
        refine ⟨59575962236219744621401381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79434616314959659495201841 59575962236219744621401381)
        ·
          refine ⟨11170492919291202116512759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 59575962236219744621401381 11170492919291202116512759)
          ·
            refine ⟨16755739378936803174769139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11170492919291202116512759 16755739378936803174769139)
            ·
              refine ⟨25133609068405204762153709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16755739378936803174769139 25133609068405204762153709)
              ·
                refine ⟨9425103400651951785807641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25133609068405204762153709 9425103400651951785807641)
                ·
                  refine ⟨7068827550488963839355731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9425103400651951785807641 7068827550488963839355731)
                  ·
                    refine ⟨10603241325733445759033597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7068827550488963839355731 10603241325733445759033597)
                    ·
                      refine ⟨3976215497150042159637599, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10603241325733445759033597 3976215497150042159637599)
                      ·
                        rfl

theorem cell23_7743652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 4, 1, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 4, 1, 1, 3, 2, 1, 3].length) (baseStart_7743652 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7743652 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7743652 prefixEnd_7743652 := by exact prefixLift 7743652
  have htrace : WordTrace (prefixWord ++ tailWord_7743652) baseStart_7743652 baseEnd_7743652 := by
    simpa [prefixWord, tailWord_7743652, baseEnd_7743652] using wordTrace_append hprefix tailTrace_7743652
  have hstable : (prefixWord ++ tailWord_7743652).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7743652).length < 2 ^ (prefixWord ++ tailWord_7743652).sum := by decide
  have hdescent : baseEnd_7743652 < baseStart_7743652 := by decide
  rcases family_descends (prefixWord ++ tailWord_7743652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7743709 : List Nat := [1, 4, 3, 2, 1, 1, 2, 3, 2, 2, 2]
def baseStart_7743709 : Nat := 118140960795 + 7743709 * 2 ^ 59
def prefixEnd_7743709 : Nat := 4983230072969 + 3 ^ 40 * 7743709 * 2
def baseEnd_7743709 : Nat := 3976244765547348436624837

theorem tailTrace_7743709 : CollatzResearch.WordTrace tailWord_7743709 prefixEnd_7743709 3976244765547348436624837 := by
  unfold tailWord_7743709
  simp only [CollatzResearch.WordTrace]
  refine ⟨282436270302872288051098181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188290846868581525367398787 282436270302872288051098181)
  ·
    refine ⟨52956800681788554009580909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 282436270302872288051098181 52956800681788554009580909)
    ·
      refine ⟨19858800255670707753592841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 52956800681788554009580909 19858800255670707753592841)
      ·
        refine ⟨14894100191753030815194631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19858800255670707753592841 14894100191753030815194631)
        ·
          refine ⟨22341150287629546222791947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14894100191753030815194631 22341150287629546222791947)
          ·
            refine ⟨33511725431444319334187921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22341150287629546222791947 33511725431444319334187921)
            ·
              refine ⟨25133794073583239500640941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33511725431444319334187921 25133794073583239500640941)
              ·
                refine ⟨9425172777593714812740353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25133794073583239500640941 9425172777593714812740353)
                ·
                  refine ⟨7068879583195286109555265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9425172777593714812740353 7068879583195286109555265)
                  ·
                    refine ⟨5301659687396464582166449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7068879583195286109555265 5301659687396464582166449)
                    ·
                      refine ⟨3976244765547348436624837, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5301659687396464582166449 3976244765547348436624837)
                      ·
                        rfl

theorem cell23_7743709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 1, 2, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 1, 2, 3, 2, 2, 2].length) (baseStart_7743709 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7743709 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7743709 prefixEnd_7743709 := by exact prefixLift 7743709
  have htrace : WordTrace (prefixWord ++ tailWord_7743709) baseStart_7743709 baseEnd_7743709 := by
    simpa [prefixWord, tailWord_7743709, baseEnd_7743709] using wordTrace_append hprefix tailTrace_7743709
  have hstable : (prefixWord ++ tailWord_7743709).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7743709).length < 2 ^ (prefixWord ++ tailWord_7743709).sum := by decide
  have hdescent : baseEnd_7743709 < baseStart_7743709 := by decide
  rcases family_descends (prefixWord ++ tailWord_7743709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7743711 : List Nat := [1, 1, 2, 3, 2, 1, 1, 4, 1, 7]
def baseStart_7743711 : Nat := 118140960795 + 7743711 * 2 ^ 59
def prefixEnd_7743711 : Nat := 4983230072969 + 3 ^ 40 * 7743711 * 2
def baseEnd_7743711 : Nat := 1325415264169552476266609

theorem tailTrace_7743711 : CollatzResearch.WordTrace tailWord_7743711 prefixEnd_7743711 1325415264169552476266609 := by
  unfold tailWord_7743711
  simp only [CollatzResearch.WordTrace]
  refine ⟨282436343248865042392670987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188290895499243361595113991 282436343248865042392670987)
  ·
    refine ⟨423654514873297563589006481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 282436343248865042392670987 423654514873297563589006481)
    ·
      refine ⟨317740886154973172691754861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 423654514873297563589006481 317740886154973172691754861)
      ·
        refine ⟨119152832308114939759408073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 317740886154973172691754861 119152832308114939759408073)
        ·
          refine ⟨89364624231086204819556055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 119152832308114939759408073 89364624231086204819556055)
          ·
            refine ⟨134046936346629307229334083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89364624231086204819556055 134046936346629307229334083)
            ·
              refine ⟨201070404519943960844001125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 134046936346629307229334083 201070404519943960844001125)
              ·
                refine ⟨37700700847489492658250211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 201070404519943960844001125 37700700847489492658250211)
                ·
                  refine ⟨56551051271234238987375317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37700700847489492658250211 56551051271234238987375317)
                  ·
                    refine ⟨1325415264169552476266609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 56551051271234238987375317 1325415264169552476266609)
                    ·
                      rfl

theorem cell23_7743711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 1, 4, 1, 7].length) (baseStart_7743711 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7743711 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7743711 prefixEnd_7743711 := by exact prefixLift 7743711
  have htrace : WordTrace (prefixWord ++ tailWord_7743711) baseStart_7743711 baseEnd_7743711 := by
    simpa [prefixWord, tailWord_7743711, baseEnd_7743711] using wordTrace_append hprefix tailTrace_7743711
  have hstable : (prefixWord ++ tailWord_7743711).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7743711).length < 2 ^ (prefixWord ++ tailWord_7743711).sum := by decide
  have hdescent : baseEnd_7743711 < baseStart_7743711 := by decide
  rcases family_descends (prefixWord ++ tailWord_7743711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7743715 : List Nat := [1, 1, 1, 8, 1, 1, 1, 2, 7]
def baseStart_7743715 : Nat := 118140960795 + 7743715 * 2 ^ 59
def prefixEnd_7743715 : Nat := 4983230072969 + 3 ^ 40 * 7743715 * 2
def baseEnd_7743715 : Nat := 441805316270141712572201

theorem tailTrace_7743715 : CollatzResearch.WordTrace tailWord_7743715 prefixEnd_7743715 441805316270141712572201 := by
  unfold tailWord_7743715
  simp only [CollatzResearch.WordTrace]
  refine ⟨282436489140850551075816599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188290992760567034050544399 282436489140850551075816599)
  ·
    refine ⟨423654733711275826613724899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 282436489140850551075816599 423654733711275826613724899)
    ·
      refine ⟨635482100566913739920587349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 423654733711275826613724899 635482100566913739920587349)
      ·
        refine ⟨7447055866018520389694383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 8 635482100566913739920587349 7447055866018520389694383)
        ·
          refine ⟨11170583799027780584541575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7447055866018520389694383 11170583799027780584541575)
          ·
            refine ⟨16755875698541670876812363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11170583799027780584541575 16755875698541670876812363)
            ·
              refine ⟨25133813547812506315218545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16755875698541670876812363 25133813547812506315218545)
              ·
                refine ⟨18850360160859379736413909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25133813547812506315218545 18850360160859379736413909)
                ·
                  refine ⟨441805316270141712572201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18850360160859379736413909 441805316270141712572201)
                  ·
                    rfl

theorem cell23_7743715_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 1, 1, 1, 2, 7].length) (baseStart_7743715 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7743715 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7743715 prefixEnd_7743715 := by exact prefixLift 7743715
  have htrace : WordTrace (prefixWord ++ tailWord_7743715) baseStart_7743715 baseEnd_7743715 := by
    simpa [prefixWord, tailWord_7743715, baseEnd_7743715] using wordTrace_append hprefix tailTrace_7743715
  have hstable : (prefixWord ++ tailWord_7743715).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7743715).length < 2 ^ (prefixWord ++ tailWord_7743715).sum := by decide
  have hdescent : baseEnd_7743715 < baseStart_7743715 := by decide
  rcases family_descends (prefixWord ++ tailWord_7743715) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7743741 : List Nat := [1, 4, 1, 1, 1, 1, 1, 2, 1, 10]
def baseStart_7743741 : Nat := 118140960795 + 7743741 * 2 ^ 59
def prefixEnd_7743741 : Nat := 4983230072969 + 3 ^ 40 * 7743741 * 2
def baseEnd_7743741 : Nat := 1325420398976097437141563

theorem tailTrace_7743741 : CollatzResearch.WordTrace tailWord_7743741 prefixEnd_7743741 1325420398976097437141563 := by
  unfold tailWord_7743741
  simp only [CollatzResearch.WordTrace]
  refine ⟨282437437438756357516263077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188291624959170905010842051 282437437438756357516263077)
  ·
    refine ⟨52957019519766817034299327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 282437437438756357516263077 52957019519766817034299327)
    ·
      refine ⟨79435529279650225551448991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52957019519766817034299327 79435529279650225551448991)
      ·
        refine ⟨119153293919475338327173487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79435529279650225551448991 119153293919475338327173487)
        ·
          refine ⟨178729940879213007490760231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 119153293919475338327173487 178729940879213007490760231)
          ·
            refine ⟨268094911318819511236140347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 178729940879213007490760231 268094911318819511236140347)
            ·
              refine ⟨402142366978229266854210521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 268094911318819511236140347 402142366978229266854210521)
              ·
                refine ⟨301606775233671950140657891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 402142366978229266854210521 301606775233671950140657891)
                ·
                  refine ⟨452410162850507925210986837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 301606775233671950140657891 452410162850507925210986837)
                  ·
                    refine ⟨1325420398976097437141563, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 452410162850507925210986837 1325420398976097437141563)
                    ·
                      rfl

theorem cell23_7743741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 1, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 1, 2, 1, 10].length) (baseStart_7743741 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7743741 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7743741 prefixEnd_7743741 := by exact prefixLift 7743741
  have htrace : WordTrace (prefixWord ++ tailWord_7743741) baseStart_7743741 baseEnd_7743741 := by
    simpa [prefixWord, tailWord_7743741, baseEnd_7743741] using wordTrace_append hprefix tailTrace_7743741
  have hstable : (prefixWord ++ tailWord_7743741).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7743741).length < 2 ^ (prefixWord ++ tailWord_7743741).sum := by decide
  have hdescent : baseEnd_7743741 < baseStart_7743741 := by decide
  rcases family_descends (prefixWord ++ tailWord_7743741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7743765 : List Nat := [1, 3, 2, 1, 2, 1, 4, 1, 2, 4, 2]
def baseStart_7743765 : Nat := 118140960795 + 7743765 * 2 ^ 59
def prefixEnd_7743765 : Nat := 4983230072969 + 3 ^ 40 * 7743765 * 2
def baseEnd_7743765 : Nat := 3976273520464000217524579

theorem tailTrace_7743765 : CollatzResearch.WordTrace tailWord_7743765 prefixEnd_7743765 3976273520464000217524579 := by
  unfold tailWord_7743765
  simp only [CollatzResearch.WordTrace]
  refine ⟨282438312790669409615136749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188292208527112939743424499 282438312790669409615136749)
  ·
    refine ⟨105914367296501028605676281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 282438312790669409615136749 105914367296501028605676281)
    ·
      refine ⟨79435775472375771454257211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 105914367296501028605676281 79435775472375771454257211)
      ·
        refine ⟨119153663208563657181385817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79435775472375771454257211 119153663208563657181385817)
        ·
          refine ⟨89365247406422742886039363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 119153663208563657181385817 89365247406422742886039363)
          ·
            refine ⟨134047871109634114329059045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89365247406422742886039363 134047871109634114329059045)
            ·
              refine ⟨25133975833056396436698571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 134047871109634114329059045 25133975833056396436698571)
              ·
                refine ⟨37700963749584594655047857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25133975833056396436698571 37700963749584594655047857)
                ·
                  refine ⟨28275722812188445991285893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37700963749584594655047857 28275722812188445991285893)
                  ·
                    refine ⟨5301698027285333623366105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28275722812188445991285893 5301698027285333623366105)
                    ·
                      refine ⟨3976273520464000217524579, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5301698027285333623366105 3976273520464000217524579)
                      ·
                        rfl

theorem cell23_7743765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 4, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 4, 1, 2, 4, 2].length) (baseStart_7743765 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7743765 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7743765 prefixEnd_7743765 := by exact prefixLift 7743765
  have htrace : WordTrace (prefixWord ++ tailWord_7743765) baseStart_7743765 baseEnd_7743765 := by
    simpa [prefixWord, tailWord_7743765, baseEnd_7743765] using wordTrace_append hprefix tailTrace_7743765
  have hstable : (prefixWord ++ tailWord_7743765).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7743765).length < 2 ^ (prefixWord ++ tailWord_7743765).sum := by decide
  have hdescent : baseEnd_7743765 < baseStart_7743765 := by decide
  rcases family_descends (prefixWord ++ tailWord_7743765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7743768 : List Nat := [2, 1, 2, 3, 1, 2, 1, 1, 3, 4, 3]
def baseStart_7743768 : Nat := 118140960795 + 7743768 * 2 ^ 59
def prefixEnd_7743768 : Nat := 4983230072969 + 3 ^ 40 * 7743768 * 2
def baseEnd_7743768 : Nat := 3976275060905963705787065

theorem tailTrace_7743768 : CollatzResearch.WordTrace tailWord_7743768 prefixEnd_7743768 3976275060905963705787065 := by
  unfold tailWord_7743768
  simp only [CollatzResearch.WordTrace]
  refine ⟨141219211104829270563747979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 188292281473105694084997305 141219211104829270563747979)
  ·
    refine ⟨211828816657243905845621969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141219211104829270563747979 211828816657243905845621969)
    ·
      refine ⟨158871612492932929384216477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 211828816657243905845621969 158871612492932929384216477)
      ·
        refine ⟨59576854684849848519081179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 158871612492932929384216477 59576854684849848519081179)
        ·
          refine ⟨89365282027274772778621769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59576854684849848519081179 89365282027274772778621769)
          ·
            refine ⟨67023961520456079583966327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 89365282027274772778621769 67023961520456079583966327)
            ·
              refine ⟨100535942280684119375949491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67023961520456079583966327 100535942280684119375949491)
              ·
                refine ⟨150803913421026179063924237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 100535942280684119375949491 150803913421026179063924237)
                ·
                  refine ⟨56551467532884817148971589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 150803913421026179063924237 56551467532884817148971589)
                  ·
                    refine ⟨10603400162415903215432173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 56551467532884817148971589 10603400162415903215432173)
                    ·
                      refine ⟨3976275060905963705787065, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10603400162415903215432173 3976275060905963705787065)
                      ·
                        rfl

theorem cell23_7743768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 1, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 1, 1, 3, 4, 3].length) (baseStart_7743768 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7743768 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7743768 prefixEnd_7743768 := by exact prefixLift 7743768
  have htrace : WordTrace (prefixWord ++ tailWord_7743768) baseStart_7743768 baseEnd_7743768 := by
    simpa [prefixWord, tailWord_7743768, baseEnd_7743768] using wordTrace_append hprefix tailTrace_7743768
  have hstable : (prefixWord ++ tailWord_7743768).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7743768).length < 2 ^ (prefixWord ++ tailWord_7743768).sum := by decide
  have hdescent : baseEnd_7743768 < baseStart_7743768 := by decide
  rcases family_descends (prefixWord ++ tailWord_7743768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7743775 : List Nat := [1, 1, 2, 4, 3, 1, 2, 2, 3, 4]
def baseStart_7743775 : Nat := 118140960795 + 7743775 * 2 ^ 59
def prefixEnd_7743775 : Nat := 4983230072969 + 3 ^ 40 * 7743775 * 2
def baseEnd_7743775 : Nat := 1325426218423515059466511

theorem tailTrace_7743775 : CollatzResearch.WordTrace tailWord_7743775 prefixEnd_7743775 1325426218423515059466511 := by
  unfold tailWord_7743775
  simp only [CollatzResearch.WordTrace]
  refine ⟨282438677520633181323000779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188292451680422120882000519 282438677520633181323000779)
  ·
    refine ⟨423658016280949771984501169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 282438677520633181323000779 423658016280949771984501169)
    ·
      refine ⟨317743512210712328988375877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 423658016280949771984501169 317743512210712328988375877)
      ·
        refine ⟨59576908539508561685320477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 317743512210712328988375877 59576908539508561685320477)
        ·
          refine ⟨22341340702315710631995179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 59576908539508561685320477 22341340702315710631995179)
          ·
            refine ⟨33512011053473565947992769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22341340702315710631995179 33512011053473565947992769)
            ·
              refine ⟨25134008290105174460994577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33512011053473565947992769 25134008290105174460994577)
              ·
                refine ⟨18850506217578880845745933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25134008290105174460994577 18850506217578880845745933)
                ·
                  refine ⟨7068939831592080317154725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18850506217578880845745933 7068939831592080317154725)
                  ·
                    refine ⟨1325426218423515059466511, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7068939831592080317154725 1325426218423515059466511)
                    ·
                      rfl

theorem cell23_7743775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 1, 2, 2, 3, 4].length) (baseStart_7743775 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7743775 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7743775 prefixEnd_7743775 := by exact prefixLift 7743775
  have htrace : WordTrace (prefixWord ++ tailWord_7743775) baseStart_7743775 baseEnd_7743775 := by
    simpa [prefixWord, tailWord_7743775, baseEnd_7743775] using wordTrace_append hprefix tailTrace_7743775
  have hstable : (prefixWord ++ tailWord_7743775).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7743775).length < 2 ^ (prefixWord ++ tailWord_7743775).sum := by decide
  have hdescent : baseEnd_7743775 < baseStart_7743775 := by decide
  rcases family_descends (prefixWord ++ tailWord_7743775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7743783 : List Nat := [1, 1, 8, 1, 2, 1, 1, 3, 5]
def baseStart_7743783 : Nat := 118140960795 + 7743783 * 2 ^ 59
def prefixEnd_7743783 : Nat := 4983230072969 + 3 ^ 40 * 7743783 * 2
def baseEnd_7743783 : Nat := 441809195901753460788833

theorem tailTrace_7743783 : CollatzResearch.WordTrace tailWord_7743783 prefixEnd_7743783 441809195901753460788833 := by
  unfold tailWord_7743783
  simp only [CollatzResearch.WordTrace]
  refine ⟨282438969304604198689292003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188292646203069465792861335 282438969304604198689292003)
  ·
    refine ⟨423658453956906298033938005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 282438969304604198689292003 423658453956906298033938005)
    ·
      refine ⟨4964747507307495680085211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 8 423658453956906298033938005 4964747507307495680085211)
      ·
        refine ⟨7447121260961243520127817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4964747507307495680085211 7447121260961243520127817)
        ·
          refine ⟨5585340945720932640095863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7447121260961243520127817 5585340945720932640095863)
          ·
            refine ⟨8378011418581398960143795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5585340945720932640095863 8378011418581398960143795)
            ·
              refine ⟨12567017127872098440215693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8378011418581398960143795 12567017127872098440215693)
              ·
                refine ⟨4712631422952036915080885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12567017127872098440215693 4712631422952036915080885)
                ·
                  refine ⟨441809195901753460788833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4712631422952036915080885 441809195901753460788833)
                  ·
                    rfl

theorem cell23_7743783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 2, 1, 1, 3, 5].length) (baseStart_7743783 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7743783 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7743783 prefixEnd_7743783 := by exact prefixLift 7743783
  have htrace : WordTrace (prefixWord ++ tailWord_7743783) baseStart_7743783 baseEnd_7743783 := by
    simpa [prefixWord, tailWord_7743783, baseEnd_7743783] using wordTrace_append hprefix tailTrace_7743783
  have hstable : (prefixWord ++ tailWord_7743783).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7743783).length < 2 ^ (prefixWord ++ tailWord_7743783).sum := by decide
  have hdescent : baseEnd_7743783 < baseStart_7743783 := by decide
  rcases family_descends (prefixWord ++ tailWord_7743783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7743809 : List Nat := [1, 2, 5, 2, 2, 2, 1, 1, 3, 4]
def baseStart_7743809 : Nat := 118140960795 + 7743809 * 2 ^ 59
def prefixEnd_7743809 : Nat := 4983230072969 + 3 ^ 40 * 7743809 * 2
def baseEnd_7743809 : Nat := 1325432037870932681791459

theorem tailTrace_7743809 : CollatzResearch.WordTrace tailWord_7743809 prefixEnd_7743809 1325432037870932681791459 := by
  unfold tailWord_7743809
  simp only [CollatzResearch.WordTrace]
  refine ⟨282439917602510005129738481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188293278401673336753158987 282439917602510005129738481)
  ·
    refine ⟨211829938201882503847303861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 282439917602510005129738481 211829938201882503847303861)
    ·
      refine ⟨19859056706426484735684737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 211829938201882503847303861 19859056706426484735684737)
      ·
        refine ⟨14894292529819863551763553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19859056706426484735684737 14894292529819863551763553)
        ·
          refine ⟨11170719397364897663822665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14894292529819863551763553 11170719397364897663822665)
          ·
            refine ⟨8378039548023673247866999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11170719397364897663822665 8378039548023673247866999)
            ·
              refine ⟨12567059322035509871800499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8378039548023673247866999 12567059322035509871800499)
              ·
                refine ⟨18850588983053264807700749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12567059322035509871800499 18850588983053264807700749)
                ·
                  refine ⟨7068970868644974302887781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18850588983053264807700749 7068970868644974302887781)
                  ·
                    refine ⟨1325432037870932681791459, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7068970868644974302887781 1325432037870932681791459)
                    ·
                      rfl

theorem cell23_7743809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 2, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 2, 2, 1, 1, 3, 4].length) (baseStart_7743809 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7743809 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7743809 prefixEnd_7743809 := by exact prefixLift 7743809
  have htrace : WordTrace (prefixWord ++ tailWord_7743809) baseStart_7743809 baseEnd_7743809 := by
    simpa [prefixWord, tailWord_7743809, baseEnd_7743809] using wordTrace_append hprefix tailTrace_7743809
  have hstable : (prefixWord ++ tailWord_7743809).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7743809).length < 2 ^ (prefixWord ++ tailWord_7743809).sum := by decide
  have hdescent : baseEnd_7743809 < baseStart_7743809 := by decide
  rcases family_descends (prefixWord ++ tailWord_7743809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7743868 : List Nat := [2, 2, 2, 1, 1, 1, 2, 4, 1, 1, 6]
def baseStart_7743868 : Nat := 118140960795 + 7743868 * 2 ^ 59
def prefixEnd_7743868 : Nat := 4983230072969 + 3 ^ 40 * 7743868 * 2
def baseEnd_7743868 : Nat := 3976326408971413314536605

theorem tailTrace_7743868 : CollatzResearch.WordTrace tailWord_7743868 prefixEnd_7743868 3976326408971413314536605 := by
  unfold tailWord_7743868
  simp only [CollatzResearch.WordTrace]
  refine ⟨141221034754648129103068129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 188294713006197505470757505 141221034754648129103068129)
  ·
    refine ⟨105915776065986096827301097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 141221034754648129103068129 105915776065986096827301097)
    ·
      refine ⟨79436832049489572620475823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 105915776065986096827301097 79436832049489572620475823)
      ·
        refine ⟨119155248074234358930713735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79436832049489572620475823 119155248074234358930713735)
        ·
          refine ⟨178732872111351538396070603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 119155248074234358930713735 178732872111351538396070603)
          ·
            refine ⟨268099308167027307594105905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 178732872111351538396070603 268099308167027307594105905)
            ·
              refine ⟨201074481125270480695579429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 268099308167027307594105905 201074481125270480695579429)
              ·
                refine ⟨37701465210988215130421143, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 201074481125270480695579429 37701465210988215130421143)
                ·
                  refine ⟨56552197816482322695631715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37701465210988215130421143 56552197816482322695631715)
                  ·
                    refine ⟨84828296724723484043447573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 56552197816482322695631715 84828296724723484043447573)
                    ·
                      refine ⟨3976326408971413314536605, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 84828296724723484043447573 3976326408971413314536605)
                      ·
                        rfl

theorem cell23_7743868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 2, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 2, 4, 1, 1, 6].length) (baseStart_7743868 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7743868 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7743868 prefixEnd_7743868 := by exact prefixLift 7743868
  have htrace : WordTrace (prefixWord ++ tailWord_7743868) baseStart_7743868 baseEnd_7743868 := by
    simpa [prefixWord, tailWord_7743868, baseEnd_7743868] using wordTrace_append hprefix tailTrace_7743868
  have hstable : (prefixWord ++ tailWord_7743868).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7743868).length < 2 ^ (prefixWord ++ tailWord_7743868).sum := by decide
  have hdescent : baseEnd_7743868 < baseStart_7743868 := by decide
  rcases family_descends (prefixWord ++ tailWord_7743868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7743922 : List Nat := [3, 2, 1, 1, 1, 1, 5, 1, 4, 1, 3]
def baseStart_7743922 : Nat := 118140960795 + 7743922 * 2 ^ 59
def prefixEnd_7743922 : Nat := 4983230072969 + 3 ^ 40 * 7743922 * 2
def baseEnd_7743922 : Nat := 3976354136926756103261357

theorem tailTrace_7743922 : CollatzResearch.WordTrace tailWord_7743922 prefixEnd_7743922 3976354136926756103261357 := by
  unfold tailWord_7743922
  simp only [CollatzResearch.WordTrace]
  refine ⟨70611009762775156357150505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 188296026034067083619068013 70611009762775156357150505)
  ·
    refine ⟨52958257322081367267862879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70611009762775156357150505 52958257322081367267862879)
    ·
      refine ⟨79437385983122050901794319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52958257322081367267862879 79437385983122050901794319)
      ·
        refine ⟨119156078974683076352691479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79437385983122050901794319 119156078974683076352691479)
        ·
          refine ⟨178734118462024614529037219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 119156078974683076352691479 178734118462024614529037219)
          ·
            refine ⟨268101177693036921793555829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 178734118462024614529037219 268101177693036921793555829)
            ·
              refine ⟨25134485408722211418145859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 268101177693036921793555829 25134485408722211418145859)
              ·
                refine ⟨37701728113083317127218789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25134485408722211418145859 37701728113083317127218789)
                ·
                  refine ⟨7069074021203121961353523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 37701728113083317127218789 7069074021203121961353523)
                  ·
                    refine ⟨10603611031804682942030285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7069074021203121961353523 10603611031804682942030285)
                    ·
                      refine ⟨3976354136926756103261357, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10603611031804682942030285 3976354136926756103261357)
                      ·
                        rfl

theorem cell23_7743922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 5, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 5, 1, 4, 1, 3].length) (baseStart_7743922 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7743922 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7743922 prefixEnd_7743922 := by exact prefixLift 7743922
  have htrace : WordTrace (prefixWord ++ tailWord_7743922) baseStart_7743922 baseEnd_7743922 := by
    simpa [prefixWord, tailWord_7743922, baseEnd_7743922] using wordTrace_append hprefix tailTrace_7743922
  have hstable : (prefixWord ++ tailWord_7743922).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7743922).length < 2 ^ (prefixWord ++ tailWord_7743922).sum := by decide
  have hdescent : baseEnd_7743922 < baseStart_7743922 := by decide
  rcases family_descends (prefixWord ++ tailWord_7743922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7743962 : List Nat := [3, 1, 1, 2, 3, 1, 2, 1, 3, 4, 2]
def baseStart_7743962 : Nat := 118140960795 + 7743962 * 2 ^ 59
def prefixEnd_7743962 : Nat := 4983230072969 + 3 ^ 40 * 7743962 * 2
def baseEnd_7743962 : Nat := 3976374676152935946761173

theorem tailTrace_7743962 : CollatzResearch.WordTrace tailWord_7743962 prefixEnd_7743962 3976374676152935946761173 := by
  unfold tailWord_7743962
  simp only [CollatzResearch.WordTrace]
  refine ⟨70611374492738928065014535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 188296998647303808173372093 70611374492738928065014535)
  ·
    refine ⟨105917061739108392097521803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70611374492738928065014535 105917061739108392097521803)
    ·
      refine ⟨158875592608662588146282705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105917061739108392097521803 158875592608662588146282705)
      ·
        refine ⟨119156694456496941109712029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 158875592608662588146282705 119156694456496941109712029)
        ·
          refine ⟨44683760421186352916142011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 119156694456496941109712029 44683760421186352916142011)
          ·
            refine ⟨67025640631779529374213017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44683760421186352916142011 67025640631779529374213017)
            ·
              refine ⟨50269230473834647030659763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 67025640631779529374213017 50269230473834647030659763)
              ·
                refine ⟨75403845710751970545989645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50269230473834647030659763 75403845710751970545989645)
                ·
                  refine ⟨28276442141531988954746117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 75403845710751970545989645 28276442141531988954746117)
                  ·
                    refine ⟨5301832901537247929014897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28276442141531988954746117 5301832901537247929014897)
                    ·
                      refine ⟨3976374676152935946761173, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5301832901537247929014897 3976374676152935946761173)
                      ·
                        rfl

theorem cell23_7743962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 2, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 2, 1, 3, 4, 2].length) (baseStart_7743962 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7743962 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7743962 prefixEnd_7743962 := by exact prefixLift 7743962
  have htrace : WordTrace (prefixWord ++ tailWord_7743962) baseStart_7743962 baseEnd_7743962 := by
    simpa [prefixWord, tailWord_7743962, baseEnd_7743962] using wordTrace_append hprefix tailTrace_7743962
  have hstable : (prefixWord ++ tailWord_7743962).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7743962).length < 2 ^ (prefixWord ++ tailWord_7743962).sum := by decide
  have hdescent : baseEnd_7743962 < baseStart_7743962 := by decide
  rcases family_descends (prefixWord ++ tailWord_7743962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7743979 : List Nat := [1, 1, 1, 1, 2, 3, 4, 4, 2, 2, 2]
def baseStart_7743979 : Nat := 118140960795 + 7743979 * 2 ^ 59
def prefixEnd_7743979 : Nat := 4983230072969 + 3 ^ 40 * 7743979 * 2
def baseEnd_7743979 : Nat := 3976383405324062380248595

theorem tailTrace_7743979 : CollatzResearch.WordTrace tailWord_7743979 prefixEnd_7743979 3976383405324062380248595 := by
  unfold tailWord_7743979
  simp only [CollatzResearch.WordTrace]
  refine ⟨282446118011894124163426991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188297412007929416108951327 282446118011894124163426991)
  ·
    refine ⟨423669177017841186245140487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 282446118011894124163426991 423669177017841186245140487)
    ·
      refine ⟨635503765526761779367710731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 423669177017841186245140487 635503765526761779367710731)
      ·
        refine ⟨953255648290142669051566097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 635503765526761779367710731 953255648290142669051566097)
        ·
          refine ⟨714941736217607001788674573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 953255648290142669051566097 714941736217607001788674573)
          ·
            refine ⟨268103151081602625670752965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 714941736217607001788674573 268103151081602625670752965)
            ·
              refine ⟨50269340827800492313266181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 268103151081602625670752965 50269340827800492313266181)
              ·
                refine ⟨9425501405212592308737409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 50269340827800492313266181 9425501405212592308737409)
                ·
                  refine ⟨7069126053909444231553057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9425501405212592308737409 7069126053909444231553057)
                  ·
                    refine ⟨5301844540432083173664793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7069126053909444231553057 5301844540432083173664793)
                    ·
                      refine ⟨3976383405324062380248595, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5301844540432083173664793 3976383405324062380248595)
                      ·
                        rfl

theorem cell23_7743979_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 4, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 4, 4, 2, 2, 2].length) (baseStart_7743979 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7743979 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7743979 prefixEnd_7743979 := by exact prefixLift 7743979
  have htrace : WordTrace (prefixWord ++ tailWord_7743979) baseStart_7743979 baseEnd_7743979 := by
    simpa [prefixWord, tailWord_7743979, baseEnd_7743979] using wordTrace_append hprefix tailTrace_7743979
  have hstable : (prefixWord ++ tailWord_7743979).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7743979).length < 2 ^ (prefixWord ++ tailWord_7743979).sum := by decide
  have hdescent : baseEnd_7743979 < baseStart_7743979 := by decide
  rcases family_descends (prefixWord ++ tailWord_7743979) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7744013 : List Nat := [1, 7, 1, 1, 1, 2, 1, 2, 1, 4, 2]
def baseStart_7744013 : Nat := 118140960795 + 7744013 * 2 ^ 59
def prefixEnd_7744013 : Nat := 4983230072969 + 3 ^ 40 * 7744013 * 2
def baseEnd_7744013 : Nat := 3976400863666315247223439

theorem tailTrace_7744013 : CollatzResearch.WordTrace tailWord_7744013 prefixEnd_7744013 3976400863666315247223439 := by
  unfold tailWord_7744013
  simp only [CollatzResearch.WordTrace]
  refine ⟨282447358093770947970164693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188298238729180631980109795 282447358093770947970164693)
  ·
    refine ⟨6619859955322756593050735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 282447358093770947970164693 6619859955322756593050735)
    ·
      refine ⟨9929789932984134889576103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6619859955322756593050735 9929789932984134889576103)
      ·
        refine ⟨14894684899476202334364155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9929789932984134889576103 14894684899476202334364155)
        ·
          refine ⟨22342027349214303501546233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14894684899476202334364155 22342027349214303501546233)
          ·
            refine ⟨16756520511910727626159675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22342027349214303501546233 16756520511910727626159675)
            ·
              refine ⟨25134780767866091439239513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16756520511910727626159675 25134780767866091439239513)
              ·
                refine ⟨18851085575899568579429635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25134780767866091439239513 18851085575899568579429635)
                ·
                  refine ⟨28276628363849352869144453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18851085575899568579429635 28276628363849352869144453)
                  ·
                    refine ⟨5301867818221753662964585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28276628363849352869144453 5301867818221753662964585)
                    ·
                      refine ⟨3976400863666315247223439, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5301867818221753662964585 3976400863666315247223439)
                      ·
                        rfl

theorem cell23_7744013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 2, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 2, 1, 2, 1, 4, 2].length) (baseStart_7744013 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7744013 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7744013 prefixEnd_7744013 := by exact prefixLift 7744013
  have htrace : WordTrace (prefixWord ++ tailWord_7744013) baseStart_7744013 baseEnd_7744013 := by
    simpa [prefixWord, tailWord_7744013, baseEnd_7744013] using wordTrace_append hprefix tailTrace_7744013
  have hstable : (prefixWord ++ tailWord_7744013).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7744013).length < 2 ^ (prefixWord ++ tailWord_7744013).sum := by decide
  have hdescent : baseEnd_7744013 < baseStart_7744013 := by decide
  rcases family_descends (prefixWord ++ tailWord_7744013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7744015 : List Nat := [1, 1, 2, 1, 1, 1, 2, 7, 2, 5]
def baseStart_7744015 : Nat := 118140960795 + 7744015 * 2 ^ 59
def prefixEnd_7744015 : Nat := 4983230072969 + 3 ^ 40 * 7744015 * 2
def baseEnd_7744015 : Nat := 1325467296875874746466143

theorem tailTrace_7744015 : CollatzResearch.WordTrace tailWord_7744015 prefixEnd_7744015 1325467296875874746466143 := by
  unfold tailWord_7744015
  simp only [CollatzResearch.WordTrace]
  refine ⟨282447431039763702311737499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188298287359842468207824999 282447431039763702311737499)
  ·
    refine ⟨423671146559645553467606249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 282447431039763702311737499 423671146559645553467606249)
    ·
      refine ⟨317753359919734165100704687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 423671146559645553467606249 317753359919734165100704687)
      ·
        refine ⟨476630039879601247651057031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 317753359919734165100704687 476630039879601247651057031)
        ·
          refine ⟨714945059819401871476585547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 476630039879601247651057031 714945059819401871476585547)
          ·
            refine ⟨1072417589729102807214878321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 714945059819401871476585547 1072417589729102807214878321)
            ·
              refine ⟨804313192296827105411158741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1072417589729102807214878321 804313192296827105411158741)
              ·
                refine ⟨18851090444456885283074033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 804313192296827105411158741 18851090444456885283074033)
                ·
                  refine ⟨14138317833342663962305525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18851090444456885283074033 14138317833342663962305525)
                  ·
                    refine ⟨1325467296875874746466143, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14138317833342663962305525 1325467296875874746466143)
                    ·
                      rfl

theorem cell23_7744015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 7, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 7, 2, 5].length) (baseStart_7744015 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7744015 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7744015 prefixEnd_7744015 := by exact prefixLift 7744015
  have htrace : WordTrace (prefixWord ++ tailWord_7744015) baseStart_7744015 baseEnd_7744015 := by
    simpa [prefixWord, tailWord_7744015, baseEnd_7744015] using wordTrace_append hprefix tailTrace_7744015
  have hstable : (prefixWord ++ tailWord_7744015).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7744015).length < 2 ^ (prefixWord ++ tailWord_7744015).sum := by decide
  have hdescent : baseEnd_7744015 < baseStart_7744015 := by decide
  rcases family_descends (prefixWord ++ tailWord_7744015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7744036 : List Nat := [2, 3, 1, 5, 1, 1, 1, 4, 5]
def baseStart_7744036 : Nat := 118140960795 + 7744036 * 2 ^ 59
def prefixEnd_7744036 : Nat := 4983230072969 + 3 ^ 40 * 7744036 * 2
def baseEnd_7744036 : Nat := 441823630413485406359537

theorem tailTrace_7744036 : CollatzResearch.WordTrace tailWord_7744036 prefixEnd_7744036 441823630413485406359537 := by
  unfold tailWord_7744036
  simp only [CollatzResearch.WordTrace]
  refine ⟨141224098486343811449125981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 188298797981791748598834641 141224098486343811449125981)
  ·
    refine ⟨52959036932378929293422243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 141224098486343811449125981 52959036932378929293422243)
    ·
      refine ⟨79438555398568393940133365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52959036932378929293422243 79438555398568393940133365)
      ·
        refine ⟨7447364568615786931887503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 79438555398568393940133365 7447364568615786931887503)
        ·
          refine ⟨11171046852923680397831255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7447364568615786931887503 11171046852923680397831255)
          ·
            refine ⟨16756570279385520596746883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11171046852923680397831255 16756570279385520596746883)
            ·
              refine ⟨25134855419078280895120325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16756570279385520596746883 25134855419078280895120325)
              ·
                refine ⟨4712785391077177667835061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25134855419078280895120325 4712785391077177667835061)
                ·
                  refine ⟨441823630413485406359537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4712785391077177667835061 441823630413485406359537)
                  ·
                    rfl

theorem cell23_7744036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 1, 1, 1, 4, 5].length) (baseStart_7744036 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7744036 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7744036 prefixEnd_7744036 := by exact prefixLift 7744036
  have htrace : WordTrace (prefixWord ++ tailWord_7744036) baseStart_7744036 baseEnd_7744036 := by
    simpa [prefixWord, tailWord_7744036, baseEnd_7744036] using wordTrace_append hprefix tailTrace_7744036
  have hstable : (prefixWord ++ tailWord_7744036).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7744036).length < 2 ^ (prefixWord ++ tailWord_7744036).sum := by decide
  have hdescent : baseEnd_7744036 < baseStart_7744036 := by decide
  rcases family_descends (prefixWord ++ tailWord_7744036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7744042 : List Nat := [3, 1, 4, 1, 1, 2, 2, 1, 1, 2, 5]
def baseStart_7744042 : Nat := 118140960795 + 7744042 * 2 ^ 59
def prefixEnd_7744042 : Nat := 4983230072969 + 3 ^ 40 * 7744042 * 2
def baseEnd_7744042 : Nat := 3976415754605295633760805

theorem tailTrace_7744042 : CollatzResearch.WordTrace tailWord_7744042 prefixEnd_7744042 3976415754605295633760805 := by
  unfold tailWord_7744042
  simp only [CollatzResearch.WordTrace]
  refine ⟨70612103952666471480742595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 188298943873777257281980253 70612103952666471480742595)
  ·
    refine ⟨105918155928999707221113893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70612103952666471480742595 105918155928999707221113893)
    ·
      refine ⟨19859654236687445103958855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 105918155928999707221113893 19859654236687445103958855)
      ·
        refine ⟨29789481355031167655938283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19859654236687445103958855 29789481355031167655938283)
        ·
          refine ⟨44684222032546751483907425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29789481355031167655938283 44684222032546751483907425)
          ·
            refine ⟨33513166524410063612930569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44684222032546751483907425 33513166524410063612930569)
            ·
              refine ⟨25134874893307547709697927, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33513166524410063612930569 25134874893307547709697927)
              ·
                refine ⟨37702312339961321564546891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25134874893307547709697927 37702312339961321564546891)
                ·
                  refine ⟨56553468509941982346820337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37702312339961321564546891 56553468509941982346820337)
                  ·
                    refine ⟨42415101382456486760115253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 56553468509941982346820337 42415101382456486760115253)
                    ·
                      refine ⟨3976415754605295633760805, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 42415101382456486760115253 3976415754605295633760805)
                      ·
                        rfl

theorem cell23_7744042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 2, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 2, 2, 1, 1, 2, 5].length) (baseStart_7744042 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7744042 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7744042 prefixEnd_7744042 := by exact prefixLift 7744042
  have htrace : WordTrace (prefixWord ++ tailWord_7744042) baseStart_7744042 baseEnd_7744042 := by
    simpa [prefixWord, tailWord_7744042, baseEnd_7744042] using wordTrace_append hprefix tailTrace_7744042
  have hstable : (prefixWord ++ tailWord_7744042).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7744042).length < 2 ^ (prefixWord ++ tailWord_7744042).sum := by decide
  have hdescent : baseEnd_7744042 < baseStart_7744042 := by decide
  rcases family_descends (prefixWord ++ tailWord_7744042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7744069 : List Nat := [1, 3, 1, 1, 1, 7, 1, 1, 2, 1, 4]
def baseStart_7744069 : Nat := 118140960795 + 7744069 * 2 ^ 59
def prefixEnd_7744069 : Nat := 4983230072969 + 3 ^ 40 * 7744069 * 2
def baseEnd_7744069 : Nat := 3976429618582967028123181

theorem tailTrace_7744069 : CollatzResearch.WordTrace tailWord_7744069 prefixEnd_7744069 3976429618582967028123181 := by
  unfold tailWord_7744069
  simp only [CollatzResearch.WordTrace]
  refine ⟨282449400581568069534203261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188299600387712046356135507 282449400581568069534203261)
  ·
    refine ⟨105918525218088026075326223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 282449400581568069534203261 105918525218088026075326223)
    ·
      refine ⟨158877787827132039112989335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105918525218088026075326223 158877787827132039112989335)
      ·
        refine ⟨238316681740698058669484003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 158877787827132039112989335 238316681740698058669484003)
        ·
          refine ⟨357475022611047088004226005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 238316681740698058669484003 357475022611047088004226005)
          ·
            refine ⟨8378320842446416125099047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 357475022611047088004226005 8378320842446416125099047)
            ·
              refine ⟨12567481263669624187648571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8378320842446416125099047 12567481263669624187648571)
              ·
                refine ⟨18851221895504436281472857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12567481263669624187648571 18851221895504436281472857)
                ·
                  refine ⟨14138416421628327211104643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18851221895504436281472857 14138416421628327211104643)
                  ·
                    refine ⟨21207624632442490816656965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14138416421628327211104643 21207624632442490816656965)
                    ·
                      refine ⟨3976429618582967028123181, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21207624632442490816656965 3976429618582967028123181)
                      ·
                        rfl

theorem cell23_7744069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 7, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 7, 1, 1, 2, 1, 4].length) (baseStart_7744069 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7744069 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7744069 prefixEnd_7744069 := by exact prefixLift 7744069
  have htrace : WordTrace (prefixWord ++ tailWord_7744069) baseStart_7744069 baseEnd_7744069 := by
    simpa [prefixWord, tailWord_7744069, baseEnd_7744069] using wordTrace_append hprefix tailTrace_7744069
  have hstable : (prefixWord ++ tailWord_7744069).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7744069).length < 2 ^ (prefixWord ++ tailWord_7744069).sum := by decide
  have hdescent : baseEnd_7744069 < baseStart_7744069 := by decide
  rcases family_descends (prefixWord ++ tailWord_7744069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7744079 : List Nat := [1, 1, 2, 1, 1, 2, 5, 5, 1, 4]
def baseStart_7744079 : Nat := 118140960795 + 7744079 * 2 ^ 59
def prefixEnd_7744079 : Nat := 4983230072969 + 3 ^ 40 * 7744079 * 2
def baseEnd_7744079 : Nat := 1325478251129837329666045

theorem tailTrace_7744079 : CollatzResearch.WordTrace tailWord_7744079 prefixEnd_7744079 1325478251129837329666045 := by
  unfold tailWord_7744079
  simp only [CollatzResearch.WordTrace]
  refine ⟨282449765311531841242067291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188299843541021227494711527 282449765311531841242067291)
  ·
    refine ⟨423674647967297761863100937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 282449765311531841242067291 423674647967297761863100937)
    ·
      refine ⟨317755985975473321397325703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 423674647967297761863100937 317755985975473321397325703)
      ·
        refine ⟨476633978963209982095988555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 317755985975473321397325703 476633978963209982095988555)
        ·
          refine ⟨714950968444814973143982833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 476633978963209982095988555 714950968444814973143982833)
          ·
            refine ⟨536213226333611229857987125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 714950968444814973143982833 536213226333611229857987125)
            ·
              refine ⟨50269989968776052799186293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 536213226333611229857987125 50269989968776052799186293)
              ·
                refine ⟨4712811559572754949923715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 50269989968776052799186293 4712811559572754949923715)
                ·
                  refine ⟨7069217339359132424885573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4712811559572754949923715 7069217339359132424885573)
                  ·
                    refine ⟨1325478251129837329666045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7069217339359132424885573 1325478251129837329666045)
                    ·
                      rfl

theorem cell23_7744079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 5, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 5, 5, 1, 4].length) (baseStart_7744079 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7744079 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7744079 prefixEnd_7744079 := by exact prefixLift 7744079
  have htrace : WordTrace (prefixWord ++ tailWord_7744079) baseStart_7744079 baseEnd_7744079 := by
    simpa [prefixWord, tailWord_7744079, baseEnd_7744079] using wordTrace_append hprefix tailTrace_7744079
  have hstable : (prefixWord ++ tailWord_7744079).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7744079).length < 2 ^ (prefixWord ++ tailWord_7744079).sum := by decide
  have hdescent : baseEnd_7744079 < baseStart_7744079 := by decide
  rcases family_descends (prefixWord ++ tailWord_7744079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7744119 : List Nat := [1, 1, 3, 1, 1, 3, 4, 2, 3, 1, 3]
def baseStart_7744119 : Nat := 118140960795 + 7744119 * 2 ^ 59
def prefixEnd_7744119 : Nat := 4983230072969 + 3 ^ 40 * 7744119 * 2
def baseEnd_7744119 : Nat := 3976455292615691832497951

theorem tailTrace_7744119 : CollatzResearch.WordTrace tailWord_7744119 prefixEnd_7744119 3976455292615691832497951 := by
  unfold tailWord_7744119
  simp only [CollatzResearch.WordTrace]
  refine ⟨282451224231386928073523411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188300816154257952049015607 282451224231386928073523411)
  ·
    refine ⟨423676836347080392110285117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 282451224231386928073523411 423676836347080392110285117)
    ·
      refine ⟨158878813630155147041356919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 423676836347080392110285117 158878813630155147041356919)
      ·
        refine ⟨238318220445232720562035379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 158878813630155147041356919 238318220445232720562035379)
        ·
          refine ⟨357477330667849080843053069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 238318220445232720562035379 357477330667849080843053069)
          ·
            refine ⟨134053999000443405316144901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 357477330667849080843053069 134053999000443405316144901)
            ·
              refine ⟨25135124812583138496777169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 134053999000443405316144901 25135124812583138496777169)
              ·
                refine ⟨18851343609437353872582877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25135124812583138496777169 18851343609437353872582877)
                ·
                  refine ⟨7069253853539007702218579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18851343609437353872582877 7069253853539007702218579)
                  ·
                    refine ⟨10603880780308511553327869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7069253853539007702218579 10603880780308511553327869)
                    ·
                      refine ⟨3976455292615691832497951, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10603880780308511553327869 3976455292615691832497951)
                      ·
                        rfl

theorem cell23_7744119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 4, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 4, 2, 3, 1, 3].length) (baseStart_7744119 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7744119 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7744119 prefixEnd_7744119 := by exact prefixLift 7744119
  have htrace : WordTrace (prefixWord ++ tailWord_7744119) baseStart_7744119 baseEnd_7744119 := by
    simpa [prefixWord, tailWord_7744119, baseEnd_7744119] using wordTrace_append hprefix tailTrace_7744119
  have hstable : (prefixWord ++ tailWord_7744119).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7744119).length < 2 ^ (prefixWord ++ tailWord_7744119).sum := by decide
  have hdescent : baseEnd_7744119 < baseStart_7744119 := by decide
  rcases family_descends (prefixWord ++ tailWord_7744119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7744129 : List Nat := [1, 2, 4, 2, 1, 1, 1, 3, 1, 5, 2]
def baseStart_7744129 : Nat := 118140960795 + 7744129 * 2 ^ 59
def prefixEnd_7744129 : Nat := 4983230072969 + 3 ^ 40 * 7744129 * 2
def baseEnd_7744129 : Nat := 3976460427422236793372905

theorem tailTrace_7744129 : CollatzResearch.WordTrace tailWord_7744129 prefixEnd_7744129 3976460427422236793372905 := by
  unfold tailWord_7744129
  simp only [CollatzResearch.WordTrace]
  refine ⟨282451588961350699781387441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188301059307567133187591627 282451588961350699781387441)
  ·
    refine ⟨211838691721013024836040581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 282451588961350699781387441 211838691721013024836040581)
    ·
      refine ⟨39719754697689942156757609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 211838691721013024836040581 39719754697689942156757609)
      ·
        refine ⟨29789816023267456617568207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39719754697689942156757609 29789816023267456617568207)
        ·
          refine ⟨44684724034901184926352311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29789816023267456617568207 44684724034901184926352311)
          ·
            refine ⟨67027086052351777389528467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44684724034901184926352311 67027086052351777389528467)
            ·
              refine ⟨100540629078527666084292701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67027086052351777389528467 100540629078527666084292701)
              ·
                refine ⟨37702735904447874781609763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 100540629078527666084292701 37702735904447874781609763)
                ·
                  refine ⟨56554103856671812172414645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37702735904447874781609763 56554103856671812172414645)
                  ·
                    refine ⟨5301947236562982391163873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 56554103856671812172414645 5301947236562982391163873)
                    ·
                      refine ⟨3976460427422236793372905, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5301947236562982391163873 3976460427422236793372905)
                      ·
                        rfl

theorem cell23_7744129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 1, 3, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 1, 3, 1, 5, 2].length) (baseStart_7744129 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7744129 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7744129 prefixEnd_7744129 := by exact prefixLift 7744129
  have htrace : WordTrace (prefixWord ++ tailWord_7744129) baseStart_7744129 baseEnd_7744129 := by
    simpa [prefixWord, tailWord_7744129, baseEnd_7744129] using wordTrace_append hprefix tailTrace_7744129
  have hstable : (prefixWord ++ tailWord_7744129).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7744129).length < 2 ^ (prefixWord ++ tailWord_7744129).sum := by decide
  have hdescent : baseEnd_7744129 < baseStart_7744129 := by decide
  rcases family_descends (prefixWord ++ tailWord_7744129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7744146 : List Nat := [3, 2, 3, 1, 2, 1, 1, 1, 4, 3, 2]
def baseStart_7744146 : Nat := 118140960795 + 7744146 * 2 ^ 59
def prefixEnd_7744146 : Nat := 4983230072969 + 3 ^ 40 * 7744146 * 2
def baseEnd_7744146 : Nat := 3976469156593363226860327

theorem tailTrace_7744146 : CollatzResearch.WordTrace tailWord_7744146 prefixEnd_7744146 3976469156593363226860327 := by
  unfold tailWord_7744146
  simp only [CollatzResearch.WordTrace]
  refine ⟨70613052250572277921189073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 188301472668192741123170861 70613052250572277921189073)
  ·
    refine ⟨52959789187929208440891805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70613052250572277921189073 52959789187929208440891805)
    ·
      refine ⟨19859920945473453165334427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 52959789187929208440891805 19859920945473453165334427)
      ·
        refine ⟨29789881418210179748001641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19859920945473453165334427 29789881418210179748001641)
        ·
          refine ⟨22342411063657634811001231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29789881418210179748001641 22342411063657634811001231)
          ·
            refine ⟨33513616595486452216501847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22342411063657634811001231 33513616595486452216501847)
            ·
              refine ⟨50270424893229678324752771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33513616595486452216501847 50270424893229678324752771)
              ·
                refine ⟨75405637339844517487129157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50270424893229678324752771 75405637339844517487129157)
                ·
                  refine ⟨14138557001220847028836717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 75405637339844517487129157 14138557001220847028836717)
                  ·
                    refine ⟨5301958875457817635813769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14138557001220847028836717 5301958875457817635813769)
                    ·
                      refine ⟨3976469156593363226860327, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5301958875457817635813769 3976469156593363226860327)
                      ·
                        rfl

theorem cell23_7744146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 1, 1, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 1, 1, 1, 4, 3, 2].length) (baseStart_7744146 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7744146 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7744146 prefixEnd_7744146 := by exact prefixLift 7744146
  have htrace : WordTrace (prefixWord ++ tailWord_7744146) baseStart_7744146 baseEnd_7744146 := by
    simpa [prefixWord, tailWord_7744146, baseEnd_7744146] using wordTrace_append hprefix tailTrace_7744146
  have hstable : (prefixWord ++ tailWord_7744146).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7744146).length < 2 ^ (prefixWord ++ tailWord_7744146).sum := by decide
  have hdescent : baseEnd_7744146 < baseStart_7744146 := by decide
  rcases family_descends (prefixWord ++ tailWord_7744146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7744153 : List Nat := [1, 2, 1, 2, 1, 2, 7, 2, 1, 1, 3]
def baseStart_7744153 : Nat := 118140960795 + 7744153 * 2 ^ 59
def prefixEnd_7744153 : Nat := 4983230072969 + 3 ^ 40 * 7744153 * 2
def baseEnd_7744153 : Nat := 3976472750957944699472795

theorem tailTrace_7744153 : CollatzResearch.WordTrace tailWord_7744153 prefixEnd_7744153 3976472750957944699472795 := by
  unfold tailWord_7744153
  simp only [CollatzResearch.WordTrace]
  refine ⟨282452464313263751880261113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188301642875509167920174075 282452464313263751880261113)
  ·
    refine ⟨211839348234947813910195835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 282452464313263751880261113 211839348234947813910195835)
    ·
      refine ⟨317759022352421720865293753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 211839348234947813910195835 317759022352421720865293753)
      ·
        refine ⟨238319266764316290648970315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 317759022352421720865293753 238319266764316290648970315)
        ·
          refine ⟨357478900146474435973455473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 238319266764316290648970315 357478900146474435973455473)
          ·
            refine ⟨268109175109855826980091605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 357478900146474435973455473 268109175109855826980091605)
            ·
              refine ⟨6283808791637245944845897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 268109175109855826980091605 6283808791637245944845897)
              ·
                refine ⟨4712856593727934458634423, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6283808791637245944845897 4712856593727934458634423)
                ·
                  refine ⟨7069284890591901687951635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4712856593727934458634423 7069284890591901687951635)
                  ·
                    refine ⟨10603927335887852531927453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7069284890591901687951635 10603927335887852531927453)
                    ·
                      refine ⟨3976472750957944699472795, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10603927335887852531927453 3976472750957944699472795)
                      ·
                        rfl

theorem cell23_7744153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 7, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 7, 2, 1, 1, 3].length) (baseStart_7744153 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7744153 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7744153 prefixEnd_7744153 := by exact prefixLift 7744153
  have htrace : WordTrace (prefixWord ++ tailWord_7744153) baseStart_7744153 baseEnd_7744153 := by
    simpa [prefixWord, tailWord_7744153, baseEnd_7744153] using wordTrace_append hprefix tailTrace_7744153
  have hstable : (prefixWord ++ tailWord_7744153).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7744153).length < 2 ^ (prefixWord ++ tailWord_7744153).sum := by decide
  have hdescent : baseEnd_7744153 < baseStart_7744153 := by decide
  rcases family_descends (prefixWord ++ tailWord_7744153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7744155 : List Nat := [1, 1, 1, 1, 1, 1, 2, 2, 2, 5, 6]
def baseStart_7744155 : Nat := 118140960795 + 7744155 * 2 ^ 59
def prefixEnd_7744155 : Nat := 4983230072969 + 3 ^ 40 * 7744155 * 2
def baseEnd_7744155 : Nat := 3976473777919253691647785

theorem tailTrace_7744155 : CollatzResearch.WordTrace tailWord_7744155 prefixEnd_7744155 3976473777919253691647785 := by
  unfold tailWord_7744155
  simp only [CollatzResearch.WordTrace]
  refine ⟨282452537259256506221833919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188301691506171004147889279 282452537259256506221833919)
  ·
    refine ⟨423678805888884759332750879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 282452537259256506221833919 423678805888884759332750879)
    ·
      refine ⟨635518208833327138999126319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 423678805888884759332750879 635518208833327138999126319)
      ·
        refine ⟨953277313249990708498689479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 635518208833327138999126319 953277313249990708498689479)
        ·
          refine ⟨1429915969874986062748034219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 953277313249990708498689479 1429915969874986062748034219)
          ·
            refine ⟨2144873954812479094122051329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1429915969874986062748034219 2144873954812479094122051329)
            ·
              refine ⟨1608655466109359320591538497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2144873954812479094122051329 1608655466109359320591538497)
              ·
                refine ⟨1206491599582019490443653873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1608655466109359320591538497 1206491599582019490443653873)
                ·
                  refine ⟨904868699686514617832740405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1206491599582019490443653873 904868699686514617832740405)
                  ·
                    refine ⟨84831440595610745421819413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 904868699686514617832740405 84831440595610745421819413)
                    ·
                      refine ⟨3976473777919253691647785, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 84831440595610745421819413 3976473777919253691647785)
                      ·
                        rfl

theorem cell23_7744155_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 5, 6].length) (baseStart_7744155 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7744155 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7744155 prefixEnd_7744155 := by exact prefixLift 7744155
  have htrace : WordTrace (prefixWord ++ tailWord_7744155) baseStart_7744155 baseEnd_7744155 := by
    simpa [prefixWord, tailWord_7744155, baseEnd_7744155] using wordTrace_append hprefix tailTrace_7744155
  have hstable : (prefixWord ++ tailWord_7744155).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7744155).length < 2 ^ (prefixWord ++ tailWord_7744155).sum := by decide
  have hdescent : baseEnd_7744155 < baseStart_7744155 := by decide
  rcases family_descends (prefixWord ++ tailWord_7744155) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7744179 : List Nat := [1, 1, 1, 2, 3, 5, 1, 1, 3, 2, 3]
def baseStart_7744179 : Nat := 118140960795 + 7744179 * 2 ^ 59
def prefixEnd_7744179 : Nat := 4983230072969 + 3 ^ 40 * 7744179 * 2
def baseEnd_7744179 : Nat := 3976486101454961597747675

theorem tailTrace_7744179 : CollatzResearch.WordTrace tailWord_7744179 prefixEnd_7744179 3976486101454961597747675 := by
  unfold tailWord_7744179
  simp only [CollatzResearch.WordTrace]
  refine ⟨282453412611169558320707591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188302275074113038880471727 282453412611169558320707591)
  ·
    refine ⟨423680118916754337481061387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 282453412611169558320707591 423680118916754337481061387)
    ·
      refine ⟨635520178375131506221592081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 423680118916754337481061387 635520178375131506221592081)
      ·
        refine ⟨476640133781348629666194061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 635520178375131506221592081 476640133781348629666194061)
        ·
          refine ⟨178740050168005736124822773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 476640133781348629666194061 178740050168005736124822773)
          ·
            refine ⟨16756879703250537761702135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 178740050168005736124822773 16756879703250537761702135)
            ·
              refine ⟨25135319554875806642553203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16756879703250537761702135 25135319554875806642553203)
              ·
                refine ⟨37702979332313709963829805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25135319554875806642553203 37702979332313709963829805)
                ·
                  refine ⟨14138617249617641236436177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 37702979332313709963829805 14138617249617641236436177)
                  ·
                    refine ⟨10603962937213230927327133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14138617249617641236436177 10603962937213230927327133)
                    ·
                      refine ⟨3976486101454961597747675, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10603962937213230927327133 3976486101454961597747675)
                      ·
                        rfl

theorem cell23_7744179_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 5, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 5, 1, 1, 3, 2, 3].length) (baseStart_7744179 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7744179 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7744179 prefixEnd_7744179 := by exact prefixLift 7744179
  have htrace : WordTrace (prefixWord ++ tailWord_7744179) baseStart_7744179 baseEnd_7744179 := by
    simpa [prefixWord, tailWord_7744179, baseEnd_7744179] using wordTrace_append hprefix tailTrace_7744179
  have hstable : (prefixWord ++ tailWord_7744179).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7744179).length < 2 ^ (prefixWord ++ tailWord_7744179).sum := by decide
  have hdescent : baseEnd_7744179 < baseStart_7744179 := by decide
  rcases family_descends (prefixWord ++ tailWord_7744179) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7744189 : List Nat := [1, 4, 1, 2, 1, 4, 1, 2, 1, 2, 4]
def baseStart_7744189 : Nat := 118140960795 + 7744189 * 2 ^ 59
def prefixEnd_7744189 : Nat := 4983230072969 + 3 ^ 40 * 7744189 * 2
def baseEnd_7744189 : Nat := 3976491236261506558622629

theorem tailTrace_7744189 : CollatzResearch.WordTrace tailWord_7744189 prefixEnd_7744189 3976491236261506558622629 := by
  unfold tailWord_7744189
  simp only [CollatzResearch.WordTrace]
  refine ⟨282453777341133330028571621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188302518227422220019047747 282453777341133330028571621)
  ·
    refine ⟨52960083251462499380357179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 282453777341133330028571621 52960083251462499380357179)
    ·
      refine ⟨79440124877193749070535769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52960083251462499380357179 79440124877193749070535769)
      ·
        refine ⟨59580093657895311802901827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79440124877193749070535769 59580093657895311802901827)
        ·
          refine ⟨89370140486842967704352741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59580093657895311802901827 89370140486842967704352741)
          ·
            refine ⟨16756901341283056444566139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 89370140486842967704352741 16756901341283056444566139)
            ·
              refine ⟨25135352011924584666849209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16756901341283056444566139 25135352011924584666849209)
              ·
                refine ⟨18851514008943438500136907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25135352011924584666849209 18851514008943438500136907)
                ·
                  refine ⟨28277271013415157750205361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18851514008943438500136907 28277271013415157750205361)
                  ·
                    refine ⟨21207953260061368312654021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 28277271013415157750205361 21207953260061368312654021)
                    ·
                      refine ⟨3976491236261506558622629, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21207953260061368312654021 3976491236261506558622629)
                      ·
                        rfl

theorem cell23_7744189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 4, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 4, 1, 2, 1, 2, 4].length) (baseStart_7744189 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7744189 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7744189 prefixEnd_7744189 := by exact prefixLift 7744189
  have htrace : WordTrace (prefixWord ++ tailWord_7744189) baseStart_7744189 baseEnd_7744189 := by
    simpa [prefixWord, tailWord_7744189, baseEnd_7744189] using wordTrace_append hprefix tailTrace_7744189
  have hstable : (prefixWord ++ tailWord_7744189).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7744189).length < 2 ^ (prefixWord ++ tailWord_7744189).sum := by decide
  have hdescent : baseEnd_7744189 < baseStart_7744189 := by decide
  rcases family_descends (prefixWord ++ tailWord_7744189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7744196 : List Nat := [2, 3, 3, 1, 1, 4, 1, 1, 1, 1, 5]
def baseStart_7744196 : Nat := 118140960795 + 7744196 * 2 ^ 59
def prefixEnd_7744196 : Nat := 4983230072969 + 3 ^ 40 * 7744196 * 2
def baseEnd_7744196 : Nat := 3976494830626088031235097

theorem tailTrace_7744196 : CollatzResearch.WordTrace tailWord_7744196 prefixEnd_7744196 3976494830626088031235097 := by
  unfold tailWord_7744196
  simp only [CollatzResearch.WordTrace]
  refine ⟨141227016326053985112038221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 188302688434738646816050961 141227016326053985112038221)
  ·
    refine ⟨52960131122270244417014333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 141227016326053985112038221 52960131122270244417014333)
    ·
      refine ⟨19860049170851341656380375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 52960131122270244417014333 19860049170851341656380375)
      ·
        refine ⟨29790073756277012484570563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19860049170851341656380375 29790073756277012484570563)
        ·
          refine ⟨44685110634415518726855845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29790073756277012484570563 44685110634415518726855845)
          ·
            refine ⟨8378458243952909761285471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 44685110634415518726855845 8378458243952909761285471)
            ·
              refine ⟨12567687365929364641928207, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8378458243952909761285471 12567687365929364641928207)
              ·
                refine ⟨18851531048894046962892311, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12567687365929364641928207 18851531048894046962892311)
                ·
                  refine ⟨28277296573341070444338467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18851531048894046962892311 28277296573341070444338467)
                  ·
                    refine ⟨42415944860011605666507701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 28277296573341070444338467 42415944860011605666507701)
                    ·
                      refine ⟨3976494830626088031235097, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 42415944860011605666507701 3976494830626088031235097)
                      ·
                        rfl

theorem cell23_7744196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 4, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 4, 1, 1, 1, 1, 5].length) (baseStart_7744196 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7744196 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7744196 prefixEnd_7744196 := by exact prefixLift 7744196
  have htrace : WordTrace (prefixWord ++ tailWord_7744196) baseStart_7744196 baseEnd_7744196 := by
    simpa [prefixWord, tailWord_7744196, baseEnd_7744196] using wordTrace_append hprefix tailTrace_7744196
  have hstable : (prefixWord ++ tailWord_7744196).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7744196).length < 2 ^ (prefixWord ++ tailWord_7744196).sum := by decide
  have hdescent : baseEnd_7744196 < baseStart_7744196 := by decide
  rcases family_descends (prefixWord ++ tailWord_7744196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7744236 : List Nat := [2, 2, 1, 1, 2, 2, 1, 6, 1, 3, 2]
def baseStart_7744236 : Nat := 118140960795 + 7744236 * 2 ^ 59
def prefixEnd_7744236 : Nat := 4983230072969 + 3 ^ 40 * 7744236 * 2
def baseEnd_7744236 : Nat := 3976515369852267874734913

theorem tailTrace_7744236 : CollatzResearch.WordTrace tailWord_7744236 prefixEnd_7744236 3976515369852267874734913 := by
  unfold tailWord_7744236
  simp only [CollatzResearch.WordTrace]
  refine ⟨141227745785981528527766281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 188303661047975371370355041 141227745785981528527766281)
  ·
    refine ⟨105920809339486146395824711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 141227745785981528527766281 105920809339486146395824711)
    ·
      refine ⟨158881214009229219593737067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105920809339486146395824711 158881214009229219593737067)
      ·
        refine ⟨238321821013843829390605601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 158881214009229219593737067 238321821013843829390605601)
        ·
          refine ⟨178741365760382872042954201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 238321821013843829390605601 178741365760382872042954201)
          ·
            refine ⟨134056024320287154032215651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 178741365760382872042954201 134056024320287154032215651)
            ·
              refine ⟨201084036480430731048323477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 134056024320287154032215651 201084036480430731048323477)
              ·
                refine ⟨9425814210020190517890163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 201084036480430731048323477 9425814210020190517890163)
                ·
                  refine ⟨14138721315030285776835245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9425814210020190517890163 14138721315030285776835245)
                  ·
                    refine ⟨5302020493136357166313217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14138721315030285776835245 5302020493136357166313217)
                    ·
                      refine ⟨3976515369852267874734913, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5302020493136357166313217 3976515369852267874734913)
                      ·
                        rfl

theorem cell23_7744236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 1, 3, 2].length) (baseStart_7744236 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7744236 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7744236 prefixEnd_7744236 := by exact prefixLift 7744236
  have htrace : WordTrace (prefixWord ++ tailWord_7744236) baseStart_7744236 baseEnd_7744236 := by
    simpa [prefixWord, tailWord_7744236, baseEnd_7744236] using wordTrace_append hprefix tailTrace_7744236
  have hstable : (prefixWord ++ tailWord_7744236).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7744236).length < 2 ^ (prefixWord ++ tailWord_7744236).sum := by decide
  have hdescent : baseEnd_7744236 < baseStart_7744236 := by decide
  rcases family_descends (prefixWord ++ tailWord_7744236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7744244 : List Nat := [2, 6, 1, 1, 3, 1, 2, 1, 1, 1, 4]
def baseStart_7744244 : Nat := 118140960795 + 7744244 * 2 ^ 59
def prefixEnd_7744244 : Nat := 4983230072969 + 3 ^ 40 * 7744244 * 2
def baseEnd_7744244 : Nat := 3976519477697503843434877

theorem tailTrace_7744244 : CollatzResearch.WordTrace tailWord_7744244 prefixEnd_7744244 3976519477697503843434877 := by
  unfold tailWord_7744244
  simp only [CollatzResearch.WordTrace]
  refine ⟨141227891677967037210911893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 188303855570622716281215857 141227891677967037210911893)
  ·
    refine ⟨6620057422404704869261495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 141227891677967037210911893 6620057422404704869261495)
    ·
      refine ⟨9930086133607057303892243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6620057422404704869261495 9930086133607057303892243)
      ·
        refine ⟨14895129200410585955838365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9930086133607057303892243 14895129200410585955838365)
        ·
          refine ⟨5585673450153969733439387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14895129200410585955838365 5585673450153969733439387)
          ·
            refine ⟨8378510175230954600159081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5585673450153969733439387 8378510175230954600159081)
            ·
              refine ⟨6283882631423215950119311, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8378510175230954600159081 6283882631423215950119311)
              ·
                refine ⟨9425823947134823925178967, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6283882631423215950119311 9425823947134823925178967)
                ·
                  refine ⟨14138735920702235887768451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9425823947134823925178967 14138735920702235887768451)
                  ·
                    refine ⟨21208103881053353831652677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14138735920702235887768451 21208103881053353831652677)
                    ·
                      refine ⟨3976519477697503843434877, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21208103881053353831652677 3976519477697503843434877)
                      ·
                        rfl

theorem cell23_7744244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 3, 1, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 3, 1, 2, 1, 1, 1, 4].length) (baseStart_7744244 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7744244 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7744244 prefixEnd_7744244 := by exact prefixLift 7744244
  have htrace : WordTrace (prefixWord ++ tailWord_7744244) baseStart_7744244 baseEnd_7744244 := by
    simpa [prefixWord, tailWord_7744244, baseEnd_7744244] using wordTrace_append hprefix tailTrace_7744244
  have hstable : (prefixWord ++ tailWord_7744244).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7744244).length < 2 ^ (prefixWord ++ tailWord_7744244).sum := by decide
  have hdescent : baseEnd_7744244 < baseStart_7744244 := by decide
  rcases family_descends (prefixWord ++ tailWord_7744244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7744319 : List Nat := [1, 1, 2, 2, 5, 1, 1, 1, 4, 5]
def baseStart_7744319 : Nat := 118140960795 + 7744319 * 2 ^ 59
def prefixEnd_7744319 : Nat := 4983230072969 + 3 ^ 40 * 7744319 * 2
def baseEnd_7744319 : Nat := 1325519329582197016665677

theorem tailTrace_7744319 : CollatzResearch.WordTrace tailWord_7744319 prefixEnd_7744319 1325519329582197016665677 := by
  unfold tailWord_7744319
  simp only [CollatzResearch.WordTrace]
  refine ⟨282458518830662362230804011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188305679220441574820536007 282458518830662362230804011)
  ·
    refine ⟨423687778245993543346206017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 282458518830662362230804011 423687778245993543346206017)
    ·
      refine ⟨317765833684495157509654513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 423687778245993543346206017 317765833684495157509654513)
      ·
        refine ⟨238324375263371368132240885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 317765833684495157509654513 238324375263371368132240885)
        ·
          refine ⟨22342910180941065762397583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 238324375263371368132240885 22342910180941065762397583)
          ·
            refine ⟨33514365271411598643596375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22342910180941065762397583 33514365271411598643596375)
            ·
              refine ⟨50271547907117397965394563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33514365271411598643596375 50271547907117397965394563)
              ·
                refine ⟨75407321860676096948091845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50271547907117397965394563 75407321860676096948091845)
                ·
                  refine ⟨14138872848876768177767221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 75407321860676096948091845 14138872848876768177767221)
                  ·
                    refine ⟨1325519329582197016665677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14138872848876768177767221 1325519329582197016665677)
                    ·
                      rfl

theorem cell23_7744319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 1, 1, 1, 4, 5].length) (baseStart_7744319 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7744319 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7744319 prefixEnd_7744319 := by exact prefixLift 7744319
  have htrace : WordTrace (prefixWord ++ tailWord_7744319) baseStart_7744319 baseEnd_7744319 := by
    simpa [prefixWord, tailWord_7744319, baseEnd_7744319] using wordTrace_append hprefix tailTrace_7744319
  have hstable : (prefixWord ++ tailWord_7744319).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7744319).length < 2 ^ (prefixWord ++ tailWord_7744319).sum := by decide
  have hdescent : baseEnd_7744319 < baseStart_7744319 := by decide
  rcases family_descends (prefixWord ++ tailWord_7744319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7744329 : List Nat := [1, 2, 1, 1, 2, 6, 1, 1, 1, 2, 5]
def baseStart_7744329 : Nat := 118140960795 + 7744329 * 2 ^ 59
def prefixEnd_7744329 : Nat := 4983230072969 + 3 ^ 40 * 7744329 * 2
def baseEnd_7744329 : Nat := 3976563123553136010871985

theorem tailTrace_7744329 : CollatzResearch.WordTrace tailWord_7744329 prefixEnd_7744329 3976563123553136010871985 := by
  unfold tailWord_7744329
  simp only [CollatzResearch.WordTrace]
  refine ⟨282458883560626133938668041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188305922373750755959112027 282458883560626133938668041)
  ·
    refine ⟨211844162670469600454001031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 282458883560626133938668041 211844162670469600454001031)
    ·
      refine ⟨317766244005704400681001547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 211844162670469600454001031 317766244005704400681001547)
      ·
        refine ⟨476649366008556601021502321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 317766244005704400681001547 476649366008556601021502321)
        ·
          refine ⟨357487024506417450766126741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 476649366008556601021502321 357487024506417450766126741)
          ·
            refine ⟨16757204273738318004662191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 357487024506417450766126741 16757204273738318004662191)
            ·
              refine ⟨25135806410607477006993287, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16757204273738318004662191 25135806410607477006993287)
              ·
                refine ⟨37703709615911215510489931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25135806410607477006993287 37703709615911215510489931)
                ·
                  refine ⟨56555564423866823265734897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37703709615911215510489931 56555564423866823265734897)
                  ·
                    refine ⟨42416673317900117449301173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 56555564423866823265734897 42416673317900117449301173)
                    ·
                      refine ⟨3976563123553136010871985, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 42416673317900117449301173 3976563123553136010871985)
                      ·
                        rfl

theorem cell23_7744329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 6, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 6, 1, 1, 1, 2, 5].length) (baseStart_7744329 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7744329 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7744329 prefixEnd_7744329 := by exact prefixLift 7744329
  have htrace : WordTrace (prefixWord ++ tailWord_7744329) baseStart_7744329 baseEnd_7744329 := by
    simpa [prefixWord, tailWord_7744329, baseEnd_7744329] using wordTrace_append hprefix tailTrace_7744329
  have hstable : (prefixWord ++ tailWord_7744329).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7744329).length < 2 ^ (prefixWord ++ tailWord_7744329).sum := by decide
  have hdescent : baseEnd_7744329 < baseStart_7744329 := by decide
  rcases family_descends (prefixWord ++ tailWord_7744329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7744356 : List Nat := [2, 3, 1, 1, 4, 1, 1, 3, 2, 1, 4]
def baseStart_7744356 : Nat := 118140960795 + 7744356 * 2 ^ 59
def prefixEnd_7744356 : Nat := 4983230072969 + 3 ^ 40 * 7744356 * 2
def baseEnd_7744356 : Nat := 3976576987530807405234361

theorem tailTrace_7744356 : CollatzResearch.WordTrace tailWord_7744356 prefixEnd_7744356 3976576987530807405234361 := by
  unfold tailWord_7744356
  simp only [CollatzResearch.WordTrace]
  refine ⟨141229934165764158774950461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 188306578887685545033267281 141229934165764158774950461)
  ·
    refine ⟨52961225312161559540606423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 141229934165764158774950461 52961225312161559540606423)
    ·
      refine ⟨79441837968242339310909635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52961225312161559540606423 79441837968242339310909635)
      ·
        refine ⟨119162756952363508966364453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79441837968242339310909635 119162756952363508966364453)
        ·
          refine ⟨22343016928568157931193335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 119162756952363508966364453 22343016928568157931193335)
          ·
            refine ⟨33514525392852236896790003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22343016928568157931193335 33514525392852236896790003)
            ·
              refine ⟨50271788089278355345185005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33514525392852236896790003 50271788089278355345185005)
              ·
                refine ⟨18851920533479383254444377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 50271788089278355345185005 18851920533479383254444377)
                ·
                  refine ⟨14138940400109537440833283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18851920533479383254444377 14138940400109537440833283)
                  ·
                    refine ⟨21208410600164306161249925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14138940400109537440833283 21208410600164306161249925)
                    ·
                      refine ⟨3976576987530807405234361, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21208410600164306161249925 3976576987530807405234361)
                      ·
                        rfl

theorem cell23_7744356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 1, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 1, 1, 3, 2, 1, 4].length) (baseStart_7744356 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7744356 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7744356 prefixEnd_7744356 := by exact prefixLift 7744356
  have htrace : WordTrace (prefixWord ++ tailWord_7744356) baseStart_7744356 baseEnd_7744356 := by
    simpa [prefixWord, tailWord_7744356, baseEnd_7744356] using wordTrace_append hprefix tailTrace_7744356
  have hstable : (prefixWord ++ tailWord_7744356).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7744356).length < 2 ^ (prefixWord ++ tailWord_7744356).sum := by decide
  have hdescent : baseEnd_7744356 < baseStart_7744356 := by decide
  rcases family_descends (prefixWord ++ tailWord_7744356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7744379 : List Nat := [1, 1, 1, 1, 1, 5, 3, 4, 6]
def baseStart_7744379 : Nat := 118140960795 + 7744379 * 2 ^ 59
def prefixEnd_7744379 : Nat := 4983230072969 + 3 ^ 40 * 7744379 * 2
def baseEnd_7744379 : Nat := 441843199731762312805195

theorem tailTrace_7744379 : CollatzResearch.WordTrace tailWord_7744379 prefixEnd_7744379 441843199731762312805195 := by
  unfold tailWord_7744379
  simp only [CollatzResearch.WordTrace]
  refine ⟨282460707210444992477988191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188307138140296661651992127 282460707210444992477988191)
  ·
    refine ⟨423691060815667488716982287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 282460707210444992477988191 423691060815667488716982287)
    ·
      refine ⟨635536591223501233075473431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 423691060815667488716982287 635536591223501233075473431)
      ·
        refine ⟨953304886835251849613210147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 635536591223501233075473431 953304886835251849613210147)
        ·
          refine ⟨1429957330252877774419815221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 953304886835251849613210147 1429957330252877774419815221)
          ·
            refine ⟨134058499711207291351857677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 1429957330252877774419815221 134058499711207291351857677)
            ·
              refine ⟨50271937391702734256946629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 134058499711207291351857677 50271937391702734256946629)
              ·
                refine ⟨9425988260944262673177493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 50271937391702734256946629 9425988260944262673177493)
                ·
                  refine ⟨441843199731762312805195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9425988260944262673177493 441843199731762312805195)
                  ·
                    rfl

theorem cell23_7744379_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 3, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 3, 4, 6].length) (baseStart_7744379 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7744379 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7744379 prefixEnd_7744379 := by exact prefixLift 7744379
  have htrace : WordTrace (prefixWord ++ tailWord_7744379) baseStart_7744379 baseEnd_7744379 := by
    simpa [prefixWord, tailWord_7744379, baseEnd_7744379] using wordTrace_append hprefix tailTrace_7744379
  have hstable : (prefixWord ++ tailWord_7744379).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7744379).length < 2 ^ (prefixWord ++ tailWord_7744379).sum := by decide
  have hdescent : baseEnd_7744379 < baseStart_7744379 := by decide
  rcases family_descends (prefixWord ++ tailWord_7744379) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7744410 : List Nat := [3, 1, 1, 4, 3, 2, 1, 1, 2, 2, 3]
def baseStart_7744410 : Nat := 118140960795 + 7744410 * 2 ^ 59
def prefixEnd_7744410 : Nat := 4983230072969 + 3 ^ 40 * 7744410 * 2
def baseEnd_7744410 : Nat := 3976604715486150193959113

theorem tailTrace_7744410 : CollatzResearch.WordTrace tailWord_7744410 prefixEnd_7744410 3976604715486150193959113 := by
  unfold tailWord_7744410
  simp only [CollatzResearch.WordTrace]
  refine ⟨70615459468333171193091671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 188307891915555123181577789 70615459468333171193091671)
  ·
    refine ⟨105923189202499756789637507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70615459468333171193091671 105923189202499756789637507)
    ·
      refine ⟨158884783803749635184456261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105923189202499756789637507 158884783803749635184456261)
      ·
        refine ⟨29790896963203056597085549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 158884783803749635184456261 29790896963203056597085549)
        ·
          refine ⟨11171586361201146223907081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29790896963203056597085549 11171586361201146223907081)
          ·
            refine ⟨8378689770900859667930311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11171586361201146223907081 8378689770900859667930311)
            ·
              refine ⟨12568034656351289501895467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8378689770900859667930311 12568034656351289501895467)
              ·
                refine ⟨18852051984526934252843201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12568034656351289501895467 18852051984526934252843201)
                ·
                  refine ⟨14139038988395200689632401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18852051984526934252843201 14139038988395200689632401)
                  ·
                    refine ⟨10604279241296400517224301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14139038988395200689632401 10604279241296400517224301)
                    ·
                      refine ⟨3976604715486150193959113, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10604279241296400517224301 3976604715486150193959113)
                      ·
                        rfl

theorem cell23_7744410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 3, 2, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 3, 2, 1, 1, 2, 2, 3].length) (baseStart_7744410 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7744410 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7744410 prefixEnd_7744410 := by exact prefixLift 7744410
  have htrace : WordTrace (prefixWord ++ tailWord_7744410) baseStart_7744410 baseEnd_7744410 := by
    simpa [prefixWord, tailWord_7744410, baseEnd_7744410] using wordTrace_append hprefix tailTrace_7744410
  have hstable : (prefixWord ++ tailWord_7744410).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7744410).length < 2 ^ (prefixWord ++ tailWord_7744410).sum := by decide
  have hdescent : baseEnd_7744410 < baseStart_7744410 := by decide
  rcases family_descends (prefixWord ++ tailWord_7744410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7744439 : List Nat := [1, 1, 3, 1, 3, 1, 2, 2, 3, 6]
def baseStart_7744439 : Nat := 118140960795 + 7744439 * 2 ^ 59
def prefixEnd_7744439 : Nat := 4983230072969 + 3 ^ 40 * 7744439 * 2
def baseEnd_7744439 : Nat := 1325539868808376860165493

theorem tailTrace_7744439 : CollatzResearch.WordTrace tailWord_7744439 prefixEnd_7744439 1325539868808376860165493 := by
  unfold tailWord_7744439
  simp only [CollatzResearch.WordTrace]
  refine ⟨282462895590227622725172371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188308597060151748483448247 282462895590227622725172371)
  ·
    refine ⟨423694343385341434087758557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 282462895590227622725172371 423694343385341434087758557)
    ·
      refine ⟨158885378769503037782909459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 423694343385341434087758557 158885378769503037782909459)
      ·
        refine ⟨238328068154254556674364189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 158885378769503037782909459 238328068154254556674364189)
        ·
          refine ⟨89373025557845458752886571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 238328068154254556674364189 89373025557845458752886571)
          ·
            refine ⟨134059538336768188129329857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89373025557845458752886571 134059538336768188129329857)
            ·
              refine ⟨100544653752576141096997393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 134059538336768188129329857 100544653752576141096997393)
              ·
                refine ⟨75408490314432105822748045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 100544653752576141096997393 75408490314432105822748045)
                ·
                  refine ⟨28278183867912039683530517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 75408490314432105822748045 28278183867912039683530517)
                  ·
                    refine ⟨1325539868808376860165493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28278183867912039683530517 1325539868808376860165493)
                    ·
                      rfl

theorem cell23_7744439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 2, 2, 3, 6].length) (baseStart_7744439 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7744439 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7744439 prefixEnd_7744439 := by exact prefixLift 7744439
  have htrace : WordTrace (prefixWord ++ tailWord_7744439) baseStart_7744439 baseEnd_7744439 := by
    simpa [prefixWord, tailWord_7744439, baseEnd_7744439] using wordTrace_append hprefix tailTrace_7744439
  have hstable : (prefixWord ++ tailWord_7744439).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7744439).length < 2 ^ (prefixWord ++ tailWord_7744439).sum := by decide
  have hdescent : baseEnd_7744439 < baseStart_7744439 := by decide
  rcases family_descends (prefixWord ++ tailWord_7744439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7744440 : List Nat := [2, 1, 2, 1, 2, 4, 2, 4, 1, 1, 3]
def baseStart_7744440 : Nat := 118140960795 + 7744440 * 2 ^ 59
def prefixEnd_7744440 : Nat := 4983230072969 + 3 ^ 40 * 7744440 * 2
def baseEnd_7744440 : Nat := 3976620119905785076583975

theorem tailTrace_7744440 : CollatzResearch.WordTrace tailWord_7744440 prefixEnd_7744440 3976620119905785076583975 := by
  unfold tailWord_7744440
  simp only [CollatzResearch.WordTrace]
  refine ⟨141231466031611999947979387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 188308621375482666597305849 141231466031611999947979387)
  ·
    refine ⟨211847199047417999921969081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141231466031611999947979387 211847199047417999921969081)
    ·
      refine ⟨158885399285563499941476811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 211847199047417999921969081 158885399285563499941476811)
      ·
        refine ⟨238328098928345249912215217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 158885399285563499941476811 238328098928345249912215217)
        ·
          refine ⟨178746074196258937434161413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 238328098928345249912215217 178746074196258937434161413)
          ·
            refine ⟨33514888911798550768905265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 178746074196258937434161413 33514888911798550768905265)
            ·
              refine ⟨25136166683848913076678949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33514888911798550768905265 25136166683848913076678949)
              ·
                refine ⟨4713031253221671201877303, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25136166683848913076678949 4713031253221671201877303)
                ·
                  refine ⟨7069546879832506802815955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4713031253221671201877303 7069546879832506802815955)
                  ·
                    refine ⟨10604320319748760204223933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7069546879832506802815955 10604320319748760204223933)
                    ·
                      refine ⟨3976620119905785076583975, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10604320319748760204223933 3976620119905785076583975)
                      ·
                        rfl

theorem cell23_7744440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 4, 2, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 4, 2, 4, 1, 1, 3].length) (baseStart_7744440 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7744440 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7744440 prefixEnd_7744440 := by exact prefixLift 7744440
  have htrace : WordTrace (prefixWord ++ tailWord_7744440) baseStart_7744440 baseEnd_7744440 := by
    simpa [prefixWord, tailWord_7744440, baseEnd_7744440] using wordTrace_append hprefix tailTrace_7744440
  have hstable : (prefixWord ++ tailWord_7744440).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7744440).length < 2 ^ (prefixWord ++ tailWord_7744440).sum := by decide
  have hdescent : baseEnd_7744440 < baseStart_7744440 := by decide
  rcases family_descends (prefixWord ++ tailWord_7744440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7744463 : List Nat := [1, 1, 2, 1, 1, 7, 2, 2, 1, 1, 4]
def baseStart_7744463 : Nat := 118140960795 + 7744463 * 2 ^ 59
def prefixEnd_7744463 : Nat := 4983230072969 + 3 ^ 40 * 7744463 * 2
def baseEnd_7744463 : Nat := 3976631929960838486596369

theorem tailTrace_7744463 : CollatzResearch.WordTrace tailWord_7744463 prefixEnd_7744463 3976631929960838486596369 := by
  unfold tailWord_7744463
  simp only [CollatzResearch.WordTrace]
  refine ⟨282463770942140674824046043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188309180628093783216030695 282463770942140674824046043)
  ·
    refine ⟨423695656413211012236069065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 282463770942140674824046043 423695656413211012236069065)
    ·
      refine ⟨317771742309908259177051799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 423695656413211012236069065 317771742309908259177051799)
      ·
        refine ⟨476657613464862388765577699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 317771742309908259177051799 476657613464862388765577699)
        ·
          refine ⟨714986420197293583148366549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 476657613464862388765577699 714986420197293583148366549)
          ·
            refine ⟨16757494223374068355039841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 714986420197293583148366549 16757494223374068355039841)
            ·
              refine ⟨12568120667530551266279881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16757494223374068355039841 12568120667530551266279881)
              ·
                refine ⟨9426090500647913449709911, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12568120667530551266279881 9426090500647913449709911)
                ·
                  refine ⟨14139135750971870174564867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9426090500647913449709911 14139135750971870174564867)
                  ·
                    refine ⟨21208703626457805261847301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14139135750971870174564867 21208703626457805261847301)
                    ·
                      refine ⟨3976631929960838486596369, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21208703626457805261847301 3976631929960838486596369)
                      ·
                        rfl

theorem cell23_7744463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 7, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 7, 2, 2, 1, 1, 4].length) (baseStart_7744463 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7744463 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7744463 prefixEnd_7744463 := by exact prefixLift 7744463
  have htrace : WordTrace (prefixWord ++ tailWord_7744463) baseStart_7744463 baseEnd_7744463 := by
    simpa [prefixWord, tailWord_7744463, baseEnd_7744463] using wordTrace_append hprefix tailTrace_7744463
  have hstable : (prefixWord ++ tailWord_7744463).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7744463).length < 2 ^ (prefixWord ++ tailWord_7744463).sum := by decide
  have hdescent : baseEnd_7744463 < baseStart_7744463 := by decide
  rcases family_descends (prefixWord ++ tailWord_7744463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7744483 : List Nat := [1, 1, 1, 6, 1, 1, 1, 5, 1, 2, 3]
def baseStart_7744483 : Nat := 118140960795 + 7744483 * 2 ^ 59
def prefixEnd_7744483 : Nat := 4983230072969 + 3 ^ 40 * 7744483 * 2
def baseEnd_7744483 : Nat := 3976642199573928408346277

theorem tailTrace_7744483 : CollatzResearch.WordTrace tailWord_7744483 prefixEnd_7744483 3976642199573928408346277 := by
  unfold tailWord_7744483
  simp only [CollatzResearch.WordTrace]
  refine ⟨282464500402068218239774103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188309666934712145493182735 282464500402068218239774103)
  ·
    refine ⟨423696750603102327359661155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 282464500402068218239774103 423696750603102327359661155)
    ·
      refine ⟨635545125904653491039491733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 423696750603102327359661155 635545125904653491039491733)
      ·
        refine ⟨29791177776780632392476175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 635545125904653491039491733 29791177776780632392476175)
        ·
          refine ⟨44686766665170948588714263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29791177776780632392476175 44686766665170948588714263)
          ·
            refine ⟨67030149997756422883071395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44686766665170948588714263 67030149997756422883071395)
            ·
              refine ⟨100545224996634634324607093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67030149997756422883071395 100545224996634634324607093)
              ·
                refine ⟨9426114843434496967931915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 100545224996634634324607093 9426114843434496967931915)
                ·
                  refine ⟨14139172265151745451897873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9426114843434496967931915 14139172265151745451897873)
                  ·
                    refine ⟨10604379198863809088923405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14139172265151745451897873 10604379198863809088923405)
                    ·
                      refine ⟨3976642199573928408346277, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10604379198863809088923405 3976642199573928408346277)
                      ·
                        rfl

theorem cell23_7744483_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 1, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 1, 5, 1, 2, 3].length) (baseStart_7744483 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7744483 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7744483 prefixEnd_7744483 := by exact prefixLift 7744483
  have htrace : WordTrace (prefixWord ++ tailWord_7744483) baseStart_7744483 baseEnd_7744483 := by
    simpa [prefixWord, tailWord_7744483, baseEnd_7744483] using wordTrace_append hprefix tailTrace_7744483
  have hstable : (prefixWord ++ tailWord_7744483).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7744483).length < 2 ^ (prefixWord ++ tailWord_7744483).sum := by decide
  have hdescent : baseEnd_7744483 < baseStart_7744483 := by decide
  rcases family_descends (prefixWord ++ tailWord_7744483) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7744497 : List Nat := [1, 2, 2, 2, 4, 3, 1, 1, 3, 2, 2]
def baseStart_7744497 : Nat := 118140960795 + 7744497 * 2 ^ 59
def prefixEnd_7744497 : Nat := 4983230072969 + 3 ^ 40 * 7744497 * 2
def baseEnd_7744497 : Nat := 3976649388303091353571213

theorem tailTrace_7744497 : CollatzResearch.WordTrace tailWord_7744497 prefixEnd_7744497 3976649388303091353571213 := by
  unfold tailWord_7744497
  simp only [CollatzResearch.WordTrace]
  refine ⟨282465011024017498630783745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188310007349344999087189163 282465011024017498630783745)
  ·
    refine ⟨211848758268013123973087809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 282465011024017498630783745 211848758268013123973087809)
    ·
      refine ⟨158886568701009842979815857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 211848758268013123973087809 158886568701009842979815857)
      ·
        refine ⟨119164926525757382234861893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 158886568701009842979815857 119164926525757382234861893)
        ·
          refine ⟨22343423723579509169036605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 119164926525757382234861893 22343423723579509169036605)
          ·
            refine ⟨8378783896342315938388727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22343423723579509169036605 8378783896342315938388727)
            ·
              refine ⟨12568175844513473907583091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8378783896342315938388727 12568175844513473907583091)
              ·
                refine ⟨18852263766770210861374637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12568175844513473907583091 18852263766770210861374637)
                ·
                  refine ⟨7069598912538829073015489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18852263766770210861374637 7069598912538829073015489)
                  ·
                    refine ⟨5302199184404121804761617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7069598912538829073015489 5302199184404121804761617)
                    ·
                      refine ⟨3976649388303091353571213, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5302199184404121804761617 3976649388303091353571213)
                      ·
                        rfl

theorem cell23_7744497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 3, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 3, 1, 1, 3, 2, 2].length) (baseStart_7744497 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7744497 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7744497 prefixEnd_7744497 := by exact prefixLift 7744497
  have htrace : WordTrace (prefixWord ++ tailWord_7744497) baseStart_7744497 baseEnd_7744497 := by
    simpa [prefixWord, tailWord_7744497, baseEnd_7744497] using wordTrace_append hprefix tailTrace_7744497
  have hstable : (prefixWord ++ tailWord_7744497).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7744497).length < 2 ^ (prefixWord ++ tailWord_7744497).sum := by decide
  have hdescent : baseEnd_7744497 < baseStart_7744497 := by decide
  rcases family_descends (prefixWord ++ tailWord_7744497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7744514 : List Nat := [3, 4, 1, 3, 1, 2, 1, 2, 1, 1, 4]
def baseStart_7744514 : Nat := 118140960795 + 7744514 * 2 ^ 59
def prefixEnd_7744514 : Nat := 4983230072969 + 3 ^ 40 * 7744514 * 2
def baseEnd_7744514 : Nat := 3976658117474217787058635

theorem tailTrace_7744514 : CollatzResearch.WordTrace tailWord_7744514 prefixEnd_7744514 3976658117474217787058635 := by
  unfold tailWord_7744514
  simp only [CollatzResearch.WordTrace]
  refine ⟨70616407766238977633538149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 188310420709970607022768397 70616407766238977633538149)
  ·
    refine ⟨13240576456169808306288403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 70616407766238977633538149 13240576456169808306288403)
    ·
      refine ⟨19860864684254712459432605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13240576456169808306288403 19860864684254712459432605)
      ·
        refine ⟨7447824256595517172287227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19860864684254712459432605 7447824256595517172287227)
        ·
          refine ⟨11171736384893275758430841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7447824256595517172287227 11171736384893275758430841)
          ·
            refine ⟨8378802288669956818823131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11171736384893275758430841 8378802288669956818823131)
            ·
              refine ⟨12568203433004935228234697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8378802288669956818823131 12568203433004935228234697)
              ·
                refine ⟨9426152574753701421176023, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12568203433004935228234697 9426152574753701421176023)
                ·
                  refine ⟨14139228862130552131764035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9426152574753701421176023 14139228862130552131764035)
                  ·
                    refine ⟨21208843293195828197646053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14139228862130552131764035 21208843293195828197646053)
                    ·
                      refine ⟨3976658117474217787058635, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21208843293195828197646053 3976658117474217787058635)
                      ·
                        rfl

theorem cell23_7744514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 1, 2, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 1, 2, 1, 2, 1, 1, 4].length) (baseStart_7744514 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7744514 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7744514 prefixEnd_7744514 := by exact prefixLift 7744514
  have htrace : WordTrace (prefixWord ++ tailWord_7744514) baseStart_7744514 baseEnd_7744514 := by
    simpa [prefixWord, tailWord_7744514, baseEnd_7744514] using wordTrace_append hprefix tailTrace_7744514
  have hstable : (prefixWord ++ tailWord_7744514).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7744514).length < 2 ^ (prefixWord ++ tailWord_7744514).sum := by decide
  have hdescent : baseEnd_7744514 < baseStart_7744514 := by decide
  rcases family_descends (prefixWord ++ tailWord_7744514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7744556 : List Nat := [2, 2, 1, 1, 1, 2, 3, 1, 1, 6, 3]
def baseStart_7744556 : Nat := 118140960795 + 7744556 * 2 ^ 59
def prefixEnd_7744556 : Nat := 4983230072969 + 3 ^ 40 * 7744556 * 2
def baseEnd_7744556 : Nat := 3976679683661706622733441

theorem tailTrace_7744556 : CollatzResearch.WordTrace tailWord_7744556 prefixEnd_7744556 3976679683661706622733441 := by
  unfold tailWord_7744556
  simp only [CollatzResearch.WordTrace]
  refine ⟨141233581465401875853590761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 188311441953869167804787681 141233581465401875853590761)
  ·
    refine ⟨105925186099051406890193071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 141233581465401875853590761 105925186099051406890193071)
    ·
      refine ⟨158887779148577110335289607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105925186099051406890193071 158887779148577110335289607)
      ·
        refine ⟨238331668722865665502934411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 158887779148577110335289607 238331668722865665502934411)
        ·
          refine ⟨357497503084298498254401617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 238331668722865665502934411 357497503084298498254401617)
          ·
            refine ⟨268123127313223873690801213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 357497503084298498254401617 268123127313223873690801213)
            ·
              refine ⟨100546172742458952634050455, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 268123127313223873690801213 100546172742458952634050455)
              ·
                refine ⟨150819259113688428951075683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 100546172742458952634050455 150819259113688428951075683)
                ·
                  refine ⟨226228888670532643426613525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 150819259113688428951075683 226228888670532643426613525)
                  ·
                    refine ⟨10604479156431217660622509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 226228888670532643426613525 10604479156431217660622509)
                    ·
                      refine ⟨3976679683661706622733441, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10604479156431217660622509 3976679683661706622733441)
                      ·
                        rfl

theorem cell23_7744556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 6, 3].length) (baseStart_7744556 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7744556 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7744556 prefixEnd_7744556 := by exact prefixLift 7744556
  have htrace : WordTrace (prefixWord ++ tailWord_7744556) baseStart_7744556 baseEnd_7744556 := by
    simpa [prefixWord, tailWord_7744556, baseEnd_7744556] using wordTrace_append hprefix tailTrace_7744556
  have hstable : (prefixWord ++ tailWord_7744556).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7744556).length < 2 ^ (prefixWord ++ tailWord_7744556).sum := by decide
  have hdescent : baseEnd_7744556 < baseStart_7744556 := by decide
  rcases family_descends (prefixWord ++ tailWord_7744556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7744576 : List Nat := [2, 1, 1, 2, 2, 3, 3, 2, 7]
def baseStart_7744576 : Nat := 118140960795 + 7744576 * 2 ^ 59
def prefixEnd_7744576 : Nat := 4983230072969 + 3 ^ 40 * 7744576 * 2
def baseEnd_7744576 : Nat := 441854439252755171609261

theorem tailTrace_7744576 : CollatzResearch.WordTrace tailWord_7744576 prefixEnd_7744576 441854439252755171609261 := by
  unfold tailWord_7744576
  simp only [CollatzResearch.WordTrace]
  refine ⟨141233946195365647561454791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 188311928260487530081939721 141233946195365647561454791)
  ·
    refine ⟨211850919293048471342182187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141233946195365647561454791 211850919293048471342182187)
    ·
      refine ⟨317776378939572707013273281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 211850919293048471342182187 317776378939572707013273281)
      ·
        refine ⟨238332284204679530259954961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 317776378939572707013273281 238332284204679530259954961)
        ·
          refine ⟨178749213153509647694966221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 238332284204679530259954961 178749213153509647694966221)
          ·
            refine ⟨67030954932566117885612333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 178749213153509647694966221 67030954932566117885612333)
            ·
              refine ⟨25136608099712294207104625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 67030954932566117885612333 25136608099712294207104625)
              ·
                refine ⟨18852456074784220655328469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25136608099712294207104625 18852456074784220655328469)
                ·
                  refine ⟨441854439252755171609261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18852456074784220655328469 441854439252755171609261)
                  ·
                    rfl

theorem cell23_7744576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 3, 2, 7].length) (baseStart_7744576 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7744576 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7744576 prefixEnd_7744576 := by exact prefixLift 7744576
  have htrace : WordTrace (prefixWord ++ tailWord_7744576) baseStart_7744576 baseEnd_7744576 := by
    simpa [prefixWord, tailWord_7744576, baseEnd_7744576] using wordTrace_append hprefix tailTrace_7744576
  have hstable : (prefixWord ++ tailWord_7744576).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7744576).length < 2 ^ (prefixWord ++ tailWord_7744576).sum := by decide
  have hdescent : baseEnd_7744576 < baseStart_7744576 := by decide
  rcases family_descends (prefixWord ++ tailWord_7744576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7744593 : List Nat := [1, 2, 2, 1, 3, 1, 3, 5, 5]
def baseStart_7744593 : Nat := 118140960795 + 7744593 * 2 ^ 59
def prefixEnd_7744593 : Nat := 4983230072969 + 3 ^ 40 * 7744593 * 2
def baseEnd_7744593 : Nat := 441855409160658108663419

theorem tailTrace_7744593 : CollatzResearch.WordTrace tailWord_7744593 prefixEnd_7744593 441855409160658108663419 := by
  unfold tailWord_7744593
  simp only [CollatzResearch.WordTrace]
  refine ⟨282468512431669707026278433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188312341621113138017518955 282468512431669707026278433)
  ·
    refine ⟨211851384323752280269708825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 282468512431669707026278433 211851384323752280269708825)
    ·
      refine ⟨158888538242814210202281619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 211851384323752280269708825 158888538242814210202281619)
      ·
        refine ⟨238332807364221315303422429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 158888538242814210202281619 238332807364221315303422429)
        ·
          refine ⟨89374802761582993238783411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 238332807364221315303422429 89374802761582993238783411)
          ·
            refine ⟨134062204142374489858175117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89374802761582993238783411 134062204142374489858175117)
            ·
              refine ⟨50273326553390433696815669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 134062204142374489858175117 50273326553390433696815669)
              ·
                refine ⟨4713124364380353159076469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 50273326553390433696815669 4713124364380353159076469)
                ·
                  refine ⟨441855409160658108663419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4713124364380353159076469 441855409160658108663419)
                  ·
                    rfl

theorem cell23_7744593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 3, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 3, 5, 5].length) (baseStart_7744593 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7744593 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7744593 prefixEnd_7744593 := by exact prefixLift 7744593
  have htrace : WordTrace (prefixWord ++ tailWord_7744593) baseStart_7744593 baseEnd_7744593 := by
    simpa [prefixWord, tailWord_7744593, baseEnd_7744593] using wordTrace_append hprefix tailTrace_7744593
  have hstable : (prefixWord ++ tailWord_7744593).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7744593).length < 2 ^ (prefixWord ++ tailWord_7744593).sum := by decide
  have hdescent : baseEnd_7744593 < baseStart_7744593 := by decide
  rcases family_descends (prefixWord ++ tailWord_7744593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7744598 : List Nat := [5, 2, 2, 1, 3, 1, 1, 2, 2, 1, 3]
def baseStart_7744598 : Nat := 118140960795 + 7744598 * 2 ^ 59
def prefixEnd_7744598 : Nat := 4983230072969 + 3 ^ 40 * 7744598 * 2
def baseEnd_7744598 : Nat := 3976701249849195458408249

theorem tailTrace_7744598 : CollatzResearch.WordTrace tailWord_7744598 prefixEnd_7744598 3976701249849195458408249 := by
  unfold tailWord_7744598
  simp only [CollatzResearch.WordTrace]
  refine ⟨17654293424790724555013153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 188312463197767728586806965 17654293424790724555013153)
  ·
    refine ⟨13240720068593043416259865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17654293424790724555013153 13240720068593043416259865)
    ·
      refine ⟨9930540051444782562194899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13240720068593043416259865 9930540051444782562194899)
      ·
        refine ⟨14895810077167173843292349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9930540051444782562194899 14895810077167173843292349)
        ·
          refine ⟨5585928778937690191234631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14895810077167173843292349 5585928778937690191234631)
          ·
            refine ⟨8378893168406535286851947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5585928778937690191234631 8378893168406535286851947)
            ·
              refine ⟨12568339752609802930277921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8378893168406535286851947 12568339752609802930277921)
              ·
                refine ⟨9426254814457352197708441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12568339752609802930277921 9426254814457352197708441)
                ·
                  refine ⟨7069691110843014148281331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9426254814457352197708441 7069691110843014148281331)
                  ·
                    refine ⟨10604536666264521222421997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7069691110843014148281331 10604536666264521222421997)
                    ·
                      refine ⟨3976701249849195458408249, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10604536666264521222421997 3976701249849195458408249)
                      ·
                        rfl

theorem cell23_7744598_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 3, 1, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 3, 1, 1, 2, 2, 1, 3].length) (baseStart_7744598 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7744598 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7744598 prefixEnd_7744598 := by exact prefixLift 7744598
  have htrace : WordTrace (prefixWord ++ tailWord_7744598) baseStart_7744598 baseEnd_7744598 := by
    simpa [prefixWord, tailWord_7744598, baseEnd_7744598] using wordTrace_append hprefix tailTrace_7744598
  have hstable : (prefixWord ++ tailWord_7744598).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7744598).length < 2 ^ (prefixWord ++ tailWord_7744598).sum := by decide
  have hdescent : baseEnd_7744598 < baseStart_7744598 := by decide
  rcases family_descends (prefixWord ++ tailWord_7744598) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7744610 : List Nat := [3, 3, 2, 2, 1, 2, 2, 1, 7]
def baseStart_7744610 : Nat := 118140960795 + 7744610 * 2 ^ 59
def prefixEnd_7744610 : Nat := 4983230072969 + 3 ^ 40 * 7744610 * 2
def baseEnd_7744610 : Nat := 441856379068561045717577

theorem tailTrace_7744610 : CollatzResearch.WordTrace tailWord_7744610 prefixEnd_7744610 441856379068561045717577 := by
  unfold tailWord_7744610
  simp only [CollatzResearch.WordTrace]
  refine ⟨70617283118152029732411821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 188312754981738745953098189 70617283118152029732411821)
  ·
    refine ⟨26481481169307011149654433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 70617283118152029732411821 26481481169307011149654433)
    ·
      refine ⟨19861110876980258362240825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26481481169307011149654433 19861110876980258362240825)
      ·
        refine ⟨14895833157735193771680619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19861110876980258362240825 14895833157735193771680619)
        ·
          refine ⟨22343749736602790657520929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14895833157735193771680619 22343749736602790657520929)
          ·
            refine ⟨16757812302452092993140697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22343749736602790657520929 16757812302452092993140697)
            ·
              refine ⟨12568359226839069744855523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16757812302452092993140697 12568359226839069744855523)
              ·
                refine ⟨18852538840258604617283285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12568359226839069744855523 18852538840258604617283285)
                ·
                  refine ⟨441856379068561045717577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18852538840258604617283285 441856379068561045717577)
                  ·
                    rfl

theorem cell23_7744610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 2, 2, 1, 7].length) (baseStart_7744610 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7744610 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7744610 prefixEnd_7744610 := by exact prefixLift 7744610
  have htrace : WordTrace (prefixWord ++ tailWord_7744610) baseStart_7744610 baseEnd_7744610 := by
    simpa [prefixWord, tailWord_7744610, baseEnd_7744610] using wordTrace_append hprefix tailTrace_7744610
  have hstable : (prefixWord ++ tailWord_7744610).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7744610).length < 2 ^ (prefixWord ++ tailWord_7744610).sum := by decide
  have hdescent : baseEnd_7744610 < baseStart_7744610 := by decide
  rcases family_descends (prefixWord ++ tailWord_7744610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7744636 : List Nat := [2, 2, 2, 1, 1, 3, 1, 1, 2, 8]
def baseStart_7744636 : Nat := 118140960795 + 7744636 * 2 ^ 59
def prefixEnd_7744636 : Nat := 4983230072969 + 3 ^ 40 * 7744636 * 2
def baseEnd_7744636 : Nat := 1325573587371355436577691

theorem tailTrace_7744636 : CollatzResearch.WordTrace tailWord_7744636 prefixEnd_7744636 1325573587371355436577691 := by
  unfold tailWord_7744636
  simp only [CollatzResearch.WordTrace]
  refine ⟨141235040385256962685046881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 188313387180342616913395841 141235040385256962685046881)
  ·
    refine ⟨105926280288942722013785161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 141235040385256962685046881 105926280288942722013785161)
    ·
      refine ⟨79444710216707041510338871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 105926280288942722013785161 79444710216707041510338871)
      ·
        refine ⟨119167065325060562265508307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79444710216707041510338871 119167065325060562265508307)
        ·
          refine ⟨178750597987590843398262461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 119167065325060562265508307 178750597987590843398262461)
          ·
            refine ⟨67031474245346566274348423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 178750597987590843398262461 67031474245346566274348423)
            ·
              refine ⟨100547211368019849411522635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67031474245346566274348423 100547211368019849411522635)
              ·
                refine ⟨150820817052029774117283953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 100547211368019849411522635 150820817052029774117283953)
                ·
                  refine ⟨113115612789022330587962965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 150820817052029774117283953 113115612789022330587962965)
                  ·
                    refine ⟨1325573587371355436577691, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 113115612789022330587962965 1325573587371355436577691)
                    ·
                      rfl

theorem cell23_7744636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 1, 1, 2, 8].length) (baseStart_7744636 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7744636 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7744636 prefixEnd_7744636 := by exact prefixLift 7744636
  have htrace : WordTrace (prefixWord ++ tailWord_7744636) baseStart_7744636 baseEnd_7744636 := by
    simpa [prefixWord, tailWord_7744636, baseEnd_7744636] using wordTrace_append hprefix tailTrace_7744636
  have hstable : (prefixWord ++ tailWord_7744636).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7744636).length < 2 ^ (prefixWord ++ tailWord_7744636).sum := by decide
  have hdescent : baseEnd_7744636 < baseStart_7744636 := by decide
  rcases family_descends (prefixWord ++ tailWord_7744636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7744643 : List Nat := [1, 1, 1, 3, 3, 2, 2, 3, 2, 1, 4]
def baseStart_7744643 : Nat := 118140960795 + 7744643 * 2 ^ 59
def prefixEnd_7744643 : Nat := 4983230072969 + 3 ^ 40 * 7744643 * 2
def baseEnd_7744643 : Nat := 3976724356478647782345541

theorem tailTrace_7744643 : CollatzResearch.WordTrace tailWord_7744643 prefixEnd_7744643 3976724356478647782345541 := by
  unfold tailWord_7744643
  simp only [CollatzResearch.WordTrace]
  refine ⟨282470336081488565565598583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188313557387659043710399055 282470336081488565565598583)
  ·
    refine ⟨423705504122232848348397875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 282470336081488565565598583 423705504122232848348397875)
    ·
      refine ⟨635558256183349272522596813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 423705504122232848348397875 635558256183349272522596813)
      ·
        refine ⟨238334346068755977195973805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 635558256183349272522596813 238334346068755977195973805)
        ·
          refine ⟨89375379775783491448490177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 238334346068755977195973805 89375379775783491448490177)
          ·
            refine ⟨67031534831837618586367633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 89375379775783491448490177 67031534831837618586367633)
            ·
              refine ⟨50273651123878213939775725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 67031534831837618586367633 50273651123878213939775725)
              ·
                refine ⟨18852619171454330227415897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 50273651123878213939775725 18852619171454330227415897)
                ·
                  refine ⟨14139464378590747670561923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18852619171454330227415897 14139464378590747670561923)
                  ·
                    refine ⟨21209196567886121505842885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14139464378590747670561923 21209196567886121505842885)
                    ·
                      refine ⟨3976724356478647782345541, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21209196567886121505842885 3976724356478647782345541)
                      ·
                        rfl

theorem cell23_7744643_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 2, 3, 2, 1, 4].length) (baseStart_7744643 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7744643 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7744643 prefixEnd_7744643 := by exact prefixLift 7744643
  have htrace : WordTrace (prefixWord ++ tailWord_7744643) baseStart_7744643 baseEnd_7744643 := by
    simpa [prefixWord, tailWord_7744643, baseEnd_7744643] using wordTrace_append hprefix tailTrace_7744643
  have hstable : (prefixWord ++ tailWord_7744643).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7744643).length < 2 ^ (prefixWord ++ tailWord_7744643).sum := by decide
  have hdescent : baseEnd_7744643 < baseStart_7744643 := by decide
  rcases family_descends (prefixWord ++ tailWord_7744643) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7744656 : List Nat := [2, 1, 1, 1, 1, 1, 4, 3, 2, 1, 6]
def baseStart_7744656 : Nat := 118140960795 + 7744656 * 2 ^ 59
def prefixEnd_7744656 : Nat := 4983230072969 + 3 ^ 40 * 7744656 * 2
def baseEnd_7744656 : Nat := 3976731031727156231482981

theorem tailTrace_7744656 : CollatzResearch.WordTrace tailWord_7744656 prefixEnd_7744656 3976731031727156231482981 := by
  unfold tailWord_7744656
  simp only [CollatzResearch.WordTrace]
  refine ⟨141235405115220734392910911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 188313873486960979190547881 141235405115220734392910911)
  ·
    refine ⟨211853107672831101589366367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141235405115220734392910911 211853107672831101589366367)
    ·
      refine ⟨317779661509246652384049551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 211853107672831101589366367 317779661509246652384049551)
      ·
        refine ⟨476669492263869978576074327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 317779661509246652384049551 476669492263869978576074327)
        ·
          refine ⟨715004238395804967864111491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 476669492263869978576074327 715004238395804967864111491)
          ·
            refine ⟨1072506357593707451796167237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 715004238395804967864111491 1072506357593707451796167237)
            ·
              refine ⟨201094942048820147211781357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1072506357593707451796167237 201094942048820147211781357)
              ·
                refine ⟨75410603268307555204418009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 201094942048820147211781357 75410603268307555204418009)
                ·
                  refine ⟨56557952451230666403313507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 75410603268307555204418009 56557952451230666403313507)
                  ·
                    refine ⟨84836928676845999604970261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 56557952451230666403313507 84836928676845999604970261)
                    ·
                      refine ⟨3976731031727156231482981, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 84836928676845999604970261 3976731031727156231482981)
                      ·
                        rfl

theorem cell23_7744656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 4, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 4, 3, 2, 1, 6].length) (baseStart_7744656 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7744656 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7744656 prefixEnd_7744656 := by exact prefixLift 7744656
  have htrace : WordTrace (prefixWord ++ tailWord_7744656) baseStart_7744656 baseEnd_7744656 := by
    simpa [prefixWord, tailWord_7744656, baseEnd_7744656] using wordTrace_append hprefix tailTrace_7744656
  have hstable : (prefixWord ++ tailWord_7744656).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7744656).length < 2 ^ (prefixWord ++ tailWord_7744656).sum := by decide
  have hdescent : baseEnd_7744656 < baseStart_7744656 := by decide
  rcases family_descends (prefixWord ++ tailWord_7744656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7744750 : List Nat := [4, 1, 2, 1, 1, 1, 4, 1, 3, 1, 4]
def baseStart_7744750 : Nat := 118140960795 + 7744750 * 2 ^ 59
def prefixEnd_7744750 : Nat := 4983230072969 + 3 ^ 40 * 7744750 * 2
def baseEnd_7744750 : Nat := 3976779298908678863707549

theorem tailTrace_7744750 : CollatzResearch.WordTrace tailWord_7744750 prefixEnd_7744750 3976779298908678863707549 := by
  unfold tailWord_7744750
  simp only [CollatzResearch.WordTrace]
  refine ⟨35309279836512615354967963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 188316159128067281893162469 35309279836512615354967963)
  ·
    refine ⟨52963919754768923032451945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35309279836512615354967963 52963919754768923032451945)
    ·
      refine ⟨39722939816076692274338959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52963919754768923032451945 39722939816076692274338959)
      ·
        refine ⟨59584409724115038411508439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39722939816076692274338959 59584409724115038411508439)
        ·
          refine ⟨89376614586172557617262659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59584409724115038411508439 89376614586172557617262659)
          ·
            refine ⟨134064921879258836425893989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89376614586172557617262659 134064921879258836425893989)
            ·
              refine ⟨25137172852361031829855123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 134064921879258836425893989 25137172852361031829855123)
              ·
                refine ⟨37705759278541547744782685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25137172852361031829855123 37705759278541547744782685)
                ·
                  refine ⟨14139659729453080404293507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 37705759278541547744782685 14139659729453080404293507)
                  ·
                    refine ⟨21209489594179620606440261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14139659729453080404293507 21209489594179620606440261)
                    ·
                      refine ⟨3976779298908678863707549, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21209489594179620606440261 3976779298908678863707549)
                      ·
                        rfl

theorem cell23_7744750_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 4, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 4, 1, 3, 1, 4].length) (baseStart_7744750 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7744750 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7744750 prefixEnd_7744750 := by exact prefixLift 7744750
  have htrace : WordTrace (prefixWord ++ tailWord_7744750) baseStart_7744750 baseEnd_7744750 := by
    simpa [prefixWord, tailWord_7744750, baseEnd_7744750] using wordTrace_append hprefix tailTrace_7744750
  have hstable : (prefixWord ++ tailWord_7744750).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7744750).length < 2 ^ (prefixWord ++ tailWord_7744750).sum := by decide
  have hdescent : baseEnd_7744750 < baseStart_7744750 := by decide
  rcases family_descends (prefixWord ++ tailWord_7744750) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7744764 : List Nat := [2, 2, 2, 1, 5, 2, 2, 1, 1, 5]
def baseStart_7744764 : Nat := 118140960795 + 7744764 * 2 ^ 59
def prefixEnd_7744764 : Nat := 4983230072969 + 3 ^ 40 * 7744764 * 2
def baseEnd_7744764 : Nat := 1325595495879280602977495

theorem tailTrace_7744764 : CollatzResearch.WordTrace tailWord_7744764 prefixEnd_7744764 1325595495879280602977495 := by
  unfold tailWord_7744764
  simp only [CollatzResearch.WordTrace]
  refine ⟨141237374657025101615376673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 188316499542700135487168897 141237374657025101615376673)
  ·
    refine ⟨105928030992768826211532505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 141237374657025101615376673 105928030992768826211532505)
    ·
      refine ⟨79446023244576619658649379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 105928030992768826211532505 79446023244576619658649379)
      ·
        refine ⟨119169034866864929487974069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79446023244576619658649379 119169034866864929487974069)
        ·
          refine ⟨11172097018768587139497569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 119169034866864929487974069 11172097018768587139497569)
          ·
            refine ⟨8379072764076440354623177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11172097018768587139497569 8379072764076440354623177)
            ·
              refine ⟨6284304573057330265967383, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8379072764076440354623177 6284304573057330265967383)
              ·
                refine ⟨9426456859585995398951075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6284304573057330265967383 9426456859585995398951075)
                ·
                  refine ⟨14139685289378993098426613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9426456859585995398951075 14139685289378993098426613)
                  ·
                    refine ⟨1325595495879280602977495, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14139685289378993098426613 1325595495879280602977495)
                    ·
                      rfl

theorem cell23_7744764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 5, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 5, 2, 2, 1, 1, 5].length) (baseStart_7744764 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7744764 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7744764 prefixEnd_7744764 := by exact prefixLift 7744764
  have htrace : WordTrace (prefixWord ++ tailWord_7744764) baseStart_7744764 baseEnd_7744764 := by
    simpa [prefixWord, tailWord_7744764, baseEnd_7744764] using wordTrace_append hprefix tailTrace_7744764
  have hstable : (prefixWord ++ tailWord_7744764).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7744764).length < 2 ^ (prefixWord ++ tailWord_7744764).sum := by decide
  have hdescent : baseEnd_7744764 < baseStart_7744764 := by decide
  rcases family_descends (prefixWord ++ tailWord_7744764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7744767 : List Nat := [1, 1, 2, 2, 1, 5, 4, 1, 1, 1, 4]
def baseStart_7744767 : Nat := 118140960795 + 7744767 * 2 ^ 59
def prefixEnd_7744767 : Nat := 4983230072969 + 3 ^ 40 * 7744767 * 2
def baseEnd_7744767 : Nat := 3976788028079805297194971

theorem tailTrace_7744767 : CollatzResearch.WordTrace tailWord_7744767 prefixEnd_7744767 3976788028079805297194971 := by
  unfold tailWord_7744767
  simp only [CollatzResearch.WordTrace]
  refine ⟨282474858733039334743112555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188316572488692889828741703 282474858733039334743112555)
  ·
    refine ⟨423712288099559002114668833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 282474858733039334743112555 423712288099559002114668833)
    ·
      refine ⟨317784216074669251586001625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 423712288099559002114668833 317784216074669251586001625)
      ·
        refine ⟨238338162056001938689501219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 317784216074669251586001625 238338162056001938689501219)
        ·
          refine ⟨357507243084002908034251829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 238338162056001938689501219 357507243084002908034251829)
          ·
            refine ⟨33516304039125272628211109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 357507243084002908034251829 33516304039125272628211109)
            ·
              refine ⟨6284307007335988617789583, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 33516304039125272628211109 6284307007335988617789583)
              ·
                refine ⟨9426460511003982926684375, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6284307007335988617789583 9426460511003982926684375)
                ·
                  refine ⟨14139690766505974390026563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9426460511003982926684375 14139690766505974390026563)
                  ·
                    refine ⟨21209536149758961585039845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14139690766505974390026563 21209536149758961585039845)
                    ·
                      refine ⟨3976788028079805297194971, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21209536149758961585039845 3976788028079805297194971)
                      ·
                        rfl

theorem cell23_7744767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 5, 4, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 5, 4, 1, 1, 1, 4].length) (baseStart_7744767 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7744767 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7744767 prefixEnd_7744767 := by exact prefixLift 7744767
  have htrace : WordTrace (prefixWord ++ tailWord_7744767) baseStart_7744767 baseEnd_7744767 := by
    simpa [prefixWord, tailWord_7744767, baseEnd_7744767] using wordTrace_append hprefix tailTrace_7744767
  have hstable : (prefixWord ++ tailWord_7744767).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7744767).length < 2 ^ (prefixWord ++ tailWord_7744767).sum := by decide
  have hdescent : baseEnd_7744767 < baseStart_7744767 := by decide
  rcases family_descends (prefixWord ++ tailWord_7744767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7744783 : List Nat := [1, 1, 2, 1, 1, 1, 3, 1, 2, 7, 3]
def baseStart_7744783 : Nat := 118140960795 + 7744783 * 2 ^ 59
def prefixEnd_7744783 : Nat := 4983230072969 + 3 ^ 40 * 7744783 * 2
def baseEnd_7744783 : Nat := 3976796243770277234594897

theorem tailTrace_7744783 : CollatzResearch.WordTrace tailWord_7744783 prefixEnd_7744783 3976796243770277234594897 := by
  unfold tailWord_7744783
  simp only [CollatzResearch.WordTrace]
  refine ⟨282475442300981369475695003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188316961533987579650463335 282475442300981369475695003)
  ·
    refine ⟨423713163451472054213542505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 282475442300981369475695003 423713163451472054213542505)
    ·
      refine ⟨317784872588604040660156879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 423713163451472054213542505 317784872588604040660156879)
      ·
        refine ⟨476677308882906060990235319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 317784872588604040660156879 476677308882906060990235319)
        ·
          refine ⟨715015963324359091485352979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 476677308882906060990235319 715015963324359091485352979)
          ·
            refine ⟨1072523944986538637228029469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 715015963324359091485352979 1072523944986538637228029469)
            ·
              refine ⟨402196479369951988960511051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1072523944986538637228029469 402196479369951988960511051)
              ·
                refine ⟨603294719054927983440766577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 402196479369951988960511051 603294719054927983440766577)
                ·
                  refine ⟨452471039291195987580574933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 603294719054927983440766577 452471039291195987580574933)
                  ·
                    refine ⟨10604789983387405958919725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 452471039291195987580574933 10604789983387405958919725)
                    ·
                      refine ⟨3976796243770277234594897, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10604789983387405958919725 3976796243770277234594897)
                      ·
                        rfl

theorem cell23_7744783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 3, 1, 2, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 3, 1, 2, 7, 3].length) (baseStart_7744783 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7744783 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7744783 prefixEnd_7744783 := by exact prefixLift 7744783
  have htrace : WordTrace (prefixWord ++ tailWord_7744783) baseStart_7744783 baseEnd_7744783 := by
    simpa [prefixWord, tailWord_7744783, baseEnd_7744783] using wordTrace_append hprefix tailTrace_7744783
  have hstable : (prefixWord ++ tailWord_7744783).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7744783).length < 2 ^ (prefixWord ++ tailWord_7744783).sum := by decide
  have hdescent : baseEnd_7744783 < baseStart_7744783 := by decide
  rcases family_descends (prefixWord ++ tailWord_7744783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7744794 : List Nat := [3, 1, 1, 3, 3, 2, 3, 1, 2, 4]
def baseStart_7744794 : Nat := 118140960795 + 7744794 * 2 ^ 59
def prefixEnd_7744794 : Nat := 4983230072969 + 3 ^ 40 * 7744794 * 2
def baseEnd_7744794 : Nat := 1325600630685825563852449

theorem tailTrace_7744794 : CollatzResearch.WordTrace tailWord_7744794 prefixEnd_7744794 1325600630685825563852449 := by
  unfold tailWord_7744794
  simp only [CollatzResearch.WordTrace]
  refine ⟨70618960875985379588586359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 188317229002627678902896957 70618960875985379588586359)
  ·
    refine ⟨105928441313978069382879539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70618960875985379588586359 105928441313978069382879539)
    ·
      refine ⟨158892661970967104074319309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105928441313978069382879539 158892661970967104074319309)
      ·
        refine ⟨59584748239112664027869741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 158892661970967104074319309 59584748239112664027869741)
        ·
          refine ⟨22344280589667249010451153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 59584748239112664027869741 22344280589667249010451153)
          ·
            refine ⟨16758210442250436757838365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22344280589667249010451153 16758210442250436757838365)
            ·
              refine ⟨6284328915843913784189387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16758210442250436757838365 6284328915843913784189387)
              ·
                refine ⟨9426493373765870676284081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6284328915843913784189387 9426493373765870676284081)
                ·
                  refine ⟨7069870030324403007213061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9426493373765870676284081 7069870030324403007213061)
                  ·
                    refine ⟨1325600630685825563852449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7069870030324403007213061 1325600630685825563852449)
                    ·
                      rfl

theorem cell23_7744794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 2, 3, 1, 2, 4].length) (baseStart_7744794 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7744794 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7744794 prefixEnd_7744794 := by exact prefixLift 7744794
  have htrace : WordTrace (prefixWord ++ tailWord_7744794) baseStart_7744794 baseEnd_7744794 := by
    simpa [prefixWord, tailWord_7744794, baseEnd_7744794] using wordTrace_append hprefix tailTrace_7744794
  have hstable : (prefixWord ++ tailWord_7744794).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7744794).length < 2 ^ (prefixWord ++ tailWord_7744794).sum := by decide
  have hdescent : baseEnd_7744794 < baseStart_7744794 := by decide
  rcases family_descends (prefixWord ++ tailWord_7744794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7744797 : List Nat := [1, 4, 2, 3, 1, 1, 3, 1, 1, 2, 4]
def baseStart_7744797 : Nat := 118140960795 + 7744797 * 2 ^ 59
def prefixEnd_7744797 : Nat := 4983230072969 + 3 ^ 40 * 7744797 * 2
def baseEnd_7744797 : Nat := 3976803432499440179819833

theorem tailTrace_7744797 : CollatzResearch.WordTrace tailWord_7744797 prefixEnd_7744797 3976803432499440179819833 := by
  unfold tailWord_7744797
  simp only [CollatzResearch.WordTrace]
  refine ⟨282475952922930649866704645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188317301948620433244469763 282475952922930649866704645)
  ·
    refine ⟨52964241173049496850007121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 282475952922930649866704645 52964241173049496850007121)
    ·
      refine ⟨39723180879787122637505341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52964241173049496850007121 39723180879787122637505341)
      ·
        refine ⟨14896192829920170989064503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39723180879787122637505341 14896192829920170989064503)
        ·
          refine ⟨22344289244880256483596755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14896192829920170989064503 22344289244880256483596755)
          ·
            refine ⟨33516433867320384725395133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22344289244880256483596755 33516433867320384725395133)
            ·
              refine ⟨12568662700245144272023175, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33516433867320384725395133 12568662700245144272023175)
              ·
                refine ⟨18852994050367716408034763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12568662700245144272023175 18852994050367716408034763)
                ·
                  refine ⟨28279491075551574612052145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18852994050367716408034763 28279491075551574612052145)
                  ·
                    refine ⟨21209618306663680959039109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 28279491075551574612052145 21209618306663680959039109)
                    ·
                      refine ⟨3976803432499440179819833, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21209618306663680959039109 3976803432499440179819833)
                      ·
                        rfl

theorem cell23_7744797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 1, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 1, 3, 1, 1, 2, 4].length) (baseStart_7744797 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7744797 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7744797 prefixEnd_7744797 := by exact prefixLift 7744797
  have htrace : WordTrace (prefixWord ++ tailWord_7744797) baseStart_7744797 baseEnd_7744797 := by
    simpa [prefixWord, tailWord_7744797, baseEnd_7744797] using wordTrace_append hprefix tailTrace_7744797
  have hstable : (prefixWord ++ tailWord_7744797).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7744797).length < 2 ^ (prefixWord ++ tailWord_7744797).sum := by decide
  have hdescent : baseEnd_7744797 < baseStart_7744797 := by decide
  rcases family_descends (prefixWord ++ tailWord_7744797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7744817 : List Nat := [1, 2, 2, 3, 3, 1, 1, 2, 4, 1, 3]
def baseStart_7744817 : Nat := 118140960795 + 7744817 * 2 ^ 59
def prefixEnd_7744817 : Nat := 4983230072969 + 3 ^ 40 * 7744817 * 2
def baseEnd_7744817 : Nat := 3976813702112530101569741

theorem tailTrace_7744817 : CollatzResearch.WordTrace tailWord_7744817 prefixEnd_7744817 3976813702112530101569741 := by
  unfold tailWord_7744817
  simp only [CollatzResearch.WordTrace]
  refine ⟨282476682382858193282432705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188317788255238795521621803 282476682382858193282432705)
  ·
    refine ⟨211857511787143644961824529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 282476682382858193282432705 211857511787143644961824529)
    ·
      refine ⟨158893133840357733721368397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 211857511787143644961824529 158893133840357733721368397)
      ·
        refine ⟨59584925190134150145513149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 158893133840357733721368397 59584925190134150145513149)
        ·
          refine ⟨22344346946300306304567431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 59584925190134150145513149 22344346946300306304567431)
          ·
            refine ⟨33516520419450459456851147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22344346946300306304567431 33516520419450459456851147)
            ·
              refine ⟨50274780629175689185276721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33516520419450459456851147 50274780629175689185276721)
              ·
                refine ⟨37706085471881766888957541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50274780629175689185276721 37706085471881766888957541)
                ·
                  refine ⟨7069891025977831291679539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 37706085471881766888957541 7069891025977831291679539)
                  ·
                    refine ⟨10604836538966746937519309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7069891025977831291679539 10604836538966746937519309)
                    ·
                      refine ⟨3976813702112530101569741, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10604836538966746937519309 3976813702112530101569741)
                      ·
                        rfl

theorem cell23_7744817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 1, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 1, 1, 2, 4, 1, 3].length) (baseStart_7744817 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7744817 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7744817 prefixEnd_7744817 := by exact prefixLift 7744817
  have htrace : WordTrace (prefixWord ++ tailWord_7744817) baseStart_7744817 baseEnd_7744817 := by
    simpa [prefixWord, tailWord_7744817, baseEnd_7744817] using wordTrace_append hprefix tailTrace_7744817
  have hstable : (prefixWord ++ tailWord_7744817).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7744817).length < 2 ^ (prefixWord ++ tailWord_7744817).sum := by decide
  have hdescent : baseEnd_7744817 < baseStart_7744817 := by decide
  rcases family_descends (prefixWord ++ tailWord_7744817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7744818 : List Nat := [3, 2, 1, 1, 4, 3, 1, 3, 1, 2, 2]
def baseStart_7744818 : Nat := 118140960795 + 7744818 * 2 ^ 59
def prefixEnd_7744818 : Nat := 4983230072969 + 3 ^ 40 * 7744818 * 2
def baseEnd_7744818 : Nat := 3976814215593184597657237

theorem tailTrace_7744818 : CollatzResearch.WordTrace tailWord_7744818 prefixEnd_7744818 3976814215593184597657237 := by
  unfold tailWord_7744818
  simp only [CollatzResearch.WordTrace]
  refine ⟨70619179713963642613304777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 188317812570569713635479405 70619179713963642613304777)
  ·
    refine ⟨52964384785472731959978583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70619179713963642613304777 52964384785472731959978583)
    ·
      refine ⟨79446577178209097939967875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52964384785472731959978583 79446577178209097939967875)
      ·
        refine ⟨119169865767313646909951813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79446577178209097939967875 119169865767313646909951813)
        ·
          refine ⟨22344349831371308795615965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 119169865767313646909951813 22344349831371308795615965)
          ·
            refine ⟨8379131186764240798355987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22344349831371308795615965 8379131186764240798355987)
            ·
              refine ⟨12568696780146361197533981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8379131186764240798355987 12568696780146361197533981)
              ·
                refine ⟨4713261292554885449075243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12568696780146361197533981 4713261292554885449075243)
                ·
                  refine ⟨7069891938832328173612865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4713261292554885449075243 7069891938832328173612865)
                  ·
                    refine ⟨5302418954124246130209649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7069891938832328173612865 5302418954124246130209649)
                    ·
                      refine ⟨3976814215593184597657237, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5302418954124246130209649 3976814215593184597657237)
                      ·
                        rfl

theorem cell23_7744818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 3, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 3, 1, 3, 1, 2, 2].length) (baseStart_7744818 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7744818 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7744818 prefixEnd_7744818 := by exact prefixLift 7744818
  have htrace : WordTrace (prefixWord ++ tailWord_7744818) baseStart_7744818 baseEnd_7744818 := by
    simpa [prefixWord, tailWord_7744818, baseEnd_7744818] using wordTrace_append hprefix tailTrace_7744818
  have hstable : (prefixWord ++ tailWord_7744818).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7744818).length < 2 ^ (prefixWord ++ tailWord_7744818).sum := by decide
  have hdescent : baseEnd_7744818 < baseStart_7744818 := by decide
  rcases family_descends (prefixWord ++ tailWord_7744818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7744823 : List Nat := [1, 1, 3, 1, 2, 1, 1, 1, 3, 5, 4]
def baseStart_7744823 : Nat := 118140960795 + 7744823 * 2 ^ 59
def prefixEnd_7744823 : Nat := 4983230072969 + 3 ^ 40 * 7744823 * 2
def baseEnd_7744823 : Nat := 3976816782996457078094713

theorem tailTrace_7744823 : CollatzResearch.WordTrace tailWord_7744823 prefixEnd_7744823 3976816782996457078094713 := by
  unfold tailWord_7744823
  simp only [CollatzResearch.WordTrace]
  refine ⟨282476901220836456307151123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188317934147224304204767415 282476901220836456307151123)
  ·
    refine ⟨423715351831254684460726685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 282476901220836456307151123 423715351831254684460726685)
    ·
      refine ⟨158893256936720506672772507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 423715351831254684460726685 158893256936720506672772507)
      ·
        refine ⟨238339885405080760009158761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 158893256936720506672772507 238339885405080760009158761)
        ·
          refine ⟨178754914053810570006869071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 238339885405080760009158761 178754914053810570006869071)
          ·
            refine ⟨268132371080715855010303607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 178754914053810570006869071 268132371080715855010303607)
            ·
              refine ⟨402198556621073782515455411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 268132371080715855010303607 402198556621073782515455411)
              ·
                refine ⟨603297834931610673773183117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 402198556621073782515455411 603297834931610673773183117)
                ·
                  refine ⟨226236688099354002664943669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 603297834931610673773183117 226236688099354002664943669)
                  ·
                    refine ⟨21209689509314437749838469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 226236688099354002664943669 21209689509314437749838469)
                    ·
                      refine ⟨3976816782996457078094713, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21209689509314437749838469 3976816782996457078094713)
                      ·
                        rfl

theorem cell23_7744823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 3, 5, 4].length) (baseStart_7744823 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7744823 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7744823 prefixEnd_7744823 := by exact prefixLift 7744823
  have htrace : WordTrace (prefixWord ++ tailWord_7744823) baseStart_7744823 baseEnd_7744823 := by
    simpa [prefixWord, tailWord_7744823, baseEnd_7744823] using wordTrace_append hprefix tailTrace_7744823
  have hstable : (prefixWord ++ tailWord_7744823).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7744823).length < 2 ^ (prefixWord ++ tailWord_7744823).sum := by decide
  have hdescent : baseEnd_7744823 < baseStart_7744823 := by decide
  rcases family_descends (prefixWord ++ tailWord_7744823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7744830 : List Nat := [4, 2, 1, 2, 1, 1, 1, 2, 2, 2, 5]
def baseStart_7744830 : Nat := 118140960795 + 7744830 * 2 ^ 59
def prefixEnd_7744830 : Nat := 4983230072969 + 3 ^ 40 * 7744830 * 2
def baseEnd_7744830 : Nat := 3976820377361038550707181

theorem tailTrace_7744830 : CollatzResearch.WordTrace tailWord_7744830 prefixEnd_7744830 3976820377361038550707181 := by
  unfold tailWord_7744830
  simp only [CollatzResearch.WordTrace]
  refine ⟨35309644566476387062831993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 188318104354540731001770629 35309644566476387062831993)
  ·
    refine ⟨26482233424857290297123995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35309644566476387062831993 26482233424857290297123995)
    ·
      refine ⟨39723350137285935445685993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26482233424857290297123995 39723350137285935445685993)
      ·
        refine ⟨29792512602964451584264495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39723350137285935445685993 29792512602964451584264495)
        ·
          refine ⟨44688768904446677376396743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29792512602964451584264495 44688768904446677376396743)
          ·
            refine ⟨67033153356670016064595115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44688768904446677376396743 67033153356670016064595115)
            ·
              refine ⟨100549730035005024096892673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67033153356670016064595115 100549730035005024096892673)
              ·
                refine ⟨75412297526253768072669505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 100549730035005024096892673 75412297526253768072669505)
                ·
                  refine ⟨56559223144690326054502129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 75412297526253768072669505 56559223144690326054502129)
                  ·
                    refine ⟨42419417358517744540876597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 56559223144690326054502129 42419417358517744540876597)
                    ·
                      refine ⟨3976820377361038550707181, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 42419417358517744540876597 3976820377361038550707181)
                      ·
                        rfl

theorem cell23_7744830_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 1, 2, 2, 2, 5].length) (baseStart_7744830 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7744830 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7744830 prefixEnd_7744830 := by exact prefixLift 7744830
  have htrace : WordTrace (prefixWord ++ tailWord_7744830) baseStart_7744830 baseEnd_7744830 := by
    simpa [prefixWord, tailWord_7744830, baseEnd_7744830] using wordTrace_append hprefix tailTrace_7744830
  have hstable : (prefixWord ++ tailWord_7744830).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7744830).length < 2 ^ (prefixWord ++ tailWord_7744830).sum := by decide
  have hdescent : baseEnd_7744830 < baseStart_7744830 := by decide
  rcases family_descends (prefixWord ++ tailWord_7744830) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7744845 : List Nat := [1, 6, 1, 3, 2, 1, 2, 1, 2, 4]
def baseStart_7744845 : Nat := 118140960795 + 7744845 * 2 ^ 59
def prefixEnd_7744845 : Nat := 4983230072969 + 3 ^ 40 * 7744845 * 2
def baseEnd_7744845 : Nat := 1325609359856951997339871

theorem tailTrace_7744845 : CollatzResearch.WordTrace tailWord_7744845 prefixEnd_7744845 1325609359856951997339871 := by
  unfold tailWord_7744845
  simp only [CollatzResearch.WordTrace]
  refine ⟨282477703626756754064451989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188318469084504502709634659 282477703626756754064451989)
  ·
    refine ⟨13241142357504222846771187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 282477703626756754064451989 13241142357504222846771187)
    ·
      refine ⟨19861713536256334270156781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13241142357504222846771187 19861713536256334270156781)
      ·
        refine ⟨7448142576096125351308793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19861713536256334270156781 7448142576096125351308793)
        ·
          refine ⟨5586106932072094013481595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7448142576096125351308793 5586106932072094013481595)
          ·
            refine ⟨8379160398108141020222393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5586106932072094013481595 8379160398108141020222393)
            ·
              refine ⟨6284370298581105765166795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8379160398108141020222393 6284370298581105765166795)
              ·
                refine ⟨9426555447871658647750193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6284370298581105765166795 9426555447871658647750193)
                ·
                  refine ⟨7069916585903743985812645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9426555447871658647750193 7069916585903743985812645)
                  ·
                    refine ⟨1325609359856951997339871, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7069916585903743985812645 1325609359856951997339871)
                    ·
                      rfl

theorem cell23_7744845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 2, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 2, 1, 2, 1, 2, 4].length) (baseStart_7744845 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7744845 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7744845 prefixEnd_7744845 := by exact prefixLift 7744845
  have htrace : WordTrace (prefixWord ++ tailWord_7744845) baseStart_7744845 baseEnd_7744845 := by
    simpa [prefixWord, tailWord_7744845, baseEnd_7744845] using wordTrace_append hprefix tailTrace_7744845
  have hstable : (prefixWord ++ tailWord_7744845).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7744845).length < 2 ^ (prefixWord ++ tailWord_7744845).sum := by decide
  have hdescent : baseEnd_7744845 < baseStart_7744845 := by decide
  rcases family_descends (prefixWord ++ tailWord_7744845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7744863 : List Nat := [1, 1, 2, 3, 1, 2, 1, 3, 9]
def baseStart_7744863 : Nat := 118140960795 + 7744863 * 2 ^ 59
def prefixEnd_7744863 : Nat := 4983230072969 + 3 ^ 40 * 7744863 * 2
def baseEnd_7744863 : Nat := 441870813580292991288281

theorem tailTrace_7744863 : CollatzResearch.WordTrace tailWord_7744863 prefixEnd_7744863 441870813580292991288281 := by
  unfold tailWord_7744863
  simp only [CollatzResearch.WordTrace]
  refine ⟨282478360140691543138607243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188318906760461028759071495 282478360140691543138607243)
  ·
    refine ⟨423717540211037314707910865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 282478360140691543138607243 423717540211037314707910865)
    ·
      refine ⟨317788155158277986030933149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 423717540211037314707910865 317788155158277986030933149)
      ·
        refine ⟨119170558184354244761599931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 317788155158277986030933149 119170558184354244761599931)
        ·
          refine ⟨178755837276531367142399897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 119170558184354244761599931 178755837276531367142399897)
          ·
            refine ⟨134066877957398525356799923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 178755837276531367142399897 134066877957398525356799923)
            ·
              refine ⟨201100316936097788035199885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 134066877957398525356799923 201100316936097788035199885)
              ·
                refine ⟨75412618851036670513199957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 201100316936097788035199885 75412618851036670513199957)
                ·
                  refine ⟨441870813580292991288281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 75412618851036670513199957 441870813580292991288281)
                  ·
                    rfl

theorem cell23_7744863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 1, 3, 9].length) (baseStart_7744863 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7744863 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7744863 prefixEnd_7744863 := by exact prefixLift 7744863
  have htrace : WordTrace (prefixWord ++ tailWord_7744863) baseStart_7744863 baseEnd_7744863 := by
    simpa [prefixWord, tailWord_7744863, baseEnd_7744863] using wordTrace_append hprefix tailTrace_7744863
  have hstable : (prefixWord ++ tailWord_7744863).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7744863).length < 2 ^ (prefixWord ++ tailWord_7744863).sum := by decide
  have hdescent : baseEnd_7744863 < baseStart_7744863 := by decide
  rcases family_descends (prefixWord ++ tailWord_7744863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7744873 : List Nat := [1, 2, 1, 1, 1, 3, 2, 2, 1, 2, 7]
def baseStart_7744873 : Nat := 118140960795 + 7744873 * 2 ^ 59
def prefixEnd_7744873 : Nat := 4983230072969 + 3 ^ 40 * 7744873 * 2
def baseEnd_7744873 : Nat := 3976842457029181882469483

theorem tailTrace_7744873 : CollatzResearch.WordTrace tailWord_7744873 prefixEnd_7744873 3976842457029181882469483 := by
  unfold tailWord_7744873
  simp only [CollatzResearch.WordTrace]
  refine ⟨282478724870655314846471273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188319149913770209897647515 282478724870655314846471273)
  ·
    refine ⟨211859043652991486134853455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 282478724870655314846471273 211859043652991486134853455)
    ·
      refine ⟨317788565479487229202280183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 211859043652991486134853455 317788565479487229202280183)
      ·
        refine ⟨476682848219230843803420275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 317788565479487229202280183 476682848219230843803420275)
        ·
          refine ⟨715024272328846265705130413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 476682848219230843803420275 715024272328846265705130413)
          ·
            refine ⟨268134102123317349639423905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 715024272328846265705130413 268134102123317349639423905)
            ·
              refine ⟨201100576592488012229567929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 268134102123317349639423905 201100576592488012229567929)
              ·
                refine ⟨150825432444366009172175947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 201100576592488012229567929 150825432444366009172175947)
                ·
                  refine ⟨226238148666549013758263921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 150825432444366009172175947 226238148666549013758263921)
                  ·
                    refine ⟨169678611499911760318697941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 226238148666549013758263921 169678611499911760318697941)
                    ·
                      refine ⟨3976842457029181882469483, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 169678611499911760318697941 3976842457029181882469483)
                      ·
                        rfl

theorem cell23_7744873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 2, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 2, 2, 1, 2, 7].length) (baseStart_7744873 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7744873 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7744873 prefixEnd_7744873 := by exact prefixLift 7744873
  have htrace : WordTrace (prefixWord ++ tailWord_7744873) baseStart_7744873 baseEnd_7744873 := by
    simpa [prefixWord, tailWord_7744873, baseEnd_7744873] using wordTrace_append hprefix tailTrace_7744873
  have hstable : (prefixWord ++ tailWord_7744873).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7744873).length < 2 ^ (prefixWord ++ tailWord_7744873).sum := by decide
  have hdescent : baseEnd_7744873 < baseStart_7744873 := by decide
  rcases family_descends (prefixWord ++ tailWord_7744873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7744883 : List Nat := [1, 1, 1, 2, 2, 1, 2, 1, 2, 4, 6]
def baseStart_7744883 : Nat := 118140960795 + 7744883 * 2 ^ 59
def prefixEnd_7744883 : Nat := 4983230072969 + 3 ^ 40 * 7744883 * 2
def baseEnd_7744883 : Nat := 3976847591835726843344437

theorem tailTrace_7744883 : CollatzResearch.WordTrace tailWord_7744883 prefixEnd_7744883 3976847591835726843344437 := by
  unfold tailWord_7744883
  simp only [CollatzResearch.WordTrace]
  refine ⟨282479089600619086554335303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188319393067079391036223535 282479089600619086554335303)
  ·
    refine ⟨423718634400928629831502955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 282479089600619086554335303 423718634400928629831502955)
    ·
      refine ⟨635577951601392944747254433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 423718634400928629831502955 635577951601392944747254433)
      ·
        refine ⟨476683463701044708560440825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 635577951601392944747254433 476683463701044708560440825)
        ·
          refine ⟨357512597775783531420330619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 476683463701044708560440825 357512597775783531420330619)
          ·
            refine ⟨536268896663675297130495929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 357512597775783531420330619 536268896663675297130495929)
            ·
              refine ⟨402201672497756472847871947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 536268896663675297130495929 402201672497756472847871947)
              ·
                refine ⟨603302508746634709271807921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 402201672497756472847871947 603302508746634709271807921)
                ·
                  refine ⟨452476881559976031953855941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 603302508746634709271807921 452476881559976031953855941)
                  ·
                    refine ⟨84839415292495505991347989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 452476881559976031953855941 84839415292495505991347989)
                    ·
                      refine ⟨3976847591835726843344437, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 84839415292495505991347989 3976847591835726843344437)
                      ·
                        rfl

theorem cell23_7744883_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 2, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 2, 1, 2, 4, 6].length) (baseStart_7744883 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7744883 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7744883 prefixEnd_7744883 := by exact prefixLift 7744883
  have htrace : WordTrace (prefixWord ++ tailWord_7744883) baseStart_7744883 baseEnd_7744883 := by
    simpa [prefixWord, tailWord_7744883, baseEnd_7744883] using wordTrace_append hprefix tailTrace_7744883
  have hstable : (prefixWord ++ tailWord_7744883).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7744883).length < 2 ^ (prefixWord ++ tailWord_7744883).sum := by decide
  have hdescent : baseEnd_7744883 < baseStart_7744883 := by decide
  rcases family_descends (prefixWord ++ tailWord_7744883) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7744890 : List Nat := [3, 1, 1, 1, 1, 1, 2, 3, 4, 3, 3]
def baseStart_7744890 : Nat := 118140960795 + 7744890 * 2 ^ 59
def prefixEnd_7744890 : Nat := 4983230072969 + 3 ^ 40 * 7744890 * 2
def baseEnd_7744890 : Nat := 3976851186200308315956905

theorem tailTrace_7744890 : CollatzResearch.WordTrace tailWord_7744890 prefixEnd_7744890 3976851186200308315956905 := by
  unfold tailWord_7744890
  simp only [CollatzResearch.WordTrace]
  refine ⟨70619836227898431687460031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 188319563274395817833226749 70619836227898431687460031)
  ·
    refine ⟨105929754341847647531190047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70619836227898431687460031 105929754341847647531190047)
    ·
      refine ⟨158894631512771471296785071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105929754341847647531190047 158894631512771471296785071)
      ·
        refine ⟨238341947269157206945177607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 158894631512771471296785071 238341947269157206945177607)
        ·
          refine ⟨357512920903735810417766411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 238341947269157206945177607 357512920903735810417766411)
          ·
            refine ⟨536269381355603715626649617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 357512920903735810417766411 536269381355603715626649617)
            ·
              refine ⟨402202036016702786719987213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 536269381355603715626649617 402202036016702786719987213)
              ·
                refine ⟨150825763506263545019995205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 402202036016702786719987213 150825763506263545019995205)
                ·
                  refine ⟨28279830657424414691249101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 150825763506263545019995205 28279830657424414691249101)
                  ·
                    refine ⟨10604936496534155509218413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 28279830657424414691249101 10604936496534155509218413)
                    ·
                      refine ⟨3976851186200308315956905, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10604936496534155509218413 3976851186200308315956905)
                      ·
                        rfl

theorem cell23_7744890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 2, 3, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 2, 3, 4, 3, 3].length) (baseStart_7744890 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7744890 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7744890 prefixEnd_7744890 := by exact prefixLift 7744890
  have htrace : WordTrace (prefixWord ++ tailWord_7744890) baseStart_7744890 baseEnd_7744890 := by
    simpa [prefixWord, tailWord_7744890, baseEnd_7744890] using wordTrace_append hprefix tailTrace_7744890
  have hstable : (prefixWord ++ tailWord_7744890).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7744890).length < 2 ^ (prefixWord ++ tailWord_7744890).sum := by decide
  have hdescent : baseEnd_7744890 < baseStart_7744890 := by decide
  rcases family_descends (prefixWord ++ tailWord_7744890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7744914 : List Nat := [3, 2, 3, 3, 1, 1, 1, 2, 7]
def baseStart_7744914 : Nat := 118140960795 + 7744914 * 2 ^ 59
def prefixEnd_7744914 : Nat := 4983230072969 + 3 ^ 40 * 7744914 * 2
def baseEnd_7744914 : Nat := 441873723304001802450755

theorem tailTrace_7744914 : CollatzResearch.WordTrace tailWord_7744914 prefixEnd_7744914 441873723304001802450755 := by
  unfold tailWord_7744914
  simp only [CollatzResearch.WordTrace]
  refine ⟨70620055065876694712178449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 188320146842337852565809197 70620055065876694712178449)
  ·
    refine ⟨52965041299407521034133837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70620055065876694712178449 52965041299407521034133837)
    ·
      refine ⟨19861890487277820387800189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 52965041299407521034133837 19861890487277820387800189)
      ·
        refine ⟨7448208932729182645425071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19861890487277820387800189 7448208932729182645425071)
        ·
          refine ⟨11172313399093773968137607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7448208932729182645425071 11172313399093773968137607)
          ·
            refine ⟨16758470098640660952206411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11172313399093773968137607 16758470098640660952206411)
            ·
              refine ⟨25137705147960991428309617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16758470098640660952206411 25137705147960991428309617)
              ·
                refine ⟨18853278860970743571232213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25137705147960991428309617 18853278860970743571232213)
                ·
                  refine ⟨441873723304001802450755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18853278860970743571232213 441873723304001802450755)
                  ·
                    rfl

theorem cell23_7744914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 1, 1, 1, 2, 7].length) (baseStart_7744914 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7744914 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7744914 prefixEnd_7744914 := by exact prefixLift 7744914
  have htrace : WordTrace (prefixWord ++ tailWord_7744914) baseStart_7744914 baseEnd_7744914 := by
    simpa [prefixWord, tailWord_7744914, baseEnd_7744914] using wordTrace_append hprefix tailTrace_7744914
  have hstable : (prefixWord ++ tailWord_7744914).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7744914).length < 2 ^ (prefixWord ++ tailWord_7744914).sum := by decide
  have hdescent : baseEnd_7744914 < baseStart_7744914 := by decide
  rcases family_descends (prefixWord ++ tailWord_7744914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7744927 : List Nat := [1, 1, 2, 5, 1, 2, 3, 1, 2, 5]
def baseStart_7744927 : Nat := 118140960795 + 7744927 * 2 ^ 59
def prefixEnd_7744927 : Nat := 4983230072969 + 3 ^ 40 * 7744927 * 2
def baseEnd_7744927 : Nat := 1325623394994841557064745

theorem tailTrace_7744927 : CollatzResearch.WordTrace tailWord_7744927 prefixEnd_7744927 1325623394994841557064745 := by
  unfold tailWord_7744927
  simp only [CollatzResearch.WordTrace]
  refine ⟨282480694412459682068937035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188320462941639788045958023 282480694412459682068937035)
  ·
    refine ⟨423721041618689523103405553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 282480694412459682068937035 423721041618689523103405553)
    ·
      refine ⟨317790781214017142327554165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 423721041618689523103405553 317790781214017142327554165)
      ·
        refine ⟨29792885738814107093208203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 317790781214017142327554165 29792885738814107093208203)
        ·
          refine ⟨44689328608221160639812305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29792885738814107093208203 44689328608221160639812305)
          ·
            refine ⟨33516996456165870479859229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44689328608221160639812305 33516996456165870479859229)
            ·
              refine ⟨12568873671062201429947211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33516996456165870479859229 12568873671062201429947211)
              ·
                refine ⟨18853310506593302144920817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12568873671062201429947211 18853310506593302144920817)
                ·
                  refine ⟨14139982879944976608690613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18853310506593302144920817 14139982879944976608690613)
                  ·
                    refine ⟨1325623394994841557064745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14139982879944976608690613 1325623394994841557064745)
                    ·
                      rfl

theorem cell23_7744927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 2, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 2, 3, 1, 2, 5].length) (baseStart_7744927 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7744927 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7744927 prefixEnd_7744927 := by exact prefixLift 7744927
  have htrace : WordTrace (prefixWord ++ tailWord_7744927) baseStart_7744927 baseEnd_7744927 := by
    simpa [prefixWord, tailWord_7744927, baseEnd_7744927] using wordTrace_append hprefix tailTrace_7744927
  have hstable : (prefixWord ++ tailWord_7744927).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7744927).length < 2 ^ (prefixWord ++ tailWord_7744927).sum := by decide
  have hdescent : baseEnd_7744927 < baseStart_7744927 := by decide
  rcases family_descends (prefixWord ++ tailWord_7744927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7745034 : List Nat := [3, 1, 2, 2, 2, 2, 3, 2, 1, 5]
def baseStart_7745034 : Nat := 118140960795 + 7745034 * 2 ^ 59
def prefixEnd_7745034 : Nat := 4983230072969 + 3 ^ 40 * 7745034 * 2
def baseEnd_7745034 : Nat := 1325641709138185250852081

theorem tailTrace_7745034 : CollatzResearch.WordTrace tailWord_7745034 prefixEnd_7745034 1325641709138185250852081 := by
  unfold tailWord_7745034
  simp only [CollatzResearch.WordTrace]
  refine ⟨70621149255768009835770539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 188323064682048026228721437 70621149255768009835770539)
  ·
    refine ⟨105931723883652014753655809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70621149255768009835770539 105931723883652014753655809)
    ·
      refine ⟨79448792912739011065241857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 105931723883652014753655809 79448792912739011065241857)
      ·
        refine ⟨59586594684554258298931393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79448792912739011065241857 59586594684554258298931393)
        ·
          refine ⟨44689946013415693724198545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59586594684554258298931393 44689946013415693724198545)
          ·
            refine ⟨33517459510061770293148909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44689946013415693724198545 33517459510061770293148909)
            ·
              refine ⟨12569047316273163859930841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33517459510061770293148909 12569047316273163859930841)
              ·
                refine ⟨9426785487204872894948131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12569047316273163859930841 9426785487204872894948131)
                ·
                  refine ⟨14140178230807309342422197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9426785487204872894948131 14140178230807309342422197)
                  ·
                    refine ⟨1325641709138185250852081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14140178230807309342422197 1325641709138185250852081)
                    ·
                      rfl

theorem cell23_7745034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 2, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 2, 3, 2, 1, 5].length) (baseStart_7745034 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7745034 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7745034 prefixEnd_7745034 := by exact prefixLift 7745034
  have htrace : WordTrace (prefixWord ++ tailWord_7745034) baseStart_7745034 baseEnd_7745034 := by
    simpa [prefixWord, tailWord_7745034, baseEnd_7745034] using wordTrace_append hprefix tailTrace_7745034
  have hstable : (prefixWord ++ tailWord_7745034).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7745034).length < 2 ^ (prefixWord ++ tailWord_7745034).sum := by decide
  have hdescent : baseEnd_7745034 < baseStart_7745034 := by decide
  rcases family_descends (prefixWord ++ tailWord_7745034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7745060 : List Nat := [2, 3, 1, 17]
def baseStart_7745060 : Nat := 118140960795 + 7745060 * 2 ^ 59
def prefixEnd_7745060 : Nat := 4983230072969 + 3 ^ 40 * 7745060 * 2
def baseEnd_7745060 : Nat := 1818444662968254527129

theorem tailTrace_7745060 : CollatzResearch.WordTrace tailWord_7745060 prefixEnd_7745060 1818444662968254527129 := by
  unfold tailWord_7745060
  simp only [CollatzResearch.WordTrace]
  refine ⟨141242772660488922891764317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 188323696880651897189019089 141242772660488922891764317)
  ·
    refine ⟨52966039747683346084411619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 141242772660488922891764317 52966039747683346084411619)
    ·
      refine ⟨79449059621525019126617429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52966039747683346084411619 79449059621525019126617429)
      ·
        refine ⟨1818444662968254527129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 17 79449059621525019126617429 1818444662968254527129)
        ·
          rfl

theorem cell23_7745060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 17].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 17].length) (baseStart_7745060 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7745060 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7745060 prefixEnd_7745060 := by exact prefixLift 7745060
  have htrace : WordTrace (prefixWord ++ tailWord_7745060) baseStart_7745060 baseEnd_7745060 := by
    simpa [prefixWord, tailWord_7745060, baseEnd_7745060] using wordTrace_append hprefix tailTrace_7745060
  have hstable : (prefixWord ++ tailWord_7745060).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7745060).length < 2 ^ (prefixWord ++ tailWord_7745060).sum := by decide
  have hdescent : baseEnd_7745060 < baseStart_7745060 := by decide
  rcases family_descends (prefixWord ++ tailWord_7745060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7745077 : List Nat := [1, 3, 3, 1, 1, 3, 3, 8]
def baseStart_7745077 : Nat := 118140960795 + 7745077 * 2 ^ 59
def prefixEnd_7745077 : Nat := 4983230072969 + 3 ^ 40 * 7745077 * 2
def baseEnd_7745077 : Nat := 147294341003062929048835

theorem tailTrace_7745077 : CollatzResearch.WordTrace tailWord_7745077 prefixEnd_7745077 147294341003062929048835 := by
  unfold tailWord_7745077
  simp only [CollatzResearch.WordTrace]
  refine ⟨282486165361916257686897485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188324110241277505124598323 282486165361916257686897485)
  ·
    refine ⟨105932312010718596632586557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 282486165361916257686897485 105932312010718596632586557)
    ·
      refine ⟨39724617004019473737219959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 105932312010718596632586557 39724617004019473737219959)
      ·
        refine ⟨59586925506029210605829939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39724617004019473737219959 59586925506029210605829939)
        ·
          refine ⟨89380388259043815908744909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59586925506029210605829939 89380388259043815908744909)
          ·
            refine ⟨33517645597141430965779341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 89380388259043815908744909 33517645597141430965779341)
            ·
              refine ⟨12569117098928036612167253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33517645597141430965779341 12569117098928036612167253)
              ·
                refine ⟨147294341003062929048835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 12569117098928036612167253 147294341003062929048835)
                ·
                  rfl

theorem cell23_7745077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 3, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 3, 3, 8].length) (baseStart_7745077 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7745077 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7745077 prefixEnd_7745077 := by exact prefixLift 7745077
  have htrace : WordTrace (prefixWord ++ tailWord_7745077) baseStart_7745077 baseEnd_7745077 := by
    simpa [prefixWord, tailWord_7745077, baseEnd_7745077] using wordTrace_append hprefix tailTrace_7745077
  have hstable : (prefixWord ++ tailWord_7745077).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7745077).length < 2 ^ (prefixWord ++ tailWord_7745077).sum := by decide
  have hdescent : baseEnd_7745077 < baseStart_7745077 := by decide
  rcases family_descends (prefixWord ++ tailWord_7745077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7745104 : List Nat := [2, 1, 1, 1, 1, 3, 4, 2, 4, 1, 3]
def baseStart_7745104 : Nat := 118140960795 + 7745104 * 2 ^ 59
def prefixEnd_7745104 : Nat := 4983230072969 + 3 ^ 40 * 7745104 * 2
def baseEnd_7745104 : Nat := 3976961071060370478680921

theorem tailTrace_7745104 : CollatzResearch.WordTrace tailWord_7745104 prefixEnd_7745104 3976961071060370478680921 := by
  unfold tailWord_7745104
  simp only [CollatzResearch.WordTrace]
  refine ⟨141243575066409220649065183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 188324766755212294198753577 141243575066409220649065183)
  ·
    refine ⟨211865362599613830973597775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141243575066409220649065183 211865362599613830973597775)
    ·
      refine ⟨317798043899420746460396663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 211865362599613830973597775 317798043899420746460396663)
      ·
        refine ⟨476697065849131119690594995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 317798043899420746460396663 476697065849131119690594995)
        ·
          refine ⟨715045598773696679535892493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 476697065849131119690594995 715045598773696679535892493)
          ·
            refine ⟨268142099540136254825959685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 715045598773696679535892493 268142099540136254825959685)
            ·
              refine ⟨50276643663775547779867441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 268142099540136254825959685 50276643663775547779867441)
              ·
                refine ⟨37707482747831660834900581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50276643663775547779867441 37707482747831660834900581)
                ·
                  refine ⟨7070153015218436406543859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 37707482747831660834900581 7070153015218436406543859)
                  ·
                    refine ⟨10605229522827654609815789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7070153015218436406543859 10605229522827654609815789)
                    ·
                      refine ⟨3976961071060370478680921, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10605229522827654609815789 3976961071060370478680921)
                      ·
                        rfl

theorem cell23_7745104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 4, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 4, 2, 4, 1, 3].length) (baseStart_7745104 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7745104 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7745104 prefixEnd_7745104 := by exact prefixLift 7745104
  have htrace : WordTrace (prefixWord ++ tailWord_7745104) baseStart_7745104 baseEnd_7745104 := by
    simpa [prefixWord, tailWord_7745104, baseEnd_7745104] using wordTrace_append hprefix tailTrace_7745104
  have hstable : (prefixWord ++ tailWord_7745104).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7745104).length < 2 ^ (prefixWord ++ tailWord_7745104).sum := by decide
  have hdescent : baseEnd_7745104 < baseStart_7745104 := by decide
  rcases family_descends (prefixWord ++ tailWord_7745104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7745127 : List Nat := [1, 1, 5, 1, 1, 1, 2, 1, 1, 5, 4]
def baseStart_7745127 : Nat := 118140960795 + 7745127 * 2 ^ 59
def prefixEnd_7745127 : Nat := 4983230072969 + 3 ^ 40 * 7745127 * 2
def baseEnd_7745127 : Nat := 3976972881115423888693315

theorem tailTrace_7745127 : CollatzResearch.WordTrace tailWord_7745127 prefixEnd_7745127 3976972881115423888693315 := by
  unfold tailWord_7745127
  simp only [CollatzResearch.WordTrace]
  refine ⟨282487989011735116226217635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188325326007823410817478423 282487989011735116226217635)
  ·
    refine ⟨423731983517602674339326453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 282487989011735116226217635 423731983517602674339326453)
    ·
      refine ⟨39724873454775250719311855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 423731983517602674339326453 39724873454775250719311855)
      ·
        refine ⟨59587310182162876078967783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39724873454775250719311855 59587310182162876078967783)
        ·
          refine ⟨89380965273244314118451675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59587310182162876078967783 89380965273244314118451675)
          ·
            refine ⟨134071447909866471177677513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89380965273244314118451675 134071447909866471177677513)
            ·
              refine ⟨100553585932399853383258135, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 134071447909866471177677513 100553585932399853383258135)
              ·
                refine ⟨150830378898599780074887203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 100553585932399853383258135 150830378898599780074887203)
                ·
                  refine ⟨226245568347899670112330805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 150830378898599780074887203 226245568347899670112330805)
                  ·
                    refine ⟨21210522032615594073031013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 226245568347899670112330805 21210522032615594073031013)
                    ·
                      refine ⟨3976972881115423888693315, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21210522032615594073031013 3976972881115423888693315)
                      ·
                        rfl

theorem cell23_7745127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 2, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 2, 1, 1, 5, 4].length) (baseStart_7745127 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7745127 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7745127 prefixEnd_7745127 := by exact prefixLift 7745127
  have htrace : WordTrace (prefixWord ++ tailWord_7745127) baseStart_7745127 baseEnd_7745127 := by
    simpa [prefixWord, tailWord_7745127, baseEnd_7745127] using wordTrace_append hprefix tailTrace_7745127
  have hstable : (prefixWord ++ tailWord_7745127).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7745127).length < 2 ^ (prefixWord ++ tailWord_7745127).sum := by decide
  have hdescent : baseEnd_7745127 < baseStart_7745127 := by decide
  rcases family_descends (prefixWord ++ tailWord_7745127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7745147 : List Nat := [1, 1, 1, 1, 1, 4, 4, 2, 2, 1, 5]
def baseStart_7745147 : Nat := 118140960795 + 7745147 * 2 ^ 59
def prefixEnd_7745147 : Nat := 4983230072969 + 3 ^ 40 * 7745147 * 2
def baseEnd_7745147 : Nat := 3976983150728513810443223

theorem tailTrace_7745147 : CollatzResearch.WordTrace tailWord_7745147 prefixEnd_7745147 3976983150728513810443223 := by
  unfold tailWord_7745147
  simp only [CollatzResearch.WordTrace]
  refine ⟨282488718471662659641945695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188325812314441773094630463 282488718471662659641945695)
  ·
    refine ⟨423733077707493989462918543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 282488718471662659641945695 423733077707493989462918543)
    ·
      refine ⟨635599616561240984194377815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 423733077707493989462918543 635599616561240984194377815)
      ·
        refine ⟨953399424841861476291566723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 635599616561240984194377815 953399424841861476291566723)
        ·
          refine ⟨1430099137262792214437350085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 953399424841861476291566723 1430099137262792214437350085)
          ·
            refine ⟨268143588236773540207003141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1430099137262792214437350085 268143588236773540207003141)
            ·
              refine ⟨50276922794395038788813089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 268143588236773540207003141 50276922794395038788813089)
              ·
                refine ⟨37707692095796279091609817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50276922794395038788813089 37707692095796279091609817)
                ·
                  refine ⟨28280769071847209318707363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37707692095796279091609817 28280769071847209318707363)
                  ·
                    refine ⟨42421153607770813978061045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 28280769071847209318707363 42421153607770813978061045)
                    ·
                      refine ⟨3976983150728513810443223, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 42421153607770813978061045 3976983150728513810443223)
                      ·
                        rfl

theorem cell23_7745147_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 4, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 4, 2, 2, 1, 5].length) (baseStart_7745147 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7745147 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7745147 prefixEnd_7745147 := by exact prefixLift 7745147
  have htrace : WordTrace (prefixWord ++ tailWord_7745147) baseStart_7745147 baseEnd_7745147 := by
    simpa [prefixWord, tailWord_7745147, baseEnd_7745147] using wordTrace_append hprefix tailTrace_7745147
  have hstable : (prefixWord ++ tailWord_7745147).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7745147).length < 2 ^ (prefixWord ++ tailWord_7745147).sum := by decide
  have hdescent : baseEnd_7745147 < baseStart_7745147 := by decide
  rcases family_descends (prefixWord ++ tailWord_7745147) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7745161 : List Nat := [1, 2, 1, 1, 4, 1, 3, 2, 4, 2, 2]
def baseStart_7745161 : Nat := 118140960795 + 7745161 * 2 ^ 59
def prefixEnd_7745161 : Nat := 4983230072969 + 3 ^ 40 * 7745161 * 2
def baseEnd_7745161 : Nat := 3976990339457676755668159

theorem tailTrace_7745161 : CollatzResearch.WordTrace tailWord_7745161 prefixEnd_7745161 3976990339457676755668159 := by
  unfold tailWord_7745161
  simp only [CollatzResearch.WordTrace]
  refine ⟨282489229093611940032955337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188326152729074626688636891 282489229093611940032955337)
  ·
    refine ⟨211866921820208955024716503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 282489229093611940032955337 211866921820208955024716503)
    ·
      refine ⟨317800382730313432537074755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 211866921820208955024716503 317800382730313432537074755)
      ·
        refine ⟨476700574095470148805612133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 317800382730313432537074755 476700574095470148805612133)
        ·
          refine ⟨89381357642900652901052275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 476700574095470148805612133 89381357642900652901052275)
          ·
            refine ⟨134072036464350979351578413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89381357642900652901052275 134072036464350979351578413)
            ·
              refine ⟨50277013674131617256841905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 134072036464350979351578413 50277013674131617256841905)
              ·
                refine ⟨37707760255598712942631429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50277013674131617256841905 37707760255598712942631429)
                ·
                  refine ⟨7070205047924758676743393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 37707760255598712942631429 7070205047924758676743393)
                  ·
                    refine ⟨5302653785943569007557545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7070205047924758676743393 5302653785943569007557545)
                    ·
                      refine ⟨3976990339457676755668159, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5302653785943569007557545 3976990339457676755668159)
                      ·
                        rfl

theorem cell23_7745161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 3, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 3, 2, 4, 2, 2].length) (baseStart_7745161 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7745161 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7745161 prefixEnd_7745161 := by exact prefixLift 7745161
  have htrace : WordTrace (prefixWord ++ tailWord_7745161) baseStart_7745161 baseEnd_7745161 := by
    simpa [prefixWord, tailWord_7745161, baseEnd_7745161] using wordTrace_append hprefix tailTrace_7745161
  have hstable : (prefixWord ++ tailWord_7745161).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7745161).length < 2 ^ (prefixWord ++ tailWord_7745161).sum := by decide
  have hdescent : baseEnd_7745161 < baseStart_7745161 := by decide
  rcases family_descends (prefixWord ++ tailWord_7745161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7745184 : List Nat := [2, 1, 1, 4, 3, 1, 3, 1, 7]
def baseStart_7745184 : Nat := 118140960795 + 7745184 * 2 ^ 59
def prefixEnd_7745184 : Nat := 4983230072969 + 3 ^ 40 * 7745184 * 2
def baseEnd_7745184 : Nat := 441889127723636685075617

theorem tailTrace_7745184 : CollatzResearch.WordTrace tailWord_7745184 prefixEnd_7745184 441889127723636685075617 := by
  unfold tailWord_7745184
  simp only [CollatzResearch.WordTrace]
  refine ⟨141245033986264307480521303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 188326711981685743307361737 141245033986264307480521303)
  ·
    refine ⟨211867550979396461220781955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141245033986264307480521303 211867550979396461220781955)
    ·
      refine ⟨317801326469094691831172933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 211867550979396461220781955 317801326469094691831172933)
      ·
        refine ⟨59587748712955254718344925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 317801326469094691831172933 59587748712955254718344925)
        ·
          refine ⟨22345405767358220519379347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 59587748712955254718344925 22345405767358220519379347)
          ·
            refine ⟨33518108651037330779069021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22345405767358220519379347 33518108651037330779069021)
            ·
              refine ⟨12569290744138999042150883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33518108651037330779069021 12569290744138999042150883)
              ·
                refine ⟨18853936116208498563226325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12569290744138999042150883 18853936116208498563226325)
                ·
                  refine ⟨441889127723636685075617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18853936116208498563226325 441889127723636685075617)
                  ·
                    rfl

theorem cell23_7745184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 1, 3, 1, 7].length) (baseStart_7745184 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7745184 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7745184 prefixEnd_7745184 := by exact prefixLift 7745184
  have htrace : WordTrace (prefixWord ++ tailWord_7745184) baseStart_7745184 baseEnd_7745184 := by
    simpa [prefixWord, tailWord_7745184, baseEnd_7745184] using wordTrace_append hprefix tailTrace_7745184
  have hstable : (prefixWord ++ tailWord_7745184).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7745184).length < 2 ^ (prefixWord ++ tailWord_7745184).sum := by decide
  have hdescent : baseEnd_7745184 < baseStart_7745184 := by decide
  rcases family_descends (prefixWord ++ tailWord_7745184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7745257 : List Nat := [1, 2, 1, 1, 1, 2, 3, 2, 10]
def baseStart_7745257 : Nat := 118140960795 + 7745257 * 2 ^ 59
def prefixEnd_7745257 : Nat := 4983230072969 + 3 ^ 40 * 7745257 * 2
def baseEnd_7745257 : Nat := 441893292622278708896413

theorem tailTrace_7745257 : CollatzResearch.WordTrace tailWord_7745257 prefixEnd_7745257 441893292622278708896413 := by
  unfold tailWord_7745257
  simp only [CollatzResearch.WordTrace]
  refine ⟨282492730501264148428450025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188328487000842765618966683 282492730501264148428450025)
  ·
    refine ⟨211869547875948111321337519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 282492730501264148428450025 211869547875948111321337519)
    ·
      refine ⟨317804321813922166982006279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 211869547875948111321337519 317804321813922166982006279)
      ·
        refine ⟨476706482720883250473009419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 317804321813922166982006279 476706482720883250473009419)
        ·
          refine ⟨715059724081324875709514129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 476706482720883250473009419 715059724081324875709514129)
          ·
            refine ⟨536294793060993656782135597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 715059724081324875709514129 536294793060993656782135597)
            ·
              refine ⟨201110547397872621293300849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 536294793060993656782135597 201110547397872621293300849)
              ·
                refine ⟨150832910548404465969975637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 201110547397872621293300849 150832910548404465969975637)
                ·
                  refine ⟨441893292622278708896413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 150832910548404465969975637 441893292622278708896413)
                  ·
                    rfl

theorem cell23_7745257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 3, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 3, 2, 10].length) (baseStart_7745257 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7745257 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7745257 prefixEnd_7745257 := by exact prefixLift 7745257
  have htrace : WordTrace (prefixWord ++ tailWord_7745257) baseStart_7745257 baseEnd_7745257 := by
    simpa [prefixWord, tailWord_7745257, baseEnd_7745257] using wordTrace_append hprefix tailTrace_7745257
  have hstable : (prefixWord ++ tailWord_7745257).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7745257).length < 2 ^ (prefixWord ++ tailWord_7745257).sum := by decide
  have hdescent : baseEnd_7745257 < baseStart_7745257 := by decide
  rcases family_descends (prefixWord ++ tailWord_7745257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7745261 : List Nat := [1, 5, 1, 2, 1, 2, 1, 1, 5, 4]
def baseStart_7745261 : Nat := 118140960795 + 7745261 * 2 ^ 59
def prefixEnd_7745261 : Nat := 4983230072969 + 3 ^ 40 * 7745261 * 2
def baseEnd_7745261 : Nat := 1325680562507708788139233

theorem tailTrace_7745261 : CollatzResearch.WordTrace tailWord_7745261 prefixEnd_7745261 1325680562507708788139233 := by
  unfold tailWord_7745261
  simp only [CollatzResearch.WordTrace]
  refine ⟨282492876393249657111595637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188328584262166438074397091 282492876393249657111595637)
  ·
    refine ⟨26483707161867155354212091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 282492876393249657111595637 26483707161867155354212091)
    ·
      refine ⟨39725560742800733031318137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26483707161867155354212091 39725560742800733031318137)
      ·
        refine ⟨29794170557100549773488603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39725560742800733031318137 29794170557100549773488603)
        ·
          refine ⟨44691255835650824660232905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29794170557100549773488603 44691255835650824660232905)
          ·
            refine ⟨33518441876738118495174679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44691255835650824660232905 33518441876738118495174679)
            ·
              refine ⟨50277662815107177742762019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33518441876738118495174679 50277662815107177742762019)
              ·
                refine ⟨75416494222660766614143029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50277662815107177742762019 75416494222660766614143029)
                ·
                  refine ⟨7070296333374446870075909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 75416494222660766614143029 7070296333374446870075909)
                  ·
                    refine ⟨1325680562507708788139233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7070296333374446870075909 1325680562507708788139233)
                    ·
                      rfl

theorem cell23_7745261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 2, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 2, 1, 1, 5, 4].length) (baseStart_7745261 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7745261 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7745261 prefixEnd_7745261 := by exact prefixLift 7745261
  have htrace : WordTrace (prefixWord ++ tailWord_7745261) baseStart_7745261 baseEnd_7745261 := by
    simpa [prefixWord, tailWord_7745261, baseEnd_7745261] using wordTrace_append hprefix tailTrace_7745261
  have hstable : (prefixWord ++ tailWord_7745261).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7745261).length < 2 ^ (prefixWord ++ tailWord_7745261).sum := by decide
  have hdescent : baseEnd_7745261 < baseStart_7745261 := by decide
  rcases family_descends (prefixWord ++ tailWord_7745261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7745271 : List Nat := [1, 1, 3, 1, 1, 1, 7, 1, 2, 2, 3]
def baseStart_7745271 : Nat := 118140960795 + 7745271 * 2 ^ 59
def prefixEnd_7745271 : Nat := 4983230072969 + 3 ^ 40 * 7745271 * 2
def baseEnd_7745271 : Nat := 3977046822329671325292653

theorem tailTrace_7745271 : CollatzResearch.WordTrace tailWord_7745271 prefixEnd_7745271 3977046822329671325292653 := by
  unfold tailWord_7745271
  simp only [CollatzResearch.WordTrace]
  refine ⟨282493241123213428819459667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188328827415475619212973111 282493241123213428819459667)
  ·
    refine ⟨423739861684820143229189501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 282493241123213428819459667 423739861684820143229189501)
    ·
      refine ⟨158902448131807553710946063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 423739861684820143229189501 158902448131807553710946063)
      ·
        refine ⟨238353672197711330566419095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 158902448131807553710946063 238353672197711330566419095)
        ·
          refine ⟨357530508296566995849628643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 238353672197711330566419095 357530508296566995849628643)
          ·
            refine ⟨536295762444850493774442965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 357530508296566995849628643 536295762444850493774442965)
            ·
              refine ⟨12569431932301183447838507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 536295762444850493774442965 12569431932301183447838507)
              ·
                refine ⟨18854147898451775171757761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12569431932301183447838507 18854147898451775171757761)
                ·
                  refine ⟨14140610923838831378818321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18854147898451775171757761 14140610923838831378818321)
                  ·
                    refine ⟨10605458192879123534113741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14140610923838831378818321 10605458192879123534113741)
                    ·
                      refine ⟨3977046822329671325292653, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10605458192879123534113741 3977046822329671325292653)
                      ·
                        rfl

theorem cell23_7745271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 7, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 7, 1, 2, 2, 3].length) (baseStart_7745271 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7745271 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7745271 prefixEnd_7745271 := by exact prefixLift 7745271
  have htrace : WordTrace (prefixWord ++ tailWord_7745271) baseStart_7745271 baseEnd_7745271 := by
    simpa [prefixWord, tailWord_7745271, baseEnd_7745271] using wordTrace_append hprefix tailTrace_7745271
  have hstable : (prefixWord ++ tailWord_7745271).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7745271).length < 2 ^ (prefixWord ++ tailWord_7745271).sum := by decide
  have hdescent : baseEnd_7745271 < baseStart_7745271 := by decide
  rcases family_descends (prefixWord ++ tailWord_7745271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7745294 : List Nat := [4, 1, 1, 2, 1, 1, 3, 1, 1, 2, 6]
def baseStart_7745294 : Nat := 118140960795 + 7745294 * 2 ^ 59
def prefixEnd_7745294 : Nat := 4983230072969 + 3 ^ 40 * 7745294 * 2
def baseEnd_7745294 : Nat := 3977058632384724735305047

theorem tailTrace_7745294 : CollatzResearch.WordTrace tailWord_7745294 prefixEnd_7745294 3977058632384724735305047 := by
  unfold tailWord_7745294
  simp only [CollatzResearch.WordTrace]
  refine ⟨35311760000266262968443367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 188329386668086735831697957 35311760000266262968443367)
  ·
    refine ⟨52967640000399394452665051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35311760000266262968443367 52967640000399394452665051)
    ·
      refine ⟨79451460000599091678997577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52967640000399394452665051 79451460000599091678997577)
      ·
        refine ⟨59588595000449318759248183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79451460000599091678997577 59588595000449318759248183)
        ·
          refine ⟨89382892500673978138872275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59588595000449318759248183 89382892500673978138872275)
          ·
            refine ⟨134074338751010967208308413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89382892500673978138872275 134074338751010967208308413)
            ·
              refine ⟨50277877031629112703115655, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 134074338751010967208308413 50277877031629112703115655)
              ·
                refine ⟨75416815547443669054673483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50277877031629112703115655 75416815547443669054673483)
                ·
                  refine ⟨113125223321165503582010225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 75416815547443669054673483 113125223321165503582010225)
                  ·
                    refine ⟨84843917490874127686507669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 113125223321165503582010225 84843917490874127686507669)
                    ·
                      refine ⟨3977058632384724735305047, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 84843917490874127686507669 3977058632384724735305047)
                      ·
                        rfl

theorem cell23_7745294_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 3, 1, 1, 2, 6].length) (baseStart_7745294 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7745294 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7745294 prefixEnd_7745294 := by exact prefixLift 7745294
  have htrace : WordTrace (prefixWord ++ tailWord_7745294) baseStart_7745294 baseEnd_7745294 := by
    simpa [prefixWord, tailWord_7745294, baseEnd_7745294] using wordTrace_append hprefix tailTrace_7745294
  have hstable : (prefixWord ++ tailWord_7745294).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7745294).length < 2 ^ (prefixWord ++ tailWord_7745294).sum := by decide
  have hdescent : baseEnd_7745294 < baseStart_7745294 := by decide
  rcases family_descends (prefixWord ++ tailWord_7745294) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7745304 : List Nat := [2, 1, 2, 3, 1, 1, 2, 1, 5, 5]
def baseStart_7745304 : Nat := 118140960795 + 7745304 * 2 ^ 59
def prefixEnd_7745304 : Nat := 4983230072969 + 3 ^ 40 * 7745304 * 2
def baseEnd_7745304 : Nat := 1325687922397089898726667

theorem tailTrace_7745304 : CollatzResearch.WordTrace tailWord_7745304 prefixEnd_7745304 1325687922397089898726667 := by
  unfold tailWord_7745304
  simp only [CollatzResearch.WordTrace]
  refine ⟨141247222366046937727705483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 188329629821395916970273977 141247222366046937727705483)
  ·
    refine ⟨211870833549070406591558225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141247222366046937727705483 211870833549070406591558225)
    ·
      refine ⟨158903125161802804943668669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 211870833549070406591558225 158903125161802804943668669)
      ·
        refine ⟨59588671935676051853875751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 158903125161802804943668669 59588671935676051853875751)
        ·
          refine ⟨89383007903514077780813627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59588671935676051853875751 89383007903514077780813627)
          ·
            refine ⟨134074511855271116671220441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89383007903514077780813627 134074511855271116671220441)
            ·
              refine ⟨100555883891453337503415331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 134074511855271116671220441 100555883891453337503415331)
              ·
                refine ⟨150833825837180006255122997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 100555883891453337503415331 150833825837180006255122997)
                ·
                  refine ⟨14140671172235625586417781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 150833825837180006255122997 14140671172235625586417781)
                  ·
                    refine ⟨1325687922397089898726667, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14140671172235625586417781 1325687922397089898726667)
                    ·
                      rfl

theorem cell23_7745304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 2, 1, 5, 5].length) (baseStart_7745304 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7745304 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7745304 prefixEnd_7745304 := by exact prefixLift 7745304
  have htrace : WordTrace (prefixWord ++ tailWord_7745304) baseStart_7745304 baseEnd_7745304 := by
    simpa [prefixWord, tailWord_7745304, baseEnd_7745304] using wordTrace_append hprefix tailTrace_7745304
  have hstable : (prefixWord ++ tailWord_7745304).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7745304).length < 2 ^ (prefixWord ++ tailWord_7745304).sum := by decide
  have hdescent : baseEnd_7745304 < baseStart_7745304 := by decide
  rcases family_descends (prefixWord ++ tailWord_7745304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7745311 : List Nat := [1, 1, 2, 4, 2, 1, 1, 1, 3, 5, 2]
def baseStart_7745311 : Nat := 118140960795 + 7745311 * 2 ^ 59
def prefixEnd_7745311 : Nat := 4983230072969 + 3 ^ 40 * 7745311 * 2
def baseEnd_7745311 : Nat := 3977067361555851168792469

theorem tailTrace_7745311 : CollatzResearch.WordTrace tailWord_7745311 prefixEnd_7745311 3977067361555851168792469 := by
  unfold tailWord_7745311
  simp only [CollatzResearch.WordTrace]
  refine ⟨282494700043068515650915787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188329800028712343767277191 282494700043068515650915787)
  ·
    refine ⟨423742050064602773476373681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 282494700043068515650915787 423742050064602773476373681)
    ·
      refine ⟨317806537548452080107280261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 423742050064602773476373681 317806537548452080107280261)
      ·
        refine ⟨59588725790334765020115049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 317806537548452080107280261 59588725790334765020115049)
        ·
          refine ⟨44691544342751073765086287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59588725790334765020115049 44691544342751073765086287)
          ·
            refine ⟨67037316514126610647629431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44691544342751073765086287 67037316514126610647629431)
            ·
              refine ⟨100555974771189915971444147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67037316514126610647629431 100555974771189915971444147)
              ·
                refine ⟨150833962156784873957166221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 100555974771189915971444147 150833962156784873957166221)
                ·
                  refine ⟨56562735808794327733937333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 150833962156784873957166221 56562735808794327733937333)
                  ·
                    refine ⟨5302756482074468225056625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 56562735808794327733937333 5302756482074468225056625)
                    ·
                      refine ⟨3977067361555851168792469, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5302756482074468225056625 3977067361555851168792469)
                      ·
                        rfl

theorem cell23_7745311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 1, 1, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 1, 1, 3, 5, 2].length) (baseStart_7745311 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7745311 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7745311 prefixEnd_7745311 := by exact prefixLift 7745311
  have htrace : WordTrace (prefixWord ++ tailWord_7745311) baseStart_7745311 baseEnd_7745311 := by
    simpa [prefixWord, tailWord_7745311, baseEnd_7745311] using wordTrace_append hprefix tailTrace_7745311
  have hstable : (prefixWord ++ tailWord_7745311).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7745311).length < 2 ^ (prefixWord ++ tailWord_7745311).sum := by decide
  have hdescent : baseEnd_7745311 < baseStart_7745311 := by decide
  rcases family_descends (prefixWord ++ tailWord_7745311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7745351 : List Nat := [1, 1, 4, 1, 2, 1, 4, 1, 4, 4]
def baseStart_7745351 : Nat := 118140960795 + 7745351 * 2 ^ 59
def prefixEnd_7745351 : Nat := 4983230072969 + 3 ^ 40 * 7745351 * 2
def baseEnd_7745351 : Nat := 1325695966927343670764095

theorem tailTrace_7745351 : CollatzResearch.WordTrace tailWord_7745351 prefixEnd_7745351 1325695966927343670764095 := by
  unfold tailWord_7745351
  simp only [CollatzResearch.WordTrace]
  refine ⟨282496158962923602482371907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188330772641949068321581271 282496158962923602482371907)
  ·
    refine ⟨423744238444385403723557861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 282496158962923602482371907 423744238444385403723557861)
    ·
      refine ⟨79452044708322263198167099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 423744238444385403723557861 79452044708322263198167099)
      ·
        refine ⟨119178067062483394797250649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79452044708322263198167099 119178067062483394797250649)
        ·
          refine ⟨89383550296862546097937987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 119178067062483394797250649 89383550296862546097937987)
          ·
            refine ⟨134075325445293819146906981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89383550296862546097937987 134075325445293819146906981)
            ·
              refine ⟨25139123520992591090045059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 134075325445293819146906981 25139123520992591090045059)
              ·
                refine ⟨37708685281488886635067589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25139123520992591090045059 37708685281488886635067589)
                ·
                  refine ⟨7070378490279166244075173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 37708685281488886635067589 7070378490279166244075173)
                  ·
                    refine ⟨1325695966927343670764095, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7070378490279166244075173 1325695966927343670764095)
                    ·
                      rfl

theorem cell23_7745351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 4, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 4, 1, 4, 4].length) (baseStart_7745351 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7745351 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7745351 prefixEnd_7745351 := by exact prefixLift 7745351
  have htrace : WordTrace (prefixWord ++ tailWord_7745351) baseStart_7745351 baseEnd_7745351 := by
    simpa [prefixWord, tailWord_7745351, baseEnd_7745351] using wordTrace_append hprefix tailTrace_7745351
  have hstable : (prefixWord ++ tailWord_7745351).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7745351).length < 2 ^ (prefixWord ++ tailWord_7745351).sum := by decide
  have hdescent : baseEnd_7745351 < baseStart_7745351 := by decide
  rcases family_descends (prefixWord ++ tailWord_7745351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7745352 : List Nat := [2, 1, 3, 1, 1, 5, 3, 2, 1, 1, 3]
def baseStart_7745352 : Nat := 118140960795 + 7745352 * 2 ^ 59
def prefixEnd_7745352 : Nat := 4983230072969 + 3 ^ 40 * 7745352 * 2
def baseEnd_7745352 : Nat := 3977088414262685508379781

theorem tailTrace_7745352 : CollatzResearch.WordTrace tailWord_7745352 prefixEnd_7745352 3977088414262685508379781 := by
  unfold tailWord_7745352
  simp only [CollatzResearch.WordTrace]
  refine ⟨141248097717959989826579155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 188330796957279986435438873 141248097717959989826579155)
  ·
    refine ⟨211872146576939984739868733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141248097717959989826579155 211872146576939984739868733)
    ·
      refine ⟨79452054966352494277450775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 211872146576939984739868733 79452054966352494277450775)
      ·
        refine ⟨119178082449528741416176163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79452054966352494277450775 119178082449528741416176163)
        ·
          refine ⟨178767123674293112124264245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 119178082449528741416176163 178767123674293112124264245)
          ·
            refine ⟨16759417844464979261649773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 178767123674293112124264245 16759417844464979261649773)
            ·
              refine ⟨6284781691674367223118665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16759417844464979261649773 6284781691674367223118665)
              ·
                refine ⟨4713586268755775417338999, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6284781691674367223118665 4713586268755775417338999)
                ·
                  refine ⟨7070379403133663126008499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4713586268755775417338999 7070379403133663126008499)
                  ·
                    refine ⟨10605569104700494689012749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7070379403133663126008499 10605569104700494689012749)
                    ·
                      refine ⟨3977088414262685508379781, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10605569104700494689012749 3977088414262685508379781)
                      ·
                        rfl

theorem cell23_7745352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 5, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 5, 3, 2, 1, 1, 3].length) (baseStart_7745352 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7745352 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7745352 prefixEnd_7745352 := by exact prefixLift 7745352
  have htrace : WordTrace (prefixWord ++ tailWord_7745352) baseStart_7745352 baseEnd_7745352 := by
    simpa [prefixWord, tailWord_7745352, baseEnd_7745352] using wordTrace_append hprefix tailTrace_7745352
  have hstable : (prefixWord ++ tailWord_7745352).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7745352).length < 2 ^ (prefixWord ++ tailWord_7745352).sum := by decide
  have hdescent : baseEnd_7745352 < baseStart_7745352 := by decide
  rcases family_descends (prefixWord ++ tailWord_7745352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7745354 : List Nat := [3, 1, 2, 1, 1, 1, 3, 1, 3, 1, 6]
def baseStart_7745354 : Nat := 118140960795 + 7745354 * 2 ^ 59
def prefixEnd_7745354 : Nat := 4983230072969 + 3 ^ 40 * 7745354 * 2
def baseEnd_7745354 : Nat := 3977089441223994500554771

theorem tailTrace_7745354 : CollatzResearch.WordTrace tailWord_7745354 prefixEnd_7745354 3977089441223994500554771 := by
  unfold tailWord_7745354
  simp only [CollatzResearch.WordTrace]
  refine ⟨70624067095478183498682779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 188330845587941822663154077 70624067095478183498682779)
  ·
    refine ⟨105936100643217275248024169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70624067095478183498682779 105936100643217275248024169)
    ·
      refine ⟨79452075482412956436018127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 105936100643217275248024169 79452075482412956436018127)
      ·
        refine ⟨119178113223619434654027191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79452075482412956436018127 119178113223619434654027191)
        ·
          refine ⟨178767169835429151981040787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 119178113223619434654027191 178767169835429151981040787)
          ·
            refine ⟨268150754753143727971561181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 178767169835429151981040787 268150754753143727971561181)
            ·
              refine ⟨100556533032428897989335443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 268150754753143727971561181 100556533032428897989335443)
              ·
                refine ⟨150834799548643346984003165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 100556533032428897989335443 150834799548643346984003165)
                ·
                  refine ⟨56563049830741255119001187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 150834799548643346984003165 56563049830741255119001187)
                  ·
                    refine ⟨84844574746111882678501781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 56563049830741255119001187 84844574746111882678501781)
                    ·
                      refine ⟨3977089441223994500554771, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 84844574746111882678501781 3977089441223994500554771)
                      ·
                        rfl

theorem cell23_7745354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 3, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 3, 1, 3, 1, 6].length) (baseStart_7745354 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7745354 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7745354 prefixEnd_7745354 := by exact prefixLift 7745354
  have htrace : WordTrace (prefixWord ++ tailWord_7745354) baseStart_7745354 baseEnd_7745354 := by
    simpa [prefixWord, tailWord_7745354, baseEnd_7745354] using wordTrace_append hprefix tailTrace_7745354
  have hstable : (prefixWord ++ tailWord_7745354).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7745354).length < 2 ^ (prefixWord ++ tailWord_7745354).sum := by decide
  have hdescent : baseEnd_7745354 < baseStart_7745354 := by decide
  rcases family_descends (prefixWord ++ tailWord_7745354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7745361 : List Nat := [1, 2, 2, 1, 5, 1, 2, 2, 1, 1, 5]
def baseStart_7745361 : Nat := 118140960795 + 7745361 * 2 ^ 59
def prefixEnd_7745361 : Nat := 4983230072969 + 3 ^ 40 * 7745361 * 2
def baseEnd_7745361 : Nat := 3977093035588575973167239

theorem tailTrace_7745361 : CollatzResearch.WordTrace tailWord_7745361 prefixEnd_7745361 3977093035588575973167239 := by
  unfold tailWord_7745361
  simp only [CollatzResearch.WordTrace]
  refine ⟨282496523692887374190235937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188331015795258249460157291 282496523692887374190235937)
  ·
    refine ⟨211872392769665530642676953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 282496523692887374190235937 211872392769665530642676953)
    ·
      refine ⟨158904294577249147982007715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 211872392769665530642676953 158904294577249147982007715)
      ·
        refine ⟨238356441865873721973011573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 158904294577249147982007715 238356441865873721973011573)
        ·
          refine ⟨22345916424925661434969835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 238356441865873721973011573 22345916424925661434969835)
          ·
            refine ⟨33518874637388492152454753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22345916424925661434969835 33518874637388492152454753)
            ·
              refine ⟨25139155978041369114341065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33518874637388492152454753 25139155978041369114341065)
              ·
                refine ⟨18854366983531026835755799, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25139155978041369114341065 18854366983531026835755799)
                ·
                  refine ⟨28281550475296540253633699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18854366983531026835755799 28281550475296540253633699)
                  ·
                    refine ⟨42422325712944810380450549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 28281550475296540253633699 42422325712944810380450549)
                    ·
                      refine ⟨3977093035588575973167239, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 42422325712944810380450549 3977093035588575973167239)
                      ·
                        rfl

theorem cell23_7745361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 1, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 1, 2, 2, 1, 1, 5].length) (baseStart_7745361 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7745361 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7745361 prefixEnd_7745361 := by exact prefixLift 7745361
  have htrace : WordTrace (prefixWord ++ tailWord_7745361) baseStart_7745361 baseEnd_7745361 := by
    simpa [prefixWord, tailWord_7745361, baseEnd_7745361] using wordTrace_append hprefix tailTrace_7745361
  have hstable : (prefixWord ++ tailWord_7745361).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7745361).length < 2 ^ (prefixWord ++ tailWord_7745361).sum := by decide
  have hdescent : baseEnd_7745361 < baseStart_7745361 := by decide
  rcases family_descends (prefixWord ++ tailWord_7745361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7745372 : List Nat := [2, 2, 4, 2, 3, 1, 1, 2, 1, 5]
def baseStart_7745372 : Nat := 118140960795 + 7745372 * 2 ^ 59
def prefixEnd_7745372 : Nat := 4983230072969 + 3 ^ 40 * 7745372 * 2
def baseEnd_7745372 : Nat := 1325699561291925143376563

theorem tailTrace_7745372 : CollatzResearch.WordTrace tailWord_7745372 prefixEnd_7745372 1325699561291925143376563 := by
  unfold tailWord_7745372
  simp only [CollatzResearch.WordTrace]
  refine ⟨141248462447923761534443185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 188331283263898348712590913 141248462447923761534443185)
  ·
    refine ⟨105936346835942821150832389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 141248462447923761534443185 105936346835942821150832389)
    ·
      refine ⟨19863065031739278965781073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 105936346835942821150832389 19863065031739278965781073)
      ·
        refine ⟨14897298773804459224335805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19863065031739278965781073 14897298773804459224335805)
        ·
          refine ⟨5586487040176672209125927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14897298773804459224335805 5586487040176672209125927)
          ·
            refine ⟨8379730560265008313688891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5586487040176672209125927 8379730560265008313688891)
            ·
              refine ⟨12569595840397512470533337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8379730560265008313688891 12569595840397512470533337)
              ·
                refine ⟨9427196880298134352900003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12569595840397512470533337 9427196880298134352900003)
                ·
                  refine ⟨14140795320447201529350005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9427196880298134352900003 14140795320447201529350005)
                  ·
                    refine ⟨1325699561291925143376563, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14140795320447201529350005 1325699561291925143376563)
                    ·
                      rfl

theorem cell23_7745372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 3, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 3, 1, 1, 2, 1, 5].length) (baseStart_7745372 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7745372 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7745372 prefixEnd_7745372 := by exact prefixLift 7745372
  have htrace : WordTrace (prefixWord ++ tailWord_7745372) baseStart_7745372 baseEnd_7745372 := by
    simpa [prefixWord, tailWord_7745372, baseEnd_7745372] using wordTrace_append hprefix tailTrace_7745372
  have hstable : (prefixWord ++ tailWord_7745372).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7745372).length < 2 ^ (prefixWord ++ tailWord_7745372).sum := by decide
  have hdescent : baseEnd_7745372 < baseStart_7745372 := by decide
  rcases family_descends (prefixWord ++ tailWord_7745372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7745398 : List Nat := [5, 1, 1, 3, 3, 10]
def baseStart_7745398 : Nat := 118140960795 + 7745398 * 2 ^ 59
def prefixEnd_7745398 : Nat := 4983230072969 + 3 ^ 40 * 7745398 * 2
def baseEnd_7745398 : Nat := 16366716190834536330883

theorem tailTrace_7745398 : CollatzResearch.WordTrace tailWord_7745398 prefixEnd_7745398 16366716190834536330883 := by
  unfold tailWord_7745398
  simp only [CollatzResearch.WordTrace]
  refine ⟨17656117074609583094333303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 188331915462502219672888565 17656117074609583094333303)
  ·
    refine ⟨26484175611914374641499955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17656117074609583094333303 26484175611914374641499955)
    ·
      refine ⟨39726263417871561962249933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26484175611914374641499955 39726263417871561962249933)
      ·
        refine ⟨14897348781701835735843725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39726263417871561962249933 14897348781701835735843725)
        ·
          refine ⟨5586505793138188400941397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14897348781701835735843725 5586505793138188400941397)
          ·
            refine ⟨16366716190834536330883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 5586505793138188400941397 16366716190834536330883)
            ·
              rfl

theorem cell23_7745398_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 3, 10].length) (baseStart_7745398 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7745398 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7745398 prefixEnd_7745398 := by exact prefixLift 7745398
  have htrace : WordTrace (prefixWord ++ tailWord_7745398) baseStart_7745398 baseEnd_7745398 := by
    simpa [prefixWord, tailWord_7745398, baseEnd_7745398] using wordTrace_append hprefix tailTrace_7745398
  have hstable : (prefixWord ++ tailWord_7745398).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7745398).length < 2 ^ (prefixWord ++ tailWord_7745398).sum := by decide
  have hdescent : baseEnd_7745398 < baseStart_7745398 := by decide
  rcases family_descends (prefixWord ++ tailWord_7745398) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7745404 : List Nat := [2, 2, 2, 1, 1, 1, 1, 1, 2, 3, 7]
def baseStart_7745404 : Nat := 118140960795 + 7745404 * 2 ^ 59
def prefixEnd_7745404 : Nat := 4983230072969 + 3 ^ 40 * 7745404 * 2
def baseEnd_7745404 : Nat := 3977115115256719304929541

theorem tailTrace_7745404 : CollatzResearch.WordTrace tailWord_7745404 prefixEnd_7745404 3977115115256719304929541 := by
  unfold tailWord_7745404
  simp only [CollatzResearch.WordTrace]
  refine ⟨141249046015865796267025633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 188332061354487728356034177 141249046015865796267025633)
  ·
    refine ⟨105936784511899347200269225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 141249046015865796267025633 105936784511899347200269225)
    ·
      refine ⟨79452588383924510400201919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 105936784511899347200269225 79452588383924510400201919)
      ·
        refine ⟨119178882575886765600302879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79452588383924510400201919 119178882575886765600302879)
        ·
          refine ⟨178768323863830148400454319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 119178882575886765600302879 178768323863830148400454319)
          ·
            refine ⟨268152485795745222600681479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 178768323863830148400454319 268152485795745222600681479)
            ·
              refine ⟨402228728693617833901022219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 268152485795745222600681479 402228728693617833901022219)
              ·
                refine ⟨603343093040426750851533329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 402228728693617833901022219 603343093040426750851533329)
                ·
                  refine ⟨452507319780320063138649997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 603343093040426750851533329 452507319780320063138649997)
                  ·
                    refine ⟨169690244917620023676993749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 452507319780320063138649997 169690244917620023676993749)
                    ·
                      refine ⟨3977115115256719304929541, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 169690244917620023676993749 3977115115256719304929541)
                      ·
                        rfl

theorem cell23_7745404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 1, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 1, 1, 2, 3, 7].length) (baseStart_7745404 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7745404 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7745404 prefixEnd_7745404 := by exact prefixLift 7745404
  have htrace : WordTrace (prefixWord ++ tailWord_7745404) baseStart_7745404 baseEnd_7745404 := by
    simpa [prefixWord, tailWord_7745404, baseEnd_7745404] using wordTrace_append hprefix tailTrace_7745404
  have hstable : (prefixWord ++ tailWord_7745404).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7745404).length < 2 ^ (prefixWord ++ tailWord_7745404).sum := by decide
  have hdescent : baseEnd_7745404 < baseStart_7745404 := by decide
  rcases family_descends (prefixWord ++ tailWord_7745404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7745424 : List Nat := [2, 1, 1, 1, 1, 1, 2, 5, 1, 8]
def baseStart_7745424 : Nat := 118140960795 + 7745424 * 2 ^ 59
def prefixEnd_7745424 : Nat := 4983230072969 + 3 ^ 40 * 7745424 * 2
def baseEnd_7745424 : Nat := 1325708461623269742226483

theorem tailTrace_7745424 : CollatzResearch.WordTrace tailWord_7745424 prefixEnd_7745424 1325708461623269742226483 := by
  unfold tailWord_7745424
  simp only [CollatzResearch.WordTrace]
  refine ⟨141249410745829567974889663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 188332547661106090633186217 141249410745829567974889663)
  ·
    refine ⟨211874116118744351962334495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141249410745829567974889663 211874116118744351962334495)
    ·
      refine ⟨317811174178116527943501743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 211874116118744351962334495 317811174178116527943501743)
      ·
        refine ⟨476716761267174791915252615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 317811174178116527943501743 476716761267174791915252615)
        ·
          refine ⟨715075141900762187872878923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 476716761267174791915252615 715075141900762187872878923)
          ·
            refine ⟨1072612712851143281809318385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 715075141900762187872878923 1072612712851143281809318385)
            ·
              refine ⟨804459534638357461356988789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1072612712851143281809318385 804459534638357461356988789)
              ·
                refine ⟨75418081372346012002217699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 804459534638357461356988789 75418081372346012002217699)
                ·
                  refine ⟨113127122058519018003326549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 75418081372346012002217699 113127122058519018003326549)
                  ·
                    refine ⟨1325708461623269742226483, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 113127122058519018003326549 1325708461623269742226483)
                    ·
                      rfl

theorem cell23_7745424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 5, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 5, 1, 8].length) (baseStart_7745424 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7745424 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7745424 prefixEnd_7745424 := by exact prefixLift 7745424
  have htrace : WordTrace (prefixWord ++ tailWord_7745424) baseStart_7745424 baseEnd_7745424 := by
    simpa [prefixWord, tailWord_7745424, baseEnd_7745424] using wordTrace_append hprefix tailTrace_7745424
  have hstable : (prefixWord ++ tailWord_7745424).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7745424).length < 2 ^ (prefixWord ++ tailWord_7745424).sum := by decide
  have hdescent : baseEnd_7745424 < baseStart_7745424 := by decide
  rcases family_descends (prefixWord ++ tailWord_7745424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7745465 : List Nat := [1, 2, 1, 4, 2, 1, 3, 1, 4, 2, 2]
def baseStart_7745465 : Nat := 118140960795 + 7745465 * 2 ^ 59
def prefixEnd_7745465 : Nat := 4983230072969 + 3 ^ 40 * 7745465 * 2
def baseEnd_7745465 : Nat := 3977146437576643566266761

theorem tailTrace_7745465 : CollatzResearch.WordTrace tailWord_7745465 prefixEnd_7745465 3977146437576643566266761 := by
  unfold tailWord_7745465
  simp only [CollatzResearch.WordTrace]
  refine ⟨282500316884510599952021849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188333544589673733301347899 282500316884510599952021849)
  ·
    refine ⟨211875237663382949964016387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 282500316884510599952021849 211875237663382949964016387)
    ·
      refine ⟨317812856495074424946024581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 211875237663382949964016387 317812856495074424946024581)
      ·
        refine ⟨59589910592826454677379609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 317812856495074424946024581 59589910592826454677379609)
        ·
          refine ⟨44692432944619841008034707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59589910592826454677379609 44692432944619841008034707)
          ·
            refine ⟨67038649416929761512052061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44692432944619841008034707 67038649416929761512052061)
            ·
              refine ⟨25139493531348660567019523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 67038649416929761512052061 25139493531348660567019523)
              ·
                refine ⟨37709240297022990850529285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25139493531348660567019523 37709240297022990850529285)
                ·
                  refine ⟨7070482555691810784474241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 37709240297022990850529285 7070482555691810784474241)
                  ·
                    refine ⟨5302861916768858088355681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7070482555691810784474241 5302861916768858088355681)
                    ·
                      refine ⟨3977146437576643566266761, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5302861916768858088355681 3977146437576643566266761)
                      ·
                        rfl

theorem cell23_7745465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 3, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 3, 1, 4, 2, 2].length) (baseStart_7745465 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7745465 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7745465 prefixEnd_7745465 := by exact prefixLift 7745465
  have htrace : WordTrace (prefixWord ++ tailWord_7745465) baseStart_7745465 baseEnd_7745465 := by
    simpa [prefixWord, tailWord_7745465, baseEnd_7745465] using wordTrace_append hprefix tailTrace_7745465
  have hstable : (prefixWord ++ tailWord_7745465).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7745465).length < 2 ^ (prefixWord ++ tailWord_7745465).sum := by decide
  have hdescent : baseEnd_7745465 < baseStart_7745465 := by decide
  rcases family_descends (prefixWord ++ tailWord_7745465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7745471 : List Nat := [1, 1, 2, 2, 2, 1, 6, 1, 7]
def baseStart_7745471 : Nat := 118140960795 + 7745471 * 2 ^ 59
def prefixEnd_7745471 : Nat := 4983230072969 + 3 ^ 40 * 7745471 * 2
def baseEnd_7745471 : Nat := 441905502051174504754637

theorem tailTrace_7745471 : CollatzResearch.WordTrace tailWord_7745471 prefixEnd_7745471 441905502051174504754637 := by
  unfold tailWord_7745471
  simp only [CollatzResearch.WordTrace]
  refine ⟨282500535722488862976740267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188333690481659241984493511 282500535722488862976740267)
  ·
    refine ⟨423750803583733294465110401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 282500535722488862976740267 423750803583733294465110401)
    ·
      refine ⟨317813102687799970848832801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 423750803583733294465110401 317813102687799970848832801)
      ·
        refine ⟨238359827015849978136624601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 317813102687799970848832801 238359827015849978136624601)
        ·
          refine ⟨178769870261887483602468451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 238359827015849978136624601 178769870261887483602468451)
          ·
            refine ⟨268154805392831225403702677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 178769870261887483602468451 268154805392831225403702677)
            ·
              refine ⟨12569756502788963690798563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 268154805392831225403702677 12569756502788963690798563)
              ·
                refine ⟨18854634754183445536197845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12569756502788963690798563 18854634754183445536197845)
                ·
                  refine ⟨441905502051174504754637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18854634754183445536197845 441905502051174504754637)
                  ·
                    rfl

theorem cell23_7745471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 6, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 6, 1, 7].length) (baseStart_7745471 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7745471 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7745471 prefixEnd_7745471 := by exact prefixLift 7745471
  have htrace : WordTrace (prefixWord ++ tailWord_7745471) baseStart_7745471 baseEnd_7745471 := by
    simpa [prefixWord, tailWord_7745471, baseEnd_7745471] using wordTrace_append hprefix tailTrace_7745471
  have hstable : (prefixWord ++ tailWord_7745471).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7745471).length < 2 ^ (prefixWord ++ tailWord_7745471).sum := by decide
  have hdescent : baseEnd_7745471 < baseStart_7745471 := by decide
  rcases family_descends (prefixWord ++ tailWord_7745471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7745518 : List Nat := [4, 1, 2, 1, 3, 1, 1, 1, 4, 5]
def baseStart_7745518 : Nat := 118140960795 + 7745518 * 2 ^ 59
def prefixEnd_7745518 : Nat := 4983230072969 + 3 ^ 40 * 7745518 * 2
def baseEnd_7745518 : Nat := 1325724550683777286301339

theorem tailTrace_7745518 : CollatzResearch.WordTrace tailWord_7745518 prefixEnd_7745518 1325724550683777286301339 := by
  unfold tailWord_7745518
  simp only [CollatzResearch.WordTrace]
  refine ⟨35312781244164823750462651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 188334833302212393335800805 35312781244164823750462651)
  ·
    refine ⟨52969171866247235625693977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35312781244164823750462651 52969171866247235625693977)
    ·
      refine ⟨39726878899685426719270483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52969171866247235625693977 39726878899685426719270483)
      ·
        refine ⟨59590318349528140078905725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39726878899685426719270483 59590318349528140078905725)
        ·
          refine ⟨22346369381073052529589647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 59590318349528140078905725 22346369381073052529589647)
          ·
            refine ⟨33519554071609578794384471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22346369381073052529589647 33519554071609578794384471)
            ·
              refine ⟨50279331107414368191576707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33519554071609578794384471 50279331107414368191576707)
              ·
                refine ⟨75418996661121552287365061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50279331107414368191576707 75418996661121552287365061)
                ·
                  refine ⟨14141061873960291053880949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 75418996661121552287365061 14141061873960291053880949)
                  ·
                    refine ⟨1325724550683777286301339, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14141061873960291053880949 1325724550683777286301339)
                    ·
                      rfl

theorem cell23_7745518_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 1, 1, 1, 4, 5].length) (baseStart_7745518 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7745518 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7745518 prefixEnd_7745518 := by exact prefixLift 7745518
  have htrace : WordTrace (prefixWord ++ tailWord_7745518) baseStart_7745518 baseEnd_7745518 := by
    simpa [prefixWord, tailWord_7745518, baseEnd_7745518] using wordTrace_append hprefix tailTrace_7745518
  have hstable : (prefixWord ++ tailWord_7745518).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7745518).length < 2 ^ (prefixWord ++ tailWord_7745518).sum := by decide
  have hdescent : baseEnd_7745518 < baseStart_7745518 := by decide
  rcases family_descends (prefixWord ++ tailWord_7745518) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7745548 : List Nat := [2, 2, 1, 2, 3, 1, 2, 1, 5, 4]
def baseStart_7745548 : Nat := 118140960795 + 7745548 * 2 ^ 59
def prefixEnd_7745548 : Nat := 4983230072969 + 3 ^ 40 * 7745548 * 2
def baseEnd_7745548 : Nat := 1325729685490322247176293

theorem tailTrace_7745548 : CollatzResearch.WordTrace tailWord_7745548 prefixEnd_7745548 1325729685490322247176293 := by
  unfold tailWord_7745548
  simp only [CollatzResearch.WordTrace]
  refine ⟨141251672071604952563646649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 188335562762139936751528865 141251672071604952563646649)
  ·
    refine ⟨105938754053703714422734987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 141251672071604952563646649 105938754053703714422734987)
    ·
      refine ⟨158908131080555571634102481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105938754053703714422734987 158908131080555571634102481)
      ·
        refine ⟨119181098310416678725576861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 158908131080555571634102481 119181098310416678725576861)
        ·
          refine ⟨44692911866406254522091323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 119181098310416678725576861 44692911866406254522091323)
          ·
            refine ⟨67039367799609381783136985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44692911866406254522091323 67039367799609381783136985)
            ·
              refine ⟨50279525849707036337352739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 67039367799609381783136985 50279525849707036337352739)
              ·
                refine ⟨75419288774560554506029109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50279525849707036337352739 75419288774560554506029109)
                ·
                  refine ⟨7070558322615051984940229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 75419288774560554506029109 7070558322615051984940229)
                  ·
                    refine ⟨1325729685490322247176293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7070558322615051984940229 1325729685490322247176293)
                    ·
                      rfl

theorem cell23_7745548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 2, 1, 5, 4].length) (baseStart_7745548 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7745548 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7745548 prefixEnd_7745548 := by exact prefixLift 7745548
  have htrace : WordTrace (prefixWord ++ tailWord_7745548) baseStart_7745548 baseEnd_7745548 := by
    simpa [prefixWord, tailWord_7745548, baseEnd_7745548] using wordTrace_append hprefix tailTrace_7745548
  have hstable : (prefixWord ++ tailWord_7745548).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7745548).length < 2 ^ (prefixWord ++ tailWord_7745548).sum := by decide
  have hdescent : baseEnd_7745548 < baseStart_7745548 := by decide
  rcases family_descends (prefixWord ++ tailWord_7745548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7745648 : List Nat := [2, 1, 1, 1, 5, 2, 1, 1, 3, 1, 5]
def baseStart_7745648 : Nat := 118140960795 + 7745648 * 2 ^ 59
def prefixEnd_7745648 : Nat := 4983230072969 + 3 ^ 40 * 7745648 * 2
def baseEnd_7745648 : Nat := 3977240404536416350278419

theorem tailTrace_7745648 : CollatzResearch.WordTrace tailWord_7745648 prefixEnd_7745648 3977240404536416350278419 := by
  unfold tailWord_7745648
  simp only [CollatzResearch.WordTrace]
  refine ⟨141253495721423811102966799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 188337994295231748137289065 141253495721423811102966799)
  ·
    refine ⟨211880243582135716654450199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141253495721423811102966799 211880243582135716654450199)
    ·
      refine ⟨317820365373203574981675299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 211880243582135716654450199 317820365373203574981675299)
      ·
        refine ⟨476730548059805362472512949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 317820365373203574981675299 476730548059805362472512949)
        ·
          refine ⟨44693488880606752731798089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 476730548059805362472512949 44693488880606752731798089)
          ·
            refine ⟨33520116660455064548848567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44693488880606752731798089 33520116660455064548848567)
            ·
              refine ⟨50280174990682596823272851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33520116660455064548848567 50280174990682596823272851)
              ·
                refine ⟨75420262486023895234909277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50280174990682596823272851 75420262486023895234909277)
                ·
                  refine ⟨28282598432258960713090979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 75420262486023895234909277 28282598432258960713090979)
                  ·
                    refine ⟨42423897648388441069636469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 28282598432258960713090979 42423897648388441069636469)
                    ·
                      refine ⟨3977240404536416350278419, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 42423897648388441069636469 3977240404536416350278419)
                      ·
                        rfl

theorem cell23_7745648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 2, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 2, 1, 1, 3, 1, 5].length) (baseStart_7745648 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7745648 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7745648 prefixEnd_7745648 := by exact prefixLift 7745648
  have htrace : WordTrace (prefixWord ++ tailWord_7745648) baseStart_7745648 baseEnd_7745648 := by
    simpa [prefixWord, tailWord_7745648, baseEnd_7745648] using wordTrace_append hprefix tailTrace_7745648
  have hstable : (prefixWord ++ tailWord_7745648).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7745648).length < 2 ^ (prefixWord ++ tailWord_7745648).sum := by decide
  have hdescent : baseEnd_7745648 < baseStart_7745648 := by decide
  rcases family_descends (prefixWord ++ tailWord_7745648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7745655 : List Nat := [1, 1, 3, 1, 1, 7, 1, 1, 1, 6]
def baseStart_7745655 : Nat := 118140960795 + 7745655 * 2 ^ 59
def prefixEnd_7745655 : Nat := 4983230072969 + 3 ^ 40 * 7745655 * 2
def baseEnd_7745655 : Nat := 1325747999633665940963629

theorem tailTrace_7745655 : CollatzResearch.WordTrace tailWord_7745655 prefixEnd_7745655 1325747999633665940963629 := by
  unfold tailWord_7745655
  simp only [CollatzResearch.WordTrace]
  refine ⟨282507246753822262401438419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188338164502548174934292279 282507246753822262401438419)
  ·
    refine ⟨423760870130733393602157629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 282507246753822262401438419 423760870130733393602157629)
    ·
      refine ⟨158910326299025022600809111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 423760870130733393602157629 158910326299025022600809111)
      ·
        refine ⟨238365489448537533901213667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 158910326299025022600809111 238365489448537533901213667)
        ·
          refine ⟨357548234172806300851820501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 238365489448537533901213667 357548234172806300851820501)
          ·
            refine ⟨8380036738425147676214543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 357548234172806300851820501 8380036738425147676214543)
            ·
              refine ⟨12570055107637721514321815, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8380036738425147676214543 12570055107637721514321815)
              ·
                refine ⟨18855082661456582271482723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12570055107637721514321815 18855082661456582271482723)
                ·
                  refine ⟨28282623992184873407224085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18855082661456582271482723 28282623992184873407224085)
                  ·
                    refine ⟨1325747999633665940963629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28282623992184873407224085 1325747999633665940963629)
                    ·
                      rfl

theorem cell23_7745655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 7, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 7, 1, 1, 1, 6].length) (baseStart_7745655 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7745655 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7745655 prefixEnd_7745655 := by exact prefixLift 7745655
  have htrace : WordTrace (prefixWord ++ tailWord_7745655) baseStart_7745655 baseEnd_7745655 := by
    simpa [prefixWord, tailWord_7745655, baseEnd_7745655] using wordTrace_append hprefix tailTrace_7745655
  have hstable : (prefixWord ++ tailWord_7745655).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7745655).length < 2 ^ (prefixWord ++ tailWord_7745655).sum := by decide
  have hdescent : baseEnd_7745655 < baseStart_7745655 := by decide
  rcases family_descends (prefixWord ++ tailWord_7745655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7745668 : List Nat := [2, 3, 2, 1, 2, 1, 3, 9]
def baseStart_7745668 : Nat := 118140960795 + 7745668 * 2 ^ 59
def prefixEnd_7745668 : Nat := 4983230072969 + 3 ^ 40 * 7745668 * 2
def baseEnd_7745668 : Nat := 147305580524055787852901

theorem tailTrace_7745668 : CollatzResearch.WordTrace tailWord_7745668 prefixEnd_7745668 147305580524055787852901 := by
  unfold tailWord_7745668
  simp only [CollatzResearch.WordTrace]
  refine ⟨141253860451387582810830829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 188338480601850110414441105 141253860451387582810830829)
  ·
    refine ⟨52970197669270343554061561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 141253860451387582810830829 52970197669270343554061561)
    ·
      refine ⟨39727648251952757665546171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52970197669270343554061561 39727648251952757665546171)
      ·
        refine ⟨59591472377929136498319257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39727648251952757665546171 59591472377929136498319257)
        ·
          refine ⟨44693604283446852373739443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59591472377929136498319257 44693604283446852373739443)
          ·
            refine ⟨67040406425170278560609165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44693604283446852373739443 67040406425170278560609165)
            ·
              refine ⟨25140152409438854460228437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 67040406425170278560609165 25140152409438854460228437)
              ·
                refine ⟨147305580524055787852901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 25140152409438854460228437 147305580524055787852901)
                ·
                  rfl

theorem cell23_7745668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 3, 9].length) (baseStart_7745668 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7745668 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7745668 prefixEnd_7745668 := by exact prefixLift 7745668
  have htrace : WordTrace (prefixWord ++ tailWord_7745668) baseStart_7745668 baseEnd_7745668 := by
    simpa [prefixWord, tailWord_7745668, baseEnd_7745668] using wordTrace_append hprefix tailTrace_7745668
  have hstable : (prefixWord ++ tailWord_7745668).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7745668).length < 2 ^ (prefixWord ++ tailWord_7745668).sum := by decide
  have hdescent : baseEnd_7745668 < baseStart_7745668 := by decide
  rcases family_descends (prefixWord ++ tailWord_7745668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7745682 : List Nat := [3, 2, 3, 1, 1, 1, 1, 5, 1, 2, 3]
def baseStart_7745682 : Nat := 118140960795 + 7745682 * 2 ^ 59
def prefixEnd_7745682 : Nat := 4983230072969 + 3 ^ 40 * 7745682 * 2
def baseEnd_7745682 : Nat := 3977257862878669217253263

theorem tailTrace_7745682 : CollatzResearch.WordTrace tailWord_7745682 prefixEnd_7745682 3977257862878669217253263 := by
  unfold tailWord_7745682
  simp only [CollatzResearch.WordTrace]
  refine ⟨70627057881181111503167825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 188338821016482964008447533 70627057881181111503167825)
  ·
    refine ⟨52970293410885833627375869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70627057881181111503167825 52970293410885833627375869)
    ·
      refine ⟨19863860029082187610265951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 52970293410885833627375869 19863860029082187610265951)
      ·
        refine ⟨29795790043623281415398927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19863860029082187610265951 29795790043623281415398927)
        ·
          refine ⟨44693685065434922123098391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29795790043623281415398927 44693685065434922123098391)
          ·
            refine ⟨67040527598152383184647587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44693685065434922123098391 67040527598152383184647587)
            ·
              refine ⟨100560791397228574776971381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67040527598152383184647587 100560791397228574776971381)
              ·
                refine ⟨9427574193490178885341067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 100560791397228574776971381 9427574193490178885341067)
                ·
                  refine ⟨14141361290235268328011601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9427574193490178885341067 14141361290235268328011601)
                  ·
                    refine ⟨10606020967676451246008701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14141361290235268328011601 10606020967676451246008701)
                    ·
                      refine ⟨3977257862878669217253263, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10606020967676451246008701 3977257862878669217253263)
                      ·
                        rfl

theorem cell23_7745682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 1, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 1, 5, 1, 2, 3].length) (baseStart_7745682 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7745682 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7745682 prefixEnd_7745682 := by exact prefixLift 7745682
  have htrace : WordTrace (prefixWord ++ tailWord_7745682) baseStart_7745682 baseEnd_7745682 := by
    simpa [prefixWord, tailWord_7745682, baseEnd_7745682] using wordTrace_append hprefix tailTrace_7745682
  have hstable : (prefixWord ++ tailWord_7745682).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7745682).length < 2 ^ (prefixWord ++ tailWord_7745682).sum := by decide
  have hdescent : baseEnd_7745682 < baseStart_7745682 := by decide
  rcases family_descends (prefixWord ++ tailWord_7745682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7745729 : List Nat := [1, 2, 6, 1, 2, 1, 1, 2, 1, 3, 3]
def baseStart_7745729 : Nat := 118140960795 + 7745729 * 2 ^ 59
def prefixEnd_7745729 : Nat := 4983230072969 + 3 ^ 40 * 7745729 * 2
def baseEnd_7745729 : Nat := 3977281996469430533365547

theorem tailTrace_7745729 : CollatzResearch.WordTrace tailWord_7745729 prefixEnd_7745729 3977281996469430533365547 := by
  unfold tailWord_7745729
  simp only [CollatzResearch.WordTrace]
  refine ⟨282509945755554173039632241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188339963837036115359754827 282509945755554173039632241)
  ·
    refine ⟨211882459316665629779724181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 282509945755554173039632241 211882459316665629779724181)
    ·
      refine ⟨9931990280468701395924571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 211882459316665629779724181 9931990280468701395924571)
      ·
        refine ⟨14897985420703052093886857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9931990280468701395924571 14897985420703052093886857)
        ·
          refine ⟨11173489065527289070415143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14897985420703052093886857 11173489065527289070415143)
          ·
            refine ⟨16760233598290933605622715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11173489065527289070415143 16760233598290933605622715)
            ·
              refine ⟨25140350397436400408434073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16760233598290933605622715 25140350397436400408434073)
              ·
                refine ⟨18855262798077300306325555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25140350397436400408434073 18855262798077300306325555)
                ·
                  refine ⟨28282894197115950459488333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18855262798077300306325555 28282894197115950459488333)
                  ·
                    refine ⟨10606085323918481422308125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 28282894197115950459488333 10606085323918481422308125)
                    ·
                      refine ⟨3977281996469430533365547, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10606085323918481422308125 3977281996469430533365547)
                      ·
                        rfl

theorem cell23_7745729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 2, 1, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 2, 1, 1, 2, 1, 3, 3].length) (baseStart_7745729 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7745729 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7745729 prefixEnd_7745729 := by exact prefixLift 7745729
  have htrace : WordTrace (prefixWord ++ tailWord_7745729) baseStart_7745729 baseEnd_7745729 := by
    simpa [prefixWord, tailWord_7745729, baseEnd_7745729] using wordTrace_append hprefix tailTrace_7745729
  have hstable : (prefixWord ++ tailWord_7745729).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7745729).length < 2 ^ (prefixWord ++ tailWord_7745729).sum := by decide
  have hdescent : baseEnd_7745729 < baseStart_7745729 := by decide
  rcases family_descends (prefixWord ++ tailWord_7745729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7745739 : List Nat := [1, 1, 1, 1, 3, 2, 7, 1, 1, 3, 2]
def baseStart_7745739 : Nat := 118140960795 + 7745739 * 2 ^ 59
def prefixEnd_7745739 : Nat := 4983230072969 + 3 ^ 40 * 7745739 * 2
def baseEnd_7745739 : Nat := 3977287131275975494240501

theorem tailTrace_7745739 : CollatzResearch.WordTrace tailWord_7745739 prefixEnd_7745739 3977287131275975494240501 := by
  unfold tailWord_7745739
  simp only [CollatzResearch.WordTrace]
  refine ⟨282510310485517944747496271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188340206990345296498330847 282510310485517944747496271)
  ·
    refine ⟨423765465728276917121244407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 282510310485517944747496271 423765465728276917121244407)
    ·
      refine ⟨635648198592415375681866611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 423765465728276917121244407 635648198592415375681866611)
      ·
        refine ⟨953472297888623063522799917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 635648198592415375681866611 953472297888623063522799917)
        ·
          refine ⟨357552111708233648821049969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 953472297888623063522799917 357552111708233648821049969)
          ·
            refine ⟨268164083781175236615787477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 357552111708233648821049969 268164083781175236615787477)
            ·
              refine ⟨6285095713621294608182519, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 268164083781175236615787477 6285095713621294608182519)
              ·
                refine ⟨9427643570431941912273779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6285095713621294608182519 9427643570431941912273779)
                ·
                  refine ⟨14141465355647912868410669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9427643570431941912273779 14141465355647912868410669)
                  ·
                    refine ⟨5303049508367967325654001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14141465355647912868410669 5303049508367967325654001)
                    ·
                      refine ⟨3977287131275975494240501, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5303049508367967325654001 3977287131275975494240501)
                      ·
                        rfl

theorem cell23_7745739_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 7, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 7, 1, 1, 3, 2].length) (baseStart_7745739 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7745739 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7745739 prefixEnd_7745739 := by exact prefixLift 7745739
  have htrace : WordTrace (prefixWord ++ tailWord_7745739) baseStart_7745739 baseEnd_7745739 := by
    simpa [prefixWord, tailWord_7745739, baseEnd_7745739] using wordTrace_append hprefix tailTrace_7745739
  have hstable : (prefixWord ++ tailWord_7745739).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7745739).length < 2 ^ (prefixWord ++ tailWord_7745739).sum := by decide
  have hdescent : baseEnd_7745739 < baseStart_7745739 := by decide
  rcases family_descends (prefixWord ++ tailWord_7745739) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7745765 : List Nat := [1, 3, 1, 4, 2, 1, 1, 1, 1, 4, 4]
def baseStart_7745765 : Nat := 118140960795 + 7745765 * 2 ^ 59
def prefixEnd_7745765 : Nat := 4983230072969 + 3 ^ 40 * 7745765 * 2
def baseEnd_7745765 : Nat := 3977300481772992392515381

theorem tailTrace_7745765 : CollatzResearch.WordTrace tailWord_7745765 prefixEnd_7745765 3977300481772992392515381 := by
  unfold tailWord_7745765
  simp only [CollatzResearch.WordTrace]
  refine ⟨282511258783423751187942749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188340839188949167458628499 282511258783423751187942749)
  ·
    refine ⟨105941722043783906695478531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 282511258783423751187942749 105941722043783906695478531)
    ·
      refine ⟨158912583065675860043217797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105941722043783906695478531 158912583065675860043217797)
      ·
        refine ⟨29796109324814223758103337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 158912583065675860043217797 29796109324814223758103337)
        ·
          refine ⟨22347081993610667818577503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29796109324814223758103337 22347081993610667818577503)
          ·
            refine ⟨33520622990416001727866255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22347081993610667818577503 33520622990416001727866255)
            ·
              refine ⟨50280934485624002591799383, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33520622990416001727866255 50280934485624002591799383)
              ·
                refine ⟨75421401728436003887699075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50280934485624002591799383 75421401728436003887699075)
                ·
                  refine ⟨113132102592654005831548613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 75421401728436003887699075 113132102592654005831548613)
                  ·
                    refine ⟨21212269236122626093415365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 113132102592654005831548613 21212269236122626093415365)
                    ·
                      refine ⟨3977300481772992392515381, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21212269236122626093415365 3977300481772992392515381)
                      ·
                        rfl

theorem cell23_7745765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 1, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 1, 1, 1, 1, 4, 4].length) (baseStart_7745765 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7745765 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7745765 prefixEnd_7745765 := by exact prefixLift 7745765
  have htrace : WordTrace (prefixWord ++ tailWord_7745765) baseStart_7745765 baseEnd_7745765 := by
    simpa [prefixWord, tailWord_7745765, baseEnd_7745765] using wordTrace_append hprefix tailTrace_7745765
  have hstable : (prefixWord ++ tailWord_7745765).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7745765).length < 2 ^ (prefixWord ++ tailWord_7745765).sum := by decide
  have hdescent : baseEnd_7745765 < baseStart_7745765 := by decide
  rcases family_descends (prefixWord ++ tailWord_7745765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7745775 : List Nat := [1, 1, 2, 1, 6, 2, 1, 2, 7]
def baseStart_7745775 : Nat := 118140960795 + 7745775 * 2 ^ 59
def prefixEnd_7745775 : Nat := 4983230072969 + 3 ^ 40 * 7745775 * 2
def baseEnd_7745775 : Nat := 441922846286615261487815

theorem tailTrace_7745775 : CollatzResearch.WordTrace tailWord_7745775 prefixEnd_7745775 441922846286615261487815 := by
  unfold tailWord_7745775
  simp only [CollatzResearch.WordTrace]
  refine ⟨282511623513387522895806779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188341082342258348597204519 282511623513387522895806779)
  ·
    refine ⟨423767435270081284343710169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 282511623513387522895806779 423767435270081284343710169)
    ·
      refine ⟨317825576452560963257782627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 423767435270081284343710169 317825576452560963257782627)
      ·
        refine ⟨476738364678841444886673941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 317825576452560963257782627 476738364678841444886673941)
        ·
          refine ⟨22347110844320692729062841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 476738364678841444886673941 22347110844320692729062841)
          ·
            refine ⟨16760333133240519546797131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22347110844320692729062841 16760333133240519546797131)
            ·
              refine ⟨25140499699860779320195697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16760333133240519546797131 25140499699860779320195697)
              ·
                refine ⟨18855374774895584490146773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25140499699860779320195697 18855374774895584490146773)
                ·
                  refine ⟨441922846286615261487815, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18855374774895584490146773 441922846286615261487815)
                  ·
                    rfl

theorem cell23_7745775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 2, 1, 2, 7].length) (baseStart_7745775 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7745775 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7745775 prefixEnd_7745775 := by exact prefixLift 7745775
  have htrace : WordTrace (prefixWord ++ tailWord_7745775) baseStart_7745775 baseEnd_7745775 := by
    simpa [prefixWord, tailWord_7745775, baseEnd_7745775] using wordTrace_append hprefix tailTrace_7745775
  have hstable : (prefixWord ++ tailWord_7745775).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7745775).length < 2 ^ (prefixWord ++ tailWord_7745775).sum := by decide
  have hdescent : baseEnd_7745775 < baseStart_7745775 := by decide
  rcases family_descends (prefixWord ++ tailWord_7745775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7745825 : List Nat := [1, 2, 3, 2, 1, 1, 3, 2, 1, 3, 4]
def baseStart_7745825 : Nat := 118140960795 + 7745825 * 2 ^ 59
def prefixEnd_7745825 : Nat := 4983230072969 + 3 ^ 40 * 7745825 * 2
def baseEnd_7745825 : Nat := 3977331290612262157765105

theorem tailTrace_7745825 : CollatzResearch.WordTrace tailWord_7745825 prefixEnd_7745825 3977331290612262157765105 := by
  unfold tailWord_7745825
  simp only [CollatzResearch.WordTrace]
  refine ⟨282513447163206381435126929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188342298108804254290084619 282513447163206381435126929)
  ·
    refine ⟨211885085372404786076345197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 282513447163206381435126929 211885085372404786076345197)
    ·
      refine ⟨79456907014651794778629449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 211885085372404786076345197 79456907014651794778629449)
      ·
        refine ⟨59592680260988846083972087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79456907014651794778629449 59592680260988846083972087)
        ·
          refine ⟨89389020391483269125958131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59592680260988846083972087 89389020391483269125958131)
          ·
            refine ⟨134083530587224903688937197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89389020391483269125958131 134083530587224903688937197)
            ·
              refine ⟨50281323970209338883351449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 134083530587224903688937197 50281323970209338883351449)
              ·
                refine ⟨37710992977657004162513587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50281323970209338883351449 37710992977657004162513587)
                ·
                  refine ⟨56566489466485506243770381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37710992977657004162513587 56566489466485506243770381)
                  ·
                    refine ⟨21212433549932064841413893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 56566489466485506243770381 21212433549932064841413893)
                    ·
                      refine ⟨3977331290612262157765105, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21212433549932064841413893 3977331290612262157765105)
                      ·
                        rfl

theorem cell23_7745825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 3, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 3, 2, 1, 3, 4].length) (baseStart_7745825 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7745825 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7745825 prefixEnd_7745825 := by exact prefixLift 7745825
  have htrace : WordTrace (prefixWord ++ tailWord_7745825) baseStart_7745825 baseEnd_7745825 := by
    simpa [prefixWord, tailWord_7745825, baseEnd_7745825] using wordTrace_append hprefix tailTrace_7745825
  have hstable : (prefixWord ++ tailWord_7745825).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7745825).length < 2 ^ (prefixWord ++ tailWord_7745825).sum := by decide
  have hdescent : baseEnd_7745825 < baseStart_7745825 := by decide
  rcases family_descends (prefixWord ++ tailWord_7745825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7745865 : List Nat := [1, 2, 1, 1, 2, 3, 1, 6, 6]
def baseStart_7745865 : Nat := 118140960795 + 7745865 * 2 ^ 59
def prefixEnd_7745865 : Nat := 4983230072969 + 3 ^ 40 * 7745865 * 2
def baseEnd_7745865 : Nat := 441927981093160222362769

theorem tailTrace_7745865 : CollatzResearch.WordTrace tailWord_7745865 prefixEnd_7745865 441927981093160222362769 := by
  unfold tailWord_7745865
  simp only [CollatzResearch.WordTrace]
  refine ⟨282514906083061468266583049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188343270722040978844388699 282514906083061468266583049)
  ·
    refine ⟨211886179562296101199937287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 282514906083061468266583049 211886179562296101199937287)
    ·
      refine ⟨317829269343444151799905931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 211886179562296101199937287 317829269343444151799905931)
      ·
        refine ⟨476743904015166227699858897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 317829269343444151799905931 476743904015166227699858897)
        ·
          refine ⟨357557928011374670774894173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 476743904015166227699858897 357557928011374670774894173)
          ·
            refine ⟨134084223004265501540585315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 357557928011374670774894173 134084223004265501540585315)
            ·
              refine ⟨201126334506398252310877973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 134084223004265501540585315 201126334506398252310877973)
              ·
                refine ⟨9427796929987418077072405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 201126334506398252310877973 9427796929987418077072405)
                ·
                  refine ⟨441927981093160222362769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9427796929987418077072405 441927981093160222362769)
                  ·
                    rfl

theorem cell23_7745865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 1, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 1, 6, 6].length) (baseStart_7745865 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7745865 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7745865 prefixEnd_7745865 := by exact prefixLift 7745865
  have htrace : WordTrace (prefixWord ++ tailWord_7745865) baseStart_7745865 baseEnd_7745865 := by
    simpa [prefixWord, tailWord_7745865, baseEnd_7745865] using wordTrace_append hprefix tailTrace_7745865
  have hstable : (prefixWord ++ tailWord_7745865).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7745865).length < 2 ^ (prefixWord ++ tailWord_7745865).sum := by decide
  have hdescent : baseEnd_7745865 < baseStart_7745865 := by decide
  rcases family_descends (prefixWord ++ tailWord_7745865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7745875 : List Nat := [1, 1, 1, 2, 1, 1, 4, 2, 2, 5, 3]
def baseStart_7745875 : Nat := 118140960795 + 7745875 * 2 ^ 59
def prefixEnd_7745875 : Nat := 4983230072969 + 3 ^ 40 * 7745875 * 2
def baseEnd_7745875 : Nat := 3977356964644986962139875

theorem tailTrace_7745875 : CollatzResearch.WordTrace tailWord_7745875 prefixEnd_7745875 3977356964644986962139875 := by
  unfold tailWord_7745875
  simp only [CollatzResearch.WordTrace]
  refine ⟨282515270813025239974447079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188343513875350159982964719 282515270813025239974447079)
  ·
    refine ⟨423772906219537859961670619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 282515270813025239974447079 423772906219537859961670619)
    ·
      refine ⟨635659359329306789942505929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 423772906219537859961670619 635659359329306789942505929)
      ·
        refine ⟨476744519496980092456879447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 635659359329306789942505929 476744519496980092456879447)
        ·
          refine ⟨715116779245470138685319171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 476744519496980092456879447 715116779245470138685319171)
          ·
            refine ⟨1072675168868205208027978757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 715116779245470138685319171 1072675168868205208027978757)
            ·
              refine ⟨201126594162788476505246017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1072675168868205208027978757 201126594162788476505246017)
              ·
                refine ⟨150844945622091357378934513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 201126594162788476505246017 150844945622091357378934513)
                ·
                  refine ⟨113133709216568518034200885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 150844945622091357378934513 113133709216568518034200885)
                  ·
                    refine ⟨10606285239053298565706333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 113133709216568518034200885 10606285239053298565706333)
                    ·
                      refine ⟨3977356964644986962139875, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10606285239053298565706333 3977356964644986962139875)
                      ·
                        rfl

theorem cell23_7745875_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 4, 2, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 4, 2, 2, 5, 3].length) (baseStart_7745875 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7745875 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7745875 prefixEnd_7745875 := by exact prefixLift 7745875
  have htrace : WordTrace (prefixWord ++ tailWord_7745875) baseStart_7745875 baseEnd_7745875 := by
    simpa [prefixWord, tailWord_7745875, baseEnd_7745875] using wordTrace_append hprefix tailTrace_7745875
  have hstable : (prefixWord ++ tailWord_7745875).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7745875).length < 2 ^ (prefixWord ++ tailWord_7745875).sum := by decide
  have hdescent : baseEnd_7745875 < baseStart_7745875 := by decide
  rcases family_descends (prefixWord ++ tailWord_7745875) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7745925 : List Nat := [1, 3, 1, 1, 3, 1, 1, 1, 5, 6]
def baseStart_7745925 : Nat := 118140960795 + 7745925 * 2 ^ 59
def prefixEnd_7745925 : Nat := 4983230072969 + 3 ^ 40 * 7745925 * 2
def baseEnd_7745925 : Nat := 1325794212892570588838215

theorem tailTrace_7745925 : CollatzResearch.WordTrace tailWord_7745925 prefixEnd_7745925 1325794212892570588838215 := by
  unfold tailWord_7745925
  simp only [CollatzResearch.WordTrace]
  refine ⟨282517094462844098513767229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188344729641896065675844819 282517094462844098513767229)
  ·
    refine ⟨105943910423566536942662711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 282517094462844098513767229 105943910423566536942662711)
    ·
      refine ⟨158915865635349805413994067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105943910423566536942662711 158915865635349805413994067)
      ·
        refine ⟨238373798453024708120991101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 158915865635349805413994067 238373798453024708120991101)
        ·
          refine ⟨89390174419884265545371663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 238373798453024708120991101 89390174419884265545371663)
          ·
            refine ⟨134085261629826398318057495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89390174419884265545371663 134085261629826398318057495)
            ·
              refine ⟨201127892444739597477086243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 134085261629826398318057495 201127892444739597477086243)
              ·
                refine ⟨301691838667109396215629365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 201127892444739597477086243 301691838667109396215629365)
                ·
                  refine ⟨28283609875041505895215253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 301691838667109396215629365 28283609875041505895215253)
                  ·
                    refine ⟨1325794212892570588838215, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28283609875041505895215253 1325794212892570588838215)
                    ·
                      rfl

theorem cell23_7745925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 1, 1, 5, 6].length) (baseStart_7745925 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7745925 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7745925 prefixEnd_7745925 := by exact prefixLift 7745925
  have htrace : WordTrace (prefixWord ++ tailWord_7745925) baseStart_7745925 baseEnd_7745925 := by
    simpa [prefixWord, tailWord_7745925, baseEnd_7745925] using wordTrace_append hprefix tailTrace_7745925
  have hstable : (prefixWord ++ tailWord_7745925).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7745925).length < 2 ^ (prefixWord ++ tailWord_7745925).sum := by decide
  have hdescent : baseEnd_7745925 < baseStart_7745925 := by decide
  rcases family_descends (prefixWord ++ tailWord_7745925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7745932 : List Nat := [2, 2, 1, 2, 1, 4, 1, 2, 3, 1, 4]
def baseStart_7745932 : Nat := 118140960795 + 7745932 * 2 ^ 59
def prefixEnd_7745932 : Nat := 4983230072969 + 3 ^ 40 * 7745932 * 2
def baseEnd_7745932 : Nat := 3977386233042293239127113

theorem tailTrace_7745932 : CollatzResearch.WordTrace tailWord_7745932 prefixEnd_7745932 3977386233042293239127113 := by
  unfold tailWord_7745932
  simp only [CollatzResearch.WordTrace]
  refine ⟨141258674886909369354636025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 188344899849212492472848033 141258674886909369354636025)
  ·
    refine ⟨105944006165182027015977019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 141258674886909369354636025 105944006165182027015977019)
    ·
      refine ⟨158916009247773040523965529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105944006165182027015977019 158916009247773040523965529)
      ·
        refine ⟨119187006935829780392974147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 158916009247773040523965529 119187006935829780392974147)
        ·
          refine ⟨178780510403744670589461221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 119187006935829780392974147 178780510403744670589461221)
          ·
            refine ⟨33521345700702125735523979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 178780510403744670589461221 33521345700702125735523979)
            ·
              refine ⟨50282018551053188603285969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33521345700702125735523979 50282018551053188603285969)
              ·
                refine ⟨37711513913289891452464477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50282018551053188603285969 37711513913289891452464477)
                ·
                  refine ⟨14141817717483709294674179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 37711513913289891452464477 14141817717483709294674179)
                  ·
                    refine ⟨21212726576225563942011269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14141817717483709294674179 21212726576225563942011269)
                    ·
                      refine ⟨3977386233042293239127113, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21212726576225563942011269 3977386233042293239127113)
                      ·
                        rfl

theorem cell23_7745932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 4, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 4, 1, 2, 3, 1, 4].length) (baseStart_7745932 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7745932 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7745932 prefixEnd_7745932 := by exact prefixLift 7745932
  have htrace : WordTrace (prefixWord ++ tailWord_7745932) baseStart_7745932 baseEnd_7745932 := by
    simpa [prefixWord, tailWord_7745932, baseEnd_7745932] using wordTrace_append hprefix tailTrace_7745932
  have hstable : (prefixWord ++ tailWord_7745932).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7745932).length < 2 ^ (prefixWord ++ tailWord_7745932).sum := by decide
  have hdescent : baseEnd_7745932 < baseStart_7745932 := by decide
  rcases family_descends (prefixWord ++ tailWord_7745932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7745960 : List Nat := [2, 1, 6, 1, 1, 2, 2, 3, 1, 1, 3]
def baseStart_7745960 : Nat := 118140960795 + 7745960 * 2 ^ 59
def prefixEnd_7745960 : Nat := 4983230072969 + 3 ^ 40 * 7745960 * 2
def baseEnd_7745960 : Nat := 3977400610500619129576985

theorem tailTrace_7745960 : CollatzResearch.WordTrace tailWord_7745960 prefixEnd_7745960 3977400610500619129576985 := by
  unfold tailWord_7745960
  simp only [CollatzResearch.WordTrace]
  refine ⟨141259185508858649745645667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 188345580678478199660860889 141259185508858649745645667)
  ·
    refine ⟨211888778263287974618468501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141259185508858649745645667 211888778263287974618468501)
    ·
      refine ⟨9932286481091623810240711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 211888778263287974618468501 9932286481091623810240711)
      ·
        refine ⟨14898429721637435715361067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9932286481091623810240711 14898429721637435715361067)
        ·
          refine ⟨22347644582456153573041601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14898429721637435715361067 22347644582456153573041601)
          ·
            refine ⟨16760733436842115179781201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22347644582456153573041601 16760733436842115179781201)
            ·
              refine ⟨12570550077631586384835901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16760733436842115179781201 12570550077631586384835901)
              ·
                refine ⟨4713956279111844894313463, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12570550077631586384835901 4713956279111844894313463)
                ·
                  refine ⟨7070934418667767341470195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4713956279111844894313463 7070934418667767341470195)
                  ·
                    refine ⟨10606401628001651012205293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7070934418667767341470195 10606401628001651012205293)
                    ·
                      refine ⟨3977400610500619129576985, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10606401628001651012205293 3977400610500619129576985)
                      ·
                        rfl

theorem cell23_7745960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 2, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 2, 2, 3, 1, 1, 3].length) (baseStart_7745960 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7745960 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7745960 prefixEnd_7745960 := by exact prefixLift 7745960
  have htrace : WordTrace (prefixWord ++ tailWord_7745960) baseStart_7745960 baseEnd_7745960 := by
    simpa [prefixWord, tailWord_7745960, baseEnd_7745960] using wordTrace_append hprefix tailTrace_7745960
  have hstable : (prefixWord ++ tailWord_7745960).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7745960).length < 2 ^ (prefixWord ++ tailWord_7745960).sum := by decide
  have hdescent : baseEnd_7745960 < baseStart_7745960 := by decide
  rcases family_descends (prefixWord ++ tailWord_7745960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7745996 : List Nat := [2, 2, 1, 4, 3, 2, 1, 1, 1, 2, 4]
def baseStart_7745996 : Nat := 118140960795 + 7745996 * 2 ^ 59
def prefixEnd_7745996 : Nat := 4983230072969 + 3 ^ 40 * 7745996 * 2
def baseEnd_7745996 : Nat := 3977419095804180988726819

theorem tailTrace_7745996 : CollatzResearch.WordTrace tailWord_7745996 prefixEnd_7745996 3977419095804180988726819 := by
  unfold tailWord_7745996
  simp only [CollatzResearch.WordTrace]
  refine ⟨141259842022793438819800921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 188346456030391251759734561 141259842022793438819800921)
  ·
    refine ⟨105944881517095079114850691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 141259842022793438819800921 105944881517095079114850691)
    ·
      refine ⟨158917322275642618672276037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105944881517095079114850691 158917322275642618672276037)
      ·
        refine ⟨29796997926682991001051757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 158917322275642618672276037 29796997926682991001051757)
        ·
          refine ⟨11173874222506121625394409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29796997926682991001051757 11173874222506121625394409)
          ·
            refine ⟨8380405666879591219045807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11173874222506121625394409 8380405666879591219045807)
            ·
              refine ⟨12570608500319386828568711, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8380405666879591219045807 12570608500319386828568711)
              ·
                refine ⟨18855912750479080242853067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12570608500319386828568711 18855912750479080242853067)
                ·
                  refine ⟨28283869125718620364279601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18855912750479080242853067 28283869125718620364279601)
                  ·
                    refine ⟨21212901844288965273209701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 28283869125718620364279601 21212901844288965273209701)
                    ·
                      refine ⟨3977419095804180988726819, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21212901844288965273209701 3977419095804180988726819)
                      ·
                        rfl

theorem cell23_7745996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 3, 2, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 3, 2, 1, 1, 1, 2, 4].length) (baseStart_7745996 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7745996 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7745996 prefixEnd_7745996 := by exact prefixLift 7745996
  have htrace : WordTrace (prefixWord ++ tailWord_7745996) baseStart_7745996 baseEnd_7745996 := by
    simpa [prefixWord, tailWord_7745996, baseEnd_7745996] using wordTrace_append hprefix tailTrace_7745996
  have hstable : (prefixWord ++ tailWord_7745996).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7745996).length < 2 ^ (prefixWord ++ tailWord_7745996).sum := by decide
  have hdescent : baseEnd_7745996 < baseStart_7745996 := by decide
  rcases family_descends (prefixWord ++ tailWord_7745996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7746050 : List Nat := [3, 4, 1, 2, 2, 1, 1, 3, 2, 1, 3]
def baseStart_7746050 : Nat := 118140960795 + 7746050 * 2 ^ 59
def prefixEnd_7746050 : Nat := 4983230072969 + 3 ^ 40 * 7746050 * 2
def baseEnd_7746050 : Nat := 3977446823759523777451571

theorem tailTrace_7746050 : CollatzResearch.WordTrace tailWord_7746050 prefixEnd_7746050 3977446823759523777451571 := by
  unfold tailWord_7746050
  simp only [CollatzResearch.WordTrace]
  refine ⟨70630413396847811215516901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 188347769058260829908045069 70630413396847811215516901)
  ·
    refine ⟨13243202511908964602909419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 70630413396847811215516901 13243202511908964602909419)
    ·
      refine ⟨19864803767863446904364129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13243202511908964602909419 19864803767863446904364129)
      ·
        refine ⟨14898602825897585178273097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19864803767863446904364129 14898602825897585178273097)
        ·
          refine ⟨11173952119423188883704823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14898602825897585178273097 11173952119423188883704823)
          ·
            refine ⟨16760928179134783325557235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11173952119423188883704823 16760928179134783325557235)
            ·
              refine ⟨25141392268702174988335853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16760928179134783325557235 25141392268702174988335853)
              ·
                refine ⟨9428022100763315620625945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25141392268702174988335853 9428022100763315620625945)
                ·
                  refine ⟨7071016575572486715469459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9428022100763315620625945 7071016575572486715469459)
                  ·
                    refine ⟨10606524863358730073204189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7071016575572486715469459 10606524863358730073204189)
                    ·
                      refine ⟨3977446823759523777451571, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10606524863358730073204189 3977446823759523777451571)
                      ·
                        rfl

theorem cell23_7746050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 2, 1, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 2, 1, 1, 3, 2, 1, 3].length) (baseStart_7746050 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7746050 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7746050 prefixEnd_7746050 := by exact prefixLift 7746050
  have htrace : WordTrace (prefixWord ++ tailWord_7746050) baseStart_7746050 baseEnd_7746050 := by
    simpa [prefixWord, tailWord_7746050, baseEnd_7746050] using wordTrace_append hprefix tailTrace_7746050
  have hstable : (prefixWord ++ tailWord_7746050).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7746050).length < 2 ^ (prefixWord ++ tailWord_7746050).sum := by decide
  have hdescent : baseEnd_7746050 < baseStart_7746050 := by decide
  rcases family_descends (prefixWord ++ tailWord_7746050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7746079 : List Nat := [1, 1, 2, 4, 1, 1, 1, 7, 5]
def baseStart_7746079 : Nat := 118140960795 + 7746079 * 2 ^ 59
def prefixEnd_7746079 : Nat := 4983230072969 + 3 ^ 40 * 7746079 * 2
def baseEnd_7746079 : Nat := 441940190522056018220993

theorem tailTrace_7746079 : CollatzResearch.WordTrace tailWord_7746079 prefixEnd_7746079 441940190522056018220993 := by
  unfold tailWord_7746079
  simp only [CollatzResearch.WordTrace]
  refine ⟨282522711304286182814873291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188348474202857455209915527 282522711304286182814873291)
  ·
    refine ⟨423784066956429274222309937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 282522711304286182814873291 423784066956429274222309937)
    ·
      refine ⟨317838050217321955666732453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 423784066956429274222309937 317838050217321955666732453)
      ·
        refine ⟨59594634415747866687512335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 317838050217321955666732453 59594634415747866687512335)
        ·
          refine ⟨89391951623621800031268503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59594634415747866687512335 89391951623621800031268503)
          ·
            refine ⟨134087927435432700046902755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89391951623621800031268503 134087927435432700046902755)
            ·
              refine ⟨201131891153149050070354133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 134087927435432700046902755 201131891153149050070354133)
              ·
                refine ⟨4714028698901930861023925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 201131891153149050070354133 4714028698901930861023925)
                ·
                  refine ⟨441940190522056018220993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4714028698901930861023925 441940190522056018220993)
                  ·
                    rfl

theorem cell23_7746079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 1, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 1, 7, 5].length) (baseStart_7746079 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7746079 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7746079 prefixEnd_7746079 := by exact prefixLift 7746079
  have htrace : WordTrace (prefixWord ++ tailWord_7746079) baseStart_7746079 baseEnd_7746079 := by
    simpa [prefixWord, tailWord_7746079, baseEnd_7746079] using wordTrace_append hprefix tailTrace_7746079
  have hstable : (prefixWord ++ tailWord_7746079).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7746079).length < 2 ^ (prefixWord ++ tailWord_7746079).sum := by decide
  have hdescent : baseEnd_7746079 < baseStart_7746079 := by decide
  rcases family_descends (prefixWord ++ tailWord_7746079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7746090 : List Nat := [3, 1, 4, 1, 1, 3, 2, 2, 2, 2, 2]
def baseStart_7746090 : Nat := 118140960795 + 7746090 * 2 ^ 59
def prefixEnd_7746090 : Nat := 4983230072969 + 3 ^ 40 * 7746090 * 2
def baseEnd_7746090 : Nat := 3977467362985703620951387

theorem tailTrace_7746090 : CollatzResearch.WordTrace tailWord_7746090 prefixEnd_7746090 3977467362985703620951387 := by
  unfold tailWord_7746090
  simp only [CollatzResearch.WordTrace]
  refine ⟨70630778126811582923380931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 188348741671497554462349149 70630778126811582923380931)
  ·
    refine ⟨105946167190217374385071397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70630778126811582923380931 105946167190217374385071397)
    ·
      refine ⟨19864906348165757697200887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 105946167190217374385071397 19864906348165757697200887)
      ·
        refine ⟨29797359522248636545801331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19864906348165757697200887 29797359522248636545801331)
        ·
          refine ⟨44696039283372954818701997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29797359522248636545801331 44696039283372954818701997)
          ·
            refine ⟨16761014731264858057013249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 44696039283372954818701997 16761014731264858057013249)
            ·
              refine ⟨12570761048448643542759937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16761014731264858057013249 12570761048448643542759937)
              ·
                refine ⟨9428070786336482657069953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12570761048448643542759937 9428070786336482657069953)
                ·
                  refine ⟨7071053089752361992802465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9428070786336482657069953 7071053089752361992802465)
                  ·
                    refine ⟨5303289817314271494601849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7071053089752361992802465 5303289817314271494601849)
                    ·
                      refine ⟨3977467362985703620951387, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5303289817314271494601849 3977467362985703620951387)
                      ·
                        rfl

theorem cell23_7746090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 3, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 3, 2, 2, 2, 2, 2].length) (baseStart_7746090 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7746090 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7746090 prefixEnd_7746090 := by exact prefixLift 7746090
  have htrace : WordTrace (prefixWord ++ tailWord_7746090) baseStart_7746090 baseEnd_7746090 := by
    simpa [prefixWord, tailWord_7746090, baseEnd_7746090] using wordTrace_append hprefix tailTrace_7746090
  have hstable : (prefixWord ++ tailWord_7746090).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7746090).length < 2 ^ (prefixWord ++ tailWord_7746090).sum := by decide
  have hdescent : baseEnd_7746090 < baseStart_7746090 := by decide
  rcases family_descends (prefixWord ++ tailWord_7746090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7746096 : List Nat := [2, 1, 1, 1, 2, 3, 6, 2, 5]
def baseStart_7746096 : Nat := 118140960795 + 7746096 * 2 ^ 59
def prefixEnd_7746096 : Nat := 4983230072969 + 3 ^ 40 * 7746096 * 2
def baseEnd_7746096 : Nat := 441941160429958955275151

theorem tailTrace_7746096 : CollatzResearch.WordTrace tailWord_7746096 prefixEnd_7746096 441941160429958955275151 := by
  unfold tailWord_7746096
  simp only [CollatzResearch.WordTrace]
  refine ⟨141261665672612297359121071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 188348887563483063145494761 141261665672612297359121071)
  ·
    refine ⟨211892498508918446038681607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141261665672612297359121071 211892498508918446038681607)
    ·
      refine ⟨317838747763377669058022411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 211892498508918446038681607 317838747763377669058022411)
      ·
        refine ⟨476758121645066503587033617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 317838747763377669058022411 476758121645066503587033617)
        ·
          refine ⟨357568591233799877690275213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 476758121645066503587033617 357568591233799877690275213)
          ·
            refine ⟨134088221712674954133853205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 357568591233799877690275213 134088221712674954133853205)
            ·
              refine ⟨6285385392781638475024369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 134088221712674954133853205 6285385392781638475024369)
              ·
                refine ⟨4714039044586228856268277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6285385392781638475024369 4714039044586228856268277)
                ·
                  refine ⟨441941160429958955275151, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4714039044586228856268277 441941160429958955275151)
                  ·
                    rfl

theorem cell23_7746096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 6, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 6, 2, 5].length) (baseStart_7746096 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7746096 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7746096 prefixEnd_7746096 := by exact prefixLift 7746096
  have htrace : WordTrace (prefixWord ++ tailWord_7746096) baseStart_7746096 baseEnd_7746096 := by
    simpa [prefixWord, tailWord_7746096, baseEnd_7746096] using wordTrace_append hprefix tailTrace_7746096
  have hstable : (prefixWord ++ tailWord_7746096).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7746096).length < 2 ^ (prefixWord ++ tailWord_7746096).sum := by decide
  have hdescent : baseEnd_7746096 < baseStart_7746096 := by decide
  rcases family_descends (prefixWord ++ tailWord_7746096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7746099 : List Nat := [1, 1, 1, 2, 4, 2, 1, 1, 1, 7, 2]
def baseStart_7746099 : Nat := 118140960795 + 7746099 * 2 ^ 59
def prefixEnd_7746099 : Nat := 4983230072969 + 3 ^ 40 * 7746099 * 2
def baseEnd_7746099 : Nat := 3977471984311594085738845

theorem tailTrace_7746099 : CollatzResearch.WordTrace tailWord_7746099 prefixEnd_7746099 3977471984311594085738845 := by
  unfold tailWord_7746099
  simp only [CollatzResearch.WordTrace]
  refine ⟨282523440764213726230601351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188348960509475817487067567 282523440764213726230601351)
  ·
    refine ⟨423785161146320589345902027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 282523440764213726230601351 423785161146320589345902027)
    ·
      refine ⟨635677741719480884018853041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 423785161146320589345902027 635677741719480884018853041)
      ·
        refine ⟨476758306289610663014139781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 635677741719480884018853041 476758306289610663014139781)
        ·
          refine ⟨89392182429301999315151209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 476758306289610663014139781 89392182429301999315151209)
          ·
            refine ⟨67044136821976499486363407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 89392182429301999315151209 67044136821976499486363407)
            ·
              refine ⟨100566205232964749229545111, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67044136821976499486363407 100566205232964749229545111)
              ·
                refine ⟨150849307849447123844317667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 100566205232964749229545111 150849307849447123844317667)
                ·
                  refine ⟨226273961774170685766476501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 150849307849447123844317667 226273961774170685766476501)
                  ·
                    refine ⟨5303295979082125447651793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 226273961774170685766476501 5303295979082125447651793)
                    ·
                      refine ⟨3977471984311594085738845, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5303295979082125447651793 3977471984311594085738845)
                      ·
                        rfl

theorem cell23_7746099_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 1, 1, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 1, 1, 1, 7, 2].length) (baseStart_7746099 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7746099 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7746099 prefixEnd_7746099 := by exact prefixLift 7746099
  have htrace : WordTrace (prefixWord ++ tailWord_7746099) baseStart_7746099 baseEnd_7746099 := by
    simpa [prefixWord, tailWord_7746099, baseEnd_7746099] using wordTrace_append hprefix tailTrace_7746099
  have hstable : (prefixWord ++ tailWord_7746099).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7746099).length < 2 ^ (prefixWord ++ tailWord_7746099).sum := by decide
  have hdescent : baseEnd_7746099 < baseStart_7746099 := by decide
  rcases family_descends (prefixWord ++ tailWord_7746099) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7746129 : List Nat := [1, 2, 2, 1, 3, 4, 1, 1, 1, 3, 4]
def baseStart_7746129 : Nat := 118140960795 + 7746129 * 2 ^ 59
def prefixEnd_7746129 : Nat := 4983230072969 + 3 ^ 40 * 7746129 * 2
def baseEnd_7746129 : Nat := 3977487388731228968363707

theorem tailTrace_7746129 : CollatzResearch.WordTrace tailWord_7746129 prefixEnd_7746129 3977487388731228968363707 := by
  unfold tailWord_7746129
  simp only [CollatzResearch.WordTrace]
  refine ⟨282524534954105041354193441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188349689969403360902795627 282524534954105041354193441)
  ·
    refine ⟨211893401215578781015645081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 282524534954105041354193441 211893401215578781015645081)
    ·
      refine ⟨158920050911684085761733811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 211893401215578781015645081 158920050911684085761733811)
      ·
        refine ⟨238380076367526128642600717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 158920050911684085761733811 238380076367526128642600717)
        ·
          refine ⟨89392528637822298240975269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 238380076367526128642600717 89392528637822298240975269)
          ·
            refine ⟨16761099119591680920182863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 89392528637822298240975269 16761099119591680920182863)
            ·
              refine ⟨25141648679387521380274295, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16761099119591680920182863 25141648679387521380274295)
              ·
                refine ⟨37712473019081282070411443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25141648679387521380274295 37712473019081282070411443)
                ·
                  refine ⟨56568709528621923105617165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37712473019081282070411443 56568709528621923105617165)
                  ·
                    refine ⟨21213266073233221164606437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 56568709528621923105617165 21213266073233221164606437)
                    ·
                      refine ⟨3977487388731228968363707, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21213266073233221164606437 3977487388731228968363707)
                      ·
                        rfl

theorem cell23_7746129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 4, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 4, 1, 1, 1, 3, 4].length) (baseStart_7746129 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7746129 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7746129 prefixEnd_7746129 := by exact prefixLift 7746129
  have htrace : WordTrace (prefixWord ++ tailWord_7746129) baseStart_7746129 baseEnd_7746129 := by
    simpa [prefixWord, tailWord_7746129, baseEnd_7746129] using wordTrace_append hprefix tailTrace_7746129
  have hstable : (prefixWord ++ tailWord_7746129).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7746129).length < 2 ^ (prefixWord ++ tailWord_7746129).sum := by decide
  have hdescent : baseEnd_7746129 < baseStart_7746129 := by decide
  rcases family_descends (prefixWord ++ tailWord_7746129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7746236 : List Nat := [2, 2, 2, 3, 1, 1, 3, 1, 3, 1, 4]
def baseStart_7746236 : Nat := 118140960795 + 7746236 * 2 ^ 59
def prefixEnd_7746236 : Nat := 4983230072969 + 3 ^ 40 * 7746236 * 2
def baseEnd_7746236 : Nat := 3977542331161260049725715

theorem tailTrace_7746236 : CollatzResearch.WordTrace tailWord_7746236 prefixEnd_7746236 3977542331161260049725715 := by
  unfold tailWord_7746236
  simp only [CollatzResearch.WordTrace]
  refine ⟨141264218782358699314169281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 188352291709811599085559041 141264218782358699314169281)
  ·
    refine ⟨105948164086769024485626961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 141264218782358699314169281 105948164086769024485626961)
    ·
      refine ⟨79461123065076768364220221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 105948164086769024485626961 79461123065076768364220221)
      ·
        refine ⟨29797921149403788136582583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 79461123065076768364220221 29797921149403788136582583)
        ·
          refine ⟨44696881724105682204873875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29797921149403788136582583 44696881724105682204873875)
          ·
            refine ⟨67045322586158523307310813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44696881724105682204873875 67045322586158523307310813)
            ·
              refine ⟨25141995969809446240241555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 67045322586158523307310813 25141995969809446240241555)
              ·
                refine ⟨37712993954714169360362333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25141995969809446240241555 37712993954714169360362333)
                ·
                  refine ⟨14142372733017813510135875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 37712993954714169360362333 14142372733017813510135875)
                  ·
                    refine ⟨21213559099526720265203813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14142372733017813510135875 21213559099526720265203813)
                    ·
                      refine ⟨3977542331161260049725715, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21213559099526720265203813 3977542331161260049725715)
                      ·
                        rfl

theorem cell23_7746236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 3, 1, 3, 1, 4].length) (baseStart_7746236 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7746236 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7746236 prefixEnd_7746236 := by exact prefixLift 7746236
  have htrace : WordTrace (prefixWord ++ tailWord_7746236) baseStart_7746236 baseEnd_7746236 := by
    simpa [prefixWord, tailWord_7746236, baseEnd_7746236] using wordTrace_append hprefix tailTrace_7746236
  have hstable : (prefixWord ++ tailWord_7746236).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7746236).length < 2 ^ (prefixWord ++ tailWord_7746236).sum := by decide
  have hdescent : baseEnd_7746236 < baseStart_7746236 := by decide
  rcases family_descends (prefixWord ++ tailWord_7746236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7746263 : List Nat := [1, 1, 3, 2, 1, 5, 2, 2, 2, 4]
def baseStart_7746263 : Nat := 118140960795 + 7746263 * 2 ^ 59
def prefixEnd_7746263 : Nat := 4983230072969 + 3 ^ 40 * 7746263 * 2
def baseEnd_7746263 : Nat := 1325852065046310481362697

theorem tailTrace_7746263 : CollatzResearch.WordTrace tailWord_7746263 prefixEnd_7746263 1325852065046310481362697 := by
  unfold tailWord_7746263
  simp only [CollatzResearch.WordTrace]
  refine ⟨282529422335619582239571443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188352948223746388159714295 282529422335619582239571443)
  ·
    refine ⟨423794133503429373359357165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 282529422335619582239571443 423794133503429373359357165)
    ·
      refine ⟨158922800063786015009758937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 423794133503429373359357165 158922800063786015009758937)
      ·
        refine ⟨119192100047839511257319203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 158922800063786015009758937 119192100047839511257319203)
        ·
          refine ⟨178788150071759266885978805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 119192100047839511257319203 178788150071759266885978805)
          ·
            refine ⟨16761389069227431270560513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 178788150071759266885978805 16761389069227431270560513)
            ·
              refine ⟨12571041801920573452920385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16761389069227431270560513 12571041801920573452920385)
              ·
                refine ⟨9428281351440430089690289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12571041801920573452920385 9428281351440430089690289)
                ·
                  refine ⟨7071211013580322567267717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9428281351440430089690289 7071211013580322567267717)
                  ·
                    refine ⟨1325852065046310481362697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7071211013580322567267717 1325852065046310481362697)
                    ·
                      rfl

theorem cell23_7746263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 5, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 5, 2, 2, 2, 4].length) (baseStart_7746263 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7746263 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7746263 prefixEnd_7746263 := by exact prefixLift 7746263
  have htrace : WordTrace (prefixWord ++ tailWord_7746263) baseStart_7746263 baseEnd_7746263 := by
    simpa [prefixWord, tailWord_7746263, baseEnd_7746263] using wordTrace_append hprefix tailTrace_7746263
  have hstable : (prefixWord ++ tailWord_7746263).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7746263).length < 2 ^ (prefixWord ++ tailWord_7746263).sum := by decide
  have hdescent : baseEnd_7746263 < baseStart_7746263 := by decide
  rcases family_descends (prefixWord ++ tailWord_7746263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7746276 : List Nat := [2, 3, 1, 1, 1, 6, 1, 8]
def baseStart_7746276 : Nat := 118140960795 + 7746276 * 2 ^ 59
def prefixEnd_7746276 : Nat := 4983230072969 + 3 ^ 40 * 7746276 * 2
def baseEnd_7746276 : Nat := 147317143347682959008353

theorem tailTrace_7746276 : CollatzResearch.WordTrace tailWord_7746276 prefixEnd_7746276 147317143347682959008353 := by
  unfold tailWord_7746276
  simp only [CollatzResearch.WordTrace]
  refine ⟨141264948242286242729897341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 188353264323048323639863121 141264948242286242729897341)
  ·
    refine ⟨52974355590857341023711503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 141264948242286242729897341 52974355590857341023711503)
    ·
      refine ⟨79461533386286011535567255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52974355590857341023711503 79461533386286011535567255)
      ·
        refine ⟨119192300079429017303350883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79461533386286011535567255 119192300079429017303350883)
        ·
          refine ⟨178788450119143525955026325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 119192300079429017303350883 178788450119143525955026325)
          ·
            refine ⟨8380708599334852779141859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 178788450119143525955026325 8380708599334852779141859)
            ·
              refine ⟨12571062899002279168712789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8380708599334852779141859 12571062899002279168712789)
              ·
                refine ⟨147317143347682959008353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 12571062899002279168712789 147317143347682959008353)
                ·
                  rfl

theorem cell23_7746276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 6, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 6, 1, 8].length) (baseStart_7746276 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7746276 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7746276 prefixEnd_7746276 := by exact prefixLift 7746276
  have htrace : WordTrace (prefixWord ++ tailWord_7746276) baseStart_7746276 baseEnd_7746276 := by
    simpa [prefixWord, tailWord_7746276, baseEnd_7746276] using wordTrace_append hprefix tailTrace_7746276
  have hstable : (prefixWord ++ tailWord_7746276).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7746276).length < 2 ^ (prefixWord ++ tailWord_7746276).sum := by decide
  have hdescent : baseEnd_7746276 < baseStart_7746276 := by decide
  rcases family_descends (prefixWord ++ tailWord_7746276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7746289 : List Nat := [1, 2, 2, 2, 2, 2, 1, 2, 2, 7]
def baseStart_7746289 : Nat := 118140960795 + 7746289 * 2 ^ 59
def prefixEnd_7746289 : Nat := 4983230072969 + 3 ^ 40 * 7746289 * 2
def baseEnd_7746289 : Nat := 1325856515211982780787657

theorem tailTrace_7746289 : CollatzResearch.WordTrace tailWord_7746289 prefixEnd_7746289 1325856515211982780787657 := by
  unfold tailWord_7746289
  simp only [CollatzResearch.WordTrace]
  refine ⟨282530370633525388680017921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188353580422350259120011947 282530370633525388680017921)
  ·
    refine ⟨211897777975144041510013441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 282530370633525388680017921 211897777975144041510013441)
    ·
      refine ⟨158923333481358031132510081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 211897777975144041510013441 158923333481358031132510081)
      ·
        refine ⟨119192500111018523349382561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 158923333481358031132510081 119192500111018523349382561)
        ·
          refine ⟨89394375083263892512036921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 119192500111018523349382561 89394375083263892512036921)
          ·
            refine ⟨67045781312447919384027691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 89394375083263892512036921 67045781312447919384027691)
            ·
              refine ⟨100568671968671879076041537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67045781312447919384027691 100568671968671879076041537)
              ·
                refine ⟨75426503976503909307031153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 100568671968671879076041537 75426503976503909307031153)
                ·
                  refine ⟨56569877982377931980273365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 75426503976503909307031153 56569877982377931980273365)
                  ·
                    refine ⟨1325856515211982780787657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 56569877982377931980273365 1325856515211982780787657)
                    ·
                      rfl

theorem cell23_7746289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 1, 2, 2, 7].length) (baseStart_7746289 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7746289 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7746289 prefixEnd_7746289 := by exact prefixLift 7746289
  have htrace : WordTrace (prefixWord ++ tailWord_7746289) baseStart_7746289 baseEnd_7746289 := by
    simpa [prefixWord, tailWord_7746289, baseEnd_7746289] using wordTrace_append hprefix tailTrace_7746289
  have hstable : (prefixWord ++ tailWord_7746289).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7746289).length < 2 ^ (prefixWord ++ tailWord_7746289).sum := by decide
  have hdescent : baseEnd_7746289 < baseStart_7746289 := by decide
  rcases family_descends (prefixWord ++ tailWord_7746289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7746319 : List Nat := [1, 1, 2, 1, 1, 1, 5, 1, 4, 6]
def baseStart_7746319 : Nat := 118140960795 + 7746319 * 2 ^ 59
def prefixEnd_7746319 : Nat := 4983230072969 + 3 ^ 40 * 7746319 * 2
def baseEnd_7746319 : Nat := 1325861650018527741662611

theorem tailTrace_7746319 : CollatzResearch.WordTrace tailWord_7746319 prefixEnd_7746319 1325861650018527741662611 := by
  unfold tailWord_7746319
  simp only [CollatzResearch.WordTrace]
  refine ⟨282531464823416703803610011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188354309882277802535740007 282531464823416703803610011)
  ·
    refine ⟨423797197235125055705415017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 282531464823416703803610011 423797197235125055705415017)
    ·
      refine ⟨317847897926343791779061263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 423797197235125055705415017 317847897926343791779061263)
      ·
        refine ⟨476771846889515687668591895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 317847897926343791779061263 476771846889515687668591895)
        ·
          refine ⟨715157770334273531502887843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 476771846889515687668591895 715157770334273531502887843)
          ·
            refine ⟨1072736655501410297254331765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 715157770334273531502887843 1072736655501410297254331765)
            ·
              refine ⟨100569061453257215367593603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1072736655501410297254331765 100569061453257215367593603)
              ·
                refine ⟨150853592179885823051390405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 100569061453257215367593603 150853592179885823051390405)
                ·
                  refine ⟨28285048533728591822135701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 150853592179885823051390405 28285048533728591822135701)
                  ·
                    refine ⟨1325861650018527741662611, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28285048533728591822135701 1325861650018527741662611)
                    ·
                      rfl

theorem cell23_7746319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 5, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 5, 1, 4, 6].length) (baseStart_7746319 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7746319 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7746319 prefixEnd_7746319 := by exact prefixLift 7746319
  have htrace : WordTrace (prefixWord ++ tailWord_7746319) baseStart_7746319 baseEnd_7746319 := by
    simpa [prefixWord, tailWord_7746319, baseEnd_7746319] using wordTrace_append hprefix tailTrace_7746319
  have hstable : (prefixWord ++ tailWord_7746319).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7746319).length < 2 ^ (prefixWord ++ tailWord_7746319).sum := by decide
  have hdescent : baseEnd_7746319 < baseStart_7746319 := by decide
  rcases family_descends (prefixWord ++ tailWord_7746319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7746329 : List Nat := [1, 2, 1, 2, 1, 1, 1, 3, 3, 3, 5]
def baseStart_7746329 : Nat := 118140960795 + 7746329 * 2 ^ 59
def prefixEnd_7746329 : Nat := 4983230072969 + 3 ^ 40 * 7746329 * 2
def baseEnd_7746329 : Nat := 3977590084862128185862787

theorem tailTrace_7746329 : CollatzResearch.WordTrace tailWord_7746329 prefixEnd_7746329 3977590084862128185862787 := by
  unfold tailWord_7746329
  simp only [CollatzResearch.WordTrace]
  refine ⟨282531829553380475511474041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188354553035586983674316027 282531829553380475511474041)
  ·
    refine ⟨211898872165035356633605531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 282531829553380475511474041 211898872165035356633605531)
    ·
      refine ⟨317848308247553034950408297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 211898872165035356633605531 317848308247553034950408297)
      ·
        refine ⟨238386231185664776212806223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 317848308247553034950408297 238386231185664776212806223)
        ·
          refine ⟨357579346778497164319209335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 238386231185664776212806223 357579346778497164319209335)
          ·
            refine ⟨536369020167745746478814003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 357579346778497164319209335 536369020167745746478814003)
            ·
              refine ⟨804553530251618619718221005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 536369020167745746478814003 804553530251618619718221005)
              ·
                refine ⟨301707573844356982394332877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 804553530251618619718221005 301707573844356982394332877)
                ·
                  refine ⟨113140340191633868397874829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 301707573844356982394332877 113140340191633868397874829)
                  ·
                    refine ⟨42427627571862700649203061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 113140340191633868397874829 42427627571862700649203061)
                    ·
                      refine ⟨3977590084862128185862787, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 42427627571862700649203061 3977590084862128185862787)
                      ·
                        rfl

theorem cell23_7746329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 3, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 3, 3, 3, 5].length) (baseStart_7746329 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7746329 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7746329 prefixEnd_7746329 := by exact prefixLift 7746329
  have htrace : WordTrace (prefixWord ++ tailWord_7746329) baseStart_7746329 baseEnd_7746329 := by
    simpa [prefixWord, tailWord_7746329, baseEnd_7746329] using wordTrace_append hprefix tailTrace_7746329
  have hstable : (prefixWord ++ tailWord_7746329).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7746329).length < 2 ^ (prefixWord ++ tailWord_7746329).sum := by decide
  have hdescent : baseEnd_7746329 < baseStart_7746329 := by decide
  rcases family_descends (prefixWord ++ tailWord_7746329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7746336 : List Nat := [2, 1, 1, 5, 1, 2, 2, 1, 2, 6]
def baseStart_7746336 : Nat := 118140960795 + 7746336 * 2 ^ 59
def prefixEnd_7746336 : Nat := 4983230072969 + 3 ^ 40 * 7746336 * 2
def baseEnd_7746336 : Nat := 1325864559742236552825085

theorem tailTrace_7746336 : CollatzResearch.WordTrace tailWord_7746336 prefixEnd_7746336 1325864559742236552825085 := by
  unfold tailWord_7746336
  simp only [CollatzResearch.WordTrace]
  refine ⟨141266042432177557853489431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 188354723242903410471319241 141266042432177557853489431)
  ·
    refine ⟨211899063648266336780234147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141266042432177557853489431 211899063648266336780234147)
    ·
      refine ⟨317848595472399505170351221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 211899063648266336780234147 317848595472399505170351221)
      ·
        refine ⟨29798305825537453609720427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 317848595472399505170351221 29798305825537453609720427)
        ·
          refine ⟨44697458738306180414580641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29798305825537453609720427 44697458738306180414580641)
          ·
            refine ⟨33523094053729635310935481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44697458738306180414580641 33523094053729635310935481)
            ·
              refine ⟨25142320540297226483201611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33523094053729635310935481 25142320540297226483201611)
              ·
                refine ⟨37713480810445839724802417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25142320540297226483201611 37713480810445839724802417)
                ·
                  refine ⟨28285110607834379793601813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37713480810445839724802417 28285110607834379793601813)
                  ·
                    refine ⟨1325864559742236552825085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28285110607834379793601813 1325864559742236552825085)
                    ·
                      rfl

theorem cell23_7746336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 2, 2, 1, 2, 6].length) (baseStart_7746336 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7746336 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7746336 prefixEnd_7746336 := by exact prefixLift 7746336
  have htrace : WordTrace (prefixWord ++ tailWord_7746336) baseStart_7746336 baseEnd_7746336 := by
    simpa [prefixWord, tailWord_7746336, baseEnd_7746336] using wordTrace_append hprefix tailTrace_7746336
  have hstable : (prefixWord ++ tailWord_7746336).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7746336).length < 2 ^ (prefixWord ++ tailWord_7746336).sum := by decide
  have hdescent : baseEnd_7746336 < baseStart_7746336 := by decide
  rcases family_descends (prefixWord ++ tailWord_7746336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7746379 : List Nat := [1, 1, 1, 1, 3, 1, 1, 1, 2, 11]
def baseStart_7746379 : Nat := 118140960795 + 7746379 * 2 ^ 59
def prefixEnd_7746379 : Nat := 4983230072969 + 3 ^ 40 * 7746379 * 2
def baseEnd_7746379 : Nat := 1325871919631617663412519

theorem tailTrace_7746379 : CollatzResearch.WordTrace tailWord_7746379 prefixEnd_7746379 1325871919631617663412519 := by
  unfold tailWord_7746379
  simp only [CollatzResearch.WordTrace]
  refine ⟨282533653203199334050794191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188355768802132889367196127 282533653203199334050794191)
  ·
    refine ⟨423800479804799001076191287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 282533653203199334050794191 423800479804799001076191287)
    ·
      refine ⟨635700719707198501614286931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 423800479804799001076191287 635700719707198501614286931)
      ·
        refine ⟨953551079560797752421430397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 635700719707198501614286931 953551079560797752421430397)
        ·
          refine ⟨357581654835299157158036399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 953551079560797752421430397 357581654835299157158036399)
          ·
            refine ⟨536372482252948735737054599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 357581654835299157158036399 536372482252948735737054599)
            ·
              refine ⟨804558723379423103605581899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 536372482252948735737054599 804558723379423103605581899)
              ·
                refine ⟨1206838085069134655408372849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 804558723379423103605581899 1206838085069134655408372849)
                ·
                  refine ⟨905128563801850991556279637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1206838085069134655408372849 905128563801850991556279637)
                  ·
                    refine ⟨1325871919631617663412519, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 11 905128563801850991556279637 1325871919631617663412519)
                    ·
                      rfl

theorem cell23_7746379_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 1, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 1, 2, 11].length) (baseStart_7746379 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7746379 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7746379 prefixEnd_7746379 := by exact prefixLift 7746379
  have htrace : WordTrace (prefixWord ++ tailWord_7746379) baseStart_7746379 baseEnd_7746379 := by
    simpa [prefixWord, tailWord_7746379, baseEnd_7746379] using wordTrace_append hprefix tailTrace_7746379
  have hstable : (prefixWord ++ tailWord_7746379).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7746379).length < 2 ^ (prefixWord ++ tailWord_7746379).sum := by decide
  have hdescent : baseEnd_7746379 < baseStart_7746379 := by decide
  rcases family_descends (prefixWord ++ tailWord_7746379) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7746394 : List Nat := [3, 1, 1, 2, 1, 6, 2, 1, 2, 2, 2]
def baseStart_7746394 : Nat := 118140960795 + 7746394 * 2 ^ 59
def prefixEnd_7746394 : Nat := 4983230072969 + 3 ^ 40 * 7746394 * 2
def baseEnd_7746394 : Nat := 3977623461104670431549989

theorem tailTrace_7746394 : CollatzResearch.WordTrace tailWord_7746394 prefixEnd_7746394 3977623461104670431549989 := by
  unfold tailWord_7746394
  simp only [CollatzResearch.WordTrace]
  refine ⟨70633550074536247903147559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 188356133532096661075060157 70633550074536247903147559)
  ·
    refine ⟨105950325111804371854721339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70633550074536247903147559 105950325111804371854721339)
    ·
      refine ⟨158925487667706557782082009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105950325111804371854721339 158925487667706557782082009)
      ·
        refine ⟨119194115750779918336561507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 158925487667706557782082009 119194115750779918336561507)
        ·
          refine ⟨178791173626169877504842261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 119194115750779918336561507 178791173626169877504842261)
          ·
            refine ⟨8380836263726713008039481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 178791173626169877504842261 8380836263726713008039481)
            ·
              refine ⟨6285627197795034756029611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8380836263726713008039481 6285627197795034756029611)
              ·
                refine ⟨9428440796692552134044417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6285627197795034756029611 9428440796692552134044417)
                ·
                  refine ⟨7071330597519414100533313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9428440796692552134044417 7071330597519414100533313)
                  ·
                    refine ⟨5303497948139560575399985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7071330597519414100533313 5303497948139560575399985)
                    ·
                      refine ⟨3977623461104670431549989, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5303497948139560575399985 3977623461104670431549989)
                      ·
                        rfl

theorem cell23_7746394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 6, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 6, 2, 1, 2, 2, 2].length) (baseStart_7746394 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7746394 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7746394 prefixEnd_7746394 := by exact prefixLift 7746394
  have htrace : WordTrace (prefixWord ++ tailWord_7746394) baseStart_7746394 baseEnd_7746394 := by
    simpa [prefixWord, tailWord_7746394, baseEnd_7746394] using wordTrace_append hprefix tailTrace_7746394
  have hstable : (prefixWord ++ tailWord_7746394).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7746394).length < 2 ^ (prefixWord ++ tailWord_7746394).sum := by decide
  have hdescent : baseEnd_7746394 < baseStart_7746394 := by decide
  rcases family_descends (prefixWord ++ tailWord_7746394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7746416 : List Nat := [2, 1, 1, 1, 4, 1, 2, 3, 1, 3, 4]
def baseStart_7746416 : Nat := 118140960795 + 7746416 * 2 ^ 59
def prefixEnd_7746416 : Nat := 4983230072969 + 3 ^ 40 * 7746416 * 2
def baseEnd_7746416 : Nat := 3977634757679069345474887

theorem tailTrace_7746416 : CollatzResearch.WordTrace tailWord_7746416 prefixEnd_7746416 3977634757679069345474887 := by
  unfold tailWord_7746416
  simp only [CollatzResearch.WordTrace]
  refine ⟨141267501352032644684945551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 188356668469376859579927401 141267501352032644684945551)
  ·
    refine ⟨211901252028048967027418327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141267501352032644684945551 211901252028048967027418327)
    ·
      refine ⟨317851878042073450541127491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 211901252028048967027418327 317851878042073450541127491)
      ·
        refine ⟨476777817063110175811691237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 317851878042073450541127491 476777817063110175811691237)
        ·
          refine ⟨89395840699333157964692107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 476777817063110175811691237 89395840699333157964692107)
          ·
            refine ⟨134093761048999736947038161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89395840699333157964692107 134093761048999736947038161)
            ·
              refine ⟨100570320786749802710278621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 134093761048999736947038161 100570320786749802710278621)
              ·
                refine ⟨37713870295031176016354483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 100570320786749802710278621 37713870295031176016354483)
                ·
                  refine ⟨56570805442546764024531725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37713870295031176016354483 56570805442546764024531725)
                  ·
                    refine ⟨21214052040955036509199397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 56570805442546764024531725 21214052040955036509199397)
                    ·
                      refine ⟨3977634757679069345474887, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21214052040955036509199397 3977634757679069345474887)
                      ·
                        rfl

theorem cell23_7746416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 2, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 2, 3, 1, 3, 4].length) (baseStart_7746416 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7746416 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7746416 prefixEnd_7746416 := by exact prefixLift 7746416
  have htrace : WordTrace (prefixWord ++ tailWord_7746416) baseStart_7746416 baseEnd_7746416 := by
    simpa [prefixWord, tailWord_7746416, baseEnd_7746416] using wordTrace_append hprefix tailTrace_7746416
  have hstable : (prefixWord ++ tailWord_7746416).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7746416).length < 2 ^ (prefixWord ++ tailWord_7746416).sum := by decide
  have hdescent : baseEnd_7746416 < baseStart_7746416 := by decide
  rcases family_descends (prefixWord ++ tailWord_7746416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7746434 : List Nat := [3, 4, 2, 2, 1, 1, 1, 4, 5]
def baseStart_7746434 : Nat := 118140960795 + 7746434 * 2 ^ 59
def prefixEnd_7746434 : Nat := 4983230072969 + 3 ^ 40 * 7746434 * 2
def baseEnd_7746434 : Nat := 441960444481205586116645

theorem tailTrace_7746434 : CollatzResearch.WordTrace tailWord_7746434 prefixEnd_7746434 441960444481205586116645 := by
  unfold tailWord_7746434
  simp only [CollatzResearch.WordTrace]
  refine ⟨70633914804500019611011589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 188357106145333385629364237 70633914804500019611011589)
  ·
    refine ⟨13243859025843753677064673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 70633914804500019611011589 13243859025843753677064673)
    ·
      refine ⟨9932894269382815257798505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13243859025843753677064673 9932894269382815257798505)
      ·
        refine ⟨7449670702037111443348879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9932894269382815257798505 7449670702037111443348879)
        ·
          refine ⟨11174506053055667165023319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7449670702037111443348879 11174506053055667165023319)
          ·
            refine ⟨16761759079583500747534979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11174506053055667165023319 16761759079583500747534979)
            ·
              refine ⟨25142638619375251121302469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16761759079583500747534979 25142638619375251121302469)
              ·
                refine ⟨4714244741132859585244213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25142638619375251121302469 4714244741132859585244213)
                ·
                  refine ⟨441960444481205586116645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4714244741132859585244213 441960444481205586116645)
                  ·
                    rfl

theorem cell23_7746434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 1, 1, 1, 4, 5].length) (baseStart_7746434 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7746434 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7746434 prefixEnd_7746434 := by exact prefixLift 7746434
  have htrace : WordTrace (prefixWord ++ tailWord_7746434) baseStart_7746434 baseEnd_7746434 := by
    simpa [prefixWord, tailWord_7746434, baseEnd_7746434] using wordTrace_append hprefix tailTrace_7746434
  have hstable : (prefixWord ++ tailWord_7746434).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7746434).length < 2 ^ (prefixWord ++ tailWord_7746434).sum := by decide
  have hdescent : baseEnd_7746434 < baseStart_7746434 := by decide
  rcases family_descends (prefixWord ++ tailWord_7746434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7746436 : List Nat := [2, 3, 2, 1, 1, 1, 1, 1, 1, 5, 5]
def baseStart_7746436 : Nat := 118140960795 + 7746436 * 2 ^ 59
def prefixEnd_7746436 : Nat := 4983230072969 + 3 ^ 40 * 7746436 * 2
def baseEnd_7746436 : Nat := 3977645027292159267224795

theorem tailTrace_7746436 : CollatzResearch.WordTrace tailWord_7746436 prefixEnd_7746436 3977645027292159267224795 := by
  unfold tailWord_7746436
  simp only [CollatzResearch.WordTrace]
  refine ⟨141267866081996416392809581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 188357154775995221857079441 141267866081996416392809581)
  ·
    refine ⟨52975449780748656147303593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 141267866081996416392809581 52975449780748656147303593)
    ·
      refine ⟨39731587335561492110477695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52975449780748656147303593 39731587335561492110477695)
      ·
        refine ⟨59597381003342238165716543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39731587335561492110477695 59597381003342238165716543)
        ·
          refine ⟨89396071505013357248574815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59597381003342238165716543 89396071505013357248574815)
          ·
            refine ⟨134094107257520035872862223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89396071505013357248574815 134094107257520035872862223)
            ·
              refine ⟨201141160886280053809293335, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 134094107257520035872862223 201141160886280053809293335)
              ·
                refine ⟨301711741329420080713940003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 201141160886280053809293335 301711741329420080713940003)
                ·
                  refine ⟨452567611994130121070910005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 301711741329420080713940003 452567611994130121070910005)
                  ·
                    refine ⟨42428213624449698850397813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 452567611994130121070910005 42428213624449698850397813)
                    ·
                      refine ⟨3977645027292159267224795, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 42428213624449698850397813 3977645027292159267224795)
                      ·
                        rfl

theorem cell23_7746436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 1, 1, 1, 5, 5].length) (baseStart_7746436 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7746436 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7746436 prefixEnd_7746436 := by exact prefixLift 7746436
  have htrace : WordTrace (prefixWord ++ tailWord_7746436) baseStart_7746436 baseEnd_7746436 := by
    simpa [prefixWord, tailWord_7746436, baseEnd_7746436] using wordTrace_append hprefix tailTrace_7746436
  have hstable : (prefixWord ++ tailWord_7746436).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7746436).length < 2 ^ (prefixWord ++ tailWord_7746436).sum := by decide
  have hdescent : baseEnd_7746436 < baseStart_7746436 := by decide
  rcases family_descends (prefixWord ++ tailWord_7746436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7746510 : List Nat := [4, 1, 1, 1, 2, 3, 1, 2, 1, 5, 2]
def baseStart_7746510 : Nat := 118140960795 + 7746510 * 2 ^ 59
def prefixEnd_7746510 : Nat := 4983230072969 + 3 ^ 40 * 7746510 * 2
def baseEnd_7746510 : Nat := 3977683024860591977699455

theorem tailTrace_7746510 : CollatzResearch.WordTrace tailWord_7746510 prefixEnd_7746510 3977683024860591977699455 := by
  unfold tailWord_7746510
  simp only [CollatzResearch.WordTrace]
  refine ⟨35317303895715592927976623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 188358954110483162282541989 35317303895715592927976623)
  ·
    refine ⟨52975955843573389391964935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35317303895715592927976623 52975955843573389391964935)
    ·
      refine ⟨79463933765360084087947403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52975955843573389391964935 79463933765360084087947403)
      ·
        refine ⟨119195900648040126131921105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79463933765360084087947403 119195900648040126131921105)
        ·
          refine ⟨89396925486030094598940829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 119195900648040126131921105 89396925486030094598940829)
          ·
            refine ⟨33523847057261285474602811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 89396925486030094598940829 33523847057261285474602811)
            ·
              refine ⟨50285770585891928211904217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33523847057261285474602811 50285770585891928211904217)
              ·
                refine ⟨37714327939418946158928163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50285770585891928211904217 37714327939418946158928163)
                ·
                  refine ⟨56571491909128419238392245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37714327939418946158928163 56571491909128419238392245)
                  ·
                    refine ⟨5303577366480789303599273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 56571491909128419238392245 5303577366480789303599273)
                    ·
                      refine ⟨3977683024860591977699455, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5303577366480789303599273 3977683024860591977699455)
                      ·
                        rfl

theorem cell23_7746510_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 3, 1, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 3, 1, 2, 1, 5, 2].length) (baseStart_7746510 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7746510 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7746510 prefixEnd_7746510 := by exact prefixLift 7746510
  have htrace : WordTrace (prefixWord ++ tailWord_7746510) baseStart_7746510 baseEnd_7746510 := by
    simpa [prefixWord, tailWord_7746510, baseEnd_7746510] using wordTrace_append hprefix tailTrace_7746510
  have hstable : (prefixWord ++ tailWord_7746510).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7746510).length < 2 ^ (prefixWord ++ tailWord_7746510).sum := by decide
  have hdescent : baseEnd_7746510 < baseStart_7746510 := by decide
  rcases family_descends (prefixWord ++ tailWord_7746510) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7746520 : List Nat := [2, 1, 2, 2, 2, 4, 2, 2, 1, 5]
def baseStart_7746520 : Nat := 118140960795 + 7746520 * 2 ^ 59
def prefixEnd_7746520 : Nat := 4983230072969 + 3 ^ 40 * 7746520 * 2
def baseEnd_7746520 : Nat := 1325896053222378979524803

theorem tailTrace_7746520 : CollatzResearch.WordTrace tailWord_7746520 prefixEnd_7746520 1325896053222378979524803 := by
  unfold tailWord_7746520
  simp only [CollatzResearch.WordTrace]
  refine ⟨141269397947844257565838507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 188359197263792343421118009 141269397947844257565838507)
  ·
    refine ⟨211904096921766386348757761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141269397947844257565838507 211904096921766386348757761)
    ·
      refine ⟨158928072691324789761568321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 211904096921766386348757761 158928072691324789761568321)
      ·
        refine ⟨119196054518493592321176241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 158928072691324789761568321 119196054518493592321176241)
        ·
          refine ⟨89397040888870194240882181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 119196054518493592321176241 89397040888870194240882181)
          ·
            refine ⟨16761945166663161420165409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 89397040888870194240882181 16761945166663161420165409)
            ·
              refine ⟨12571458874997371065124057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16761945166663161420165409 12571458874997371065124057)
              ·
                refine ⟨9428594156248028298843043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12571458874997371065124057 9428594156248028298843043)
                ·
                  refine ⟨14142891234372042448264565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9428594156248028298843043 14142891234372042448264565)
                  ·
                    refine ⟨1325896053222378979524803, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14142891234372042448264565 1325896053222378979524803)
                    ·
                      rfl

theorem cell23_7746520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 4, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 4, 2, 2, 1, 5].length) (baseStart_7746520 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7746520 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7746520 prefixEnd_7746520 := by exact prefixLift 7746520
  have htrace : WordTrace (prefixWord ++ tailWord_7746520) baseStart_7746520 baseEnd_7746520 := by
    simpa [prefixWord, tailWord_7746520, baseEnd_7746520] using wordTrace_append hprefix tailTrace_7746520
  have hstable : (prefixWord ++ tailWord_7746520).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7746520).length < 2 ^ (prefixWord ++ tailWord_7746520).sum := by decide
  have hdescent : baseEnd_7746520 < baseStart_7746520 := by decide
  rcases family_descends (prefixWord ++ tailWord_7746520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7746543 : List Nat := [1, 1, 2, 1, 4, 3, 1, 3, 1, 1, 5]
def baseStart_7746543 : Nat := 118140960795 + 7746543 * 2 ^ 59
def prefixEnd_7746543 : Nat := 4983230072969 + 3 ^ 40 * 7746543 * 2
def baseEnd_7746543 : Nat := 3977699969722190348586803

theorem tailTrace_7746543 : CollatzResearch.WordTrace tailWord_7746543 prefixEnd_7746543 3977699969722190348586803 := by
  unfold tailWord_7746543
  simp only [CollatzResearch.WordTrace]
  refine ⟨282539634774605190059764283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188359756516403460039842855 282539634774605190059764283)
  ·
    refine ⟨423809452161907785089646425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 282539634774605190059764283 423809452161907785089646425)
    ·
      refine ⟨317857089121430838817234819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 423809452161907785089646425 317857089121430838817234819)
      ·
        refine ⟨476785633682146258225852229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 317857089121430838817234819 476785633682146258225852229)
        ·
          refine ⟨89397306315402423417347293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 476785633682146258225852229 89397306315402423417347293)
          ·
            refine ⟨33523989868275908781505235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 89397306315402423417347293 33523989868275908781505235)
            ·
              refine ⟨50285984802413863172257853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33523989868275908781505235 50285984802413863172257853)
              ·
                refine ⟨18857244300905198689596695, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 50285984802413863172257853 18857244300905198689596695)
                ·
                  refine ⟨28285866451357798034395043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18857244300905198689596695 28285866451357798034395043)
                  ·
                    refine ⟨42428799677036697051592565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 28285866451357798034395043 42428799677036697051592565)
                    ·
                      refine ⟨3977699969722190348586803, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 42428799677036697051592565 3977699969722190348586803)
                      ·
                        rfl

theorem cell23_7746543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 3, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 3, 1, 3, 1, 1, 5].length) (baseStart_7746543 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7746543 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7746543 prefixEnd_7746543 := by exact prefixLift 7746543
  have htrace : WordTrace (prefixWord ++ tailWord_7746543) baseStart_7746543 baseEnd_7746543 := by
    simpa [prefixWord, tailWord_7746543, baseEnd_7746543] using wordTrace_append hprefix tailTrace_7746543
  have hstable : (prefixWord ++ tailWord_7746543).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7746543).length < 2 ^ (prefixWord ++ tailWord_7746543).sum := by decide
  have hdescent : baseEnd_7746543 < baseStart_7746543 := by decide
  rcases family_descends (prefixWord ++ tailWord_7746543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7746578 : List Nat := [3, 2, 5, 1, 1, 1, 2, 1, 2, 3, 2]
def baseStart_7746578 : Nat := 118140960795 + 7746578 * 2 ^ 59
def prefixEnd_7746578 : Nat := 4983230072969 + 3 ^ 40 * 7746578 * 2
def baseEnd_7746578 : Nat := 3977717941545097711649143

theorem tailTrace_7746578 : CollatzResearch.WordTrace tailWord_7746578 prefixEnd_7746578 3977717941545097711649143 := by
  unfold tailWord_7746578
  simp only [CollatzResearch.WordTrace]
  refine ⟨70635227832369597759322097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 188360607552985594024858925 70635227832369597759322097)
  ·
    refine ⟨52976420874277198319491573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70635227832369597759322097 52976420874277198319491573)
    ·
      refine ⟨4966539456963487342452335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 52976420874277198319491573 4966539456963487342452335)
      ·
        refine ⟨7449809185445231013678503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4966539456963487342452335 7449809185445231013678503)
        ·
          refine ⟨11174713778167846520517755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7449809185445231013678503 11174713778167846520517755)
          ·
            refine ⟨16762070667251769780776633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11174713778167846520517755 16762070667251769780776633)
            ·
              refine ⟨12571553000438827335582475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16762070667251769780776633 12571553000438827335582475)
              ·
                refine ⟨18857329500658241003373713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12571553000438827335582475 18857329500658241003373713)
                ·
                  refine ⟨14142997125493680752530285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18857329500658241003373713 14142997125493680752530285)
                  ·
                    refine ⟨5303623922060130282198857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14142997125493680752530285 5303623922060130282198857)
                    ·
                      refine ⟨3977717941545097711649143, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5303623922060130282198857 3977717941545097711649143)
                      ·
                        rfl

theorem cell23_7746578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 1, 1, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 1, 1, 2, 1, 2, 3, 2].length) (baseStart_7746578 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7746578 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7746578 prefixEnd_7746578 := by exact prefixLift 7746578
  have htrace : WordTrace (prefixWord ++ tailWord_7746578) baseStart_7746578 baseEnd_7746578 := by
    simpa [prefixWord, tailWord_7746578, baseEnd_7746578] using wordTrace_append hprefix tailTrace_7746578
  have hstable : (prefixWord ++ tailWord_7746578).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7746578).length < 2 ^ (prefixWord ++ tailWord_7746578).sum := by decide
  have hdescent : baseEnd_7746578 < baseStart_7746578 := by decide
  rcases family_descends (prefixWord ++ tailWord_7746578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7746594 : List Nat := [3, 3, 1, 1, 1, 4, 3, 1, 1, 2, 3]
def baseStart_7746594 : Nat := 118140960795 + 7746594 * 2 ^ 59
def prefixEnd_7746594 : Nat := 4983230072969 + 3 ^ 40 * 7746594 * 2
def baseEnd_7746594 : Nat := 3977726157235569649049069

theorem tailTrace_7746594 : CollatzResearch.WordTrace tailWord_7746594 prefixEnd_7746594 3977726157235569649049069 := by
  unfold tailWord_7746594
  simp only [CollatzResearch.WordTrace]
  refine ⟨70635373724355106442467709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 188360996598280283846580557 70635373724355106442467709)
  ·
    refine ⟨26488265146633164915925391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 70635373724355106442467709 26488265146633164915925391)
    ·
      refine ⟨39732397719949747373888087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26488265146633164915925391 39732397719949747373888087)
      ·
        refine ⟨59598596579924621060832131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39732397719949747373888087 59598596579924621060832131)
        ·
          refine ⟨89397894869886931591248197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59598596579924621060832131 89397894869886931591248197)
          ·
            refine ⟨16762105288103799673359037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 89397894869886931591248197 16762105288103799673359037)
            ·
              refine ⟨6285789483038924877509639, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16762105288103799673359037 6285789483038924877509639)
              ·
                refine ⟨9428684224558387316264459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6285789483038924877509639 9428684224558387316264459)
                ·
                  refine ⟨14143026336837580974396689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9428684224558387316264459 14143026336837580974396689)
                  ·
                    refine ⟨10607269752628185730797517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14143026336837580974396689 10607269752628185730797517)
                    ·
                      refine ⟨3977726157235569649049069, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10607269752628185730797517 3977726157235569649049069)
                      ·
                        rfl

theorem cell23_7746594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 4, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 4, 3, 1, 1, 2, 3].length) (baseStart_7746594 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7746594 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7746594 prefixEnd_7746594 := by exact prefixLift 7746594
  have htrace : WordTrace (prefixWord ++ tailWord_7746594) baseStart_7746594 baseEnd_7746594 := by
    simpa [prefixWord, tailWord_7746594, baseEnd_7746594] using wordTrace_append hprefix tailTrace_7746594
  have hstable : (prefixWord ++ tailWord_7746594).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7746594).length < 2 ^ (prefixWord ++ tailWord_7746594).sum := by decide
  have hdescent : baseEnd_7746594 < baseStart_7746594 := by decide
  rcases family_descends (prefixWord ++ tailWord_7746594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7746617 : List Nat := [1, 2, 1, 5, 2, 1, 1, 2, 3, 3, 2]
def baseStart_7746617 : Nat := 118140960795 + 7746617 * 2 ^ 59
def prefixEnd_7746617 : Nat := 4983230072969 + 3 ^ 40 * 7746617 * 2
def baseEnd_7746617 : Nat := 3977737967290623059061463

theorem tailTrace_7746617 : CollatzResearch.WordTrace tailWord_7746617 prefixEnd_7746617 3977737967290623059061463 := by
  unfold tailWord_7746617
  simp only [CollatzResearch.WordTrace]
  refine ⟨282542333776337100697958105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188361555850891400465305403 282542333776337100697958105)
  ·
    refine ⟨211906750332252825523468579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 282542333776337100697958105 211906750332252825523468579)
    ·
      refine ⟨317860125498379238285202869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 211906750332252825523468579 317860125498379238285202869)
      ·
        refine ⟨29799386765473053589237769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 317860125498379238285202869 29799386765473053589237769)
        ·
          refine ⟨22349540074104790191928327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29799386765473053589237769 22349540074104790191928327)
          ·
            refine ⟨33524310111157185287892491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22349540074104790191928327 33524310111157185287892491)
            ·
              refine ⟨50286465166735777931838737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33524310111157185287892491 50286465166735777931838737)
              ·
                refine ⟨37714848875051833448879053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50286465166735777931838737 37714848875051833448879053)
                ·
                  refine ⟨14143068328144437543329645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 37714848875051833448879053 14143068328144437543329645)
                  ·
                    refine ⟨5303650623054164078748617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14143068328144437543329645 5303650623054164078748617)
                    ·
                      refine ⟨3977737967290623059061463, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5303650623054164078748617 3977737967290623059061463)
                      ·
                        rfl

theorem cell23_7746617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 1, 1, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 1, 1, 2, 3, 3, 2].length) (baseStart_7746617 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7746617 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7746617 prefixEnd_7746617 := by exact prefixLift 7746617
  have htrace : WordTrace (prefixWord ++ tailWord_7746617) baseStart_7746617 baseEnd_7746617 := by
    simpa [prefixWord, tailWord_7746617, baseEnd_7746617] using wordTrace_append hprefix tailTrace_7746617
  have hstable : (prefixWord ++ tailWord_7746617).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7746617).length < 2 ^ (prefixWord ++ tailWord_7746617).sum := by decide
  have hdescent : baseEnd_7746617 < baseStart_7746617 := by decide
  rcases family_descends (prefixWord ++ tailWord_7746617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7746633 : List Nat := [1, 2, 1, 1, 2, 2, 2, 4, 2, 1, 5]
def baseStart_7746633 : Nat := 118140960795 + 7746633 * 2 ^ 59
def prefixEnd_7746633 : Nat := 4983230072969 + 3 ^ 40 * 7746633 * 2
def baseEnd_7746633 : Nat := 3977746182981094996461389

theorem tailTrace_7746633 : CollatzResearch.WordTrace tailWord_7746633 prefixEnd_7746633 3977746182981094996461389 := by
  unfold tailWord_7746633
  simp only [CollatzResearch.WordTrace]
  refine ⟨282542917344279135430540553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188361944896186090287027035 282542917344279135430540553)
  ·
    refine ⟨211907188008209351572905415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 282542917344279135430540553 211907188008209351572905415)
    ·
      refine ⟨317860782012314027359358123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 211907188008209351572905415 317860782012314027359358123)
      ·
        refine ⟨476791173018471041039037185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 317860782012314027359358123 476791173018471041039037185)
        ·
          refine ⟨357593379763853280779277889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 476791173018471041039037185 357593379763853280779277889)
          ·
            refine ⟨268195034822889960584458417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 357593379763853280779277889 268195034822889960584458417)
            ·
              refine ⟨201146276117167470438343813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 268195034822889960584458417 201146276117167470438343813)
              ·
                refine ⟨37714926771968900707189465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 201146276117167470438343813 37714926771968900707189465)
                ·
                  refine ⟨28286195078976675530392099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37714926771968900707189465 28286195078976675530392099)
                  ·
                    refine ⟨42429292618465013295588149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 28286195078976675530392099 42429292618465013295588149)
                    ·
                      refine ⟨3977746182981094996461389, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 42429292618465013295588149 3977746182981094996461389)
                      ·
                        rfl

theorem cell23_7746633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 2, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 2, 4, 2, 1, 5].length) (baseStart_7746633 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7746633 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7746633 prefixEnd_7746633 := by exact prefixLift 7746633
  have htrace : WordTrace (prefixWord ++ tailWord_7746633) baseStart_7746633 baseEnd_7746633 := by
    simpa [prefixWord, tailWord_7746633, baseEnd_7746633] using wordTrace_append hprefix tailTrace_7746633
  have hstable : (prefixWord ++ tailWord_7746633).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7746633).length < 2 ^ (prefixWord ++ tailWord_7746633).sum := by decide
  have hdescent : baseEnd_7746633 < baseStart_7746633 := by decide
  rcases family_descends (prefixWord ++ tailWord_7746633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7746643 : List Nat := [1, 1, 1, 2, 1, 1, 2, 4, 4, 2, 4]
def baseStart_7746643 : Nat := 118140960795 + 7746643 * 2 ^ 59
def prefixEnd_7746643 : Nat := 4983230072969 + 3 ^ 40 * 7746643 * 2
def baseEnd_7746643 : Nat := 3977751317787639957336343

theorem tailTrace_7746643 : CollatzResearch.WordTrace tailWord_7746643 prefixEnd_7746643 3977751317787639957336343 := by
  unfold tailWord_7746643
  simp only [CollatzResearch.WordTrace]
  refine ⟨282543282074242907138404583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188362188049495271425603055 282543282074242907138404583)
  ·
    refine ⟨423814923111364360707606875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 282543282074242907138404583 423814923111364360707606875)
    ·
      refine ⟨635722384667046541061410313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 423814923111364360707606875 635722384667046541061410313)
      ·
        refine ⟨476791788500284905796057735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 635722384667046541061410313 476791788500284905796057735)
        ·
          refine ⟨715187682750427358694086603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 476791788500284905796057735 715187682750427358694086603)
          ·
            refine ⟨1072781524125641038041129905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 715187682750427358694086603 1072781524125641038041129905)
            ·
              refine ⟨804586143094230778530847429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1072781524125641038041129905 804586143094230778530847429)
              ·
                refine ⟨150859901830168270974533893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 804586143094230778530847429 150859901830168270974533893)
                ·
                  refine ⟨28286231593156550807725105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 150859901830168270974533893 28286231593156550807725105)
                  ·
                    refine ⟨21214673694867413105793829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 28286231593156550807725105 21214673694867413105793829)
                    ·
                      refine ⟨3977751317787639957336343, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21214673694867413105793829 3977751317787639957336343)
                      ·
                        rfl

theorem cell23_7746643_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 4, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 4, 4, 2, 4].length) (baseStart_7746643 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7746643 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7746643 prefixEnd_7746643 := by exact prefixLift 7746643
  have htrace : WordTrace (prefixWord ++ tailWord_7746643) baseStart_7746643 baseEnd_7746643 := by
    simpa [prefixWord, tailWord_7746643, baseEnd_7746643] using wordTrace_append hprefix tailTrace_7746643
  have hstable : (prefixWord ++ tailWord_7746643).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7746643).length < 2 ^ (prefixWord ++ tailWord_7746643).sum := by decide
  have hdescent : baseEnd_7746643 < baseStart_7746643 := by decide
  rcases family_descends (prefixWord ++ tailWord_7746643) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7746647 : List Nat := [1, 1, 3, 2, 2, 1, 1, 4, 4, 2, 2]
def baseStart_7746647 : Nat := 118140960795 + 7746647 * 2 ^ 59
def prefixEnd_7746647 : Nat := 4983230072969 + 3 ^ 40 * 7746647 * 2
def baseEnd_7746647 : Nat := 3977753371710257941686325

theorem tailTrace_7746647 : CollatzResearch.WordTrace tailWord_7746647 prefixEnd_7746647 3977753371710257941686325 := by
  unfold tailWord_7746647
  simp only [CollatzResearch.WordTrace]
  refine ⟨282543427966228415821550195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188362285310818943881033463 282543427966228415821550195)
  ·
    refine ⟨423815141949342623732325293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 282543427966228415821550195 423815141949342623732325293)
    ·
      refine ⟨158930678231003483899621985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 423815141949342623732325293 158930678231003483899621985)
      ·
        refine ⟨119198008673252612924716489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 158930678231003483899621985 119198008673252612924716489)
        ·
          refine ⟨89398506504939459693537367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 119198008673252612924716489 89398506504939459693537367)
          ·
            refine ⟨134097759757409189540306051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89398506504939459693537367 134097759757409189540306051)
            ·
              refine ⟨201146639636113784310459077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 134097759757409189540306051 201146639636113784310459077)
              ·
                refine ⟨37714994931771334558211077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 201146639636113784310459077 37714994931771334558211077)
                ·
                  refine ⟨7071561549707125229664577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 37714994931771334558211077 7071561549707125229664577)
                  ·
                    refine ⟨5303671162280343922248433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7071561549707125229664577 5303671162280343922248433)
                    ·
                      refine ⟨3977753371710257941686325, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5303671162280343922248433 3977753371710257941686325)
                      ·
                        rfl

theorem cell23_7746647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 1, 4, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 1, 4, 4, 2, 2].length) (baseStart_7746647 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7746647 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7746647 prefixEnd_7746647 := by exact prefixLift 7746647
  have htrace : WordTrace (prefixWord ++ tailWord_7746647) baseStart_7746647 baseEnd_7746647 := by
    simpa [prefixWord, tailWord_7746647, baseEnd_7746647] using wordTrace_append hprefix tailTrace_7746647
  have hstable : (prefixWord ++ tailWord_7746647).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7746647).length < 2 ^ (prefixWord ++ tailWord_7746647).sum := by decide
  have hdescent : baseEnd_7746647 < baseStart_7746647 := by decide
  rcases family_descends (prefixWord ++ tailWord_7746647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7746670 : List Nat := [4, 1, 2, 2, 1, 2, 1, 3, 7]
def baseStart_7746670 : Nat := 118140960795 + 7746670 * 2 ^ 59
def prefixEnd_7746670 : Nat := 4983230072969 + 3 ^ 40 * 7746670 * 2
def baseEnd_7746670 : Nat := 441973909085034594633191

theorem tailTrace_7746670 : CollatzResearch.WordTrace tailWord_7746670 prefixEnd_7746670 441973909085034594633191 := by
  unfold tailWord_7746670
  simp only [CollatzResearch.WordTrace]
  refine ⟨35318033355643136343704683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 188362844563430060499758309 35318033355643136343704683)
  ·
    refine ⟨52977050033464704515557025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35318033355643136343704683 52977050033464704515557025)
    ·
      refine ⟨39732787525098528386667769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52977050033464704515557025 39732787525098528386667769)
      ·
        refine ⟨29799590643823896290000827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39732787525098528386667769 29799590643823896290000827)
        ·
          refine ⟨44699385965735844435001241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29799590643823896290000827 44699385965735844435001241)
          ·
            refine ⟨33524539474301883326250931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44699385965735844435001241 33524539474301883326250931)
            ·
              refine ⟨50286809211452824989376397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33524539474301883326250931 50286809211452824989376397)
              ·
                refine ⟨18857553454294809371016149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 50286809211452824989376397 18857553454294809371016149)
                ·
                  refine ⟨441973909085034594633191, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18857553454294809371016149 441973909085034594633191)
                  ·
                    rfl

theorem cell23_7746670_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 2, 1, 3, 7].length) (baseStart_7746670 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7746670 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7746670 prefixEnd_7746670 := by exact prefixLift 7746670
  have htrace : WordTrace (prefixWord ++ tailWord_7746670) baseStart_7746670 baseEnd_7746670 := by
    simpa [prefixWord, tailWord_7746670, baseEnd_7746670] using wordTrace_append hprefix tailTrace_7746670
  have hstable : (prefixWord ++ tailWord_7746670).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7746670).length < 2 ^ (prefixWord ++ tailWord_7746670).sum := by decide
  have hdescent : baseEnd_7746670 < baseStart_7746670 := by decide
  rcases family_descends (prefixWord ++ tailWord_7746670) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7746680 : List Nat := [2, 1, 2, 1, 1, 1, 6, 1, 2, 3, 3]
def baseStart_7746680 : Nat := 118140960795 + 7746680 * 2 ^ 59
def prefixEnd_7746680 : Nat := 4983230072969 + 3 ^ 40 * 7746680 * 2
def baseEnd_7746680 : Nat := 3977770316571856312573673

theorem tailTrace_7746680 : CollatzResearch.WordTrace tailWord_7746680 prefixEnd_7746680 3977770316571856312573673 := by
  unfold tailWord_7746680
  simp only [CollatzResearch.WordTrace]
  refine ⟨141272315787554431228750747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 188363087716739241638334329 141272315787554431228750747)
  ·
    refine ⟨211908473681331646843126121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141272315787554431228750747 211908473681331646843126121)
    ·
      refine ⟨158931355260998735132344591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 211908473681331646843126121 158931355260998735132344591)
      ·
        refine ⟨238397032891498102698516887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 158931355260998735132344591 238397032891498102698516887)
        ·
          refine ⟨357595549337247154047775331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 238397032891498102698516887 357595549337247154047775331)
          ·
            refine ⟨536393324005870731071662997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 357595549337247154047775331 536393324005870731071662997)
            ·
              refine ⟨25143437062775190518984203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 536393324005870731071662997 25143437062775190518984203)
              ·
                refine ⟨37715155594162785778476305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25143437062775190518984203 37715155594162785778476305)
                ·
                  refine ⟨28286366695622089333857229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37715155594162785778476305 28286366695622089333857229)
                  ·
                    refine ⟨10607387510858283500196461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 28286366695622089333857229 10607387510858283500196461)
                    ·
                      refine ⟨3977770316571856312573673, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10607387510858283500196461 3977770316571856312573673)
                      ·
                        rfl

theorem cell23_7746680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 6, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 6, 1, 2, 3, 3].length) (baseStart_7746680 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7746680 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7746680 prefixEnd_7746680 := by exact prefixLift 7746680
  have htrace : WordTrace (prefixWord ++ tailWord_7746680) baseStart_7746680 baseEnd_7746680 := by
    simpa [prefixWord, tailWord_7746680, baseEnd_7746680] using wordTrace_append hprefix tailTrace_7746680
  have hstable : (prefixWord ++ tailWord_7746680).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7746680).length < 2 ^ (prefixWord ++ tailWord_7746680).sum := by decide
  have hdescent : baseEnd_7746680 < baseStart_7746680 := by decide
  rcases family_descends (prefixWord ++ tailWord_7746680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7746681 : List Nat := [1, 2, 1, 3, 6, 1, 1, 1, 1, 4, 2]
def baseStart_7746681 : Nat := 118140960795 + 7746681 * 2 ^ 59
def prefixEnd_7746681 : Nat := 4983230072969 + 3 ^ 40 * 7746681 * 2
def baseEnd_7746681 : Nat := 3977770830052510808661169

theorem tailTrace_7746681 : CollatzResearch.WordTrace tailWord_7746681 prefixEnd_7746681 3977770830052510808661169 := by
  unfold tailWord_7746681
  simp only [CollatzResearch.WordTrace]
  refine ⟨282544668048105239628287897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188363112032070159752191931 282544668048105239628287897)
  ·
    refine ⟨211908501036078929721215923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 282544668048105239628287897 211908501036078929721215923)
    ·
      refine ⟨317862751554118394581823885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 211908501036078929721215923 317862751554118394581823885)
      ·
        refine ⟨119198531832794397968183957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 317862751554118394581823885 119198531832794397968183957)
        ·
          refine ⟨5587431179662237404758623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 119198531832794397968183957 5587431179662237404758623)
          ·
            refine ⟨8381146769493356107137935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5587431179662237404758623 8381146769493356107137935)
            ·
              refine ⟨12571720154240034160706903, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8381146769493356107137935 12571720154240034160706903)
              ·
                refine ⟨18857580231360051241060355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12571720154240034160706903 18857580231360051241060355)
                ·
                  refine ⟨28286370347040076861590533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18857580231360051241060355 28286370347040076861590533)
                  ·
                    refine ⟨5303694440070014411548225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28286370347040076861590533 5303694440070014411548225)
                    ·
                      refine ⟨3977770830052510808661169, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5303694440070014411548225 3977770830052510808661169)
                      ·
                        rfl

theorem cell23_7746681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 6, 1, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 6, 1, 1, 1, 1, 4, 2].length) (baseStart_7746681 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7746681 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7746681 prefixEnd_7746681 := by exact prefixLift 7746681
  have htrace : WordTrace (prefixWord ++ tailWord_7746681) baseStart_7746681 baseEnd_7746681 := by
    simpa [prefixWord, tailWord_7746681, baseEnd_7746681] using wordTrace_append hprefix tailTrace_7746681
  have hstable : (prefixWord ++ tailWord_7746681).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7746681).length < 2 ^ (prefixWord ++ tailWord_7746681).sum := by decide
  have hdescent : baseEnd_7746681 < baseStart_7746681 := by decide
  rcases family_descends (prefixWord ++ tailWord_7746681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7746727 : List Nat := [1, 1, 6, 2, 1, 2, 1, 1, 1, 2, 5]
def baseStart_7746727 : Nat := 118140960795 + 7746727 * 2 ^ 59
def prefixEnd_7746727 : Nat := 4983230072969 + 3 ^ 40 * 7746727 * 2
def baseEnd_7746727 : Nat := 3977794450162617628685957

theorem tailTrace_7746727 : CollatzResearch.WordTrace tailWord_7746727 prefixEnd_7746727 3977794450162617628685957 := by
  unfold tailWord_7746727
  simp only [CollatzResearch.WordTrace]
  refine ⟨282546345805938589484462435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188364230537292392989641623 282546345805938589484462435)
  ·
    refine ⟨423819518708907884226693653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 282546345805938589484462435 423819518708907884226693653)
    ·
      refine ⟨19866539939480057073126265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 423819518708907884226693653 19866539939480057073126265)
      ·
        refine ⟨14899904954610042804844699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19866539939480057073126265 14899904954610042804844699)
        ·
          refine ⟨22349857431915064207267049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14899904954610042804844699 22349857431915064207267049)
          ·
            refine ⟨16762393073936298155450287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22349857431915064207267049 16762393073936298155450287)
            ·
              refine ⟨25143589610904447233175431, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16762393073936298155450287 25143589610904447233175431)
              ·
                refine ⟨37715384416356670849763147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25143589610904447233175431 37715384416356670849763147)
                ·
                  refine ⟨56573076624535006274644721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37715384416356670849763147 56573076624535006274644721)
                  ·
                    refine ⟨42429807468401254705983541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 56573076624535006274644721 42429807468401254705983541)
                    ·
                      refine ⟨3977794450162617628685957, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 42429807468401254705983541 3977794450162617628685957)
                      ·
                        rfl

theorem cell23_7746727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 2, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 2, 1, 1, 1, 2, 5].length) (baseStart_7746727 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7746727 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7746727 prefixEnd_7746727 := by exact prefixLift 7746727
  have htrace : WordTrace (prefixWord ++ tailWord_7746727) baseStart_7746727 baseEnd_7746727 := by
    simpa [prefixWord, tailWord_7746727, baseEnd_7746727] using wordTrace_append hprefix tailTrace_7746727
  have hstable : (prefixWord ++ tailWord_7746727).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7746727).length < 2 ^ (prefixWord ++ tailWord_7746727).sum := by decide
  have hdescent : baseEnd_7746727 < baseStart_7746727 := by decide
  rcases family_descends (prefixWord ++ tailWord_7746727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7746821 : List Nat := [1, 3, 1, 1, 2, 1, 6, 3, 1, 1, 3]
def baseStart_7746821 : Nat := 118140960795 + 7746821 * 2 ^ 59
def prefixEnd_7746821 : Nat := 4983230072969 + 3 ^ 40 * 7746821 * 2
def baseEnd_7746821 : Nat := 3977842717344140260910525

theorem tailTrace_7746821 : CollatzResearch.WordTrace tailWord_7746821 prefixEnd_7746821 3977842717344140260910525 := by
  unfold tailWord_7746821
  simp only [CollatzResearch.WordTrace]
  refine ⟨282549774267598043538384317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188366516178398695692256211 282549774267598043538384317)
  ·
    refine ⟨105956165350349266326894119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 282549774267598043538384317 105956165350349266326894119)
    ·
      refine ⟨158934248025523899490341179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105956165350349266326894119 158934248025523899490341179)
      ·
        refine ⟨238401372038285849235511769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 158934248025523899490341179 238401372038285849235511769)
        ·
          refine ⟨178801029028714386926633827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 238401372038285849235511769 178801029028714386926633827)
          ·
            refine ⟨268201543543071580389950741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 178801029028714386926633827 268201543543071580389950741)
            ·
              refine ⟨12571947353581480330778941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 268201543543071580389950741 12571947353581480330778941)
              ·
                refine ⟨4714480257593055124042103, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12571947353581480330778941 4714480257593055124042103)
                ·
                  refine ⟨7071720386389582686063155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4714480257593055124042103 7071720386389582686063155)
                  ·
                    refine ⟨10607580579584374029094733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7071720386389582686063155 10607580579584374029094733)
                    ·
                      refine ⟨3977842717344140260910525, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10607580579584374029094733 3977842717344140260910525)
                      ·
                        rfl

theorem cell23_7746821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 6, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 6, 3, 1, 1, 3].length) (baseStart_7746821 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7746821 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7746821 prefixEnd_7746821 := by exact prefixLift 7746821
  have htrace : WordTrace (prefixWord ++ tailWord_7746821) baseStart_7746821 baseEnd_7746821 := by
    simpa [prefixWord, tailWord_7746821, baseEnd_7746821] using wordTrace_append hprefix tailTrace_7746821
  have hstable : (prefixWord ++ tailWord_7746821).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7746821).length < 2 ^ (prefixWord ++ tailWord_7746821).sum := by decide
  have hdescent : baseEnd_7746821 < baseStart_7746821 := by decide
  rcases family_descends (prefixWord ++ tailWord_7746821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7746824 : List Nat := [2, 1, 3, 2, 4, 1, 1, 3, 1, 5]
def baseStart_7746824 : Nat := 118140960795 + 7746824 * 2 ^ 59
def prefixEnd_7746824 : Nat := 4983230072969 + 3 ^ 40 * 7746824 * 2
def baseEnd_7746824 : Nat := 1325948085928701249724337

theorem tailTrace_7746824 : CollatzResearch.WordTrace tailWord_7746824 prefixEnd_7746824 1325948085928701249724337 := by
  unfold tailWord_7746824
  simp only [CollatzResearch.WordTrace]
  refine ⟨141274941843293587525371763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 188366589124391450033829017 141274941843293587525371763)
  ·
    refine ⟨211912412764940381288057645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141274941843293587525371763 211912412764940381288057645)
    ·
      refine ⟨79467154786852642983021617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 211912412764940381288057645 79467154786852642983021617)
      ·
        refine ⟨59600366090139482237266213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79467154786852642983021617 59600366090139482237266213)
        ·
          refine ⟨11175068641901152919487415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 59600366090139482237266213 11175068641901152919487415)
          ·
            refine ⟨16762602962851729379231123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11175068641901152919487415 16762602962851729379231123)
            ·
              refine ⟨25143904444277594068846685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16762602962851729379231123 25143904444277594068846685)
              ·
                refine ⟨9428964166604097775817507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25143904444277594068846685 9428964166604097775817507)
                ·
                  refine ⟨14143446249906146663726261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9428964166604097775817507 14143446249906146663726261)
                  ·
                    refine ⟨1325948085928701249724337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14143446249906146663726261 1325948085928701249724337)
                    ·
                      rfl

theorem cell23_7746824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 4, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 4, 1, 1, 3, 1, 5].length) (baseStart_7746824 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7746824 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7746824 prefixEnd_7746824 := by exact prefixLift 7746824
  have htrace : WordTrace (prefixWord ++ tailWord_7746824) baseStart_7746824 baseEnd_7746824 := by
    simpa [prefixWord, tailWord_7746824, baseEnd_7746824] using wordTrace_append hprefix tailTrace_7746824
  have hstable : (prefixWord ++ tailWord_7746824).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7746824).length < 2 ^ (prefixWord ++ tailWord_7746824).sum := by decide
  have hdescent : baseEnd_7746824 < baseStart_7746824 := by decide
  rcases family_descends (prefixWord ++ tailWord_7746824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7746861 : List Nat := [1, 5, 3, 1, 1, 1, 1, 4, 1, 1, 4]
def baseStart_7746861 : Nat := 118140960795 + 7746861 * 2 ^ 59
def prefixEnd_7746861 : Nat := 4983230072969 + 3 ^ 40 * 7746861 * 2
def baseEnd_7746861 : Nat := 3977863256570320104410341

theorem tailTrace_7746861 : CollatzResearch.WordTrace tailWord_7746861 prefixEnd_7746861 3977863256570320104410341 := by
  unfold tailWord_7746861
  simp only [CollatzResearch.WordTrace]
  refine ⟨282551233187453130369840437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188367488791635420246560291 282551233187453130369840437)
  ·
    refine ⟨26489178111323730972172541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 282551233187453130369840437 26489178111323730972172541)
    ·
      refine ⟨9933441791746399114564703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26489178111323730972172541 9933441791746399114564703)
      ·
        refine ⟨14900162687619598671847055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9933441791746399114564703 14900162687619598671847055)
        ·
          refine ⟨22350244031429398007770583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14900162687619598671847055 22350244031429398007770583)
          ·
            refine ⟨33525366047144097011655875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22350244031429398007770583 33525366047144097011655875)
            ·
              refine ⟨50288049070716145517483813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33525366047144097011655875 50288049070716145517483813)
              ·
                refine ⟨9429009200759277284528215, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 50288049070716145517483813 9429009200759277284528215)
                ·
                  refine ⟨14143513801138915926792323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9429009200759277284528215 14143513801138915926792323)
                  ·
                    refine ⟨21215270701708373890188485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14143513801138915926792323 21215270701708373890188485)
                    ·
                      refine ⟨3977863256570320104410341, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21215270701708373890188485 3977863256570320104410341)
                      ·
                        rfl

theorem cell23_7746861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 1, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 1, 1, 4, 1, 1, 4].length) (baseStart_7746861 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7746861 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7746861 prefixEnd_7746861 := by exact prefixLift 7746861
  have htrace : WordTrace (prefixWord ++ tailWord_7746861) baseStart_7746861 baseEnd_7746861 := by
    simpa [prefixWord, tailWord_7746861, baseEnd_7746861] using wordTrace_append hprefix tailTrace_7746861
  have hstable : (prefixWord ++ tailWord_7746861).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7746861).length < 2 ^ (prefixWord ++ tailWord_7746861).sum := by decide
  have hdescent : baseEnd_7746861 < baseStart_7746861 := by decide
  rcases family_descends (prefixWord ++ tailWord_7746861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7746864 : List Nat := [2, 1, 1, 1, 2, 2, 6, 2, 1, 2, 3]
def baseStart_7746864 : Nat := 118140960795 + 7746864 * 2 ^ 59
def prefixEnd_7746864 : Nat := 4983230072969 + 3 ^ 40 * 7746864 * 2
def baseEnd_7746864 : Nat := 3977864797012283592672827

theorem tailTrace_7746864 : CollatzResearch.WordTrace tailWord_7746864 prefixEnd_7746864 3977864797012283592672827 := by
  unfold tailWord_7746864
  simp only [CollatzResearch.WordTrace]
  refine ⟨141275671303221130941099823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 188367561737628174588133097 141275671303221130941099823)
  ·
    refine ⟨211913506954831696411649735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141275671303221130941099823 211913506954831696411649735)
    ·
      refine ⟨317870260432247544617474603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 211913506954831696411649735 317870260432247544617474603)
      ·
        refine ⟨476805390648371316926211905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 317870260432247544617474603 476805390648371316926211905)
        ·
          refine ⟨357604042986278487694658929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 476805390648371316926211905 357604042986278487694658929)
          ·
            refine ⟨268203032239708865770994197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 357604042986278487694658929 268203032239708865770994197)
            ·
              refine ⟨12572017136236353083015353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 268203032239708865770994197 12572017136236353083015353)
              ·
                refine ⟨9429012852177264812261515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12572017136236353083015353 9429012852177264812261515)
                ·
                  refine ⟨14143519278265897218392273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9429012852177264812261515 14143519278265897218392273)
                  ·
                    refine ⟨10607639458699422913794205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14143519278265897218392273 10607639458699422913794205)
                    ·
                      refine ⟨3977864797012283592672827, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10607639458699422913794205 3977864797012283592672827)
                      ·
                        rfl

theorem cell23_7746864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 6, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 6, 2, 1, 2, 3].length) (baseStart_7746864 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7746864 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7746864 prefixEnd_7746864 := by exact prefixLift 7746864
  have htrace : WordTrace (prefixWord ++ tailWord_7746864) baseStart_7746864 baseEnd_7746864 := by
    simpa [prefixWord, tailWord_7746864, baseEnd_7746864] using wordTrace_append hprefix tailTrace_7746864
  have hstable : (prefixWord ++ tailWord_7746864).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7746864).length < 2 ^ (prefixWord ++ tailWord_7746864).sum := by decide
  have hdescent : baseEnd_7746864 < baseStart_7746864 := by decide
  rcases family_descends (prefixWord ++ tailWord_7746864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7746867 : List Nat := [1, 1, 1, 2, 5, 2, 4, 7]
def baseStart_7746867 : Nat := 118140960795 + 7746867 * 2 ^ 59
def prefixEnd_7746867 : Nat := 4983230072969 + 3 ^ 40 * 7746867 * 2
def baseEnd_7746867 : Nat := 147328382868675817812419

theorem tailTrace_7746867 : CollatzResearch.WordTrace tailWord_7746867 prefixEnd_7746867 147328382868675817812419 := by
  unfold tailWord_7746867
  simp only [CollatzResearch.WordTrace]
  refine ⟨282551452025431393394558855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188367634683620928929705903 282551452025431393394558855)
  ·
    refine ⟨423827178038147090091838283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 282551452025431393394558855 423827178038147090091838283)
    ·
      refine ⟨635740767057220635137757425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 423827178038147090091838283 635740767057220635137757425)
      ·
        refine ⟨476805575292915476353318069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 635740767057220635137757425 476805575292915476353318069)
        ·
          refine ⟨44700522683710825908123569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 476805575292915476353318069 44700522683710825908123569)
          ·
            refine ⟨33525392012783119431092677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44700522683710825908123569 33525392012783119431092677)
            ·
              refine ⟨6286011002396834893329877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 33525392012783119431092677 6286011002396834893329877)
              ·
                refine ⟨147328382868675817812419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6286011002396834893329877 147328382868675817812419)
                ·
                  rfl

theorem cell23_7746867_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 2, 4, 7].length) (baseStart_7746867 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7746867 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7746867 prefixEnd_7746867 := by exact prefixLift 7746867
  have htrace : WordTrace (prefixWord ++ tailWord_7746867) baseStart_7746867 baseEnd_7746867 := by
    simpa [prefixWord, tailWord_7746867, baseEnd_7746867] using wordTrace_append hprefix tailTrace_7746867
  have hstable : (prefixWord ++ tailWord_7746867).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7746867).length < 2 ^ (prefixWord ++ tailWord_7746867).sum := by decide
  have hdescent : baseEnd_7746867 < baseStart_7746867 := by decide
  rcases family_descends (prefixWord ++ tailWord_7746867) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7746881 : List Nat := [1, 2, 5, 2, 1, 1, 2, 3, 1, 2, 3]
def baseStart_7746881 : Nat := 118140960795 + 7746881 * 2 ^ 59
def prefixEnd_7746881 : Nat := 4983230072969 + 3 ^ 40 * 7746881 * 2
def baseEnd_7746881 : Nat := 3977873526183410026160249

theorem tailTrace_7746881 : CollatzResearch.WordTrace tailWord_7746881 prefixEnd_7746881 3977873526183410026160249 := by
  unfold tailWord_7746881
  simp only [CollatzResearch.WordTrace]
  refine ⟨282551962647380673785568497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188367975098253782523712331 282551962647380673785568497)
  ·
    refine ⟨211913971985535505339176373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 282551962647380673785568497 211913971985535505339176373)
    ·
      refine ⟨19866934873643953625547785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 211913971985535505339176373 19866934873643953625547785)
      ·
        refine ⟨14900201155232965219160839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19866934873643953625547785 14900201155232965219160839)
        ·
          refine ⟨22350301732849447828741259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14900201155232965219160839 22350301732849447828741259)
          ·
            refine ⟨33525452599274171743111889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22350301732849447828741259 33525452599274171743111889)
            ·
              refine ⟨25144089449455628807333917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33525452599274171743111889 25144089449455628807333917)
              ·
                refine ⟨9429033543545860802750219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25144089449455628807333917 9429033543545860802750219)
                ·
                  refine ⟨14143550315318791204125329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9429033543545860802750219 14143550315318791204125329)
                  ·
                    refine ⟨10607662736489093403093997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14143550315318791204125329 10607662736489093403093997)
                    ·
                      refine ⟨3977873526183410026160249, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10607662736489093403093997 3977873526183410026160249)
                      ·
                        rfl

theorem cell23_7746881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 1, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 1, 2, 3, 1, 2, 3].length) (baseStart_7746881 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7746881 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7746881 prefixEnd_7746881 := by exact prefixLift 7746881
  have htrace : WordTrace (prefixWord ++ tailWord_7746881) baseStart_7746881 baseEnd_7746881 := by
    simpa [prefixWord, tailWord_7746881, baseEnd_7746881] using wordTrace_append hprefix tailTrace_7746881
  have hstable : (prefixWord ++ tailWord_7746881).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7746881).length < 2 ^ (prefixWord ++ tailWord_7746881).sum := by decide
  have hdescent : baseEnd_7746881 < baseStart_7746881 := by decide
  rcases family_descends (prefixWord ++ tailWord_7746881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7746884 : List Nat := [2, 3, 4, 1, 1, 3, 9]
def baseStart_7746884 : Nat := 118140960795 + 7746884 * 2 ^ 59
def prefixEnd_7746884 : Nat := 4983230072969 + 3 ^ 40 * 7746884 * 2
def baseEnd_7746884 : Nat := 49109568723770043387935

theorem tailTrace_7746884 : CollatzResearch.WordTrace tailWord_7746884 prefixEnd_7746884 49109568723770043387935 := by
  unfold tailWord_7746884
  simp only [CollatzResearch.WordTrace]
  refine ⟨141276036033184902648963853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 188368048044246536865285137 141276036033184902648963853)
  ·
    refine ⟨52978513512444338493361445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 141276036033184902648963853 52978513512444338493361445)
    ·
      refine ⟨9933471283583313467505271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 52978513512444338493361445 9933471283583313467505271)
      ·
        refine ⟨14900206925374970201257907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9933471283583313467505271 14900206925374970201257907)
        ·
          refine ⟨22350310388062455301886861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14900206925374970201257907 22350310388062455301886861)
          ·
            refine ⟨8381366395523420738207573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22350310388062455301886861 8381366395523420738207573)
            ·
              refine ⟨49109568723770043387935, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 8381366395523420738207573 49109568723770043387935)
              ·
                rfl

theorem cell23_7746884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 3, 9].length) (baseStart_7746884 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7746884 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7746884 prefixEnd_7746884 := by exact prefixLift 7746884
  have htrace : WordTrace (prefixWord ++ tailWord_7746884) baseStart_7746884 baseEnd_7746884 := by
    simpa [prefixWord, tailWord_7746884, baseEnd_7746884] using wordTrace_append hprefix tailTrace_7746884
  have hstable : (prefixWord ++ tailWord_7746884).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7746884).length < 2 ^ (prefixWord ++ tailWord_7746884).sum := by decide
  have hdescent : baseEnd_7746884 < baseStart_7746884 := by decide
  rcases family_descends (prefixWord ++ tailWord_7746884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7746894 : List Nat := [4, 1, 1, 1, 1, 1, 3, 3, 4, 1, 3]
def baseStart_7746894 : Nat := 118140960795 + 7746894 * 2 ^ 59
def prefixEnd_7746894 : Nat := 4983230072969 + 3 ^ 40 * 7746894 * 2
def baseEnd_7746894 : Nat := 3977880201431918475297689

theorem tailTrace_7746894 : CollatzResearch.WordTrace tailWord_7746894 prefixEnd_7746894 3977880201431918475297689 := by
  unfold tailWord_7746894
  simp only [CollatzResearch.WordTrace]
  refine ⟨35319054599541697125723967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 188368291197555718003861157 35319054599541697125723967)
  ·
    refine ⟨52978581899312545688585951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35319054599541697125723967 52978581899312545688585951)
    ·
      refine ⟨79467872848968818532878927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52978581899312545688585951 79467872848968818532878927)
      ·
        refine ⟨119201809273453227799318391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79467872848968818532878927 119201809273453227799318391)
        ·
          refine ⟨178802713910179841698977587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 119201809273453227799318391 178802713910179841698977587)
          ·
            refine ⟨268204070865269762548466381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 178802713910179841698977587 268204070865269762548466381)
            ·
              refine ⟨100576526574476160955674893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 268204070865269762548466381 100576526574476160955674893)
              ·
                refine ⟨37716197465428560358378085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 100576526574476160955674893 37716197465428560358378085)
                ·
                  refine ⟨7071787024767855067195891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 37716197465428560358378085 7071787024767855067195891)
                  ·
                    refine ⟨10607680537151782600793837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7071787024767855067195891 10607680537151782600793837)
                    ·
                      refine ⟨3977880201431918475297689, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10607680537151782600793837 3977880201431918475297689)
                      ·
                        rfl

theorem cell23_7746894_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 3, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 3, 3, 4, 1, 3].length) (baseStart_7746894 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7746894 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7746894 prefixEnd_7746894 := by exact prefixLift 7746894
  have htrace : WordTrace (prefixWord ++ tailWord_7746894) baseStart_7746894 baseEnd_7746894 := by
    simpa [prefixWord, tailWord_7746894, baseEnd_7746894] using wordTrace_append hprefix tailTrace_7746894
  have hstable : (prefixWord ++ tailWord_7746894).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7746894).length < 2 ^ (prefixWord ++ tailWord_7746894).sum := by decide
  have hdescent : baseEnd_7746894 < baseStart_7746894 := by decide
  rcases family_descends (prefixWord ++ tailWord_7746894) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7746904 : List Nat := [2, 1, 2, 2, 1, 1, 4, 2, 3, 3, 2]
def baseStart_7746904 : Nat := 118140960795 + 7746904 * 2 ^ 59
def prefixEnd_7746904 : Nat := 4983230072969 + 3 ^ 40 * 7746904 * 2
def baseEnd_7746904 : Nat := 3977885336238463436172643

theorem tailTrace_7746904 : CollatzResearch.WordTrace tailWord_7746904 prefixEnd_7746904 3977885336238463436172643 := by
  unfold tailWord_7746904
  simp only [CollatzResearch.WordTrace]
  refine ⟨141276400763148674356827883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 188368534350864899142437177 141276400763148674356827883)
  ·
    refine ⟨211914601144723011535241825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141276400763148674356827883 211914601144723011535241825)
    ·
      refine ⟨158935950858542258651431369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 211914601144723011535241825 158935950858542258651431369)
      ·
        refine ⟨119201963143906693988573527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 158935950858542258651431369 119201963143906693988573527)
        ·
          refine ⟨178802944715860040982860291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 119201963143906693988573527 178802944715860040982860291)
          ·
            refine ⟨268204417073790061474290437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 178802944715860040982860291 268204417073790061474290437)
            ·
              refine ⟨50288328201335636526429457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 268204417073790061474290437 50288328201335636526429457)
              ·
                refine ⟨37716246151001727394822093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50288328201335636526429457 37716246151001727394822093)
                ·
                  refine ⟨14143592306625647773058285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 37716246151001727394822093 14143592306625647773058285)
                  ·
                    refine ⟨5303847114984617914896857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14143592306625647773058285 5303847114984617914896857)
                    ·
                      refine ⟨3977885336238463436172643, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5303847114984617914896857 3977885336238463436172643)
                      ·
                        rfl

theorem cell23_7746904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 4, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 4, 2, 3, 3, 2].length) (baseStart_7746904 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7746904 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7746904 prefixEnd_7746904 := by exact prefixLift 7746904
  have htrace : WordTrace (prefixWord ++ tailWord_7746904) baseStart_7746904 baseEnd_7746904 := by
    simpa [prefixWord, tailWord_7746904, baseEnd_7746904] using wordTrace_append hprefix tailTrace_7746904
  have hstable : (prefixWord ++ tailWord_7746904).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7746904).length < 2 ^ (prefixWord ++ tailWord_7746904).sum := by decide
  have hdescent : baseEnd_7746904 < baseStart_7746904 := by decide
  rcases family_descends (prefixWord ++ tailWord_7746904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7746937 : List Nat := [1, 2, 1, 3, 2, 1, 4, 1, 2, 1, 5]
def baseStart_7746937 : Nat := 118140960795 + 7746937 * 2 ^ 59
def prefixEnd_7746937 : Nat := 4983230072969 + 3 ^ 40 * 7746937 * 2
def baseEnd_7746937 : Nat := 3977902281100061807059991

theorem tailTrace_7746937 : CollatzResearch.WordTrace tailWord_7746937 prefixEnd_7746937 3977902281100061807059991 := by
  unfold tailWord_7746937
  simp only [CollatzResearch.WordTrace]
  refine ⟨282554005135177795349607065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188369336756785196899738043 282554005135177795349607065)
  ·
    refine ⟨211915503851383346512205299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 282554005135177795349607065 211915503851383346512205299)
    ·
      refine ⟨317873255777075019768307949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 211915503851383346512205299 317873255777075019768307949)
      ·
        refine ⟨119202470916403132413115481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 317873255777075019768307949 119202470916403132413115481)
        ·
          refine ⟨89401853187302349309836611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 119202470916403132413115481 89401853187302349309836611)
          ·
            refine ⟨134102779780953523964754917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89401853187302349309836611 134102779780953523964754917)
            ·
              refine ⟨25144271208928785743391547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 134102779780953523964754917 25144271208928785743391547)
              ·
                refine ⟨37716406813393178615087321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25144271208928785743391547 37716406813393178615087321)
                ·
                  refine ⟨28287305110044883961315491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37716406813393178615087321 28287305110044883961315491)
                  ·
                    refine ⟨42430957665067325941973237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 28287305110044883961315491 42430957665067325941973237)
                    ·
                      refine ⟨3977902281100061807059991, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 42430957665067325941973237 3977902281100061807059991)
                      ·
                        rfl

theorem cell23_7746937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 4, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 4, 1, 2, 1, 5].length) (baseStart_7746937 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7746937 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7746937 prefixEnd_7746937 := by exact prefixLift 7746937
  have htrace : WordTrace (prefixWord ++ tailWord_7746937) baseStart_7746937 baseEnd_7746937 := by
    simpa [prefixWord, tailWord_7746937, baseEnd_7746937] using wordTrace_append hprefix tailTrace_7746937
  have hstable : (prefixWord ++ tailWord_7746937).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7746937).length < 2 ^ (prefixWord ++ tailWord_7746937).sum := by decide
  have hdescent : baseEnd_7746937 < baseStart_7746937 := by decide
  rcases family_descends (prefixWord ++ tailWord_7746937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7746964 : List Nat := [2, 4, 2, 1, 2, 1, 1, 1, 1, 4, 4]
def baseStart_7746964 : Nat := 118140960795 + 7746964 * 2 ^ 59
def prefixEnd_7746964 : Nat := 4983230072969 + 3 ^ 40 * 7746964 * 2
def baseEnd_7746964 : Nat := 3977916145077733201422367

theorem tailTrace_7746964 : CollatzResearch.WordTrace tailWord_7746964 prefixEnd_7746964 3977916145077733201422367 := by
  unfold tailWord_7746964
  simp only [CollatzResearch.WordTrace]
  refine ⟨141277494953039989480419973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 188369993270719985973893297 141277494953039989480419973)
  ·
    refine ⟨26489530303694998027578745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 141277494953039989480419973 26489530303694998027578745)
    ·
      refine ⟨19867147727771248520684059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26489530303694998027578745 19867147727771248520684059)
      ·
        refine ⟨29800721591656872781026089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19867147727771248520684059 29800721591656872781026089)
        ·
          refine ⟨22350541193742654585769567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29800721591656872781026089 22350541193742654585769567)
          ·
            refine ⟨33525811790613981878654351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22350541193742654585769567 33525811790613981878654351)
            ·
              refine ⟨50288717685920972817981527, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33525811790613981878654351 50288717685920972817981527)
              ·
                refine ⟨75433076528881459226972291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50288717685920972817981527 75433076528881459226972291)
                ·
                  refine ⟨113149614793322188840458437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 75433076528881459226972291 113149614793322188840458437)
                  ·
                    refine ⟨21215552773747910407585957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 113149614793322188840458437 21215552773747910407585957)
                    ·
                      refine ⟨3977916145077733201422367, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21215552773747910407585957 3977916145077733201422367)
                      ·
                        rfl

theorem cell23_7746964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 1, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 1, 1, 1, 1, 4, 4].length) (baseStart_7746964 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7746964 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7746964 prefixEnd_7746964 := by exact prefixLift 7746964
  have htrace : WordTrace (prefixWord ++ tailWord_7746964) baseStart_7746964 baseEnd_7746964 := by
    simpa [prefixWord, tailWord_7746964, baseEnd_7746964] using wordTrace_append hprefix tailTrace_7746964
  have hstable : (prefixWord ++ tailWord_7746964).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7746964).length < 2 ^ (prefixWord ++ tailWord_7746964).sum := by decide
  have hdescent : baseEnd_7746964 < baseStart_7746964 := by decide
  rcases family_descends (prefixWord ++ tailWord_7746964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7746968 : List Nat := [2, 1, 2, 5, 2, 1, 2, 1, 1, 4, 2]
def baseStart_7746968 : Nat := 118140960795 + 7746968 * 2 ^ 59
def prefixEnd_7746968 : Nat := 4983230072969 + 3 ^ 40 * 7746968 * 2
def baseEnd_7746968 : Nat := 3977918199000351185772349

theorem tailTrace_7746968 : CollatzResearch.WordTrace tailWord_7746968 prefixEnd_7746968 3977918199000351185772349 := by
  unfold tailWord_7746968
  simp only [CollatzResearch.WordTrace]
  refine ⟨141277567899032743821992779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 188370090532043658429323705 141277567899032743821992779)
  ·
    refine ⟨211916351848549115732989169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141277567899032743821992779 211916351848549115732989169)
    ·
      refine ⟨158937263886411836799741877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 211916351848549115732989169 158937263886411836799741877)
      ·
        refine ⟨14900368489351109699975801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 158937263886411836799741877 14900368489351109699975801)
        ·
          refine ⟨11175276367013332274981851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14900368489351109699975801 11175276367013332274981851)
          ·
            refine ⟨16762914550519998412472777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11175276367013332274981851 16762914550519998412472777)
            ·
              refine ⟨12572185912889998809354583, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16762914550519998412472777 12572185912889998809354583)
              ·
                refine ⟨18858278869334998214031875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12572185912889998809354583 18858278869334998214031875)
                ·
                  refine ⟨28287418304002497321047813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18858278869334998214031875 28287418304002497321047813)
                  ·
                    refine ⟨5303890932000468247696465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28287418304002497321047813 5303890932000468247696465)
                    ·
                      refine ⟨3977918199000351185772349, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5303890932000468247696465 3977918199000351185772349)
                      ·
                        rfl

theorem cell23_7746968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 2, 1, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 2, 1, 2, 1, 1, 4, 2].length) (baseStart_7746968 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7746968 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7746968 prefixEnd_7746968 := by exact prefixLift 7746968
  have htrace : WordTrace (prefixWord ++ tailWord_7746968) baseStart_7746968 baseEnd_7746968 := by
    simpa [prefixWord, tailWord_7746968, baseEnd_7746968] using wordTrace_append hprefix tailTrace_7746968
  have hstable : (prefixWord ++ tailWord_7746968).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7746968).length < 2 ^ (prefixWord ++ tailWord_7746968).sum := by decide
  have hdescent : baseEnd_7746968 < baseStart_7746968 := by decide
  rcases family_descends (prefixWord ++ tailWord_7746968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7746994 : List Nat := [3, 2, 1, 1, 1, 1, 2, 2, 1, 7, 2]
def baseStart_7746994 : Nat := 118140960795 + 7746994 * 2 ^ 59
def prefixEnd_7746994 : Nat := 4983230072969 + 3 ^ 40 * 7746994 * 2
def baseEnd_7746994 : Nat := 3977931549497368084047229

theorem tailTrace_7746994 : CollatzResearch.WordTrace tailWord_7746994 prefixEnd_7746994 3977931549497368084047229 := by
  unfold tailWord_7746994
  simp only [CollatzResearch.WordTrace]
  refine ⟨70639021023992823521108009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 188370722730647529389621357 70639021023992823521108009)
  ·
    refine ⟨52979265767994617640831007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70639021023992823521108009 52979265767994617640831007)
    ·
      refine ⟨79468898651991926461246511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52979265767994617640831007 79468898651991926461246511)
      ·
        refine ⟨119203347977987889691869767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79468898651991926461246511 119203347977987889691869767)
        ·
          refine ⟨178805021966981834537804651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 119203347977987889691869767 178805021966981834537804651)
          ·
            refine ⟨268207532950472751806706977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 178805021966981834537804651 268207532950472751806706977)
            ·
              refine ⟨201155649712854563855030233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 268207532950472751806706977 201155649712854563855030233)
              ·
                refine ⟨150866737284640922891272675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 201155649712854563855030233 150866737284640922891272675)
                ·
                  refine ⟨226300105926961384336909013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 150866737284640922891272675 226300105926961384336909013)
                  ·
                    refine ⟨5303908732663157445396305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 226300105926961384336909013 5303908732663157445396305)
                    ·
                      refine ⟨3977931549497368084047229, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5303908732663157445396305 3977931549497368084047229)
                      ·
                        rfl

theorem cell23_7746994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 2, 2, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 2, 2, 1, 7, 2].length) (baseStart_7746994 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7746994 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7746994 prefixEnd_7746994 := by exact prefixLift 7746994
  have htrace : WordTrace (prefixWord ++ tailWord_7746994) baseStart_7746994 baseEnd_7746994 := by
    simpa [prefixWord, tailWord_7746994, baseEnd_7746994] using wordTrace_append hprefix tailTrace_7746994
  have hstable : (prefixWord ++ tailWord_7746994).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7746994).length < 2 ^ (prefixWord ++ tailWord_7746994).sum := by decide
  have hdescent : baseEnd_7746994 < baseStart_7746994 := by decide
  rcases family_descends (prefixWord ++ tailWord_7746994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7747044 : List Nat := [2, 3, 1, 1, 1, 1, 1, 2, 6, 2, 3]
def baseStart_7747044 : Nat := 118140960795 + 7747044 * 2 ^ 59
def prefixEnd_7747044 : Nat := 4983230072969 + 3 ^ 40 * 7747044 * 2
def baseEnd_7747044 : Nat := 3977957223530092888421999

theorem tailTrace_7747044 : CollatzResearch.WordTrace tailWord_7747044 prefixEnd_7747044 3977957223530092888421999 := by
  unfold tailWord_7747044
  simp only [CollatzResearch.WordTrace]
  refine ⟨141278953872895076311876093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 188371938497193435082501457 141278953872895076311876093)
  ·
    refine ⟨52979607702335653616953535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 141278953872895076311876093 52979607702335653616953535)
    ·
      refine ⟨79469411553503480425430303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52979607702335653616953535 79469411553503480425430303)
      ·
        refine ⟨119204117330255220638145455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79469411553503480425430303 119204117330255220638145455)
        ·
          refine ⟨178806175995382830957218183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 119204117330255220638145455 178806175995382830957218183)
          ·
            refine ⟨268209263993074246435827275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 178806175995382830957218183 268209263993074246435827275)
            ·
              refine ⟨402313895989611369653740913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 268209263993074246435827275 402313895989611369653740913)
              ·
                refine ⟨301735421992208527240305685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 402313895989611369653740913 301735421992208527240305685)
                ·
                  refine ⟨14143847905884774714389329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 301735421992208527240305685 14143847905884774714389329)
                  ·
                    refine ⟨10607885929413581035791997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14143847905884774714389329 10607885929413581035791997)
                    ·
                      refine ⟨3977957223530092888421999, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10607885929413581035791997 3977957223530092888421999)
                      ·
                        rfl

theorem cell23_7747044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 1, 2, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 1, 2, 6, 2, 3].length) (baseStart_7747044 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7747044 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7747044 prefixEnd_7747044 := by exact prefixLift 7747044
  have htrace : WordTrace (prefixWord ++ tailWord_7747044) baseStart_7747044 baseEnd_7747044 := by
    simpa [prefixWord, tailWord_7747044, baseEnd_7747044] using wordTrace_append hprefix tailTrace_7747044
  have hstable : (prefixWord ++ tailWord_7747044).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7747044).length < 2 ^ (prefixWord ++ tailWord_7747044).sum := by decide
  have hdescent : baseEnd_7747044 < baseStart_7747044 := by decide
  rcases family_descends (prefixWord ++ tailWord_7747044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7747051 : List Nat := [1, 1, 1, 1, 2, 3, 2, 7, 1, 4]
def baseStart_7747051 : Nat := 118140960795 + 7747051 * 2 ^ 59
def prefixEnd_7747051 : Nat := 4983230072969 + 3 ^ 40 * 7747051 * 2
def baseEnd_7747051 : Nat := 1325986939298224787011489

theorem tailTrace_7747051 : CollatzResearch.WordTrace tailWord_7747051 prefixEnd_7747051 1325986939298224787011489 := by
  unfold tailWord_7747051
  simp only [CollatzResearch.WordTrace]
  refine ⟨282558163056764792819257007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188372108704509861879504671 282558163056764792819257007)
  ·
    refine ⟨423837244585147189228885511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 282558163056764792819257007 423837244585147189228885511)
    ·
      refine ⟨635755866877720783843328267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 423837244585147189228885511 635755866877720783843328267)
      ·
        refine ⟨953633800316581175764992401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 635755866877720783843328267 953633800316581175764992401)
        ·
          refine ⟨715225350237435881823744301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 953633800316581175764992401 715225350237435881823744301)
          ·
            refine ⟨268209506339038455683904113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 715225350237435881823744301 268209506339038455683904113)
            ·
              refine ⟨201157129754278841762928085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 268209506339038455683904113 201157129754278841762928085)
              ·
                refine ⟨4714620228615910353818627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 201157129754278841762928085 4714620228615910353818627)
                ·
                  refine ⟨7071930342923865530727941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4714620228615910353818627 7071930342923865530727941)
                  ·
                    refine ⟨1325986939298224787011489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7071930342923865530727941 1325986939298224787011489)
                    ·
                      rfl

theorem cell23_7747051_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 2, 7, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 2, 7, 1, 4].length) (baseStart_7747051 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7747051 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7747051 prefixEnd_7747051 := by exact prefixLift 7747051
  have htrace : WordTrace (prefixWord ++ tailWord_7747051) baseStart_7747051 baseEnd_7747051 := by
    simpa [prefixWord, tailWord_7747051, baseEnd_7747051] using wordTrace_append hprefix tailTrace_7747051
  have hstable : (prefixWord ++ tailWord_7747051).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7747051).length < 2 ^ (prefixWord ++ tailWord_7747051).sum := by decide
  have hdescent : baseEnd_7747051 < baseStart_7747051 := by decide
  rcases family_descends (prefixWord ++ tailWord_7747051) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7747077 : List Nat := [1, 3, 1, 1, 2, 2, 1, 1, 2, 9]
def baseStart_7747077 : Nat := 118140960795 + 7747077 * 2 ^ 59
def prefixEnd_7747077 : Nat := 4983230072969 + 3 ^ 40 * 7747077 * 2
def baseEnd_7747077 : Nat := 1325991389463897086436449

theorem tailTrace_7747077 : CollatzResearch.WordTrace tailWord_7747077 prefixEnd_7747077 1325991389463897086436449 := by
  unfold tailWord_7747077
  simp only [CollatzResearch.WordTrace]
  refine ⟨282559111354670599259703485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188372740903113732839802323 282559111354670599259703485)
  ·
    refine ⟨105959666758001474722388807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 282559111354670599259703485 105959666758001474722388807)
    ·
      refine ⟨158939500137002212083583211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105959666758001474722388807 158939500137002212083583211)
      ·
        refine ⟨238409250205503318125374817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 158939500137002212083583211 238409250205503318125374817)
        ·
          refine ⟨178806937654127488594031113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 238409250205503318125374817 178806937654127488594031113)
          ·
            refine ⟨134105203240595616445523335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 178806937654127488594031113 134105203240595616445523335)
            ·
              refine ⟨201157804860893424668285003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 134105203240595616445523335 201157804860893424668285003)
              ·
                refine ⟨301736707291340137002427505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 201157804860893424668285003 301736707291340137002427505)
                ·
                  refine ⟨226302530468505102751820629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 301736707291340137002427505 226302530468505102751820629)
                  ·
                    refine ⟨1325991389463897086436449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 226302530468505102751820629 1325991389463897086436449)
                    ·
                      rfl

theorem cell23_7747077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 1, 1, 2, 9].length) (baseStart_7747077 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7747077 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7747077 prefixEnd_7747077 := by exact prefixLift 7747077
  have htrace : WordTrace (prefixWord ++ tailWord_7747077) baseStart_7747077 baseEnd_7747077 := by
    simpa [prefixWord, tailWord_7747077, baseEnd_7747077] using wordTrace_append hprefix tailTrace_7747077
  have hstable : (prefixWord ++ tailWord_7747077).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7747077).length < 2 ^ (prefixWord ++ tailWord_7747077).sum := by decide
  have hdescent : baseEnd_7747077 < baseStart_7747077 := by decide
  rcases family_descends (prefixWord ++ tailWord_7747077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7747087 : List Nat := [1, 1, 2, 1, 1, 1, 2, 2, 1, 6, 5]
def baseStart_7747087 : Nat := 118140960795 + 7747087 * 2 ^ 59
def prefixEnd_7747087 : Nat := 4983230072969 + 3 ^ 40 * 7747087 * 2
def baseEnd_7747087 : Nat := 3977979303198236220184301

theorem tailTrace_7747087 : CollatzResearch.WordTrace tailWord_7747087 prefixEnd_7747087 3977979303198236220184301 := by
  unfold tailWord_7747087
  simp only [CollatzResearch.WordTrace]
  refine ⟨282559476084634370967567515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188372984056422913978378343 282559476084634370967567515)
  ·
    refine ⟨423839214126951556451351273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 282559476084634370967567515 423839214126951556451351273)
    ·
      refine ⟨317879410595213667338513455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 423839214126951556451351273 317879410595213667338513455)
      ·
        refine ⟨476819115892820501007770183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 317879410595213667338513455 476819115892820501007770183)
        ·
          refine ⟨715228673839230751511655275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 476819115892820501007770183 715228673839230751511655275)
          ·
            refine ⟨1072843010758846127267482913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 715228673839230751511655275 1072843010758846127267482913)
            ·
              refine ⟨804632258069134595450612185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1072843010758846127267482913 804632258069134595450612185)
              ·
                refine ⟨603474193551850946587959139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 804632258069134595450612185 603474193551850946587959139)
                ·
                  refine ⟨905211290327776419881938709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 603474193551850946587959139 905211290327776419881938709)
                  ·
                    refine ⟨42431779234114519681965877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 905211290327776419881938709 42431779234114519681965877)
                    ·
                      refine ⟨3977979303198236220184301, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 42431779234114519681965877 3977979303198236220184301)
                      ·
                        rfl

theorem cell23_7747087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 2, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 2, 1, 6, 5].length) (baseStart_7747087 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7747087 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7747087 prefixEnd_7747087 := by exact prefixLift 7747087
  have htrace : WordTrace (prefixWord ++ tailWord_7747087) baseStart_7747087 baseEnd_7747087 := by
    simpa [prefixWord, tailWord_7747087, baseEnd_7747087] using wordTrace_append hprefix tailTrace_7747087
  have hstable : (prefixWord ++ tailWord_7747087).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7747087).length < 2 ^ (prefixWord ++ tailWord_7747087).sum := by decide
  have hdescent : baseEnd_7747087 < baseStart_7747087 := by decide
  rcases family_descends (prefixWord ++ tailWord_7747087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7747125 : List Nat := [1, 3, 3, 1, 1, 4, 1, 4, 1, 1, 3]
def baseStart_7747125 : Nat := 118140960795 + 7747125 * 2 ^ 59
def prefixEnd_7747125 : Nat := 4983230072969 + 3 ^ 40 * 7747125 * 2
def baseEnd_7747125 : Nat := 3977998815463107071509127

theorem tailTrace_7747125 : CollatzResearch.WordTrace tailWord_7747125 prefixEnd_7747125 3977998815463107071509127 := by
  unfold tailWord_7747125
  simp only [CollatzResearch.WordTrace]
  refine ⟨282560862058496703457450829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188373908038997802304967219 282560862058496703457450829)
  ·
    refine ⟨105960323271936263796544061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 282560862058496703457450829 105960323271936263796544061)
    ·
      refine ⟨39735121226976098923704023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 105960323271936263796544061 39735121226976098923704023)
      ·
        refine ⟨59602681840464148385556035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39735121226976098923704023 59602681840464148385556035)
        ·
          refine ⟨89404022760696222578334053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59602681840464148385556035 89404022760696222578334053)
          ·
            refine ⟨16763254267630541733437635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 89404022760696222578334053 16763254267630541733437635)
            ·
              refine ⟨25144881401445812600156453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16763254267630541733437635 25144881401445812600156453)
              ·
                refine ⟨4714665262771089862529335, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25144881401445812600156453 4714665262771089862529335)
                ·
                  refine ⟨7071997894156634793794003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4714665262771089862529335 7071997894156634793794003)
                  ·
                    refine ⟨10607996841234952190691005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7071997894156634793794003 10607996841234952190691005)
                    ·
                      refine ⟨3977998815463107071509127, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10607996841234952190691005 3977998815463107071509127)
                      ·
                        rfl

theorem cell23_7747125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 4, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 4, 1, 4, 1, 1, 3].length) (baseStart_7747125 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7747125 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7747125 prefixEnd_7747125 := by exact prefixLift 7747125
  have htrace : WordTrace (prefixWord ++ tailWord_7747125) baseStart_7747125 baseEnd_7747125 := by
    simpa [prefixWord, tailWord_7747125, baseEnd_7747125] using wordTrace_append hprefix tailTrace_7747125
  have hstable : (prefixWord ++ tailWord_7747125).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7747125).length < 2 ^ (prefixWord ++ tailWord_7747125).sum := by decide
  have hdescent : baseEnd_7747125 < baseStart_7747125 := by decide
  rcases family_descends (prefixWord ++ tailWord_7747125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7747141 : List Nat := [1, 3, 1, 1, 1, 4, 1, 5, 2, 4]
def baseStart_7747141 : Nat := 118140960795 + 7747141 * 2 ^ 59
def prefixEnd_7747141 : Nat := 4983230072969 + 3 ^ 40 * 7747141 * 2
def baseEnd_7747141 : Nat := 1326002343717859669636351

theorem tailTrace_7747141 : CollatzResearch.WordTrace tailWord_7747141 prefixEnd_7747141 1326002343717859669636351 := by
  unfold tailWord_7747141
  simp only [CollatzResearch.WordTrace]
  refine ⟨282561445626438738190033277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188374297084292492126688851 282561445626438738190033277)
  ·
    refine ⟨105960542109914526821262479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 282561445626438738190033277 105960542109914526821262479)
    ·
      refine ⟨158940813164871790231893719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105960542109914526821262479 158940813164871790231893719)
      ·
        refine ⟨238411219747307685347840579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 158940813164871790231893719 238411219747307685347840579)
        ·
          refine ⟨357616829620961528021760869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 238411219747307685347840579 357616829620961528021760869)
          ·
            refine ⟨67053155553930286504080163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 357616829620961528021760869 67053155553930286504080163)
            ·
              refine ⟨100579733330895429756120245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67053155553930286504080163 100579733330895429756120245)
              ·
                refine ⟨9429349999771446539636273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 100579733330895429756120245 9429349999771446539636273)
                ·
                  refine ⟨7072012499828584904727205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9429349999771446539636273 7072012499828584904727205)
                  ·
                    refine ⟨1326002343717859669636351, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7072012499828584904727205 1326002343717859669636351)
                    ·
                      rfl

theorem cell23_7747141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 1, 5, 2, 4].length) (baseStart_7747141 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7747141 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7747141 prefixEnd_7747141 := by exact prefixLift 7747141
  have htrace : WordTrace (prefixWord ++ tailWord_7747141) baseStart_7747141 baseEnd_7747141 := by
    simpa [prefixWord, tailWord_7747141, baseEnd_7747141] using wordTrace_append hprefix tailTrace_7747141
  have hstable : (prefixWord ++ tailWord_7747141).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7747141).length < 2 ^ (prefixWord ++ tailWord_7747141).sum := by decide
  have hdescent : baseEnd_7747141 < baseStart_7747141 := by decide
  rcases family_descends (prefixWord ++ tailWord_7747141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7747142 : List Nat := [6, 1, 1, 1, 3, 1, 1, 2, 3, 1, 3]
def baseStart_7747142 : Nat := 118140960795 + 7747142 * 2 ^ 59
def prefixEnd_7747142 : Nat := 4983230072969 + 3 ^ 40 * 7747142 * 2
def baseEnd_7747142 : Nat := 3978007544634233504996549

theorem tailTrace_7747142 : CollatzResearch.WordTrace tailWord_7747142 prefixEnd_7747142 3978007544634233504996549 := by
  unfold tailWord_7747142
  simp only [CollatzResearch.WordTrace]
  refine ⟨8830046315607347355025615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 188374321399623410240546453 8830046315607347355025615)
  ·
    refine ⟨13245069473411021032538423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8830046315607347355025615 13245069473411021032538423)
    ·
      refine ⟨19867604210116531548807635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13245069473411021032538423 19867604210116531548807635)
      ·
        refine ⟨29801406315174797323211453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19867604210116531548807635 29801406315174797323211453)
        ·
          refine ⟨11175527368190548996204295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29801406315174797323211453 11175527368190548996204295)
          ·
            refine ⟨16763291052285823494306443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11175527368190548996204295 16763291052285823494306443)
            ·
              refine ⟨25144936578428735241459665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16763291052285823494306443 25144936578428735241459665)
              ·
                refine ⟨18858702433821551431094749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25144936578428735241459665 18858702433821551431094749)
                ·
                  refine ⟨7072013412683081786660531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18858702433821551431094749 7072013412683081786660531)
                  ·
                    refine ⟨10608020119024622679990797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7072013412683081786660531 10608020119024622679990797)
                    ·
                      refine ⟨3978007544634233504996549, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10608020119024622679990797 3978007544634233504996549)
                      ·
                        rfl

theorem cell23_7747142_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 3, 1, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 3, 1, 1, 2, 3, 1, 3].length) (baseStart_7747142 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7747142 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7747142 prefixEnd_7747142 := by exact prefixLift 7747142
  have htrace : WordTrace (prefixWord ++ tailWord_7747142) baseStart_7747142 baseEnd_7747142 := by
    simpa [prefixWord, tailWord_7747142, baseEnd_7747142] using wordTrace_append hprefix tailTrace_7747142
  have hstable : (prefixWord ++ tailWord_7747142).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7747142).length < 2 ^ (prefixWord ++ tailWord_7747142).sum := by decide
  have hdescent : baseEnd_7747142 < baseStart_7747142 := by decide
  rcases family_descends (prefixWord ++ tailWord_7747142) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7747148 : List Nat := [2, 2, 1, 3, 1, 3, 1, 1, 5, 2, 2]
def baseStart_7747148 : Nat := 118140960795 + 7747148 * 2 ^ 59
def prefixEnd_7747148 : Nat := 4983230072969 + 3 ^ 40 * 7747148 * 2
def baseEnd_7747148 : Nat := 3978010625518160481521521

theorem tailTrace_7747148 : CollatzResearch.WordTrace tailWord_7747148 prefixEnd_7747148 3978010625518160481521521 := by
  unfold tailWord_7747148
  simp only [CollatzResearch.WordTrace]
  refine ⟨141280850468706689192769049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 188374467291608918923692065 141280850468706689192769049)
  ·
    refine ⟨105960637851530016894576787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 141280850468706689192769049 105960637851530016894576787)
    ·
      refine ⟨158940956777295025341865181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105960637851530016894576787 158940956777295025341865181)
      ·
        refine ⟨59602858791485634503199443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 158940956777295025341865181 59602858791485634503199443)
        ·
          refine ⟨89404288187228451754799165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59602858791485634503199443 89404288187228451754799165)
          ·
            refine ⟨33526608070210669408049687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 89404288187228451754799165 33526608070210669408049687)
            ·
              refine ⟨50289912105316004112074531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33526608070210669408049687 50289912105316004112074531)
              ·
                refine ⟨75434868157974006168111797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50289912105316004112074531 75434868157974006168111797)
                ·
                  refine ⟨7072018889810063078260481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 75434868157974006168111797 7072018889810063078260481)
                  ·
                    refine ⟨5304014167357547308695361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7072018889810063078260481 5304014167357547308695361)
                    ·
                      refine ⟨3978010625518160481521521, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5304014167357547308695361 3978010625518160481521521)
                      ·
                        rfl

theorem cell23_7747148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 3, 1, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 3, 1, 1, 5, 2, 2].length) (baseStart_7747148 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7747148 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7747148 prefixEnd_7747148 := by exact prefixLift 7747148
  have htrace : WordTrace (prefixWord ++ tailWord_7747148) baseStart_7747148 baseEnd_7747148 := by
    simpa [prefixWord, tailWord_7747148, baseEnd_7747148] using wordTrace_append hprefix tailTrace_7747148
  have hstable : (prefixWord ++ tailWord_7747148).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7747148).length < 2 ^ (prefixWord ++ tailWord_7747148).sum := by decide
  have hdescent : baseEnd_7747148 < baseStart_7747148 := by decide
  rcases family_descends (prefixWord ++ tailWord_7747148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7747151 : List Nat := [1, 1, 2, 1, 1, 2, 3, 6, 1, 2, 3]
def baseStart_7747151 : Nat := 118140960795 + 7747151 * 2 ^ 59
def prefixEnd_7747151 : Nat := 4983230072969 + 3 ^ 40 * 7747151 * 2
def baseEnd_7747151 : Nat := 3978012165960123969784007

theorem tailTrace_7747151 : CollatzResearch.WordTrace tailWord_7747151 prefixEnd_7747151 3978012165960123969784007 := by
  unfold tailWord_7747151
  simp only [CollatzResearch.WordTrace]
  refine ⟨282561810356402509897897307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188374540237601673265264871 282561810356402509897897307)
  ·
    refine ⟨423842715534603764846845961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 282561810356402509897897307 423842715534603764846845961)
    ·
      refine ⟨317882036650952823635134471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 423842715534603764846845961 317882036650952823635134471)
      ·
        refine ⟨476823054976429235452701707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 317882036650952823635134471 476823054976429235452701707)
        ·
          refine ⟨715234582464643853179052561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 476823054976429235452701707 715234582464643853179052561)
          ·
            refine ⟨536425936848482889884289421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 715234582464643853179052561 536425936848482889884289421)
            ·
              refine ⟨201159726318181083706608533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 536425936848482889884289421 201159726318181083706608533)
              ·
                refine ⟨9429362171164738298747275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 201159726318181083706608533 9429362171164738298747275)
                ·
                  refine ⟨14144043256747107448120913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9429362171164738298747275 14144043256747107448120913)
                  ·
                    refine ⟨10608032442560330586090685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14144043256747107448120913 10608032442560330586090685)
                    ·
                      refine ⟨3978012165960123969784007, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10608032442560330586090685 3978012165960123969784007)
                      ·
                        rfl

theorem cell23_7747151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 3, 6, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 3, 6, 1, 2, 3].length) (baseStart_7747151 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7747151 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7747151 prefixEnd_7747151 := by exact prefixLift 7747151
  have htrace : WordTrace (prefixWord ++ tailWord_7747151) baseStart_7747151 baseEnd_7747151 := by
    simpa [prefixWord, tailWord_7747151, baseEnd_7747151] using wordTrace_append hprefix tailTrace_7747151
  have hstable : (prefixWord ++ tailWord_7747151).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7747151).length < 2 ^ (prefixWord ++ tailWord_7747151).sum := by decide
  have hdescent : baseEnd_7747151 < baseStart_7747151 := by decide
  rcases family_descends (prefixWord ++ tailWord_7747151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7747182 : List Nat := [4, 1, 2, 2, 3, 1, 2, 1, 3, 2, 2]
def baseStart_7747182 : Nat := 118140960795 + 7747182 * 2 ^ 59
def prefixEnd_7747182 : Nat := 4983230072969 + 3 ^ 40 * 7747182 * 2
def baseEnd_7747182 : Nat := 3978028083860413348496365

theorem tailTrace_7747182 : CollatzResearch.WordTrace tailWord_7747182 prefixEnd_7747182 3978028083860413348496365 := by
  unfold tailWord_7747182
  simp only [CollatzResearch.WordTrace]
  refine ⟨35320367627411275274034475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 188375294012860134794850533 35320367627411275274034475)
  ·
    refine ⟨52980551441116912911051713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35320367627411275274034475 52980551441116912911051713)
    ·
      refine ⟨39735413580837684683288785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52980551441116912911051713 39735413580837684683288785)
      ·
        refine ⟨29801560185628263512466589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39735413580837684683288785 29801560185628263512466589)
        ·
          refine ⟨11175585069610598817174971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29801560185628263512466589 11175585069610598817174971)
          ·
            refine ⟨16763377604415898225762457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11175585069610598817174971 16763377604415898225762457)
            ·
              refine ⟨12572533203311923669321843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16763377604415898225762457 12572533203311923669321843)
              ·
                refine ⟨18858799804967885503982765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12572533203311923669321843 18858799804967885503982765)
                ·
                  refine ⟨7072049926862957063993537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18858799804967885503982765 7072049926862957063993537)
                  ·
                    refine ⟨5304037445147217797995153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7072049926862957063993537 5304037445147217797995153)
                    ·
                      refine ⟨3978028083860413348496365, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5304037445147217797995153 3978028083860413348496365)
                      ·
                        rfl

theorem cell23_7747182_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 3, 1, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 3, 1, 2, 1, 3, 2, 2].length) (baseStart_7747182 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7747182 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7747182 prefixEnd_7747182 := by exact prefixLift 7747182
  have htrace : WordTrace (prefixWord ++ tailWord_7747182) baseStart_7747182 baseEnd_7747182 := by
    simpa [prefixWord, tailWord_7747182, baseEnd_7747182] using wordTrace_append hprefix tailTrace_7747182
  have hstable : (prefixWord ++ tailWord_7747182).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7747182).length < 2 ^ (prefixWord ++ tailWord_7747182).sum := by decide
  have hdescent : baseEnd_7747182 < baseStart_7747182 := by decide
  rcases family_descends (prefixWord ++ tailWord_7747182) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
