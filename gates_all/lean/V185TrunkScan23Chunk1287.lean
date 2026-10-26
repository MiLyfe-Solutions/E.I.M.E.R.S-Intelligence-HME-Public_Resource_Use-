import V185TrunkScan23Chunk1286

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_7622420 : List Nat := [2, 4, 4, 1, 1, 2, 1, 1, 7]
def baseStart_7622420 : Nat := 118140960795 + 7622420 * 2 ^ 59
def prefixEnd_7622420 : Nat := 4983230072969 + 3 ^ 40 * 7622420 * 2
def baseEnd_7622420 : Nat := 434885023382685831155015

theorem tailTrace_7622420 : CollatzResearch.WordTrace tailWord_7622420 prefixEnd_7622420 434885023382685831155015 := by
  unfold tailWord_7622420
  simp only [CollatzResearch.WordTrace]
  refine ⟨139006248522640810269532357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 185341664696854413692709809 139006248522640810269532357)
  ·
    refine ⟨26063671597995151925537317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 139006248522640810269532357 26063671597995151925537317)
    ·
      refine ⟨4886938424624090986038247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 26063671597995151925537317 4886938424624090986038247)
      ·
        refine ⟨7330407636936136479057371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4886938424624090986038247 7330407636936136479057371)
        ·
          refine ⟨10995611455404204718586057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7330407636936136479057371 10995611455404204718586057)
          ·
            refine ⟨8246708591553153538939543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10995611455404204718586057 8246708591553153538939543)
            ·
              refine ⟨12370062887329730308409315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8246708591553153538939543 12370062887329730308409315)
              ·
                refine ⟨18555094330994595462613973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12370062887329730308409315 18555094330994595462613973)
                ·
                  refine ⟨434885023382685831155015, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18555094330994595462613973 434885023382685831155015)
                  ·
                    rfl

theorem cell23_7622420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 1, 2, 1, 1, 7].length) (baseStart_7622420 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7622420 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7622420 prefixEnd_7622420 := by exact prefixLift 7622420
  have htrace : WordTrace (prefixWord ++ tailWord_7622420) baseStart_7622420 baseEnd_7622420 := by
    simpa [prefixWord, tailWord_7622420, baseEnd_7622420] using wordTrace_append hprefix tailTrace_7622420
  have hstable : (prefixWord ++ tailWord_7622420).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7622420).length < 2 ^ (prefixWord ++ tailWord_7622420).sum := by decide
  have hdescent : baseEnd_7622420 < baseStart_7622420 := by decide
  rcases family_descends (prefixWord ++ tailWord_7622420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7622456 : List Nat := [2, 1, 2, 1, 3, 4, 2, 1, 2, 2, 3]
def baseStart_7622456 : Nat := 118140960795 + 7622456 * 2 ^ 59
def prefixEnd_7622456 : Nat := 4983230072969 + 3 ^ 40 * 7622456 * 2
def baseEnd_7622456 : Nat := 3913983695747734339544969

theorem tailTrace_7622456 : CollatzResearch.WordTrace tailWord_7622456 prefixEnd_7622456 3913983695747734339544969 := by
  unfold tailWord_7622456
  simp only [CollatzResearch.WordTrace]
  refine ⟨139006905036575599343687611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 185342540048767465791583481 139006905036575599343687611)
  ·
    refine ⟨208510357554863399015531417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139006905036575599343687611 208510357554863399015531417)
    ·
      refine ⟨156382768166147549261648563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 208510357554863399015531417 156382768166147549261648563)
      ·
        refine ⟨234574152249221323892472845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 156382768166147549261648563 234574152249221323892472845)
        ·
          refine ⟨87965307093457996459677317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 234574152249221323892472845 87965307093457996459677317)
          ·
            refine ⟨16493495080023374336189497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 87965307093457996459677317 16493495080023374336189497)
            ·
              refine ⟨12370121310017530752142123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16493495080023374336189497 12370121310017530752142123)
              ·
                refine ⟨18555181965026296128213185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12370121310017530752142123 18555181965026296128213185)
                ·
                  refine ⟨13916386473769722096159889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18555181965026296128213185 13916386473769722096159889)
                  ·
                    refine ⟨10437289855327291572119917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13916386473769722096159889 10437289855327291572119917)
                    ·
                      refine ⟨3913983695747734339544969, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10437289855327291572119917 3913983695747734339544969)
                      ·
                        rfl

theorem cell23_7622456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 4, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 4, 2, 1, 2, 2, 3].length) (baseStart_7622456 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7622456 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7622456 prefixEnd_7622456 := by exact prefixLift 7622456
  have htrace : WordTrace (prefixWord ++ tailWord_7622456) baseStart_7622456 baseEnd_7622456 := by
    simpa [prefixWord, tailWord_7622456, baseEnd_7622456] using wordTrace_append hprefix tailTrace_7622456
  have hstable : (prefixWord ++ tailWord_7622456).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7622456).length < 2 ^ (prefixWord ++ tailWord_7622456).sum := by decide
  have hdescent : baseEnd_7622456 < baseStart_7622456 := by decide
  rcases family_descends (prefixWord ++ tailWord_7622456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7622476 : List Nat := [2, 2, 1, 3, 4, 1, 2, 2, 6]
def baseStart_7622476 : Nat := 118140960795 + 7622476 * 2 ^ 59
def prefixEnd_7622476 : Nat := 4983230072969 + 3 ^ 40 * 7622476 * 2
def baseEnd_7622476 : Nat := 434888218373424917921653

theorem tailTrace_7622476 : CollatzResearch.WordTrace tailWord_7622476 prefixEnd_7622476 434888218373424917921653 := by
  unfold tailWord_7622476
  simp only [CollatzResearch.WordTrace]
  refine ⟨139007269766539371051551641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 185343026355385828068735521 139007269766539371051551641)
  ·
    refine ⟨104255452324904528288663731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 139007269766539371051551641 104255452324904528288663731)
    ·
      refine ⟨156383178487356792432995597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104255452324904528288663731 156383178487356792432995597)
      ·
        refine ⟨58643691932758797162373349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 156383178487356792432995597 58643691932758797162373349)
        ·
          refine ⟨10995692237392274467945003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 58643691932758797162373349 10995692237392274467945003)
          ·
            refine ⟨16493538356088411701917505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10995692237392274467945003 16493538356088411701917505)
            ·
              refine ⟨12370153767066308776438129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16493538356088411701917505 12370153767066308776438129)
              ·
                refine ⟨9277615325299731582328597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12370153767066308776438129 9277615325299731582328597)
                ·
                  refine ⟨434888218373424917921653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9277615325299731582328597 434888218373424917921653)
                  ·
                    rfl

theorem cell23_7622476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 4, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 4, 1, 2, 2, 6].length) (baseStart_7622476 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7622476 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7622476 prefixEnd_7622476 := by exact prefixLift 7622476
  have htrace : WordTrace (prefixWord ++ tailWord_7622476) baseStart_7622476 baseEnd_7622476 := by
    simpa [prefixWord, tailWord_7622476, baseEnd_7622476] using wordTrace_append hprefix tailTrace_7622476
  have hstable : (prefixWord ++ tailWord_7622476).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7622476).length < 2 ^ (prefixWord ++ tailWord_7622476).sum := by decide
  have hdescent : baseEnd_7622476 < baseStart_7622476 := by decide
  rcases family_descends (prefixWord ++ tailWord_7622476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7622546 : List Nat := [3, 2, 3, 2, 1, 1, 1, 1, 3, 1, 5]
def baseStart_7622546 : Nat := 118140960795 + 7622546 * 2 ^ 59
def prefixEnd_7622546 : Nat := 4983230072969 + 3 ^ 40 * 7622546 * 2
def baseEnd_7622546 : Nat := 3914029909006638987419555

theorem tailTrace_7622546 : CollatzResearch.WordTrace tailWord_7622546 prefixEnd_7622546 3914029909006638987419555 := by
  unfold tailWord_7622546
  simp only [CollatzResearch.WordTrace]
  refine ⟨69504273160706286014537873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 185344728428550096038767661 69504273160706286014537873)
  ·
    refine ⟨52128204870529714510903405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69504273160706286014537873 52128204870529714510903405)
    ·
      refine ⟨19548076826448642941588777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 52128204870529714510903405 19548076826448642941588777)
      ·
        refine ⟨14661057619836482206191583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19548076826448642941588777 14661057619836482206191583)
        ·
          refine ⟨21991586429754723309287375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14661057619836482206191583 21991586429754723309287375)
          ·
            refine ⟨32987379644632084963931063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21991586429754723309287375 32987379644632084963931063)
            ·
              refine ⟨49481069466948127445896595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32987379644632084963931063 49481069466948127445896595)
              ·
                refine ⟨74221604200422191168844893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49481069466948127445896595 74221604200422191168844893)
                ·
                  refine ⟨27833101575158321688316835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 74221604200422191168844893 27833101575158321688316835)
                  ·
                    refine ⟨41749652362737482532475253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27833101575158321688316835 41749652362737482532475253)
                    ·
                      refine ⟨3914029909006638987419555, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41749652362737482532475253 3914029909006638987419555)
                      ·
                        rfl

theorem cell23_7622546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 1, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 1, 1, 1, 3, 1, 5].length) (baseStart_7622546 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7622546 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7622546 prefixEnd_7622546 := by exact prefixLift 7622546
  have htrace : WordTrace (prefixWord ++ tailWord_7622546) baseStart_7622546 baseEnd_7622546 := by
    simpa [prefixWord, tailWord_7622546, baseEnd_7622546] using wordTrace_append hprefix tailTrace_7622546
  have hstable : (prefixWord ++ tailWord_7622546).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7622546).length < 2 ^ (prefixWord ++ tailWord_7622546).sum := by decide
  have hdescent : baseEnd_7622546 < baseStart_7622546 := by decide
  rcases family_descends (prefixWord ++ tailWord_7622546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7622556 : List Nat := [2, 2, 3, 3, 1, 2, 1, 1, 1, 1, 6]
def baseStart_7622556 : Nat := 118140960795 + 7622556 * 2 ^ 59
def prefixEnd_7622556 : Nat := 4983230072969 + 3 ^ 40 * 7622556 * 2
def baseEnd_7622556 : Nat := 3914035043813183948294509

theorem tailTrace_7622556 : CollatzResearch.WordTrace tailWord_7622556 prefixEnd_7622556 3914035043813183948294509 := by
  unfold tailWord_7622556
  simp only [CollatzResearch.WordTrace]
  refine ⟨139008728686394457883007761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 185344971581859277177343681 139008728686394457883007761)
  ·
    refine ⟨104256546514795843412255821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 139008728686394457883007761 104256546514795843412255821)
    ·
      refine ⟨39096204943048441279595933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 104256546514795843412255821 39096204943048441279595933)
      ·
        refine ⟨14661076853643165479848475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39096204943048441279595933 14661076853643165479848475)
        ·
          refine ⟨21991615280464748219772713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14661076853643165479848475 21991615280464748219772713)
          ·
            refine ⟨16493711460348561164829535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21991615280464748219772713 16493711460348561164829535)
            ·
              refine ⟨24740567190522841747244303, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16493711460348561164829535 24740567190522841747244303)
              ·
                refine ⟨37110850785784262620866455, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24740567190522841747244303 37110850785784262620866455)
                ·
                  refine ⟨55666276178676393931299683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37110850785784262620866455 55666276178676393931299683)
                  ·
                    refine ⟨83499414268014590896949525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 55666276178676393931299683 83499414268014590896949525)
                    ·
                      refine ⟨3914035043813183948294509, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 83499414268014590896949525 3914035043813183948294509)
                      ·
                        rfl

theorem cell23_7622556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 2, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 2, 1, 1, 1, 1, 6].length) (baseStart_7622556 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7622556 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7622556 prefixEnd_7622556 := by exact prefixLift 7622556
  have htrace : WordTrace (prefixWord ++ tailWord_7622556) baseStart_7622556 baseEnd_7622556 := by
    simpa [prefixWord, tailWord_7622556, baseEnd_7622556] using wordTrace_append hprefix tailTrace_7622556
  have hstable : (prefixWord ++ tailWord_7622556).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7622556).length < 2 ^ (prefixWord ++ tailWord_7622556).sum := by decide
  have hdescent : baseEnd_7622556 < baseStart_7622556 := by decide
  rcases family_descends (prefixWord ++ tailWord_7622556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7622577 : List Nat := [1, 2, 2, 4, 2, 1, 3, 3, 1, 2, 2]
def baseStart_7622577 : Nat := 118140960795 + 7622577 * 2 ^ 59
def prefixEnd_7622577 : Nat := 4983230072969 + 3 ^ 40 * 7622577 * 2
def baseEnd_7622577 : Nat := 3914045826906928366131913

theorem tailTrace_7622577 : CollatzResearch.WordTrace tailWord_7622577 prefixEnd_7622577 3914045826906928366131913 := by
  unfold tailWord_7622577
  simp only [CollatzResearch.WordTrace]
  refine ⟨278018223305712836352529985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185345482203808557568353323 278018223305712836352529985)
  ·
    refine ⟨208513667479284627264397489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 278018223305712836352529985 208513667479284627264397489)
    ·
      refine ⟨156385250609463470448298117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 208513667479284627264397489 156385250609463470448298117)
      ·
        refine ⟨29322234489274400709055897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 156385250609463470448298117 29322234489274400709055897)
        ·
          refine ⟨21991675866955800531791923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29322234489274400709055897 21991675866955800531791923)
          ·
            refine ⟨32987513800433700797687885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21991675866955800531791923 32987513800433700797687885)
            ·
              refine ⟨12370317675162637799132957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32987513800433700797687885 12370317675162637799132957)
              ·
                refine ⟨4638869128185989174674859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12370317675162637799132957 4638869128185989174674859)
                ·
                  refine ⟨6958303692278983762012289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4638869128185989174674859 6958303692278983762012289)
                  ·
                    refine ⟨5218727769209237821509217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6958303692278983762012289 5218727769209237821509217)
                    ·
                      refine ⟨3914045826906928366131913, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5218727769209237821509217 3914045826906928366131913)
                      ·
                        rfl

theorem cell23_7622577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 1, 3, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 1, 3, 3, 1, 2, 2].length) (baseStart_7622577 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7622577 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7622577 prefixEnd_7622577 := by exact prefixLift 7622577
  have htrace : WordTrace (prefixWord ++ tailWord_7622577) baseStart_7622577 baseEnd_7622577 := by
    simpa [prefixWord, tailWord_7622577, baseEnd_7622577] using wordTrace_append hprefix tailTrace_7622577
  have hstable : (prefixWord ++ tailWord_7622577).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7622577).length < 2 ^ (prefixWord ++ tailWord_7622577).sum := by decide
  have hdescent : baseEnd_7622577 < baseStart_7622577 := by decide
  rcases family_descends (prefixWord ++ tailWord_7622577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7622580 : List Nat := [2, 5, 2, 1, 2, 1, 2, 1, 1, 1, 5]
def baseStart_7622580 : Nat := 118140960795 + 7622580 * 2 ^ 59
def prefixEnd_7622580 : Nat := 4983230072969 + 3 ^ 40 * 7622580 * 2
def baseEnd_7622580 : Nat := 3914047367348891854394399

theorem tailTrace_7622580 : CollatzResearch.WordTrace tailWord_7622580 prefixEnd_7622580 3914047367348891854394399 := by
  unfold tailWord_7622580
  simp only [CollatzResearch.WordTrace]
  refine ⟨139009166362350983932444597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 185345555149801311909926129 139009166362350983932444597)
  ·
    refine ⟨13032109346470404743666681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 139009166362350983932444597 13032109346470404743666681)
    ·
      refine ⟨9774082009852803557750011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13032109346470404743666681 9774082009852803557750011)
      ·
        refine ⟨14661123014779205336625017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9774082009852803557750011 14661123014779205336625017)
        ·
          refine ⟨10995842261084404002468763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14661123014779205336625017 10995842261084404002468763)
          ·
            refine ⟨16493763391626606003703145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10995842261084404002468763 16493763391626606003703145)
            ·
              refine ⟨12370322543719954502777359, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16493763391626606003703145 12370322543719954502777359)
              ·
                refine ⟨18555483815579931754166039, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12370322543719954502777359 18555483815579931754166039)
                ·
                  refine ⟨27833225723369897631249059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18555483815579931754166039 27833225723369897631249059)
                  ·
                    refine ⟨41749838585054846446873589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27833225723369897631249059 41749838585054846446873589)
                    ·
                      refine ⟨3914047367348891854394399, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41749838585054846446873589 3914047367348891854394399)
                      ·
                        rfl

theorem cell23_7622580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 2, 1, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 2, 1, 2, 1, 1, 1, 5].length) (baseStart_7622580 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7622580 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7622580 prefixEnd_7622580 := by exact prefixLift 7622580
  have htrace : WordTrace (prefixWord ++ tailWord_7622580) baseStart_7622580 baseEnd_7622580 := by
    simpa [prefixWord, tailWord_7622580, baseEnd_7622580] using wordTrace_append hprefix tailTrace_7622580
  have hstable : (prefixWord ++ tailWord_7622580).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7622580).length < 2 ^ (prefixWord ++ tailWord_7622580).sum := by decide
  have hdescent : baseEnd_7622580 < baseStart_7622580 := by decide
  rcases family_descends (prefixWord ++ tailWord_7622580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7622599 : List Nat := [1, 1, 4, 1, 1, 2, 1, 3, 2, 3, 4]
def baseStart_7622599 : Nat := 118140960795 + 7622599 * 2 ^ 59
def prefixEnd_7622599 : Nat := 4983230072969 + 3 ^ 40 * 7622599 * 2
def baseEnd_7622599 : Nat := 3914057123481327280056811

theorem tailTrace_7622599 : CollatzResearch.WordTrace tailWord_7622599 prefixEnd_7622599 3914057123481327280056811 := by
  unfold tailWord_7622599
  simp only [CollatzResearch.WordTrace]
  refine ⟨278019025711633134109830851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185346017141088756073220567 278019025711633134109830851)
  ·
    refine ⟨417028538567449701164746277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 278019025711633134109830851 417028538567449701164746277)
    ·
      refine ⟨78192850981396818968389927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 417028538567449701164746277 78192850981396818968389927)
      ·
        refine ⟨117289276472095228452584891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78192850981396818968389927 117289276472095228452584891)
        ·
          refine ⟨175933914708142842678877337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 117289276472095228452584891 175933914708142842678877337)
          ·
            refine ⟨131950436031107132009158003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 175933914708142842678877337 131950436031107132009158003)
            ·
              refine ⟨197925654046660698013737005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 131950436031107132009158003 197925654046660698013737005)
              ·
                refine ⟨74222120267497761755151377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 197925654046660698013737005 74222120267497761755151377)
                ·
                  refine ⟨55666590200623321316363533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 74222120267497761755151377 55666590200623321316363533)
                  ·
                    refine ⟨20874971325233745493636325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 55666590200623321316363533 20874971325233745493636325)
                    ·
                      refine ⟨3914057123481327280056811, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20874971325233745493636325 3914057123481327280056811)
                      ·
                        rfl

theorem cell23_7622599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 1, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 1, 3, 2, 3, 4].length) (baseStart_7622599 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7622599 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7622599 prefixEnd_7622599 := by exact prefixLift 7622599
  have htrace : WordTrace (prefixWord ++ tailWord_7622599) baseStart_7622599 baseEnd_7622599 := by
    simpa [prefixWord, tailWord_7622599, baseEnd_7622599] using wordTrace_append hprefix tailTrace_7622599
  have hstable : (prefixWord ++ tailWord_7622599).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7622599).length < 2 ^ (prefixWord ++ tailWord_7622599).sum := by decide
  have hdescent : baseEnd_7622599 < baseStart_7622599 := by decide
  rcases family_descends (prefixWord ++ tailWord_7622599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7622614 : List Nat := [5, 2, 1, 1, 4, 1, 1, 2, 1, 2, 3]
def baseStart_7622614 : Nat := 118140960795 + 7622614 * 2 ^ 59
def prefixEnd_7622614 : Nat := 4983230072969 + 3 ^ 40 * 7622614 * 2
def baseEnd_7622614 : Nat := 3914064825691144721369243

theorem tailTrace_7622614 : CollatzResearch.WordTrace tailWord_7622614 prefixEnd_7622614 3914064825691144721369243 := by
  unfold tailWord_7622614
  simp only [CollatzResearch.WordTrace]
  refine ⟨17376223300411174479476681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 185346381871052527781084597 17376223300411174479476681)
  ·
    refine ⟨13032167475308380859607511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17376223300411174479476681 13032167475308380859607511)
    ·
      refine ⟨19548251212962571289411267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13032167475308380859607511 19548251212962571289411267)
      ·
        refine ⟨29322376819443856934116901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19548251212962571289411267 29322376819443856934116901)
        ·
          refine ⟨5497945653645723175146919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 29322376819443856934116901 5497945653645723175146919)
          ·
            refine ⟨8246918480468584762720379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5497945653645723175146919 8246918480468584762720379)
            ·
              refine ⟨12370377720702877144080569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8246918480468584762720379 12370377720702877144080569)
              ·
                refine ⟨9277783290527157858060427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12370377720702877144080569 9277783290527157858060427)
                ·
                  refine ⟨13916674935790736787090641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9277783290527157858060427 13916674935790736787090641)
                  ·
                    refine ⟨10437506201843052590317981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13916674935790736787090641 10437506201843052590317981)
                    ·
                      refine ⟨3914064825691144721369243, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10437506201843052590317981 3914064825691144721369243)
                      ·
                        rfl

theorem cell23_7622614_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 4, 1, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 4, 1, 1, 2, 1, 2, 3].length) (baseStart_7622614 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7622614 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7622614 prefixEnd_7622614 := by exact prefixLift 7622614
  have htrace : WordTrace (prefixWord ++ tailWord_7622614) baseStart_7622614 baseEnd_7622614 := by
    simpa [prefixWord, tailWord_7622614, baseEnd_7622614] using wordTrace_append hprefix tailTrace_7622614
  have hstable : (prefixWord ++ tailWord_7622614).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7622614).length < 2 ^ (prefixWord ++ tailWord_7622614).sum := by decide
  have hdescent : baseEnd_7622614 < baseStart_7622614 := by decide
  rcases family_descends (prefixWord ++ tailWord_7622614) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7622767 : List Nat := [1, 1, 2, 1, 3, 5, 3, 2, 1, 4]
def baseStart_7622767 : Nat := 118140960795 + 7622767 * 2 ^ 59
def prefixEnd_7622767 : Nat := 4983230072969 + 3 ^ 40 * 7622767 * 2
def baseEnd_7622767 : Nat := 1304714462743760874252013

theorem tailTrace_7622767 : CollatzResearch.WordTrace tailWord_7622767 prefixEnd_7622767 1304714462743760874252013 := by
  unfold tailWord_7622767
  simp only [CollatzResearch.WordTrace]
  refine ⟨278025153175024498801946555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185350102116682999201297703 278025153175024498801946555)
  ·
    refine ⟨417037729762536748202919833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 278025153175024498801946555 417037729762536748202919833)
    ·
      refine ⟨312778297321902561152189875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 417037729762536748202919833 312778297321902561152189875)
      ·
        refine ⟨469167445982853841728284813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 312778297321902561152189875 469167445982853841728284813)
        ·
          refine ⟨175937792243570190648106805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 469167445982853841728284813 175937792243570190648106805)
          ·
            refine ⟨16494168022834705373260013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 175937792243570190648106805 16494168022834705373260013)
            ·
              refine ⟨6185313008563014514972505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16494168022834705373260013 6185313008563014514972505)
              ·
                refine ⟨4638984756422260886229379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6185313008563014514972505 4638984756422260886229379)
                ·
                  refine ⟨6958477134633391329344069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4638984756422260886229379 6958477134633391329344069)
                  ·
                    refine ⟨1304714462743760874252013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6958477134633391329344069 1304714462743760874252013)
                    ·
                      rfl

theorem cell23_7622767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 5, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 5, 3, 2, 1, 4].length) (baseStart_7622767 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7622767 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7622767 prefixEnd_7622767 := by exact prefixLift 7622767
  have htrace : WordTrace (prefixWord ++ tailWord_7622767) baseStart_7622767 baseEnd_7622767 := by
    simpa [prefixWord, tailWord_7622767, baseEnd_7622767] using wordTrace_append hprefix tailTrace_7622767
  have hstable : (prefixWord ++ tailWord_7622767).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7622767).length < 2 ^ (prefixWord ++ tailWord_7622767).sum := by decide
  have hdescent : baseEnd_7622767 < baseStart_7622767 := by decide
  rcases family_descends (prefixWord ++ tailWord_7622767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7622776 : List Nat := [2, 1, 2, 1, 1, 1, 3, 4, 3, 5]
def baseStart_7622776 : Nat := 118140960795 + 7622776 * 2 ^ 59
def prefixEnd_7622776 : Nat := 4983230072969 + 3 ^ 40 * 7622776 * 2
def baseEnd_7622776 : Nat := 1304716003185724362514499

theorem tailTrace_7622776 : CollatzResearch.WordTrace tailWord_7622776 prefixEnd_7622776 1304716003185724362514499 := by
  unfold tailWord_7622776
  simp only [CollatzResearch.WordTrace]
  refine ⟨139012740715995946669512091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 185350320954661262226016121 139012740715995946669512091)
  ·
    refine ⟨208519111073993920004268137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139012740715995946669512091 208519111073993920004268137)
    ·
      refine ⟨156389333305495440003201103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 208519111073993920004268137 156389333305495440003201103)
      ·
        refine ⟨234583999958243160004801655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 156389333305495440003201103 234583999958243160004801655)
        ·
          refine ⟨351875999937364740007202483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 234583999958243160004801655 351875999937364740007202483)
          ·
            refine ⟨527813999906047110010803725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 351875999937364740007202483 527813999906047110010803725)
            ·
              refine ⟨197930249964767666254051397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 527813999906047110010803725 197930249964767666254051397)
              ·
                refine ⟨37111921868393937422634637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 197930249964767666254051397 37111921868393937422634637)
                ·
                  refine ⟨13916970700647726533487989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 37111921868393937422634637 13916970700647726533487989)
                  ·
                    refine ⟨1304716003185724362514499, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13916970700647726533487989 1304716003185724362514499)
                    ·
                      rfl

theorem cell23_7622776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 3, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 3, 4, 3, 5].length) (baseStart_7622776 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7622776 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7622776 prefixEnd_7622776 := by exact prefixLift 7622776
  have htrace : WordTrace (prefixWord ++ tailWord_7622776) baseStart_7622776 baseEnd_7622776 := by
    simpa [prefixWord, tailWord_7622776, baseEnd_7622776] using wordTrace_append hprefix tailTrace_7622776
  have hstable : (prefixWord ++ tailWord_7622776).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7622776).length < 2 ^ (prefixWord ++ tailWord_7622776).sum := by decide
  have hdescent : baseEnd_7622776 < baseStart_7622776 := by decide
  rcases family_descends (prefixWord ++ tailWord_7622776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7622780 : List Nat := [2, 2, 2, 1, 1, 6, 2, 1, 6]
def baseStart_7622780 : Nat := 118140960795 + 7622780 * 2 ^ 59
def prefixEnd_7622780 : Nat := 4983230072969 + 3 ^ 40 * 7622780 * 2
def baseEnd_7622780 : Nat := 434905562608865674654831

theorem tailTrace_7622780 : CollatzResearch.WordTrace tailWord_7622780 prefixEnd_7622780 434905562608865674654831 := by
  unfold tailWord_7622780
  simp only [CollatzResearch.WordTrace]
  refine ⟨139012813661988701011084897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 185350418215984934681446529 139012813661988701011084897)
  ·
    refine ⟨104259610246491525758313673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 139012813661988701011084897 104259610246491525758313673)
    ·
      refine ⟨78194707684868644318735255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 104259610246491525758313673 78194707684868644318735255)
      ·
        refine ⟨117292061527302966478102883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78194707684868644318735255 117292061527302966478102883)
        ·
          refine ⟨175938092290954449717154325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 117292061527302966478102883 175938092290954449717154325)
          ·
            refine ⟨8247098076138489830491609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 175938092290954449717154325 8247098076138489830491609)
            ·
              refine ⟨6185323557103867372868707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8247098076138489830491609 6185323557103867372868707)
              ·
                refine ⟨9277985335655801059303061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6185323557103867372868707 9277985335655801059303061)
                ·
                  refine ⟨434905562608865674654831, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9277985335655801059303061 434905562608865674654831)
                  ·
                    rfl

theorem cell23_7622780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 6, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 6, 2, 1, 6].length) (baseStart_7622780 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7622780 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7622780 prefixEnd_7622780 := by exact prefixLift 7622780
  have htrace : WordTrace (prefixWord ++ tailWord_7622780) baseStart_7622780 baseEnd_7622780 := by
    simpa [prefixWord, tailWord_7622780, baseEnd_7622780] using wordTrace_append hprefix tailTrace_7622780
  have hstable : (prefixWord ++ tailWord_7622780).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7622780).length < 2 ^ (prefixWord ++ tailWord_7622780).sum := by decide
  have hdescent : baseEnd_7622780 < baseStart_7622780 := by decide
  rcases family_descends (prefixWord ++ tailWord_7622780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7622800 : List Nat := [2, 1, 1, 1, 1, 1, 8, 1, 2, 3, 2]
def baseStart_7622800 : Nat := 118140960795 + 7622800 * 2 ^ 59
def prefixEnd_7622800 : Nat := 4983230072969 + 3 ^ 40 * 7622800 * 2
def baseEnd_7622800 : Nat := 3914160333092880993643387

theorem tailTrace_7622800 : CollatzResearch.WordTrace tailWord_7622800 prefixEnd_7622800 3914160333092880993643387 := by
  unfold tailWord_7622800
  simp only [CollatzResearch.WordTrace]
  refine ⟨139013178391952472718948927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 185350904522603296958598569 139013178391952472718948927)
  ·
    refine ⟨208519767587928709078423391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139013178391952472718948927 208519767587928709078423391)
    ·
      refine ⟨312779651381893063617635087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 208519767587928709078423391 312779651381893063617635087)
      ·
        refine ⟨469169477072839595426452631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 312779651381893063617635087 469169477072839595426452631)
        ·
          refine ⟨703754215609259393139678947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 469169477072839595426452631 703754215609259393139678947)
          ·
            refine ⟨1055631323413889089709518421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 703754215609259393139678947 1055631323413889089709518421)
            ·
              refine ⟨12370679571256512770033419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1055631323413889089709518421 12370679571256512770033419)
              ·
                refine ⟨18556019356884769155050129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12370679571256512770033419 18556019356884769155050129)
                ·
                  refine ⟨13917014517663576866287597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18556019356884769155050129 13917014517663576866287597)
                  ·
                    refine ⟨5218880444123841324857849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13917014517663576866287597 5218880444123841324857849)
                    ·
                      refine ⟨3914160333092880993643387, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5218880444123841324857849 3914160333092880993643387)
                      ·
                        rfl

theorem cell23_7622800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 8, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 8, 1, 2, 3, 2].length) (baseStart_7622800 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7622800 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7622800 prefixEnd_7622800 := by exact prefixLift 7622800
  have htrace : WordTrace (prefixWord ++ tailWord_7622800) baseStart_7622800 baseEnd_7622800 := by
    simpa [prefixWord, tailWord_7622800, baseEnd_7622800] using wordTrace_append hprefix tailTrace_7622800
  have hstable : (prefixWord ++ tailWord_7622800).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7622800).length < 2 ^ (prefixWord ++ tailWord_7622800).sum := by decide
  have hdescent : baseEnd_7622800 < baseStart_7622800 := by decide
  rcases family_descends (prefixWord ++ tailWord_7622800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7622843 : List Nat := [1, 1, 1, 1, 1, 2, 8, 1, 1, 2, 4]
def baseStart_7622843 : Nat := 118140960795 + 7622843 * 2 ^ 59
def prefixEnd_7622843 : Nat := 4983230072969 + 3 ^ 40 * 7622843 * 2
def baseEnd_7622843 : Nat := 3914182412761024325405689

theorem tailTrace_7622843 : CollatzResearch.WordTrace tailWord_7622843 prefixEnd_7622843 3914182412761024325405689 := by
  unfold tailWord_7622843
  simp only [CollatzResearch.WordTrace]
  refine ⟨278027925122749163781713183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185351950081832775854475455 278027925122749163781713183)
  ·
    refine ⟨417041887684123745672569775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 278027925122749163781713183 417041887684123745672569775)
    ·
      refine ⟨625562831526185618508854663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 417041887684123745672569775 625562831526185618508854663)
      ·
        refine ⟨938344247289278427763281995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 625562831526185618508854663 938344247289278427763281995)
        ·
          refine ⟨1407516370933917641644922993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 938344247289278427763281995 1407516370933917641644922993)
          ·
            refine ⟨1055637278200438231233692245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1407516370933917641644922993 1055637278200438231233692245)
            ·
              refine ⟨12370749353911385522269831, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1055637278200438231233692245 12370749353911385522269831)
              ·
                refine ⟨18556124030867078283404747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12370749353911385522269831 18556124030867078283404747)
                ·
                  refine ⟨27834186046300617425107121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18556124030867078283404747 27834186046300617425107121)
                  ·
                    refine ⟨20875639534725463068830341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27834186046300617425107121 20875639534725463068830341)
                    ·
                      refine ⟨3914182412761024325405689, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20875639534725463068830341 3914182412761024325405689)
                      ·
                        rfl

theorem cell23_7622843_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 8, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 8, 1, 1, 2, 4].length) (baseStart_7622843 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7622843 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7622843 prefixEnd_7622843 := by exact prefixLift 7622843
  have htrace : WordTrace (prefixWord ++ tailWord_7622843) baseStart_7622843 baseEnd_7622843 := by
    simpa [prefixWord, tailWord_7622843, baseEnd_7622843] using wordTrace_append hprefix tailTrace_7622843
  have hstable : (prefixWord ++ tailWord_7622843).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7622843).length < 2 ^ (prefixWord ++ tailWord_7622843).sum := by decide
  have hdescent : baseEnd_7622843 < baseStart_7622843 := by decide
  rcases family_descends (prefixWord ++ tailWord_7622843) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7622863 : List Nat := [1, 1, 2, 1, 1, 3, 3, 4, 1, 3, 3]
def baseStart_7622863 : Nat := 118140960795 + 7622863 * 2 ^ 59
def prefixEnd_7622863 : Nat := 4983230072969 + 3 ^ 40 * 7622863 * 2
def baseEnd_7622863 : Nat := 3914192682374114247155597

theorem tailTrace_7622863 : CollatzResearch.WordTrace tailWord_7622863 prefixEnd_7622863 3914192682374114247155597 := by
  unfold tailWord_7622863
  simp only [CollatzResearch.WordTrace]
  refine ⟨278028654582676707197441243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185352436388451138131627495 278028654582676707197441243)
  ·
    refine ⟨417042981874015060796161865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 278028654582676707197441243 417042981874015060796161865)
    ·
      refine ⟨312782236405511295597121399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 417042981874015060796161865 312782236405511295597121399)
      ·
        refine ⟨469173354608266943395682099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 312782236405511295597121399 469173354608266943395682099)
        ·
          refine ⟨703760031912400415093523149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 469173354608266943395682099 703760031912400415093523149)
          ·
            refine ⟨263910011967150155660071181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 703760031912400415093523149 263910011967150155660071181)
            ·
              refine ⟨98966254487681308372526693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 263910011967150155660071181 98966254487681308372526693)
              ·
                refine ⟨18556172716440245319848755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 98966254487681308372526693 18556172716440245319848755)
                ·
                  refine ⟨27834259074660367979773133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18556172716440245319848755 27834259074660367979773133)
                  ·
                    refine ⟨10437847152997637992414925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27834259074660367979773133 10437847152997637992414925)
                    ·
                      refine ⟨3914192682374114247155597, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10437847152997637992414925 3914192682374114247155597)
                      ·
                        rfl

theorem cell23_7622863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 3, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 3, 4, 1, 3, 3].length) (baseStart_7622863 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7622863 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7622863 prefixEnd_7622863 := by exact prefixLift 7622863
  have htrace : WordTrace (prefixWord ++ tailWord_7622863) baseStart_7622863 baseEnd_7622863 := by
    simpa [prefixWord, tailWord_7622863, baseEnd_7622863] using wordTrace_append hprefix tailTrace_7622863
  have hstable : (prefixWord ++ tailWord_7622863).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7622863).length < 2 ^ (prefixWord ++ tailWord_7622863).sum := by decide
  have hdescent : baseEnd_7622863 < baseStart_7622863 := by decide
  rcases family_descends (prefixWord ++ tailWord_7622863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7622870 : List Nat := [5, 2, 1, 2, 1, 2, 10]
def baseStart_7622870 : Nat := 118140960795 + 7622870 * 2 ^ 59
def prefixEnd_7622870 : Nat := 4983230072969 + 3 ^ 40 * 7622870 * 2
def baseEnd_7622870 : Nat := 48323410823934515058865

theorem tailTrace_7622870 : CollatzResearch.WordTrace tailWord_7622870 prefixEnd_7622870 48323410823934515058865 := by
  unfold tailWord_7622870
  simp only [CollatzResearch.WordTrace]
  refine ⟨17376806868353209212059129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 185352606595767564928630709 17376806868353209212059129)
  ·
    refine ⟨13032605151264906909044347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17376806868353209212059129 13032605151264906909044347)
    ·
      refine ⟨19548907726897360363566521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13032605151264906909044347 19548907726897360363566521)
      ·
        refine ⟨14661680795173020272674891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19548907726897360363566521 14661680795173020272674891)
        ·
          refine ⟨21992521192759530409012337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14661680795173020272674891 21992521192759530409012337)
          ·
            refine ⟨16494390894569647806759253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21992521192759530409012337 16494390894569647806759253)
            ·
              refine ⟨48323410823934515058865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 16494390894569647806759253 48323410823934515058865)
              ·
                rfl

theorem cell23_7622870_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 2, 10].length) (baseStart_7622870 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7622870 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7622870 prefixEnd_7622870 := by exact prefixLift 7622870
  have htrace : WordTrace (prefixWord ++ tailWord_7622870) baseStart_7622870 baseEnd_7622870 := by
    simpa [prefixWord, tailWord_7622870, baseEnd_7622870] using wordTrace_append hprefix tailTrace_7622870
  have hstable : (prefixWord ++ tailWord_7622870).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7622870).length < 2 ^ (prefixWord ++ tailWord_7622870).sum := by decide
  have hdescent : baseEnd_7622870 < baseStart_7622870 := by decide
  rcases family_descends (prefixWord ++ tailWord_7622870) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7622880 : List Nat := [2, 1, 1, 3, 1, 3, 3, 1, 4, 1, 3]
def baseStart_7622880 : Nat := 118140960795 + 7622880 * 2 ^ 59
def prefixEnd_7622880 : Nat := 4983230072969 + 3 ^ 40 * 7622880 * 2
def baseEnd_7622880 : Nat := 3914201411545240680643019

theorem tailTrace_7622880 : CollatzResearch.WordTrace tailWord_7622880 prefixEnd_7622880 3914201411545240680643019 := by
  unfold tailWord_7622880
  simp only [CollatzResearch.WordTrace]
  refine ⟨139014637311807559550405047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 185352849749076746067206729 139014637311807559550405047)
  ·
    refine ⟨208521955967711339325607571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139014637311807559550405047 208521955967711339325607571)
    ·
      refine ⟨312782933951567008988411357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 208521955967711339325607571 312782933951567008988411357)
      ·
        refine ⟨117293600231837628370654259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 312782933951567008988411357 117293600231837628370654259)
        ·
          refine ⟨175940400347756442555981389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 117293600231837628370654259 175940400347756442555981389)
          ·
            refine ⟨65977650130408665958493021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 175940400347756442555981389 65977650130408665958493021)
            ·
              refine ⟨24741618798903249734434883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 65977650130408665958493021 24741618798903249734434883)
              ·
                refine ⟨37112428198354874601652325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24741618798903249734434883 37112428198354874601652325)
                ·
                  refine ⟨6958580287191538987809811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 37112428198354874601652325 6958580287191538987809811)
                  ·
                    refine ⟨10437870430787308481714717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6958580287191538987809811 10437870430787308481714717)
                    ·
                      refine ⟨3914201411545240680643019, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10437870430787308481714717 3914201411545240680643019)
                      ·
                        rfl

theorem cell23_7622880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 3, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 3, 1, 4, 1, 3].length) (baseStart_7622880 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7622880 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7622880 prefixEnd_7622880 := by exact prefixLift 7622880
  have htrace : WordTrace (prefixWord ++ tailWord_7622880) baseStart_7622880 baseEnd_7622880 := by
    simpa [prefixWord, tailWord_7622880, baseEnd_7622880] using wordTrace_append hprefix tailTrace_7622880
  have hstable : (prefixWord ++ tailWord_7622880).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7622880).length < 2 ^ (prefixWord ++ tailWord_7622880).sum := by decide
  have hdescent : baseEnd_7622880 < baseStart_7622880 := by decide
  rcases family_descends (prefixWord ++ tailWord_7622880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7622923 : List Nat := [1, 1, 1, 1, 5, 2, 3, 1, 2, 1, 5]
def baseStart_7622923 : Nat := 118140960795 + 7622923 * 2 ^ 59
def prefixEnd_7622923 : Nat := 4983230072969 + 3 ^ 40 * 7622923 * 2
def baseEnd_7622923 : Nat := 3914223491213384012405321

theorem tailTrace_7622923 : CollatzResearch.WordTrace tailWord_7622923 prefixEnd_7622923 3914223491213384012405321 := by
  unfold tailWord_7622923
  simp only [CollatzResearch.WordTrace]
  refine ⟨278030842962459337444625423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185353895308306224963083615 278030842962459337444625423)
  ·
    refine ⟨417046264443689006166938135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 278030842962459337444625423 417046264443689006166938135)
    ·
      refine ⟨625569396665533509250407203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 417046264443689006166938135 625569396665533509250407203)
      ·
        refine ⟨938354094998300263875610805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 625569396665533509250407203 938354094998300263875610805)
        ·
          refine ⟨87970696406090649738338513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 938354094998300263875610805 87970696406090649738338513)
          ·
            refine ⟨65978022304567987303753885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 87970696406090649738338513 65978022304567987303753885)
            ·
              refine ⟨24741758364212995238907707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 65978022304567987303753885 24741758364212995238907707)
              ·
                refine ⟨37112637546319492858361561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24741758364212995238907707 37112637546319492858361561)
                ·
                  refine ⟨27834478159739619643771171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37112637546319492858361561 27834478159739619643771171)
                  ·
                    refine ⟨41751717239609429465656757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27834478159739619643771171 41751717239609429465656757)
                    ·
                      refine ⟨3914223491213384012405321, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41751717239609429465656757 3914223491213384012405321)
                      ·
                        rfl

theorem cell23_7622923_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 3, 1, 2, 1, 5].length) (baseStart_7622923 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7622923 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7622923 prefixEnd_7622923 := by exact prefixLift 7622923
  have htrace : WordTrace (prefixWord ++ tailWord_7622923) baseStart_7622923 baseEnd_7622923 := by
    simpa [prefixWord, tailWord_7622923, baseEnd_7622923] using wordTrace_append hprefix tailTrace_7622923
  have hstable : (prefixWord ++ tailWord_7622923).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7622923).length < 2 ^ (prefixWord ++ tailWord_7622923).sum := by decide
  have hdescent : baseEnd_7622923 < baseStart_7622923 := by decide
  rcases family_descends (prefixWord ++ tailWord_7622923) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7622933 : List Nat := [1, 3, 2, 1, 2, 1, 2, 1, 4, 2, 4]
def baseStart_7622933 : Nat := 118140960795 + 7622933 * 2 ^ 59
def prefixEnd_7622933 : Nat := 4983230072969 + 3 ^ 40 * 7622933 * 2
def baseEnd_7622933 : Nat := 3914228626019928973280275

theorem tailTrace_7622933 : CollatzResearch.WordTrace tailWord_7622933 prefixEnd_7622933 3914228626019928973280275 := by
  unfold tailWord_7622933
  simp only [CollatzResearch.WordTrace]
  refine ⟨278031207692423109152489453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185354138461615406101659635 278031207692423109152489453)
  ·
    refine ⟨104261702884658665932183545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 278031207692423109152489453 104261702884658665932183545)
    ·
      refine ⟨78196277163493999449137659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 104261702884658665932183545 78196277163493999449137659)
      ·
        refine ⟨117294415745240999173706489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78196277163493999449137659 117294415745240999173706489)
        ·
          refine ⟨87970811808930749380279867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 117294415745240999173706489 87970811808930749380279867)
          ·
            refine ⟨131956217713396124070419801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87970811808930749380279867 131956217713396124070419801)
            ·
              refine ⟨98967163285047093052814851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 131956217713396124070419801 98967163285047093052814851)
              ·
                refine ⟨148450744927570639579222277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 98967163285047093052814851 148450744927570639579222277)
                ·
                  refine ⟨27834514673919494921104177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 148450744927570639579222277 27834514673919494921104177)
                  ·
                    refine ⟨20875886005439621190828133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27834514673919494921104177 20875886005439621190828133)
                    ·
                      refine ⟨3914228626019928973280275, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20875886005439621190828133 3914228626019928973280275)
                      ·
                        rfl

theorem cell23_7622933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 2, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 2, 1, 4, 2, 4].length) (baseStart_7622933 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7622933 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7622933 prefixEnd_7622933 := by exact prefixLift 7622933
  have htrace : WordTrace (prefixWord ++ tailWord_7622933) baseStart_7622933 baseEnd_7622933 := by
    simpa [prefixWord, tailWord_7622933, baseEnd_7622933] using wordTrace_append hprefix tailTrace_7622933
  have hstable : (prefixWord ++ tailWord_7622933).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7622933).length < 2 ^ (prefixWord ++ tailWord_7622933).sum := by decide
  have hdescent : baseEnd_7622933 < baseStart_7622933 := by decide
  rcases family_descends (prefixWord ++ tailWord_7622933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7622958 : List Nat := [4, 1, 3, 3, 1, 2, 1, 2, 1, 3, 2]
def baseStart_7622958 : Nat := 118140960795 + 7622958 * 2 ^ 59
def prefixEnd_7622958 : Nat := 4983230072969 + 3 ^ 40 * 7622958 * 2
def baseEnd_7622958 : Nat := 3914241463036291375467661

theorem tailTrace_7622958 : CollatzResearch.WordTrace tailWord_7622958 prefixEnd_7622958 3914241463036291375467661 := by
  unfold tailWord_7622958
  simp only [CollatzResearch.WordTrace]
  refine ⟨34754014939666567302768691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 185354746344888358948099685 34754014939666567302768691)
  ·
    refine ⟨52131022409499850954153037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34754014939666567302768691 52131022409499850954153037)
    ·
      refine ⟨19549133403562444107807389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 52131022409499850954153037 19549133403562444107807389)
      ·
        refine ⟨7330925026335916540427771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19549133403562444107807389 7330925026335916540427771)
        ·
          refine ⟨10996387539503874810641657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7330925026335916540427771 10996387539503874810641657)
          ·
            refine ⟨8247290654627906107981243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10996387539503874810641657 8247290654627906107981243)
            ·
              refine ⟨12370935981941859161971865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8247290654627906107981243 12370935981941859161971865)
              ·
                refine ⟨9278201986456394371478899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12370935981941859161971865 9278201986456394371478899)
                ·
                  refine ⟨13917302979684591557218349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9278201986456394371478899 13917302979684591557218349)
                  ·
                    refine ⟨5218988617381721833956881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13917302979684591557218349 5218988617381721833956881)
                    ·
                      refine ⟨3914241463036291375467661, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5218988617381721833956881 3914241463036291375467661)
                      ·
                        rfl

theorem cell23_7622958_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 1, 2, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 1, 2, 1, 2, 1, 3, 2].length) (baseStart_7622958 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7622958 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7622958 prefixEnd_7622958 := by exact prefixLift 7622958
  have htrace : WordTrace (prefixWord ++ tailWord_7622958) baseStart_7622958 baseEnd_7622958 := by
    simpa [prefixWord, tailWord_7622958, baseEnd_7622958] using wordTrace_append hprefix tailTrace_7622958
  have hstable : (prefixWord ++ tailWord_7622958).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7622958).length < 2 ^ (prefixWord ++ tailWord_7622958).sum := by decide
  have hdescent : baseEnd_7622958 < baseStart_7622958 := by decide
  rcases family_descends (prefixWord ++ tailWord_7622958) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7622983 : List Nat := [1, 1, 4, 1, 2, 2, 1, 1, 3, 2, 5]
def baseStart_7622983 : Nat := 118140960795 + 7622983 * 2 ^ 59
def prefixEnd_7622983 : Nat := 4983230072969 + 3 ^ 40 * 7622983 * 2
def baseEnd_7622983 : Nat := 3914254300052653777655045

theorem tailTrace_7622983 : CollatzResearch.WordTrace tailWord_7622983 prefixEnd_7622983 3914254300052653777655045 := by
  unfold tailWord_7622983
  simp only [CollatzResearch.WordTrace]
  refine ⟨278033031342241967691809603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185355354228161311794539735 278033031342241967691809603)
  ·
    refine ⟨417049547013362951537714405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 278033031342241967691809603 417049547013362951537714405)
    ·
      refine ⟨78196790065005553413321451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 417049547013362951537714405 78196790065005553413321451)
      ·
        refine ⟨117295185097508330119982177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78196790065005553413321451 117295185097508330119982177)
        ·
          refine ⟨87971388823131247589986633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 117295185097508330119982177 87971388823131247589986633)
          ·
            refine ⟨65978541617348435692489975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 87971388823131247589986633 65978541617348435692489975)
            ·
              refine ⟨98967812426022653538734963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65978541617348435692489975 98967812426022653538734963)
              ·
                refine ⟨148451718639033980308102445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 98967812426022653538734963 148451718639033980308102445)
                ·
                  refine ⟨55669394489637742615538417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 148451718639033980308102445 55669394489637742615538417)
                  ·
                    refine ⟨41752045867228306961653813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 55669394489637742615538417 41752045867228306961653813)
                    ·
                      refine ⟨3914254300052653777655045, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41752045867228306961653813 3914254300052653777655045)
                      ·
                        rfl

theorem cell23_7622983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 1, 1, 3, 2, 5].length) (baseStart_7622983 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7622983 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7622983 prefixEnd_7622983 := by exact prefixLift 7622983
  have htrace : WordTrace (prefixWord ++ tailWord_7622983) baseStart_7622983 baseEnd_7622983 := by
    simpa [prefixWord, tailWord_7622983, baseEnd_7622983] using wordTrace_append hprefix tailTrace_7622983
  have hstable : (prefixWord ++ tailWord_7622983).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7622983).length < 2 ^ (prefixWord ++ tailWord_7622983).sum := by decide
  have hdescent : baseEnd_7622983 < baseStart_7622983 := by decide
  rcases family_descends (prefixWord ++ tailWord_7622983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7623004 : List Nat := [2, 2, 4, 3, 1, 1, 1, 1, 2, 3, 3]
def baseStart_7623004 : Nat := 118140960795 + 7623004 * 2 ^ 59
def prefixEnd_7623004 : Nat := 4983230072969 + 3 ^ 40 * 7623004 * 2
def baseEnd_7623004 : Nat := 3914265083146398195492449

theorem tailTrace_7623004 : CollatzResearch.WordTrace tailWord_7623004 prefixEnd_7623004 3914265083146398195492449 := by
  unfold tailWord_7623004
  simp only [CollatzResearch.WordTrace]
  refine ⟨139016898637582944139162033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 185355864850110592185549377 139016898637582944139162033)
  ·
    refine ⟨104262673978187208104371525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 139016898637582944139162033 104262673978187208104371525)
    ·
      refine ⟨19549251370910101519569661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 104262673978187208104371525 19549251370910101519569661)
      ·
        refine ⟨7330969264091288069838623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19549251370910101519569661 7330969264091288069838623)
        ·
          refine ⟨10996453896136932104757935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7330969264091288069838623 10996453896136932104757935)
          ·
            refine ⟨16494680844205398157136903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10996453896136932104757935 16494680844205398157136903)
            ·
              refine ⟨24742021266308097235705355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16494680844205398157136903 24742021266308097235705355)
              ·
                refine ⟨37113031899462145853558033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24742021266308097235705355 37113031899462145853558033)
                ·
                  refine ⟨27834773924596609390168525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37113031899462145853558033 27834773924596609390168525)
                  ·
                    refine ⟨10438040221723728521313197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27834773924596609390168525 10438040221723728521313197)
                    ·
                      refine ⟨3914265083146398195492449, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10438040221723728521313197 3914265083146398195492449)
                      ·
                        rfl

theorem cell23_7623004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 1, 1, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 1, 1, 1, 1, 2, 3, 3].length) (baseStart_7623004 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7623004 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7623004 prefixEnd_7623004 := by exact prefixLift 7623004
  have htrace : WordTrace (prefixWord ++ tailWord_7623004) baseStart_7623004 baseEnd_7623004 := by
    simpa [prefixWord, tailWord_7623004, baseEnd_7623004] using wordTrace_append hprefix tailTrace_7623004
  have hstable : (prefixWord ++ tailWord_7623004).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7623004).length < 2 ^ (prefixWord ++ tailWord_7623004).sum := by decide
  have hdescent : baseEnd_7623004 < baseStart_7623004 := by decide
  rcases family_descends (prefixWord ++ tailWord_7623004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7623023 : List Nat := [1, 1, 2, 1, 3, 1, 2, 1, 1, 6, 4]
def baseStart_7623023 : Nat := 118140960795 + 7623023 * 2 ^ 59
def prefixEnd_7623023 : Nat := 4983230072969 + 3 ^ 40 * 7623023 * 2
def baseEnd_7623023 : Nat := 3914274839278833621154861

theorem tailTrace_7623023 : CollatzResearch.WordTrace tailWord_7623023 prefixEnd_7623023 3914274839278833621154861 := by
  unfold tailWord_7623023
  simp only [CollatzResearch.WordTrace]
  refine ⟨278034490262097054523265723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185356326841398036348843815 278034490262097054523265723)
  ·
    refine ⟨417051735393145581784898585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 278034490262097054523265723 417051735393145581784898585)
    ·
      refine ⟨312788801544859186338673939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 417051735393145581784898585 312788801544859186338673939)
      ·
        refine ⟨469183202317288779508010909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 312788801544859186338673939 469183202317288779508010909)
        ·
          refine ⟨175943700868983292315504091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 469183202317288779508010909 175943700868983292315504091)
          ·
            refine ⟨263915551303474938473256137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 175943700868983292315504091 263915551303474938473256137)
            ·
              refine ⟨197936663477606203854942103, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 263915551303474938473256137 197936663477606203854942103)
              ·
                refine ⟨296904995216409305782413155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 197936663477606203854942103 296904995216409305782413155)
                ·
                  refine ⟨445357492824613958673619733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 296904995216409305782413155 445357492824613958673619733)
                  ·
                    refine ⟨20876132476153779312825925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 445357492824613958673619733 20876132476153779312825925)
                    ·
                      refine ⟨3914274839278833621154861, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20876132476153779312825925 3914274839278833621154861)
                      ·
                        rfl

theorem cell23_7623023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 2, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 2, 1, 1, 6, 4].length) (baseStart_7623023 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7623023 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7623023 prefixEnd_7623023 := by exact prefixLift 7623023
  have htrace : WordTrace (prefixWord ++ tailWord_7623023) baseStart_7623023 baseEnd_7623023 := by
    simpa [prefixWord, tailWord_7623023, baseEnd_7623023] using wordTrace_append hprefix tailTrace_7623023
  have hstable : (prefixWord ++ tailWord_7623023).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7623023).length < 2 ^ (prefixWord ++ tailWord_7623023).sum := by decide
  have hdescent : baseEnd_7623023 < baseStart_7623023 := by decide
  rcases family_descends (prefixWord ++ tailWord_7623023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7623033 : List Nat := [1, 2, 1, 3, 2, 1, 1, 4, 8]
def baseStart_7623033 : Nat := 118140960795 + 7623033 * 2 ^ 59
def prefixEnd_7623033 : Nat := 4983230072969 + 3 ^ 40 * 7623033 * 2
def baseEnd_7623033 : Nat := 434919997120597620225535

theorem tailTrace_7623033 : CollatzResearch.WordTrace tailWord_7623033 prefixEnd_7623033 434919997120597620225535 := by
  unfold tailWord_7623033
  simp only [CollatzResearch.WordTrace]
  refine ⟨278034854992060826231129753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185356569994707217487419835 278034854992060826231129753)
  ·
    refine ⟨208526141244045619673347315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 278034854992060826231129753 208526141244045619673347315)
    ·
      refine ⟨312789211866068429510020973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 208526141244045619673347315 312789211866068429510020973)
      ·
        refine ⟨117295954449775661066257865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 312789211866068429510020973 117295954449775661066257865)
        ·
          refine ⟨87971965837331745799693399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 117295954449775661066257865 87971965837331745799693399)
          ·
            refine ⟨131957948755997618699540099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87971965837331745799693399 131957948755997618699540099)
            ·
              refine ⟨197936923133996428049310149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 131957948755997618699540099 197936923133996428049310149)
              ·
                refine ⟨37113173087624330259245653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 197936923133996428049310149 37113173087624330259245653)
                ·
                  refine ⟨434919997120597620225535, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 37113173087624330259245653 434919997120597620225535)
                  ·
                    rfl

theorem cell23_7623033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 1, 4, 8].length) (baseStart_7623033 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7623033 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7623033 prefixEnd_7623033 := by exact prefixLift 7623033
  have htrace : WordTrace (prefixWord ++ tailWord_7623033) baseStart_7623033 baseEnd_7623033 := by
    simpa [prefixWord, tailWord_7623033, baseEnd_7623033] using wordTrace_append hprefix tailTrace_7623033
  have hstable : (prefixWord ++ tailWord_7623033).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7623033).length < 2 ^ (prefixWord ++ tailWord_7623033).sum := by decide
  have hdescent : baseEnd_7623033 < baseStart_7623033 := by decide
  rcases family_descends (prefixWord ++ tailWord_7623033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7623054 : List Nat := [4, 1, 1, 4, 1, 2, 2, 1, 3, 4]
def baseStart_7623054 : Nat := 118140960795 + 7623054 * 2 ^ 59
def prefixEnd_7623054 : Nat := 4983230072969 + 3 ^ 40 * 7623054 * 2
def baseEnd_7623054 : Nat := 1304763585726374333289073

theorem tailTrace_7623054 : CollatzResearch.WordTrace tailWord_7623054 prefixEnd_7623054 1304763585726374333289073 := by
  unfold tailWord_7623054
  simp only [CollatzResearch.WordTrace]
  refine ⟨34754452615623093352205527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 185357080616656497878429477 34754452615623093352205527)
  ·
    refine ⟨52131678923434640028308291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34754452615623093352205527 52131678923434640028308291)
    ·
      refine ⟨78197518385151960042462437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52131678923434640028308291 78197518385151960042462437)
      ·
        refine ⟨14662034697215992507961707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 78197518385151960042462437 14662034697215992507961707)
        ·
          refine ⟨21993052045823988761942561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14662034697215992507961707 21993052045823988761942561)
          ·
            refine ⟨16494789034367991571456921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21993052045823988761942561 16494789034367991571456921)
            ·
              refine ⟨12371091775775993678592691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16494789034367991571456921 12371091775775993678592691)
              ·
                refine ⟨18556637663663990517889037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12371091775775993678592691 18556637663663990517889037)
                ·
                  refine ⟨6958739123873996444208389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18556637663663990517889037 6958739123873996444208389)
                  ·
                    refine ⟨1304763585726374333289073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6958739123873996444208389 1304763585726374333289073)
                    ·
                      rfl

theorem cell23_7623054_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 2, 2, 1, 3, 4].length) (baseStart_7623054 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7623054 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7623054 prefixEnd_7623054 := by exact prefixLift 7623054
  have htrace : WordTrace (prefixWord ++ tailWord_7623054) baseStart_7623054 baseEnd_7623054 := by
    simpa [prefixWord, tailWord_7623054, baseEnd_7623054] using wordTrace_append hprefix tailTrace_7623054
  have hstable : (prefixWord ++ tailWord_7623054).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7623054).length < 2 ^ (prefixWord ++ tailWord_7623054).sum := by decide
  have hdescent : baseEnd_7623054 < baseStart_7623054 := by decide
  rcases family_descends (prefixWord ++ tailWord_7623054) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7623077 : List Nat := [1, 3, 1, 2, 1, 1, 3, 4, 3, 1, 3]
def baseStart_7623077 : Nat := 118140960795 + 7623077 * 2 ^ 59
def prefixEnd_7623077 : Nat := 4983230072969 + 3 ^ 40 * 7623077 * 2
def baseEnd_7623077 : Nat := 3914302567234176409879613

theorem tailTrace_7623077 : CollatzResearch.WordTrace tailWord_7623077 prefixEnd_7623077 3914302567234176409879613 := by
  unfold tailWord_7623077
  simp only [CollatzResearch.WordTrace]
  refine ⟨278036459803901421745731485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185357639869267614497154323 278036459803901421745731485)
  ·
    refine ⟨104263672426463033154649307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 278036459803901421745731485 104263672426463033154649307)
    ·
      refine ⟨156395508639694549731973961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104263672426463033154649307 156395508639694549731973961)
      ·
        refine ⟨117296631479770912298980471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 156395508639694549731973961 117296631479770912298980471)
        ·
          refine ⟨175944947219656368448470707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 117296631479770912298980471 175944947219656368448470707)
          ·
            refine ⟨263917420829484552672706061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 175944947219656368448470707 263917420829484552672706061)
            ·
              refine ⟨98969032811056707252264773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 263917420829484552672706061 98969032811056707252264773)
              ·
                refine ⟨18556693652073132609799645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 98969032811056707252264773 18556693652073132609799645)
                ·
                  refine ⟨6958760119527424728674867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18556693652073132609799645 6958760119527424728674867)
                  ·
                    refine ⟨10438140179291137093012301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6958760119527424728674867 10438140179291137093012301)
                    ·
                      refine ⟨3914302567234176409879613, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10438140179291137093012301 3914302567234176409879613)
                      ·
                        rfl

theorem cell23_7623077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 3, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 3, 4, 3, 1, 3].length) (baseStart_7623077 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7623077 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7623077 prefixEnd_7623077 := by exact prefixLift 7623077
  have htrace : WordTrace (prefixWord ++ tailWord_7623077) baseStart_7623077 baseEnd_7623077 := by
    simpa [prefixWord, tailWord_7623077, baseEnd_7623077] using wordTrace_append hprefix tailTrace_7623077
  have hstable : (prefixWord ++ tailWord_7623077).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7623077).length < 2 ^ (prefixWord ++ tailWord_7623077).sum := by decide
  have hdescent : baseEnd_7623077 < baseStart_7623077 := by decide
  rcases family_descends (prefixWord ++ tailWord_7623077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7623097 : List Nat := [1, 2, 1, 4, 3, 1, 2, 3, 1, 5]
def baseStart_7623097 : Nat := 118140960795 + 7623097 * 2 ^ 59
def prefixEnd_7623097 : Nat := 4983230072969 + 3 ^ 40 * 7623097 * 2
def baseEnd_7623097 : Nat := 1304770945615755443876507

theorem tailTrace_7623097 : CollatzResearch.WordTrace tailWord_7623097 prefixEnd_7623097 1304770945615755443876507 := by
  unfold tailWord_7623097
  simp only [CollatzResearch.WordTrace]
  refine ⟨278037189263828965161459545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185358126175885976774306363 278037189263828965161459545)
  ·
    refine ⟨208527891947871723871094659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 278037189263828965161459545 208527891947871723871094659)
    ·
      refine ⟨312791837921807585806641989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 208527891947871723871094659 312791837921807585806641989)
      ·
        refine ⟨58648469610338922338745373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 312791837921807585806641989 58648469610338922338745373)
        ·
          refine ⟨21993176103877095877029515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 58648469610338922338745373 21993176103877095877029515)
          ·
            refine ⟨32989764155815643815544273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21993176103877095877029515 32989764155815643815544273)
            ·
              refine ⟨24742323116861732861658205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32989764155815643815544273 24742323116861732861658205)
              ·
                refine ⟨9278371168823149823121827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24742323116861732861658205 9278371168823149823121827)
                ·
                  refine ⟨13917556753234724734682741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9278371168823149823121827 13917556753234724734682741)
                  ·
                    refine ⟨1304770945615755443876507, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13917556753234724734682741 1304770945615755443876507)
                    ·
                      rfl

theorem cell23_7623097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 1, 2, 3, 1, 5].length) (baseStart_7623097 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7623097 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7623097 prefixEnd_7623097 := by exact prefixLift 7623097
  have htrace : WordTrace (prefixWord ++ tailWord_7623097) baseStart_7623097 baseEnd_7623097 := by
    simpa [prefixWord, tailWord_7623097, baseEnd_7623097] using wordTrace_append hprefix tailTrace_7623097
  have hstable : (prefixWord ++ tailWord_7623097).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7623097).length < 2 ^ (prefixWord ++ tailWord_7623097).sum := by decide
  have hdescent : baseEnd_7623097 < baseStart_7623097 := by decide
  rcases family_descends (prefixWord ++ tailWord_7623097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7623105 : List Nat := [1, 2, 7, 1, 2, 1, 1, 1, 3, 4]
def baseStart_7623105 : Nat := 118140960795 + 7623105 * 2 ^ 59
def prefixEnd_7623105 : Nat := 4983230072969 + 3 ^ 40 * 7623105 * 2
def baseEnd_7623105 : Nat := 1304772314897500766776495

theorem tailTrace_7623105 : CollatzResearch.WordTrace tailWord_7623105 prefixEnd_7623105 1304772314897500766776495 := by
  unfold tailWord_7623105
  simp only [CollatzResearch.WordTrace]
  refine ⟨278037481047799982527750769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185358320698533321685167179 278037481047799982527750769)
  ·
    refine ⟨208528110785849986895813077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 278037481047799982527750769 208528110785849986895813077)
    ·
      refine ⟨4887377596543359067870619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 208528110785849986895813077 4887377596543359067870619)
      ·
        refine ⟨7331066394815038601805929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4887377596543359067870619 7331066394815038601805929)
        ·
          refine ⟨5498299796111278951354447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7331066394815038601805929 5498299796111278951354447)
          ·
            refine ⟨8247449694166918427031671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5498299796111278951354447 8247449694166918427031671)
            ·
              refine ⟨12371174541250377640547507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8247449694166918427031671 12371174541250377640547507)
              ·
                refine ⟨18556761811875566460821261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12371174541250377640547507 18556761811875566460821261)
                ·
                  refine ⟨6958785679453337422807973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18556761811875566460821261 6958785679453337422807973)
                  ·
                    refine ⟨1304772314897500766776495, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6958785679453337422807973 1304772314897500766776495)
                    ·
                      rfl

theorem cell23_7623105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 2, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 2, 1, 1, 1, 3, 4].length) (baseStart_7623105 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7623105 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7623105 prefixEnd_7623105 := by exact prefixLift 7623105
  have htrace : WordTrace (prefixWord ++ tailWord_7623105) baseStart_7623105 baseEnd_7623105 := by
    simpa [prefixWord, tailWord_7623105, baseEnd_7623105] using wordTrace_append hprefix tailTrace_7623105
  have hstable : (prefixWord ++ tailWord_7623105).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7623105).length < 2 ^ (prefixWord ++ tailWord_7623105).sum := by decide
  have hdescent : baseEnd_7623105 < baseStart_7623105 := by decide
  rcases family_descends (prefixWord ++ tailWord_7623105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7623130 : List Nat := [3, 1, 1, 2, 3, 1, 1, 3, 1, 1, 6]
def baseStart_7623130 : Nat := 118140960795 + 7623130 * 2 ^ 59
def prefixEnd_7623130 : Nat := 4983230072969 + 3 ^ 40 * 7623130 * 2
def baseEnd_7623130 : Nat := 3914329781708864702516869

theorem tailTrace_7623130 : CollatzResearch.WordTrace tailWord_7623130 prefixEnd_7623130 3914329781708864702516869 := by
  unfold tailWord_7623130
  simp only [CollatzResearch.WordTrace]
  refine ⟨69509598218177352949352711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 185358928581806274531607229 69509598218177352949352711)
  ·
    refine ⟨104264397327266029424029067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69509598218177352949352711 104264397327266029424029067)
    ·
      refine ⟨156396595990899044136043601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104264397327266029424029067 156396595990899044136043601)
      ·
        refine ⟨117297446993174283102032701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 156396595990899044136043601 117297446993174283102032701)
        ·
          refine ⟨43986542622440356163262263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 117297446993174283102032701 43986542622440356163262263)
          ·
            refine ⟨65979813933660534244893395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43986542622440356163262263 65979813933660534244893395)
            ·
              refine ⟨98969720900490801367340093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65979813933660534244893395 98969720900490801367340093)
              ·
                refine ⟨37113645337684050512752535, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 98969720900490801367340093 37113645337684050512752535)
                ·
                  refine ⟨55670468006526075769128803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37113645337684050512752535 55670468006526075769128803)
                  ·
                    refine ⟨83505702009789113653693205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 55670468006526075769128803 83505702009789113653693205)
                    ·
                      refine ⟨3914329781708864702516869, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 83505702009789113653693205 3914329781708864702516869)
                      ·
                        rfl

theorem cell23_7623130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 1, 3, 1, 1, 6].length) (baseStart_7623130 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7623130 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7623130 prefixEnd_7623130 := by exact prefixLift 7623130
  have htrace : WordTrace (prefixWord ++ tailWord_7623130) baseStart_7623130 baseEnd_7623130 := by
    simpa [prefixWord, tailWord_7623130, baseEnd_7623130] using wordTrace_append hprefix tailTrace_7623130
  have hstable : (prefixWord ++ tailWord_7623130).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7623130).length < 2 ^ (prefixWord ++ tailWord_7623130).sum := by decide
  have hdescent : baseEnd_7623130 < baseStart_7623130 := by decide
  rcases family_descends (prefixWord ++ tailWord_7623130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7623137 : List Nat := [1, 2, 3, 1, 2, 2, 3, 1, 3, 2, 3]
def baseStart_7623137 : Nat := 118140960795 + 7623137 * 2 ^ 59
def prefixEnd_7623137 : Nat := 4983230072969 + 3 ^ 40 * 7623137 * 2
def baseEnd_7623137 : Nat := 3914333376073446175129337

theorem tailTrace_7623137 : CollatzResearch.WordTrace tailWord_7623137 prefixEnd_7623137 3914333376073446175129337 := by
  unfold tailWord_7623137
  simp only [CollatzResearch.WordTrace]
  refine ⟨278038648183684051992915665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185359098789122701328610443 278038648183684051992915665)
  ·
    refine ⟨208528986137763038994686749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 278038648183684051992915665 208528986137763038994686749)
    ·
      refine ⟨78198369801661139623007531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 208528986137763038994686749 78198369801661139623007531)
      ·
        refine ⟨117297554702491709434511297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78198369801661139623007531 117297554702491709434511297)
        ·
          refine ⟨87973166026868782075883473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 117297554702491709434511297 87973166026868782075883473)
          ·
            refine ⟨65979874520151586556912605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 87973166026868782075883473 65979874520151586556912605)
            ·
              refine ⟨24742452945056844958842227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 65979874520151586556912605 24742452945056844958842227)
              ·
                refine ⟨37113679417585267438263341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24742452945056844958842227 37113679417585267438263341)
                ·
                  refine ⟨13917629781594475289348753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 37113679417585267438263341 13917629781594475289348753)
                  ·
                    refine ⟨10438222336195856467011565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13917629781594475289348753 10438222336195856467011565)
                    ·
                      refine ⟨3914333376073446175129337, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10438222336195856467011565 3914333376073446175129337)
                      ·
                        rfl

theorem cell23_7623137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 3, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 3, 1, 3, 2, 3].length) (baseStart_7623137 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7623137 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7623137 prefixEnd_7623137 := by exact prefixLift 7623137
  have htrace : WordTrace (prefixWord ++ tailWord_7623137) baseStart_7623137 baseEnd_7623137 := by
    simpa [prefixWord, tailWord_7623137, baseEnd_7623137] using wordTrace_append hprefix tailTrace_7623137
  have hstable : (prefixWord ++ tailWord_7623137).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7623137).length < 2 ^ (prefixWord ++ tailWord_7623137).sum := by decide
  have hdescent : baseEnd_7623137 < baseStart_7623137 := by decide
  rcases family_descends (prefixWord ++ tailWord_7623137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7623151 : List Nat := [1, 1, 2, 1, 4, 1, 1, 7, 1, 2, 2]
def baseStart_7623151 : Nat := 118140960795 + 7623151 * 2 ^ 59
def prefixEnd_7623151 : Nat := 4983230072969 + 3 ^ 40 * 7623151 * 2
def baseEnd_7623151 : Nat := 3914340564802609120354273

theorem tailTrace_7623151 : CollatzResearch.WordTrace tailWord_7623151 prefixEnd_7623151 3914340564802609120354273 := by
  unfold tailWord_7623151
  simp only [CollatzResearch.WordTrace]
  refine ⟨278039158805633332383925307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185359439203755554922616871 278039158805633332383925307)
  ·
    refine ⟨417058738208449998575887961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 278039158805633332383925307 417058738208449998575887961)
    ·
      refine ⟨312794053656337498931915971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 417058738208449998575887961 312794053656337498931915971)
      ·
        refine ⟨469191080484506248397873957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 312794053656337498931915971 469191080484506248397873957)
        ·
          refine ⟨87973327590844921574601367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 469191080484506248397873957 87973327590844921574601367)
          ·
            refine ⟨131959991386267382361902051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87973327590844921574601367 131959991386267382361902051)
            ·
              refine ⟨197939987079401073542853077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 131959991386267382361902051 197939987079401073542853077)
              ·
                refine ⟨4639218447173462661160619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 197939987079401073542853077 4639218447173462661160619)
                ·
                  refine ⟨6958827670760193991740929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4639218447173462661160619 6958827670760193991740929)
                  ·
                    refine ⟨5219120753070145493805697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6958827670760193991740929 5219120753070145493805697)
                    ·
                      refine ⟨3914340564802609120354273, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5219120753070145493805697 3914340564802609120354273)
                      ·
                        rfl

theorem cell23_7623151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 1, 7, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 1, 7, 1, 2, 2].length) (baseStart_7623151 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7623151 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7623151 prefixEnd_7623151 := by exact prefixLift 7623151
  have htrace : WordTrace (prefixWord ++ tailWord_7623151) baseStart_7623151 baseEnd_7623151 := by
    simpa [prefixWord, tailWord_7623151, baseEnd_7623151] using wordTrace_append hprefix tailTrace_7623151
  have hstable : (prefixWord ++ tailWord_7623151).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7623151).length < 2 ^ (prefixWord ++ tailWord_7623151).sum := by decide
  have hdescent : baseEnd_7623151 < baseStart_7623151 := by decide
  rcases family_descends (prefixWord ++ tailWord_7623151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7623157 : List Nat := [1, 3, 5, 1, 2, 11]
def baseStart_7623157 : Nat := 118140960795 + 7623157 * 2 ^ 59
def prefixEnd_7623157 : Nat := 4983230072969 + 3 ^ 40 * 7623157 * 2
def baseEnd_7623157 : Nat := 16108410064553646489215

theorem tailTrace_7623157 : CollatzResearch.WordTrace tailWord_7623157 prefixEnd_7623157 16108410064553646489215 := by
  unfold tailWord_7623157
  simp only [CollatzResearch.WordTrace]
  refine ⟨278039377643611595408643725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185359585095741063605762483 278039377643611595408643725)
  ·
    refine ⟨104264766616354348278241397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 278039377643611595408643725 104264766616354348278241397)
    ·
      refine ⟨9774821870283220151085131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 104264766616354348278241397 9774821870283220151085131)
      ·
        refine ⟨14662232805424830226627697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9774821870283220151085131 14662232805424830226627697)
        ·
          refine ⟨10996674604068622669970773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14662232805424830226627697 10996674604068622669970773)
          ·
            refine ⟨16108410064553646489215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 10996674604068622669970773 16108410064553646489215)
            ·
              rfl

theorem cell23_7623157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 2, 11].length) (baseStart_7623157 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7623157 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7623157 prefixEnd_7623157 := by exact prefixLift 7623157
  have htrace : WordTrace (prefixWord ++ tailWord_7623157) baseStart_7623157 baseEnd_7623157 := by
    simpa [prefixWord, tailWord_7623157, baseEnd_7623157] using wordTrace_append hprefix tailTrace_7623157
  have hstable : (prefixWord ++ tailWord_7623157).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7623157).length < 2 ^ (prefixWord ++ tailWord_7623157).sum := by decide
  have hdescent : baseEnd_7623157 < baseStart_7623157 := by decide
  rcases family_descends (prefixWord ++ tailWord_7623157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7623181 : List Nat := [1, 7, 1, 1, 1, 1, 1, 3, 1, 2, 4]
def baseStart_7623181 : Nat := 118140960795 + 7623181 * 2 ^ 59
def prefixEnd_7623181 : Nat := 4983230072969 + 3 ^ 40 * 7623181 * 2
def baseEnd_7623181 : Nat := 3914355969222244002979135

theorem tailTrace_7623181 : CollatzResearch.WordTrace tailWord_7623181 prefixEnd_7623181 3914355969222244002979135 := by
  unfold tailWord_7623181
  simp only [CollatzResearch.WordTrace]
  refine ⟨278040252995524647507517397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185360168663683098338344931 278040252995524647507517397)
  ·
    refine ⟨6516568429582608925957439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 278040252995524647507517397 6516568429582608925957439)
    ·
      refine ⟨9774852644373913388936159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6516568429582608925957439 9774852644373913388936159)
      ·
        refine ⟨14662278966560870083404239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9774852644373913388936159 14662278966560870083404239)
        ·
          refine ⟨21993418449841305125106359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14662278966560870083404239 21993418449841305125106359)
          ·
            refine ⟨32990127674761957687659539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21993418449841305125106359 32990127674761957687659539)
            ·
              refine ⟨49485191512142936531489309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32990127674761957687659539 49485191512142936531489309)
              ·
                refine ⟨18556946817053601199308491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 49485191512142936531489309 18556946817053601199308491)
                ·
                  refine ⟨27835420225580401798962737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18556946817053601199308491 27835420225580401798962737)
                  ·
                    refine ⟨20876565169185301349222053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27835420225580401798962737 20876565169185301349222053)
                    ·
                      refine ⟨3914355969222244002979135, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20876565169185301349222053 3914355969222244002979135)
                      ·
                        rfl

theorem cell23_7623181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 1, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 1, 1, 3, 1, 2, 4].length) (baseStart_7623181 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7623181 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7623181 prefixEnd_7623181 := by exact prefixLift 7623181
  have htrace : WordTrace (prefixWord ++ tailWord_7623181) baseStart_7623181 baseEnd_7623181 := by
    simpa [prefixWord, tailWord_7623181, baseEnd_7623181] using wordTrace_append hprefix tailTrace_7623181
  have hstable : (prefixWord ++ tailWord_7623181).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7623181).length < 2 ^ (prefixWord ++ tailWord_7623181).sum := by decide
  have hdescent : baseEnd_7623181 < baseStart_7623181 := by decide
  rcases family_descends (prefixWord ++ tailWord_7623181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7623194 : List Nat := [3, 1, 1, 3, 1, 1, 4, 1, 3, 3, 2]
def baseStart_7623194 : Nat := 118140960795 + 7623194 * 2 ^ 59
def prefixEnd_7623194 : Nat := 4983230072969 + 3 ^ 40 * 7623194 * 2
def baseEnd_7623194 : Nat := 3914362644470752452116575

theorem tailTrace_7623194 : CollatzResearch.WordTrace tailWord_7623194 prefixEnd_7623194 3914362644470752452116575 := by
  unfold tailWord_7623194
  simp only [CollatzResearch.WordTrace]
  refine ⟨69510181786119387681935159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 185360484762985033818493757 69510181786119387681935159)
  ·
    refine ⟨104265272679179081522902739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69510181786119387681935159 104265272679179081522902739)
    ·
      refine ⟨156397909018768622284354109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104265272679179081522902739 156397909018768622284354109)
      ·
        refine ⟨58649215882038233356632791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 156397909018768622284354109 58649215882038233356632791)
        ·
          refine ⟨87973823823057350034949187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58649215882038233356632791 87973823823057350034949187)
          ·
            refine ⟨131960735734586025052423781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87973823823057350034949187 131960735734586025052423781)
            ·
              refine ⟨24742637950234879697329459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 131960735734586025052423781 24742637950234879697329459)
              ·
                refine ⟨37113956925352319545994189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24742637950234879697329459 37113956925352319545994189)
                ·
                  refine ⟨13917733847007119829747821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 37113956925352319545994189 13917733847007119829747821)
                  ·
                    refine ⟨5219150192627669936155433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13917733847007119829747821 5219150192627669936155433)
                    ·
                      refine ⟨3914362644470752452116575, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5219150192627669936155433 3914362644470752452116575)
                      ·
                        rfl

theorem cell23_7623194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 4, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 4, 1, 3, 3, 2].length) (baseStart_7623194 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7623194 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7623194 prefixEnd_7623194 := by exact prefixLift 7623194
  have htrace : WordTrace (prefixWord ++ tailWord_7623194) baseStart_7623194 baseEnd_7623194 := by
    simpa [prefixWord, tailWord_7623194, baseEnd_7623194] using wordTrace_append hprefix tailTrace_7623194
  have hstable : (prefixWord ++ tailWord_7623194).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7623194).length < 2 ^ (prefixWord ++ tailWord_7623194).sum := by decide
  have hdescent : baseEnd_7623194 < baseStart_7623194 := by decide
  rcases family_descends (prefixWord ++ tailWord_7623194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7623237 : List Nat := [1, 3, 1, 1, 1, 5, 2, 1, 2, 2, 4]
def baseStart_7623237 : Nat := 118140960795 + 7623237 * 2 ^ 59
def prefixEnd_7623237 : Nat := 4983230072969 + 3 ^ 40 * 7623237 * 2
def baseEnd_7623237 : Nat := 3914384724138895783878877

theorem tailTrace_7623237 : CollatzResearch.WordTrace tailWord_7623237 prefixEnd_7623237 3914384724138895783878877 := by
  unfold tailWord_7623237
  simp only [CollatzResearch.WordTrace]
  refine ⟨278042295483321769071555965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185361530322214512714370643 278042295483321769071555965)
  ·
    refine ⟨104265860806245663401833487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 278042295483321769071555965 104265860806245663401833487)
    ·
      refine ⟨156398791209368495102750231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104265860806245663401833487 156398791209368495102750231)
      ·
        refine ⟨234598186814052742654125347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 156398791209368495102750231 234598186814052742654125347)
        ·
          refine ⟨351897280221079113981188021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 234598186814052742654125347 351897280221079113981188021)
          ·
            refine ⟨32990370020726166935736377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 351897280221079113981188021 32990370020726166935736377)
            ·
              refine ⟨24742777515544625201802283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32990370020726166935736377 24742777515544625201802283)
              ·
                refine ⟨37114166273316937802703425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24742777515544625201802283 37114166273316937802703425)
                ·
                  refine ⟨27835624704987703352027569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37114166273316937802703425 27835624704987703352027569)
                  ·
                    refine ⟨20876718528740777514020677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27835624704987703352027569 20876718528740777514020677)
                    ·
                      refine ⟨3914384724138895783878877, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20876718528740777514020677 3914384724138895783878877)
                      ·
                        rfl

theorem cell23_7623237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 5, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 5, 2, 1, 2, 2, 4].length) (baseStart_7623237 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7623237 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7623237 prefixEnd_7623237 := by exact prefixLift 7623237
  have htrace : WordTrace (prefixWord ++ tailWord_7623237) baseStart_7623237 baseEnd_7623237 := by
    simpa [prefixWord, tailWord_7623237, baseEnd_7623237] using wordTrace_append hprefix tailTrace_7623237
  have hstable : (prefixWord ++ tailWord_7623237).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7623237).length < 2 ^ (prefixWord ++ tailWord_7623237).sum := by decide
  have hdescent : baseEnd_7623237 < baseStart_7623237 := by decide
  rcases family_descends (prefixWord ++ tailWord_7623237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7623240 : List Nat := [2, 1, 3, 1, 1, 1, 1, 2, 1, 1, 9]
def baseStart_7623240 : Nat := 118140960795 + 7623240 * 2 ^ 59
def prefixEnd_7623240 : Nat := 4983230072969 + 3 ^ 40 * 7623240 * 2
def baseEnd_7623240 : Nat := 3914386264580859272141363

theorem tailTrace_7623240 : CollatzResearch.WordTrace tailWord_7623240 prefixEnd_7623240 3914386264580859272141363 := by
  unfold tailWord_7623240
  simp only [CollatzResearch.WordTrace]
  refine ⟨139021202451155450291957587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 185361603268207267055943449 139021202451155450291957587)
  ·
    refine ⟨208531803676733175437936381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139021202451155450291957587 208531803676733175437936381)
    ·
      refine ⟨78199426378774940789226143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 208531803676733175437936381 78199426378774940789226143)
      ·
        refine ⟨117299139568162411183839215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78199426378774940789226143 117299139568162411183839215)
        ·
          refine ⟨175948709352243616775758823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 117299139568162411183839215 175948709352243616775758823)
          ·
            refine ⟨263923064028365425163638235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 175948709352243616775758823 263923064028365425163638235)
            ·
              refine ⟨395884596042548137745457353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 263923064028365425163638235 395884596042548137745457353)
              ·
                refine ⟨296913447031911103309093015, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 395884596042548137745457353 296913447031911103309093015)
                ·
                  refine ⟨445370170547866654963639523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 296913447031911103309093015 445370170547866654963639523)
                  ·
                    refine ⟨668055255821799982445459285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 445370170547866654963639523 668055255821799982445459285)
                    ·
                      refine ⟨3914386264580859272141363, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 668055255821799982445459285 3914386264580859272141363)
                      ·
                        rfl

theorem cell23_7623240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 1, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 1, 2, 1, 1, 9].length) (baseStart_7623240 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7623240 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7623240 prefixEnd_7623240 := by exact prefixLift 7623240
  have htrace : WordTrace (prefixWord ++ tailWord_7623240) baseStart_7623240 baseEnd_7623240 := by
    simpa [prefixWord, tailWord_7623240, baseEnd_7623240] using wordTrace_append hprefix tailTrace_7623240
  have hstable : (prefixWord ++ tailWord_7623240).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7623240).length < 2 ^ (prefixWord ++ tailWord_7623240).sum := by decide
  have hdescent : baseEnd_7623240 < baseStart_7623240 := by decide
  rcases family_descends (prefixWord ++ tailWord_7623240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7623264 : List Nat := [2, 1, 1, 3, 2, 1, 5, 3, 5]
def baseStart_7623264 : Nat := 118140960795 + 7623264 * 2 ^ 59
def prefixEnd_7623264 : Nat := 4983230072969 + 3 ^ 40 * 7623264 * 2
def baseEnd_7623264 : Nat := 434933176457396353137917

theorem tailTrace_7623264 : CollatzResearch.WordTrace tailWord_7623264 prefixEnd_7623264 434933176457396353137917 := by
  unfold tailWord_7623264
  simp only [CollatzResearch.WordTrace]
  refine ⟨139021640127111976341394423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 185362186836149301788525897 139021640127111976341394423)
  ·
    refine ⟨208532460190667964512091635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139021640127111976341394423 208532460190667964512091635)
    ·
      refine ⟨312798690286001946768137453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 208532460190667964512091635 312798690286001946768137453)
      ·
        refine ⟨117299508857250730038051545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 312798690286001946768137453 117299508857250730038051545)
        ·
          refine ⟨87974631642938047528538659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 117299508857250730038051545 87974631642938047528538659)
          ·
            refine ⟨131961947464407071292807989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87974631642938047528538659 131961947464407071292807989)
            ·
              refine ⟨12371432574788162933700749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 131961947464407071292807989 12371432574788162933700749)
              ·
                refine ⟨4639287215545561100137781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12371432574788162933700749 4639287215545561100137781)
                ·
                  refine ⟨434933176457396353137917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4639287215545561100137781 434933176457396353137917)
                  ·
                    rfl

theorem cell23_7623264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 5, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 5, 3, 5].length) (baseStart_7623264 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7623264 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7623264 prefixEnd_7623264 := by exact prefixLift 7623264
  have htrace : WordTrace (prefixWord ++ tailWord_7623264) baseStart_7623264 baseEnd_7623264 := by
    simpa [prefixWord, tailWord_7623264, baseEnd_7623264] using wordTrace_append hprefix tailTrace_7623264
  have hstable : (prefixWord ++ tailWord_7623264).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7623264).length < 2 ^ (prefixWord ++ tailWord_7623264).sum := by decide
  have hdescent : baseEnd_7623264 < baseStart_7623264 := by decide
  rcases family_descends (prefixWord ++ tailWord_7623264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7623337 : List Nat := [1, 2, 1, 1, 1, 1, 2, 8, 6]
def baseStart_7623337 : Nat := 118140960795 + 7623337 * 2 ^ 59
def prefixEnd_7623337 : Nat := 4983230072969 + 3 ^ 40 * 7623337 * 2
def baseEnd_7623337 : Nat := 434937341356038376958713

theorem tailTrace_7623337 : CollatzResearch.WordTrace tailWord_7623337 prefixEnd_7623337 434937341356038376958713 := by
  unfold tailWord_7623337
  simp only [CollatzResearch.WordTrace]
  refine ⟨278045942782959486150196265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185363961855306324100130843 278045942782959486150196265)
  ·
    refine ⟨208534457087219614612647199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 278045942782959486150196265 208534457087219614612647199)
    ·
      refine ⟨312801685630829421918970799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 208534457087219614612647199 312801685630829421918970799)
      ·
        refine ⟨469202528446244132878456199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 312801685630829421918970799 469202528446244132878456199)
        ·
          refine ⟨703803792669366199317684299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 469202528446244132878456199 703803792669366199317684299)
          ·
            refine ⟨1055705689004049298976526449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 703803792669366199317684299 1055705689004049298976526449)
            ·
              refine ⟨791779266753036974232394837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1055705689004049298976526449 791779266753036974232394837)
              ·
                refine ⟨9278663282262152041785877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 791779266753036974232394837 9278663282262152041785877)
                ·
                  refine ⟨434937341356038376958713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9278663282262152041785877 434937341356038376958713)
                  ·
                    rfl

theorem cell23_7623337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 8, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 8, 6].length) (baseStart_7623337 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7623337 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7623337 prefixEnd_7623337 := by exact prefixLift 7623337
  have htrace : WordTrace (prefixWord ++ tailWord_7623337) baseStart_7623337 baseEnd_7623337 := by
    simpa [prefixWord, tailWord_7623337, baseEnd_7623337] using wordTrace_append hprefix tailTrace_7623337
  have hstable : (prefixWord ++ tailWord_7623337).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7623337).length < 2 ^ (prefixWord ++ tailWord_7623337).sum := by decide
  have hdescent : baseEnd_7623337 < baseStart_7623337 := by decide
  rcases family_descends (prefixWord ++ tailWord_7623337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7623388 : List Nat := [2, 2, 5, 1, 1, 3, 1, 2, 6]
def baseStart_7623388 : Nat := 118140960795 + 7623388 * 2 ^ 59
def prefixEnd_7623388 : Nat := 4983230072969 + 3 ^ 40 * 7623388 * 2
def baseEnd_7623388 : Nat := 434940251079747188121187

theorem tailTrace_7623388 : CollatzResearch.WordTrace tailWord_7623388 prefixEnd_7623388 434940251079747188121187 := by
  unfold tailWord_7623388
  simp only [CollatzResearch.WordTrace]
  refine ⟨139023901452887360930151409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 185365201937183147906868545 139023901452887360930151409)
  ·
    refine ⟨104267926089665520697613557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 139023901452887360930151409 104267926089665520697613557)
    ·
      refine ⟨9775118070906142565401271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 104267926089665520697613557 9775118070906142565401271)
      ·
        refine ⟨14662677106359213848101907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9775118070906142565401271 14662677106359213848101907)
        ·
          refine ⟨21994015659538820772152861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14662677106359213848101907 21994015659538820772152861)
          ·
            refine ⟨8247755872327057789557323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21994015659538820772152861 8247755872327057789557323)
            ·
              refine ⟨12371633808490586684335985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8247755872327057789557323 12371633808490586684335985)
              ·
                refine ⟨9278725356367940013251989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12371633808490586684335985 9278725356367940013251989)
                ·
                  refine ⟨434940251079747188121187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9278725356367940013251989 434940251079747188121187)
                  ·
                    rfl

theorem cell23_7623388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 3, 1, 2, 6].length) (baseStart_7623388 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7623388 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7623388 prefixEnd_7623388 := by exact prefixLift 7623388
  have htrace : WordTrace (prefixWord ++ tailWord_7623388) baseStart_7623388 baseEnd_7623388 := by
    simpa [prefixWord, tailWord_7623388, baseEnd_7623388] using wordTrace_append hprefix tailTrace_7623388
  have hstable : (prefixWord ++ tailWord_7623388).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7623388).length < 2 ^ (prefixWord ++ tailWord_7623388).sum := by decide
  have hdescent : baseEnd_7623388 < baseStart_7623388 := by decide
  rcases family_descends (prefixWord ++ tailWord_7623388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7623421 : List Nat := [1, 4, 1, 1, 1, 1, 6, 2, 1, 1, 4]
def baseStart_7623421 : Nat := 118140960795 + 7623421 * 2 ^ 59
def prefixEnd_7623421 : Nat := 4983230072969 + 3 ^ 40 * 7623421 * 2
def baseEnd_7623421 : Nat := 3914479204579323063978031

theorem tailTrace_7623421 : CollatzResearch.WordTrace tailWord_7623421 prefixEnd_7623421 3914479204579323063978031 := by
  unfold tailWord_7623421
  simp only [CollatzResearch.WordTrace]
  refine ⟨278049006514655168496254117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185366004343103445664169411 278049006514655168496254117)
  ·
    refine ⟨52134188721497844093047647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 278049006514655168496254117 52134188721497844093047647)
    ·
      refine ⟨78201283082246766139571471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52134188721497844093047647 78201283082246766139571471)
      ·
        refine ⟨117301924623370149209357207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78201283082246766139571471 117301924623370149209357207)
        ·
          refine ⟨175952886935055223814035811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 117301924623370149209357207 175952886935055223814035811)
          ·
            refine ⟨263929330402582835721053717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 175952886935055223814035811 263929330402582835721053717)
            ·
              refine ⟨12371687362621070424424393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 263929330402582835721053717 12371687362621070424424393)
              ·
                refine ⟨9278765521965802818318295, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12371687362621070424424393 9278765521965802818318295)
                ·
                  refine ⟨13918148282948704227477443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9278765521965802818318295 13918148282948704227477443)
                  ·
                    refine ⟨20877222424423056341216165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13918148282948704227477443 20877222424423056341216165)
                    ·
                      refine ⟨3914479204579323063978031, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20877222424423056341216165 3914479204579323063978031)
                      ·
                        rfl

theorem cell23_7623421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 6, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 6, 2, 1, 1, 4].length) (baseStart_7623421 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7623421 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7623421 prefixEnd_7623421 := by exact prefixLift 7623421
  have htrace : WordTrace (prefixWord ++ tailWord_7623421) baseStart_7623421 baseEnd_7623421 := by
    simpa [prefixWord, tailWord_7623421, baseEnd_7623421] using wordTrace_append hprefix tailTrace_7623421
  have hstable : (prefixWord ++ tailWord_7623421).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7623421).length < 2 ^ (prefixWord ++ tailWord_7623421).sum := by decide
  have hdescent : baseEnd_7623421 < baseStart_7623421 := by decide
  rcases family_descends (prefixWord ++ tailWord_7623421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7623431 : List Nat := [1, 1, 4, 4, 1, 1, 1, 2, 4, 4]
def baseStart_7623431 : Nat := 118140960795 + 7623431 * 2 ^ 59
def prefixEnd_7623431 : Nat := 4983230072969 + 3 ^ 40 * 7623431 * 2
def baseEnd_7623431 : Nat := 1304828113128622674950995

theorem tailTrace_7623431 : CollatzResearch.WordTrace tailWord_7623431 prefixEnd_7623431 1304828113128622674950995 := by
  unfold tailWord_7623431
  simp only [CollatzResearch.WordTrace]
  refine ⟨278049371244618940204118147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185366247496412626802745431 278049371244618940204118147)
  ·
    refine ⟨417074056866928410306177221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 278049371244618940204118147 417074056866928410306177221)
    ·
      refine ⟨78201385662549076932408229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 417074056866928410306177221 78201385662549076932408229)
      ·
        refine ⟨14662759811727951924826543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 78201385662549076932408229 14662759811727951924826543)
        ·
          refine ⟨21994139717591927887239815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14662759811727951924826543 21994139717591927887239815)
          ·
            refine ⟨32991209576387891830859723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21994139717591927887239815 32991209576387891830859723)
            ·
              refine ⟨49486814364581837746289585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32991209576387891830859723 49486814364581837746289585)
              ·
                refine ⟨37115110773436378309717189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49486814364581837746289585 37115110773436378309717189)
                ·
                  refine ⟨6959083270019320933071973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 37115110773436378309717189 6959083270019320933071973)
                  ·
                    refine ⟨1304828113128622674950995, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6959083270019320933071973 1304828113128622674950995)
                    ·
                      rfl

theorem cell23_7623431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 1, 1, 2, 4, 4].length) (baseStart_7623431 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7623431 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7623431 prefixEnd_7623431 := by exact prefixLift 7623431
  have htrace : WordTrace (prefixWord ++ tailWord_7623431) baseStart_7623431 baseEnd_7623431 := by
    simpa [prefixWord, tailWord_7623431, baseEnd_7623431] using wordTrace_append hprefix tailTrace_7623431
  have hstable : (prefixWord ++ tailWord_7623431).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7623431).length < 2 ^ (prefixWord ++ tailWord_7623431).sum := by decide
  have hdescent : baseEnd_7623431 < baseStart_7623431 := by decide
  rcases family_descends (prefixWord ++ tailWord_7623431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7623434 : List Nat := [3, 1, 2, 2, 1, 2, 2, 1, 3, 2, 4]
def baseStart_7623434 : Nat := 118140960795 + 7623434 * 2 ^ 59
def prefixEnd_7623434 : Nat := 4983230072969 + 3 ^ 40 * 7623434 * 2
def baseEnd_7623434 : Nat := 3914485879827831513115471

theorem tailTrace_7623434 : CollatzResearch.WordTrace tailWord_7623434 prefixEnd_7623434 3914485879827831513115471 := by
  unfold tailWord_7623434
  simp only [CollatzResearch.WordTrace]
  refine ⟨69512370165902017929119339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 185366320442405381144318237 69512370165902017929119339)
  ·
    refine ⟨104268555248853026893679009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69512370165902017929119339 104268555248853026893679009)
    ·
      refine ⟨78201416436639770170259257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 104268555248853026893679009 78201416436639770170259257)
      ·
        refine ⟨58651062327479827627694443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78201416436639770170259257 58651062327479827627694443)
        ·
          refine ⟨87976593491219741441541665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58651062327479827627694443 87976593491219741441541665)
          ·
            refine ⟨65982445118414806081156249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 87976593491219741441541665 65982445118414806081156249)
            ·
              refine ⟨49486833838811104560867187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 65982445118414806081156249 49486833838811104560867187)
              ·
                refine ⟨74230250758216656841300781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49486833838811104560867187 74230250758216656841300781)
                ·
                  refine ⟨27836344034331246315487793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 74230250758216656841300781 27836344034331246315487793)
                  ·
                    refine ⟨20877258025748434736615845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27836344034331246315487793 20877258025748434736615845)
                    ·
                      refine ⟨3914485879827831513115471, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20877258025748434736615845 3914485879827831513115471)
                      ·
                        rfl

theorem cell23_7623434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 2, 1, 3, 2, 4].length) (baseStart_7623434 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7623434 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7623434 prefixEnd_7623434 := by exact prefixLift 7623434
  have htrace : WordTrace (prefixWord ++ tailWord_7623434) baseStart_7623434 baseEnd_7623434 := by
    simpa [prefixWord, tailWord_7623434, baseEnd_7623434] using wordTrace_append hprefix tailTrace_7623434
  have hstable : (prefixWord ++ tailWord_7623434).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7623434).length < 2 ^ (prefixWord ++ tailWord_7623434).sum := by decide
  have hdescent : baseEnd_7623434 < baseStart_7623434 := by decide
  rcases family_descends (prefixWord ++ tailWord_7623434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7623441 : List Nat := [1, 2, 2, 1, 1, 3, 4, 3, 1, 2, 3]
def baseStart_7623441 : Nat := 118140960795 + 7623441 * 2 ^ 59
def prefixEnd_7623441 : Nat := 4983230072969 + 3 ^ 40 * 7623441 * 2
def baseEnd_7623441 : Nat := 3914489474192412985727939

theorem tailTrace_7623441 : CollatzResearch.WordTrace tailWord_7623441 prefixEnd_7623441 3914489474192412985727939 := by
  unfold tailWord_7623441
  simp only [CollatzResearch.WordTrace]
  refine ⟨278049735974582711911982177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185366490649721807941321451 278049735974582711911982177)
  ·
    refine ⟨208537301980937033933986633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 278049735974582711911982177 208537301980937033933986633)
    ·
      refine ⟨156402976485702775450489975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 208537301980937033933986633 156402976485702775450489975)
      ·
        refine ⟨234604464728554163175734963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 156402976485702775450489975 234604464728554163175734963)
        ·
          refine ⟨351906697092831244763602445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 234604464728554163175734963 351906697092831244763602445)
          ·
            refine ⟨131965011409811716786350917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 351906697092831244763602445 131965011409811716786350917)
            ·
              refine ⟨24743439639339696897440797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 131965011409811716786350917 24743439639339696897440797)
              ·
                refine ⟨9278789864752386336540299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24743439639339696897440797 9278789864752386336540299)
                ·
                  refine ⟨13918184797128579504810449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9278789864752386336540299 13918184797128579504810449)
                  ·
                    refine ⟨10438638597846434628607837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13918184797128579504810449 10438638597846434628607837)
                    ·
                      refine ⟨3914489474192412985727939, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10438638597846434628607837 3914489474192412985727939)
                      ·
                        rfl

theorem cell23_7623441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 2, 3].length) (baseStart_7623441 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7623441 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7623441 prefixEnd_7623441 := by exact prefixLift 7623441
  have htrace : WordTrace (prefixWord ++ tailWord_7623441) baseStart_7623441 baseEnd_7623441 := by
    simpa [prefixWord, tailWord_7623441, baseEnd_7623441] using wordTrace_append hprefix tailTrace_7623441
  have hstable : (prefixWord ++ tailWord_7623441).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7623441).length < 2 ^ (prefixWord ++ tailWord_7623441).sum := by decide
  have hdescent : baseEnd_7623441 < baseStart_7623441 := by decide
  rcases family_descends (prefixWord ++ tailWord_7623441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7623455 : List Nat := [1, 1, 2, 4, 2, 4, 1, 1, 3, 2, 2]
def baseStart_7623455 : Nat := 118140960795 + 7623455 * 2 ^ 59
def prefixEnd_7623455 : Nat := 4983230072969 + 3 ^ 40 * 7623455 * 2
def baseEnd_7623455 : Nat := 3914496662921575930952875

theorem tailTrace_7623455 : CollatzResearch.WordTrace tailWord_7623455 prefixEnd_7623455 3914496662921575930952875 := by
  unfold tailWord_7623455
  simp only [CollatzResearch.WordTrace]
  refine ⟨278050246596531992302991819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185366831064354661535327879 278050246596531992302991819)
  ·
    refine ⟨417075369894797988454487729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 278050246596531992302991819 417075369894797988454487729)
    ·
      refine ⟨312806527421098491340865797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 417075369894797988454487729 312806527421098491340865797)
      ·
        refine ⟨58651223891455967126412337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 312806527421098491340865797 58651223891455967126412337)
        ·
          refine ⟨43988417918591975344809253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58651223891455967126412337 43988417918591975344809253)
          ·
            refine ⟨8247828359735995377151735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 43988417918591975344809253 8247828359735995377151735)
            ·
              refine ⟨12371742539603993065727603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8247828359735995377151735 12371742539603993065727603)
              ·
                refine ⟨18557613809405989598591405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12371742539603993065727603 18557613809405989598591405)
                ·
                  refine ⟨6959105178527246099471777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18557613809405989598591405 6959105178527246099471777)
                  ·
                    refine ⟨5219328883895434574603833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6959105178527246099471777 5219328883895434574603833)
                    ·
                      refine ⟨3914496662921575930952875, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5219328883895434574603833 3914496662921575930952875)
                      ·
                        rfl

theorem cell23_7623455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 4, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 4, 1, 1, 3, 2, 2].length) (baseStart_7623455 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7623455 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7623455 prefixEnd_7623455 := by exact prefixLift 7623455
  have htrace : WordTrace (prefixWord ++ tailWord_7623455) baseStart_7623455 baseEnd_7623455 := by
    simpa [prefixWord, tailWord_7623455, baseEnd_7623455] using wordTrace_append hprefix tailTrace_7623455
  have hstable : (prefixWord ++ tailWord_7623455).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7623455).length < 2 ^ (prefixWord ++ tailWord_7623455).sum := by decide
  have hdescent : baseEnd_7623455 < baseStart_7623455 := by decide
  rcases family_descends (prefixWord ++ tailWord_7623455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7623464 : List Nat := [2, 1, 5, 1, 1, 1, 1, 1, 2, 2, 6]
def baseStart_7623464 : Nat := 118140960795 + 7623464 * 2 ^ 59
def prefixEnd_7623464 : Nat := 4983230072969 + 3 ^ 40 * 7623464 * 2
def baseEnd_7623464 : Nat := 3914501284247466395740333

theorem tailTrace_7623464 : CollatzResearch.WordTrace tailWord_7623464 prefixEnd_7623464 3914501284247466395740333 := by
  unfold tailWord_7623464
  simp only [CollatzResearch.WordTrace]
  refine ⟨139025287426749693420034723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 185367049902332924560046297 139025287426749693420034723)
  ·
    refine ⟨208537931140124540130052085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139025287426749693420034723 208537931140124540130052085)
    ·
      refine ⟨19550431044386675637192383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 208537931140124540130052085 19550431044386675637192383)
      ·
        refine ⟨29325646566580013455788575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19550431044386675637192383 29325646566580013455788575)
        ·
          refine ⟨43988469849870020183682863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29325646566580013455788575 43988469849870020183682863)
          ·
            refine ⟨65982704774805030275524295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43988469849870020183682863 65982704774805030275524295)
            ·
              refine ⟨98974057162207545413286443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65982704774805030275524295 98974057162207545413286443)
              ·
                refine ⟨148461085743311318119929665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 98974057162207545413286443 148461085743311318119929665)
                ·
                  refine ⟨111345814307483488589947249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 148461085743311318119929665 111345814307483488589947249)
                  ·
                    refine ⟨83509360730612616442460437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 111345814307483488589947249 83509360730612616442460437)
                    ·
                      refine ⟨3914501284247466395740333, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 83509360730612616442460437 3914501284247466395740333)
                      ·
                        rfl

theorem cell23_7623464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 1, 1, 2, 2, 6].length) (baseStart_7623464 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7623464 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7623464 prefixEnd_7623464 := by exact prefixLift 7623464
  have htrace : WordTrace (prefixWord ++ tailWord_7623464) baseStart_7623464 baseEnd_7623464 := by
    simpa [prefixWord, tailWord_7623464, baseEnd_7623464] using wordTrace_append hprefix tailTrace_7623464
  have hstable : (prefixWord ++ tailWord_7623464).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7623464).length < 2 ^ (prefixWord ++ tailWord_7623464).sum := by decide
  have hdescent : baseEnd_7623464 < baseStart_7623464 := by decide
  rcases family_descends (prefixWord ++ tailWord_7623464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7623492 : List Nat := [2, 3, 4, 2, 2, 1, 1, 1, 1, 1, 5]
def baseStart_7623492 : Nat := 118140960795 + 7623492 * 2 ^ 59
def prefixEnd_7623492 : Nat := 4983230072969 + 3 ^ 40 * 7623492 * 2
def baseEnd_7623492 : Nat := 3914515661705792286190205

theorem tailTrace_7623492 : CollatzResearch.WordTrace tailWord_7623492 prefixEnd_7623492 3914515661705792286190205 := by
  unfold tailWord_7623492
  simp only [CollatzResearch.WordTrace]
  refine ⟨139025798048698973811044365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 185367730731598631748059153 139025798048698973811044365)
  ·
    refine ⟨52134674268262115179141637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 139025798048698973811044365 52134674268262115179141637)
    ·
      refine ⟨9775251425299146596089057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 52134674268262115179141637 9775251425299146596089057)
      ·
        refine ⟨7331438568974359947066793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9775251425299146596089057 7331438568974359947066793)
        ·
          refine ⟨5498578926730769960300095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7331438568974359947066793 5498578926730769960300095)
          ·
            refine ⟨8247868390096154940450143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5498578926730769960300095 8247868390096154940450143)
            ·
              refine ⟨12371802585144232410675215, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8247868390096154940450143 12371802585144232410675215)
              ·
                refine ⟨18557703877716348616012823, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12371802585144232410675215 18557703877716348616012823)
                ·
                  refine ⟨27836555816574522924019235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18557703877716348616012823 27836555816574522924019235)
                  ·
                    refine ⟨41754833724861784386028853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27836555816574522924019235 41754833724861784386028853)
                    ·
                      refine ⟨3914515661705792286190205, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41754833724861784386028853 3914515661705792286190205)
                      ·
                        rfl

theorem cell23_7623492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 2, 1, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 2, 1, 1, 1, 1, 1, 5].length) (baseStart_7623492 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7623492 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7623492 prefixEnd_7623492 := by exact prefixLift 7623492
  have htrace : WordTrace (prefixWord ++ tailWord_7623492) baseStart_7623492 baseEnd_7623492 := by
    simpa [prefixWord, tailWord_7623492, baseEnd_7623492] using wordTrace_append hprefix tailTrace_7623492
  have hstable : (prefixWord ++ tailWord_7623492).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7623492).length < 2 ^ (prefixWord ++ tailWord_7623492).sum := by decide
  have hdescent : baseEnd_7623492 < baseStart_7623492 := by decide
  rcases family_descends (prefixWord ++ tailWord_7623492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7623505 : List Nat := [1, 2, 2, 1, 6, 1, 2, 2, 2, 1, 3]
def baseStart_7623505 : Nat := 118140960795 + 7623505 * 2 ^ 59
def prefixEnd_7623505 : Nat := 4983230072969 + 3 ^ 40 * 7623505 * 2
def baseEnd_7623505 : Nat := 3914522336954300735327645

theorem tailTrace_7623505 : CollatzResearch.WordTrace tailWord_7623505 prefixEnd_7623505 3914522336954300735327645 := by
  unfold tailWord_7623505
  simp only [CollatzResearch.WordTrace]
  refine ⟨278052070246350850842311969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185368046830900567228207979 278052070246350850842311969)
  ·
    refine ⟨208539052684763138131733977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 278052070246350850842311969 208539052684763138131733977)
    ·
      refine ⟨156404289513572353598800483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 208539052684763138131733977 156404289513572353598800483)
      ·
        refine ⟨234606434270358530398200725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 156404289513572353598800483 234606434270358530398200725)
        ·
          refine ⟨10997176606423056112415659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 234606434270358530398200725 10997176606423056112415659)
          ·
            refine ⟨16495764909634584168623489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10997176606423056112415659 16495764909634584168623489)
            ·
              refine ⟨12371823682225938126467617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16495764909634584168623489 12371823682225938126467617)
              ·
                refine ⟨9278867761669453594850713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12371823682225938126467617 9278867761669453594850713)
                ·
                  refine ⟨6959150821252090196138035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9278867761669453594850713 6959150821252090196138035)
                  ·
                    refine ⟨10438726231878135294207053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6959150821252090196138035 10438726231878135294207053)
                    ·
                      refine ⟨3914522336954300735327645, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10438726231878135294207053 3914522336954300735327645)
                      ·
                        rfl

theorem cell23_7623505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 6, 1, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 6, 1, 2, 2, 2, 1, 3].length) (baseStart_7623505 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7623505 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7623505 prefixEnd_7623505 := by exact prefixLift 7623505
  have htrace : WordTrace (prefixWord ++ tailWord_7623505) baseStart_7623505 baseEnd_7623505 := by
    simpa [prefixWord, tailWord_7623505, baseEnd_7623505] using wordTrace_append hprefix tailTrace_7623505
  have hstable : (prefixWord ++ tailWord_7623505).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7623505).length < 2 ^ (prefixWord ++ tailWord_7623505).sum := by decide
  have hdescent : baseEnd_7623505 < baseStart_7623505 := by decide
  rcases family_descends (prefixWord ++ tailWord_7623505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7623528 : List Nat := [2, 1, 4, 2, 1, 2, 1, 3, 1, 4, 2]
def baseStart_7623528 : Nat := 118140960795 + 7623528 * 2 ^ 59
def prefixEnd_7623528 : Nat := 4983230072969 + 3 ^ 40 * 7623528 * 2
def baseEnd_7623528 : Nat := 3914534147009354145340039

theorem tailTrace_7623528 : CollatzResearch.WordTrace tailWord_7623528 prefixEnd_7623528 3914534147009354145340039 := by
  unfold tailWord_7623528
  simp only [CollatzResearch.WordTrace]
  refine ⟨139026454562633762885199619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 185368606083511683846932825 139026454562633762885199619)
  ·
    refine ⟨208539681843950644327799429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139026454562633762885199619 208539681843950644327799429)
    ·
      refine ⟨39101190345740745811462393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 208539681843950644327799429 39101190345740745811462393)
      ·
        refine ⟨29325892759305559358596795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39101190345740745811462393 29325892759305559358596795)
        ·
          refine ⟨43988839138958339037895193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29325892759305559358596795 43988839138958339037895193)
          ·
            refine ⟨32991629354218754278421395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43988839138958339037895193 32991629354218754278421395)
            ·
              refine ⟨49487444031328131417632093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32991629354218754278421395 49487444031328131417632093)
              ·
                refine ⟨18557791511748049281612035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 49487444031328131417632093 18557791511748049281612035)
                ·
                  refine ⟨27836687267622073922418053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18557791511748049281612035 27836687267622073922418053)
                  ·
                    refine ⟨5219378862679138860453385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 27836687267622073922418053 5219378862679138860453385)
                    ·
                      refine ⟨3914534147009354145340039, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5219378862679138860453385 3914534147009354145340039)
                      ·
                        rfl

theorem cell23_7623528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 2, 1, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 2, 1, 3, 1, 4, 2].length) (baseStart_7623528 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7623528 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7623528 prefixEnd_7623528 := by exact prefixLift 7623528
  have htrace : WordTrace (prefixWord ++ tailWord_7623528) baseStart_7623528 baseEnd_7623528 := by
    simpa [prefixWord, tailWord_7623528, baseEnd_7623528] using wordTrace_append hprefix tailTrace_7623528
  have hstable : (prefixWord ++ tailWord_7623528).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7623528).length < 2 ^ (prefixWord ++ tailWord_7623528).sum := by decide
  have hdescent : baseEnd_7623528 < baseStart_7623528 := by decide
  rcases family_descends (prefixWord ++ tailWord_7623528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7623551 : List Nat := [1, 1, 2, 2, 1, 1, 5, 5, 5]
def baseStart_7623551 : Nat := 118140960795 + 7623551 * 2 ^ 59
def prefixEnd_7623551 : Nat := 4983230072969 + 3 ^ 40 * 7623551 * 2
def baseEnd_7623551 : Nat := 434949550784934172816937

theorem tailTrace_7623551 : CollatzResearch.WordTrace tailWord_7623551 prefixEnd_7623551 434949550784934172816937 := by
  unfold tailWord_7623551
  simp only [CollatzResearch.WordTrace]
  refine ⟨278053748004184200698486507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185369165336122800465657671 278053748004184200698486507)
  ·
    refine ⟨417080622006276301047729761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 278053748004184200698486507 417080622006276301047729761)
    ·
      refine ⟨312810466504707225785797321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 417080622006276301047729761 312810466504707225785797321)
      ·
        refine ⟨234607849878530419339347991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 312810466504707225785797321 234607849878530419339347991)
        ·
          refine ⟨351911774817795629009021987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 234607849878530419339347991 351911774817795629009021987)
          ·
            refine ⟨527867662226693443513532981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 351911774817795629009021987 527867662226693443513532981)
            ·
              refine ⟨49487593333752510329393717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 527867662226693443513532981 49487593333752510329393717)
              ·
                refine ⟨4639461875039297843380661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 49487593333752510329393717 4639461875039297843380661)
                ·
                  refine ⟨434949550784934172816937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4639461875039297843380661 434949550784934172816937)
                  ·
                    rfl

theorem cell23_7623551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 5, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 5, 5, 5].length) (baseStart_7623551 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7623551 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7623551 prefixEnd_7623551 := by exact prefixLift 7623551
  have htrace : WordTrace (prefixWord ++ tailWord_7623551) baseStart_7623551 baseEnd_7623551 := by
    simpa [prefixWord, tailWord_7623551, baseEnd_7623551] using wordTrace_append hprefix tailTrace_7623551
  have hstable : (prefixWord ++ tailWord_7623551).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7623551).length < 2 ^ (prefixWord ++ tailWord_7623551).sum := by decide
  have hdescent : baseEnd_7623551 < baseStart_7623551 := by decide
  rcases family_descends (prefixWord ++ tailWord_7623551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7623561 : List Nat := [1, 2, 1, 1, 5, 2, 1, 2, 2, 3, 3]
def baseStart_7623561 : Nat := 118140960795 + 7623561 * 2 ^ 59
def prefixEnd_7623561 : Nat := 4983230072969 + 3 ^ 40 * 7623561 * 2
def baseEnd_7623561 : Nat := 3914551091870952516227387

theorem tailTrace_7623561 : CollatzResearch.WordTrace tailWord_7623561 prefixEnd_7623561 3914551091870952516227387 := by
  unfold tailWord_7623561
  simp only [CollatzResearch.WordTrace]
  refine ⟨278054112734147972406350537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185369408489431981604233691 278054112734147972406350537)
  ·
    refine ⟨208540584550610979304762903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 278054112734147972406350537 208540584550610979304762903)
    ·
      refine ⟨312810876825916468957144355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 208540584550610979304762903 312810876825916468957144355)
      ·
        refine ⟨469216315238874703435716533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 312810876825916468957144355 469216315238874703435716533)
        ·
          refine ⟨43989029553644503447098425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 469216315238874703435716533 43989029553644503447098425)
          ·
            refine ⟨32991772165233377585323819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43989029553644503447098425 32991772165233377585323819)
            ·
              refine ⟨49487658247850066377985729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32991772165233377585323819 49487658247850066377985729)
              ·
                refine ⟨37115743685887549783489297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49487658247850066377985729 37115743685887549783489297)
                ·
                  refine ⟨27836807764415662337616973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37115743685887549783489297 27836807764415662337616973)
                  ·
                    refine ⟨10438802911655873376606365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27836807764415662337616973 10438802911655873376606365)
                    ·
                      refine ⟨3914551091870952516227387, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10438802911655873376606365 3914551091870952516227387)
                      ·
                        rfl

theorem cell23_7623561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 2, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 2, 1, 2, 2, 3, 3].length) (baseStart_7623561 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7623561 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7623561 prefixEnd_7623561 := by exact prefixLift 7623561
  have htrace : WordTrace (prefixWord ++ tailWord_7623561) baseStart_7623561 baseEnd_7623561 := by
    simpa [prefixWord, tailWord_7623561, baseEnd_7623561] using wordTrace_append hprefix tailTrace_7623561
  have hstable : (prefixWord ++ tailWord_7623561).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7623561).length < 2 ^ (prefixWord ++ tailWord_7623561).sum := by decide
  have hdescent : baseEnd_7623561 < baseStart_7623561 := by decide
  rcases family_descends (prefixWord ++ tailWord_7623561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7623562 : List Nat := [3, 1, 2, 4, 1, 1, 3, 2, 2, 2, 2]
def baseStart_7623562 : Nat := 118140960795 + 7623562 * 2 ^ 59
def prefixEnd_7623562 : Nat := 4983230072969 + 3 ^ 40 * 7623562 * 2
def baseEnd_7623562 : Nat := 3914551605351607012314883

theorem tailTrace_7623562 : CollatzResearch.WordTrace tailWord_7623562 prefixEnd_7623562 3914551605351607012314883 := by
  unfold tailWord_7623562
  simp only [CollatzResearch.WordTrace]
  refine ⟨69513537301786087394284235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 185369432804762899718091293 69513537301786087394284235)
  ·
    refine ⟨104270305952679131091426353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69513537301786087394284235 104270305952679131091426353)
    ·
      refine ⟨78202729464509348318569765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 104270305952679131091426353 78202729464509348318569765)
      ·
        refine ⟨14663011774595502809731831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 78202729464509348318569765 14663011774595502809731831)
        ·
          refine ⟨21994517661893254214597747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14663011774595502809731831 21994517661893254214597747)
          ·
            refine ⟨32991776492839881321896621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21994517661893254214597747 32991776492839881321896621)
            ·
              refine ⟨12371916184814955495711233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32991776492839881321896621 12371916184814955495711233)
              ·
                refine ⟨9278937138611216621783425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12371916184814955495711233 9278937138611216621783425)
                ·
                  refine ⟨6959202853958412466337569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9278937138611216621783425 6959202853958412466337569)
                  ·
                    refine ⟨5219402140468809349753177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6959202853958412466337569 5219402140468809349753177)
                    ·
                      refine ⟨3914551605351607012314883, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5219402140468809349753177 3914551605351607012314883)
                      ·
                        rfl

theorem cell23_7623562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 1, 3, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 1, 3, 2, 2, 2, 2].length) (baseStart_7623562 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7623562 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7623562 prefixEnd_7623562 := by exact prefixLift 7623562
  have htrace : WordTrace (prefixWord ++ tailWord_7623562) baseStart_7623562 baseEnd_7623562 := by
    simpa [prefixWord, tailWord_7623562, baseEnd_7623562] using wordTrace_append hprefix tailTrace_7623562
  have hstable : (prefixWord ++ tailWord_7623562).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7623562).length < 2 ^ (prefixWord ++ tailWord_7623562).sum := by decide
  have hdescent : baseEnd_7623562 < baseStart_7623562 := by decide
  rcases family_descends (prefixWord ++ tailWord_7623562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7623571 : List Nat := [1, 1, 1, 2, 1, 2, 1, 5, 2, 5, 2]
def baseStart_7623571 : Nat := 118140960795 + 7623571 * 2 ^ 59
def prefixEnd_7623571 : Nat := 4983230072969 + 3 ^ 40 * 7623571 * 2
def baseEnd_7623571 : Nat := 3914556226677497477102341

theorem tailTrace_7623571 : CollatzResearch.WordTrace tailWord_7623571 prefixEnd_7623571 3914556226677497477102341 := by
  unfold tailWord_7623571
  simp only [CollatzResearch.WordTrace]
  refine ⟨278054477464111744114214567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185369651642741162742809711 278054477464111744114214567)
  ·
    refine ⟨417081716196167616171321851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 278054477464111744114214567 417081716196167616171321851)
    ·
      refine ⟨625622574294251424256982777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 417081716196167616171321851 625622574294251424256982777)
      ·
        refine ⟨469216930720688568192737083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 625622574294251424256982777 469216930720688568192737083)
        ·
          refine ⟨703825396081032852289105625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 469216930720688568192737083 703825396081032852289105625)
          ·
            refine ⟨527869047060774639216829219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 703825396081032852289105625 527869047060774639216829219)
            ·
              refine ⟨791803570591161958825243829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 527869047060774639216829219 791803570591161958825243829)
              ·
                refine ⟨74231584742921433639866609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 791803570591161958825243829 74231584742921433639866609)
                ·
                  refine ⟨55673688557191075229899957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 74231584742921433639866609 55673688557191075229899957)
                  ·
                    refine ⟨5219408302236663302803121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 55673688557191075229899957 5219408302236663302803121)
                    ·
                      refine ⟨3914556226677497477102341, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5219408302236663302803121 3914556226677497477102341)
                      ·
                        rfl

theorem cell23_7623571_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 5, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 5, 2, 5, 2].length) (baseStart_7623571 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7623571 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7623571 prefixEnd_7623571 := by exact prefixLift 7623571
  have htrace : WordTrace (prefixWord ++ tailWord_7623571) baseStart_7623571 baseEnd_7623571 := by
    simpa [prefixWord, tailWord_7623571, baseEnd_7623571] using wordTrace_append hprefix tailTrace_7623571
  have hstable : (prefixWord ++ tailWord_7623571).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7623571).length < 2 ^ (prefixWord ++ tailWord_7623571).sum := by decide
  have hdescent : baseEnd_7623571 < baseStart_7623571 := by decide
  rcases family_descends (prefixWord ++ tailWord_7623571) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7623655 : List Nat := [1, 1, 5, 2, 2, 2, 2, 1, 2, 2, 3]
def baseStart_7623655 : Nat := 118140960795 + 7623655 * 2 ^ 59
def prefixEnd_7623655 : Nat := 4983230072969 + 3 ^ 40 * 7623655 * 2
def baseEnd_7623655 : Nat := 3914599359052475148451955

theorem tailTrace_7623655 : CollatzResearch.WordTrace tailWord_7623655 prefixEnd_7623655 3914599359052475148451955 := by
  unfold tailWord_7623655
  simp only [CollatzResearch.WordTrace]
  refine ⟨278057541195807426460272419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185371694130538284306848279 278057541195807426460272419)
  ·
    refine ⟨417086311793711139690408629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 278057541195807426460272419 417086311793711139690408629)
    ·
      refine ⟨39101841730660419345975809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 417086311793711139690408629 39101841730660419345975809)
      ·
        refine ⟨29326381297995314509481857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39101841730660419345975809 29326381297995314509481857)
        ·
          refine ⟨21994785973496485882111393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29326381297995314509481857 21994785973496485882111393)
          ·
            refine ⟨16496089480122364411583545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21994785973496485882111393 16496089480122364411583545)
            ·
              refine ⟨12372067110091773308687659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16496089480122364411583545 12372067110091773308687659)
              ·
                refine ⟨18558100665137659963031489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12372067110091773308687659 18558100665137659963031489)
                ·
                  refine ⟨13918575498853244972273617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18558100665137659963031489 13918575498853244972273617)
                  ·
                    refine ⟨10438931624139933729205213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13918575498853244972273617 10438931624139933729205213)
                    ·
                      refine ⟨3914599359052475148451955, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10438931624139933729205213 3914599359052475148451955)
                      ·
                        rfl

theorem cell23_7623655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 2, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 2, 2, 1, 2, 2, 3].length) (baseStart_7623655 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7623655 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7623655 prefixEnd_7623655 := by exact prefixLift 7623655
  have htrace : WordTrace (prefixWord ++ tailWord_7623655) baseStart_7623655 baseEnd_7623655 := by
    simpa [prefixWord, tailWord_7623655, baseEnd_7623655] using wordTrace_append hprefix tailTrace_7623655
  have hstable : (prefixWord ++ tailWord_7623655).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7623655).length < 2 ^ (prefixWord ++ tailWord_7623655).sum := by decide
  have hdescent : baseEnd_7623655 < baseStart_7623655 := by decide
  rcases family_descends (prefixWord ++ tailWord_7623655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7623712 : List Nat := [2, 1, 1, 7, 1, 1, 1, 1, 1, 5, 2]
def baseStart_7623712 : Nat := 118140960795 + 7623712 * 2 ^ 59
def prefixEnd_7623712 : Nat := 4983230072969 + 3 ^ 40 * 7623712 * 2
def baseEnd_7623712 : Nat := 3914628627449781425439193

theorem tailTrace_7623712 : CollatzResearch.WordTrace tailWord_7623712 prefixEnd_7623712 3914628627449781425439193 := by
  unfold tailWord_7623712
  simp only [CollatzResearch.WordTrace]
  refine ⟨139029810078300462597548695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 185373080104400616796731593 139029810078300462597548695)
  ·
    refine ⟨208544715117450693896323043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139029810078300462597548695 208544715117450693896323043)
    ·
      refine ⟨312817072676176040844484565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 208544715117450693896323043 312817072676176040844484565)
      ·
        refine ⟨7331650140847875957292607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 312817072676176040844484565 7331650140847875957292607)
        ·
          refine ⟨10997475211271813935938911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7331650140847875957292607 10997475211271813935938911)
          ·
            refine ⟨16496212816907720903908367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10997475211271813935938911 16496212816907720903908367)
            ·
              refine ⟨24744319225361581355862551, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16496212816907720903908367 24744319225361581355862551)
              ·
                refine ⟨37116478838042372033793827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24744319225361581355862551 37116478838042372033793827)
                ·
                  refine ⟨55674718257063558050690741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37116478838042372033793827 55674718257063558050690741)
                  ·
                    refine ⟨5219504836599708567252257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 55674718257063558050690741 5219504836599708567252257)
                    ·
                      refine ⟨3914628627449781425439193, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5219504836599708567252257 3914628627449781425439193)
                      ·
                        rfl

theorem cell23_7623712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 1, 1, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 1, 1, 1, 1, 1, 5, 2].length) (baseStart_7623712 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7623712 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7623712 prefixEnd_7623712 := by exact prefixLift 7623712
  have htrace : WordTrace (prefixWord ++ tailWord_7623712) baseStart_7623712 baseEnd_7623712 := by
    simpa [prefixWord, tailWord_7623712, baseEnd_7623712] using wordTrace_append hprefix tailTrace_7623712
  have hstable : (prefixWord ++ tailWord_7623712).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7623712).length < 2 ^ (prefixWord ++ tailWord_7623712).sum := by decide
  have hdescent : baseEnd_7623712 < baseStart_7623712 := by decide
  rcases family_descends (prefixWord ++ tailWord_7623712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7623719 : List Nat := [1, 1, 7, 1, 1, 1, 1, 5, 1, 1, 3]
def baseStart_7623719 : Nat := 118140960795 + 7623719 * 2 ^ 59
def prefixEnd_7623719 : Nat := 4983230072969 + 3 ^ 40 * 7623719 * 2
def baseEnd_7623719 : Nat := 3914632221814362898051661

theorem tailTrace_7623719 : CollatzResearch.WordTrace tailWord_7623719 prefixEnd_7623719 3914632221814362898051661 := by
  unfold tailWord_7623719
  simp only [CollatzResearch.WordTrace]
  refine ⟨278059875467575565390602211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185373250311717043593734807 278059875467575565390602211)
  ·
    refine ⟨417089813201363348085903317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 278059875467575565390602211 417089813201363348085903317)
    ·
      refine ⟨9775542496906953470763359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 417089813201363348085903317 9775542496906953470763359)
      ·
        refine ⟨14663313745360430206145039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9775542496906953470763359 14663313745360430206145039)
        ·
          refine ⟨21994970618040645309217559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14663313745360430206145039 21994970618040645309217559)
          ·
            refine ⟨32992455927060967963826339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21994970618040645309217559 32992455927060967963826339)
            ·
              refine ⟨49488683890591451945739509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32992455927060967963826339 49488683890591451945739509)
              ·
                refine ⟨4639564114742948619913079, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 49488683890591451945739509 4639564114742948619913079)
                ·
                  refine ⟨6959346172114422929869619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4639564114742948619913079 6959346172114422929869619)
                  ·
                    refine ⟨10439019258171634394804429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6959346172114422929869619 10439019258171634394804429)
                    ·
                      refine ⟨3914632221814362898051661, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10439019258171634394804429 3914632221814362898051661)
                      ·
                        rfl

theorem cell23_7623719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 1, 1, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 1, 1, 5, 1, 1, 3].length) (baseStart_7623719 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7623719 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7623719 prefixEnd_7623719 := by exact prefixLift 7623719
  have htrace : WordTrace (prefixWord ++ tailWord_7623719) baseStart_7623719 baseEnd_7623719 := by
    simpa [prefixWord, tailWord_7623719, baseEnd_7623719] using wordTrace_append hprefix tailTrace_7623719
  have hstable : (prefixWord ++ tailWord_7623719).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7623719).length < 2 ^ (prefixWord ++ tailWord_7623719).sum := by decide
  have hdescent : baseEnd_7623719 < baseStart_7623719 := by decide
  rcases family_descends (prefixWord ++ tailWord_7623719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7623745 : List Nat := [1, 2, 5, 1, 3, 1, 1, 2, 1, 1, 5]
def baseStart_7623745 : Nat := 118140960795 + 7623745 * 2 ^ 59
def prefixEnd_7623745 : Nat := 4983230072969 + 3 ^ 40 * 7623745 * 2
def baseEnd_7623745 : Nat := 3914645572311379796326541

theorem tailTrace_7623745 : CollatzResearch.WordTrace tailWord_7623745 prefixEnd_7623745 3914645572311379796326541 := by
  unfold tailWord_7623745
  simp only [CollatzResearch.WordTrace]
  refine ⟨278060823765481371831048689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185373882510320914554032459 278060823765481371831048689)
  ·
    refine ⟨208545617824111028873286517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 278060823765481371831048689 208545617824111028873286517)
    ·
      refine ⟨19551151671010408956870611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 208545617824111028873286517 19551151671010408956870611)
      ·
        refine ⟨29326727506515613435305917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19551151671010408956870611 29326727506515613435305917)
        ·
          refine ⟨10997522814943355038239719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29326727506515613435305917 10997522814943355038239719)
          ·
            refine ⟨16496284222415032557359579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10997522814943355038239719 16496284222415032557359579)
            ·
              refine ⟨24744426333622548836039369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16496284222415032557359579 24744426333622548836039369)
              ·
                refine ⟨18558319750216911627029527, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24744426333622548836039369 18558319750216911627029527)
                ·
                  refine ⟨27837479625325367440544291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18558319750216911627029527 27837479625325367440544291)
                  ·
                    refine ⟨41756219437988051160816437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27837479625325367440544291 41756219437988051160816437)
                    ·
                      refine ⟨3914645572311379796326541, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41756219437988051160816437 3914645572311379796326541)
                      ·
                        rfl

theorem cell23_7623745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 3, 1, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 3, 1, 1, 2, 1, 1, 5].length) (baseStart_7623745 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7623745 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7623745 prefixEnd_7623745 := by exact prefixLift 7623745
  have htrace : WordTrace (prefixWord ++ tailWord_7623745) baseStart_7623745 baseEnd_7623745 := by
    simpa [prefixWord, tailWord_7623745, baseEnd_7623745] using wordTrace_append hprefix tailTrace_7623745
  have hstable : (prefixWord ++ tailWord_7623745).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7623745).length < 2 ^ (prefixWord ++ tailWord_7623745).sum := by decide
  have hdescent : baseEnd_7623745 < baseStart_7623745 := by decide
  rcases family_descends (prefixWord ++ tailWord_7623745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7623761 : List Nat := [1, 2, 2, 1, 3, 1, 2, 2, 2, 7]
def baseStart_7623761 : Nat := 118140960795 + 7623761 * 2 ^ 59
def prefixEnd_7623761 : Nat := 4983230072969 + 3 ^ 40 * 7623761 * 2
def baseEnd_7623761 : Nat := 1304884596000617244575489

theorem tailTrace_7623761 : CollatzResearch.WordTrace tailWord_7623761 prefixEnd_7623761 1304884596000617244575489 := by
  unfold tailWord_7623761
  simp only [CollatzResearch.WordTrace]
  refine ⟨278061407333423406563631137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185374271555615604375754091 278061407333423406563631137)
  ·
    refine ⟨208546055500067554922723353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 278061407333423406563631137 208546055500067554922723353)
    ·
      refine ⟨156409541625050666192042515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 208546055500067554922723353 156409541625050666192042515)
      ·
        refine ⟨234614312437575999288063773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 156409541625050666192042515 234614312437575999288063773)
        ·
          refine ⟨87980367164090999733023915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 234614312437575999288063773 87980367164090999733023915)
          ·
            refine ⟨131970550746136499599535873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87980367164090999733023915 131970550746136499599535873)
            ·
              refine ⟨98977913059602374699651905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 131970550746136499599535873 98977913059602374699651905)
              ·
                refine ⟨74233434794701781024738929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 98977913059602374699651905 74233434794701781024738929)
                ·
                  refine ⟨55675076096026335768554197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 74233434794701781024738929 55675076096026335768554197)
                  ·
                    refine ⟨1304884596000617244575489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 55675076096026335768554197 1304884596000617244575489)
                    ·
                      rfl

theorem cell23_7623761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 2, 2, 2, 7].length) (baseStart_7623761 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7623761 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7623761 prefixEnd_7623761 := by exact prefixLift 7623761
  have htrace : WordTrace (prefixWord ++ tailWord_7623761) baseStart_7623761 baseEnd_7623761 := by
    simpa [prefixWord, tailWord_7623761, baseEnd_7623761] using wordTrace_append hprefix tailTrace_7623761
  have hstable : (prefixWord ++ tailWord_7623761).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7623761).length < 2 ^ (prefixWord ++ tailWord_7623761).sum := by decide
  have hdescent : baseEnd_7623761 < baseStart_7623761 := by decide
  rcases family_descends (prefixWord ++ tailWord_7623761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7623762 : List Nat := [3, 2, 2, 1, 3, 2, 2, 2, 1, 2, 3]
def baseStart_7623762 : Nat := 118140960795 + 7623762 * 2 ^ 59
def prefixEnd_7623762 : Nat := 4983230072969 + 3 ^ 40 * 7623762 * 2
def baseEnd_7623762 : Nat := 3914654301482506229813963

theorem tailTrace_7623762 : CollatzResearch.WordTrace tailWord_7623762 prefixEnd_7623762 3914654301482506229813963 := by
  unfold tailWord_7623762
  simp only [CollatzResearch.WordTrace]
  refine ⟨69515360951604945933604385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 185374295870946522489611693 69515360951604945933604385)
  ·
    refine ⟨52136520713703709450203289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69515360951604945933604385 52136520713703709450203289)
    ·
      refine ⟨39102390535277782087652467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52136520713703709450203289 39102390535277782087652467)
      ·
        refine ⟨58653585802916673131478701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39102390535277782087652467 58653585802916673131478701)
        ·
          refine ⟨21995094676093752424304513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 58653585802916673131478701 21995094676093752424304513)
          ·
            refine ⟨16496321007070314318228385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21995094676093752424304513 16496321007070314318228385)
            ·
              refine ⟨12372240755302735738671289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16496321007070314318228385 12372240755302735738671289)
              ·
                refine ⟨9279180566477051804003467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12372240755302735738671289 9279180566477051804003467)
                ·
                  refine ⟨13918770849715577706005201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9279180566477051804003467 13918770849715577706005201)
                  ·
                    refine ⟨10439078137286683279503901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13918770849715577706005201 10439078137286683279503901)
                    ·
                      refine ⟨3914654301482506229813963, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10439078137286683279503901 3914654301482506229813963)
                      ·
                        rfl

theorem cell23_7623762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 2, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 2, 2, 2, 1, 2, 3].length) (baseStart_7623762 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7623762 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7623762 prefixEnd_7623762 := by exact prefixLift 7623762
  have htrace : WordTrace (prefixWord ++ tailWord_7623762) baseStart_7623762 baseEnd_7623762 := by
    simpa [prefixWord, tailWord_7623762, baseEnd_7623762] using wordTrace_append hprefix tailTrace_7623762
  have hstable : (prefixWord ++ tailWord_7623762).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7623762).length < 2 ^ (prefixWord ++ tailWord_7623762).sum := by decide
  have hdescent : baseEnd_7623762 < baseStart_7623762 := by decide
  rcases family_descends (prefixWord ++ tailWord_7623762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7623809 : List Nat := [1, 2, 4, 2, 2, 1, 4, 1, 2, 1, 3]
def baseStart_7623809 : Nat := 118140960795 + 7623809 * 2 ^ 59
def prefixEnd_7623809 : Nat := 4983230072969 + 3 ^ 40 * 7623809 * 2
def baseEnd_7623809 : Nat := 3914678435073267545926247

theorem tailTrace_7623809 : CollatzResearch.WordTrace tailWord_7623809 prefixEnd_7623809 3914678435073267545926247 := by
  unfold tailWord_7623809
  simp only [CollatzResearch.WordTrace]
  refine ⟨278063158037249510761378481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185375438691499673840918987 278063158037249510761378481)
  ·
    refine ⟨208547368527937133071033861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 278063158037249510761378481 208547368527937133071033861)
    ·
      refine ⟨39102631598988212450818849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 208547368527937133071033861 39102631598988212450818849)
      ·
        refine ⟨29326973699241159338114137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39102631598988212450818849 29326973699241159338114137)
        ·
          refine ⟨21995230274430869503585603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29326973699241159338114137 21995230274430869503585603)
          ·
            refine ⟨32992845411646304255378405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21995230274430869503585603 32992845411646304255378405)
            ·
              refine ⟨6186158514683682047883451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 32992845411646304255378405 6186158514683682047883451)
              ·
                refine ⟨9279237772025523071825177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6186158514683682047883451 9279237772025523071825177)
                ·
                  refine ⟨6959428329019142303868883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9279237772025523071825177 6959428329019142303868883)
                  ·
                    refine ⟨10439142493528713455803325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6959428329019142303868883 10439142493528713455803325)
                    ·
                      refine ⟨3914678435073267545926247, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10439142493528713455803325 3914678435073267545926247)
                      ·
                        rfl

theorem cell23_7623809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 1, 4, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 1, 4, 1, 2, 1, 3].length) (baseStart_7623809 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7623809 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7623809 prefixEnd_7623809 := by exact prefixLift 7623809
  have htrace : WordTrace (prefixWord ++ tailWord_7623809) baseStart_7623809 baseEnd_7623809 := by
    simpa [prefixWord, tailWord_7623809, baseEnd_7623809] using wordTrace_append hprefix tailTrace_7623809
  have hstable : (prefixWord ++ tailWord_7623809).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7623809).length < 2 ^ (prefixWord ++ tailWord_7623809).sum := by decide
  have hdescent : baseEnd_7623809 < baseStart_7623809 := by decide
  rcases family_descends (prefixWord ++ tailWord_7623809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7623815 : List Nat := [1, 1, 4, 2, 1, 1, 1, 5, 1, 4, 2]
def baseStart_7623815 : Nat := 118140960795 + 7623815 * 2 ^ 59
def prefixEnd_7623815 : Nat := 4983230072969 + 3 ^ 40 * 7623815 * 2
def baseEnd_7623815 : Nat := 3914681515957194522451219

theorem tailTrace_7623815 : CollatzResearch.WordTrace tailWord_7623815 prefixEnd_7623815 3914681515957194522451219 := by
  unfold tailWord_7623815
  simp only [CollatzResearch.WordTrace]
  refine ⟨278063376875227773786096899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185375584583485182524064599 278063376875227773786096899)
  ·
    refine ⟨417095065312841660679145349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 278063376875227773786096899 417095065312841660679145349)
    ·
      refine ⟨78205324746157811377339753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 417095065312841660679145349 78205324746157811377339753)
      ·
        refine ⟨58653993559618358533004815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78205324746157811377339753 58653993559618358533004815)
        ·
          refine ⟨87980990339427537799507223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58653993559618358533004815 87980990339427537799507223)
          ·
            refine ⟨131971485509141306699260835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87980990339427537799507223 131971485509141306699260835)
            ·
              refine ⟨197957228263711960048891253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 131971485509141306699260835 197957228263711960048891253)
              ·
                refine ⟨18558490149722996254583555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 197957228263711960048891253 18558490149722996254583555)
                ·
                  refine ⟨27837735224584494381875333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18558490149722996254583555 27837735224584494381875333)
                  ·
                    refine ⟨5219575354609592696601625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 27837735224584494381875333 5219575354609592696601625)
                    ·
                      refine ⟨3914681515957194522451219, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5219575354609592696601625 3914681515957194522451219)
                      ·
                        rfl

theorem cell23_7623815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 1, 5, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 1, 5, 1, 4, 2].length) (baseStart_7623815 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7623815 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7623815 prefixEnd_7623815 := by exact prefixLift 7623815
  have htrace : WordTrace (prefixWord ++ tailWord_7623815) baseStart_7623815 baseEnd_7623815 := by
    simpa [prefixWord, tailWord_7623815, baseEnd_7623815] using wordTrace_append hprefix tailTrace_7623815
  have hstable : (prefixWord ++ tailWord_7623815).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7623815).length < 2 ^ (prefixWord ++ tailWord_7623815).sum := by decide
  have hdescent : baseEnd_7623815 < baseStart_7623815 := by decide
  rcases family_descends (prefixWord ++ tailWord_7623815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7623818 : List Nat := [3, 1, 2, 3, 1, 1, 1, 1, 4, 1, 5]
def baseStart_7623818 : Nat := 118140960795 + 7623818 * 2 ^ 59
def prefixEnd_7623818 : Nat := 4983230072969 + 3 ^ 40 * 7623818 * 2
def baseEnd_7623818 : Nat := 3914683056399158010713705

theorem tailTrace_7623818 : CollatzResearch.WordTrace tailWord_7623818 prefixEnd_7623818 3914683056399158010713705 := by
  unfold tailWord_7623818
  simp only [CollatzResearch.WordTrace]
  refine ⟨69515871573554226324614027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 185375657529477936865637405 69515871573554226324614027)
  ·
    refine ⟨104273807360331339486921041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69515871573554226324614027 104273807360331339486921041)
    ·
      refine ⟨78205355520248504615190781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 104273807360331339486921041 78205355520248504615190781)
      ·
        refine ⟨29327008320093189230696543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 78205355520248504615190781 29327008320093189230696543)
        ·
          refine ⟨43990512480139783846044815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29327008320093189230696543 43990512480139783846044815)
          ·
            refine ⟨65985768720209675769067223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43990512480139783846044815 65985768720209675769067223)
            ·
              refine ⟨98978653080314513653600835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65985768720209675769067223 98978653080314513653600835)
              ·
                refine ⟨148467979620471770480401253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 98978653080314513653600835 148467979620471770480401253)
                ·
                  refine ⟨27837746178838456965075235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 148467979620471770480401253 27837746178838456965075235)
                  ·
                    refine ⟨41756619268257685447612853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27837746178838456965075235 41756619268257685447612853)
                    ·
                      refine ⟨3914683056399158010713705, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41756619268257685447612853 3914683056399158010713705)
                      ·
                        rfl

theorem cell23_7623818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 1, 1, 4, 1, 5].length) (baseStart_7623818 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7623818 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7623818 prefixEnd_7623818 := by exact prefixLift 7623818
  have htrace : WordTrace (prefixWord ++ tailWord_7623818) baseStart_7623818 baseEnd_7623818 := by
    simpa [prefixWord, tailWord_7623818, baseEnd_7623818] using wordTrace_append hprefix tailTrace_7623818
  have hstable : (prefixWord ++ tailWord_7623818).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7623818).length < 2 ^ (prefixWord ++ tailWord_7623818).sum := by decide
  have hdescent : baseEnd_7623818 < baseStart_7623818 := by decide
  rcases family_descends (prefixWord ++ tailWord_7623818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7623832 : List Nat := [2, 1, 2, 4, 2, 2, 1, 2, 1, 4, 2]
def baseStart_7623832 : Nat := 118140960795 + 7623832 * 2 ^ 59
def prefixEnd_7623832 : Nat := 4983230072969 + 3 ^ 40 * 7623832 * 2
def baseEnd_7623832 : Nat := 3914690245128320955938641

theorem tailTrace_7623832 : CollatzResearch.WordTrace tailWord_7623832 prefixEnd_7623832 3914690245128320955938641 := by
  unfold tailWord_7623832
  simp only [CollatzResearch.WordTrace]
  refine ⟨139031998458083092844732875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 185375997944110790459643833 139031998458083092844732875)
  ·
    refine ⟨208547997687124639267099313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139031998458083092844732875 208547997687124639267099313)
    ·
      refine ⟨156410998265343479450324485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 208547997687124639267099313 156410998265343479450324485)
      ·
        refine ⟨29327062174751902396935841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 156410998265343479450324485 29327062174751902396935841)
        ·
          refine ⟨21995296631063926797701881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29327062174751902396935841 21995296631063926797701881)
          ·
            refine ⟨16496472473297945098276411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21995296631063926797701881 16496472473297945098276411)
            ·
              refine ⟨24744708709946917647414617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16496472473297945098276411 24744708709946917647414617)
              ·
                refine ⟨18558531532460188235560963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24744708709946917647414617 18558531532460188235560963)
                ·
                  refine ⟨27837797298690282353341445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18558531532460188235560963 27837797298690282353341445)
                  ·
                    refine ⟨5219586993504427941251521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 27837797298690282353341445 5219586993504427941251521)
                    ·
                      refine ⟨3914690245128320955938641, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5219586993504427941251521 3914690245128320955938641)
                      ·
                        rfl

theorem cell23_7623832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 2, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 2, 1, 2, 1, 4, 2].length) (baseStart_7623832 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7623832 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7623832 prefixEnd_7623832 := by exact prefixLift 7623832
  have htrace : WordTrace (prefixWord ++ tailWord_7623832) baseStart_7623832 baseEnd_7623832 := by
    simpa [prefixWord, tailWord_7623832, baseEnd_7623832] using wordTrace_append hprefix tailTrace_7623832
  have hstable : (prefixWord ++ tailWord_7623832).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7623832).length < 2 ^ (prefixWord ++ tailWord_7623832).sum := by decide
  have hdescent : baseEnd_7623832 < baseStart_7623832 := by decide
  rcases family_descends (prefixWord ++ tailWord_7623832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7623865 : List Nat := [1, 2, 1, 4, 1, 4, 1, 1, 2, 3, 3]
def baseStart_7623865 : Nat := 118140960795 + 7623865 * 2 ^ 59
def prefixEnd_7623865 : Nat := 4983230072969 + 3 ^ 40 * 7623865 * 2
def baseEnd_7623865 : Nat := 3914707189989919326825989

theorem tailTrace_7623865 : CollatzResearch.WordTrace tailWord_7623865 prefixEnd_7623865 3914707189989919326825989 := by
  unfold tailWord_7623865
  simp only [CollatzResearch.WordTrace]
  refine ⟨278065200525046632325417049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185376800350031088216944699 278065200525046632325417049)
  ·
    refine ⟨208548900393784974244062787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 278065200525046632325417049 208548900393784974244062787)
    ·
      refine ⟨312823350590677461366094181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 208548900393784974244062787 312823350590677461366094181)
      ·
        refine ⟨58654378235752024006142659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 312823350590677461366094181 58654378235752024006142659)
        ·
          refine ⟨87981567353628036009213989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58654378235752024006142659 87981567353628036009213989)
          ·
            refine ⟨16496543878805256751727623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 87981567353628036009213989 16496543878805256751727623)
            ·
              refine ⟨24744815818207885127591435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16496543878805256751727623 24744815818207885127591435)
              ·
                refine ⟨37117223727311827691387153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24744815818207885127591435 37117223727311827691387153)
                ·
                  refine ⟨27837917795483870768540365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37117223727311827691387153 27837917795483870768540365)
                  ·
                    refine ⟨10439219173306451538202637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27837917795483870768540365 10439219173306451538202637)
                    ·
                      refine ⟨3914707189989919326825989, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10439219173306451538202637 3914707189989919326825989)
                      ·
                        rfl

theorem cell23_7623865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 4, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 4, 1, 1, 2, 3, 3].length) (baseStart_7623865 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7623865 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7623865 prefixEnd_7623865 := by exact prefixLift 7623865
  have htrace : WordTrace (prefixWord ++ tailWord_7623865) baseStart_7623865 baseEnd_7623865 := by
    simpa [prefixWord, tailWord_7623865, baseEnd_7623865] using wordTrace_append hprefix tailTrace_7623865
  have hstable : (prefixWord ++ tailWord_7623865).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7623865).length < 2 ^ (prefixWord ++ tailWord_7623865).sum := by decide
  have hdescent : baseEnd_7623865 < baseStart_7623865 := by decide
  rcases family_descends (prefixWord ++ tailWord_7623865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7623908 : List Nat := [2, 3, 1, 1, 1, 2, 2, 1, 2, 3, 5]
def baseStart_7623908 : Nat := 118140960795 + 7623908 * 2 ^ 59
def prefixEnd_7623908 : Nat := 4983230072969 + 3 ^ 40 * 7623908 * 2
def baseEnd_7623908 : Nat := 3914729269658062658588291

theorem tailTrace_7623908 : CollatzResearch.WordTrace tailWord_7623908 prefixEnd_7623908 3914729269658062658588291 := by
  unfold tailWord_7623908
  simp only [CollatzResearch.WordTrace]
  refine ⟨139033384431945425334616189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 185377845909260567112821585 139033384431945425334616189)
  ·
    refine ⟨52137519161979534500481071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 139033384431945425334616189 52137519161979534500481071)
    ·
      refine ⟨78206278742969301750721607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52137519161979534500481071 78206278742969301750721607)
      ·
        refine ⟨117309418114453952626082411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78206278742969301750721607 117309418114453952626082411)
        ·
          refine ⟨175964127171680928939123617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 117309418114453952626082411 175964127171680928939123617)
          ·
            refine ⟨131973095378760696704342713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 175964127171680928939123617 131973095378760696704342713)
            ·
              refine ⟨98979821534070522528257035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 131973095378760696704342713 98979821534070522528257035)
              ·
                refine ⟨148469732301105783792385553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 98979821534070522528257035 148469732301105783792385553)
                ·
                  refine ⟨111352299225829337844289165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 148469732301105783792385553 111352299225829337844289165)
                  ·
                    refine ⟨41757112209686001691608437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 111352299225829337844289165 41757112209686001691608437)
                    ·
                      refine ⟨3914729269658062658588291, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41757112209686001691608437 3914729269658062658588291)
                      ·
                        rfl

theorem cell23_7623908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 2, 1, 2, 3, 5].length) (baseStart_7623908 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7623908 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7623908 prefixEnd_7623908 := by exact prefixLift 7623908
  have htrace : WordTrace (prefixWord ++ tailWord_7623908) baseStart_7623908 baseEnd_7623908 := by
    simpa [prefixWord, tailWord_7623908, baseEnd_7623908] using wordTrace_append hprefix tailTrace_7623908
  have hstable : (prefixWord ++ tailWord_7623908).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7623908).length < 2 ^ (prefixWord ++ tailWord_7623908).sum := by decide
  have hdescent : baseEnd_7623908 < baseStart_7623908 := by decide
  rcases family_descends (prefixWord ++ tailWord_7623908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7623915 : List Nat := [1, 1, 1, 1, 2, 6, 1, 3, 3, 4]
def baseStart_7623915 : Nat := 118140960795 + 7623915 * 2 ^ 59
def prefixEnd_7623915 : Nat := 4983230072969 + 3 ^ 40 * 7623915 * 2
def baseEnd_7623915 : Nat := 1304910954674214710400253

theorem tailTrace_7623915 : CollatzResearch.WordTrace tailWord_7623915 prefixEnd_7623915 1304910954674214710400253 := by
  unfold tailWord_7623915
  simp only [CollatzResearch.WordTrace]
  refine ⟨278067024174865490864737199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185378016116576993909824799 278067024174865490864737199)
  ·
    refine ⟨417100536262298236297105799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 278067024174865490864737199 417100536262298236297105799)
    ·
      refine ⟨625650804393447354445658699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 417100536262298236297105799 625650804393447354445658699)
      ·
        refine ⟨938476206590171031668488049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 625650804393447354445658699 938476206590171031668488049)
        ·
          refine ⟨703857154942628273751366037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 938476206590171031668488049 703857154942628273751366037)
          ·
            refine ⟨32993304137935700332095283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 703857154942628273751366037 32993304137935700332095283)
            ·
              refine ⟨49489956206903550498142925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32993304137935700332095283 49489956206903550498142925)
              ·
                refine ⟨18558733577588831436803597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 49489956206903550498142925 18558733577588831436803597)
                ·
                  refine ⟨6959525091595811788801349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18558733577588831436803597 6959525091595811788801349)
                  ·
                    refine ⟨1304910954674214710400253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6959525091595811788801349 1304910954674214710400253)
                    ·
                      rfl

theorem cell23_7623915_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 6, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 6, 1, 3, 3, 4].length) (baseStart_7623915 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7623915 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7623915 prefixEnd_7623915 := by exact prefixLift 7623915
  have htrace : WordTrace (prefixWord ++ tailWord_7623915) baseStart_7623915 baseEnd_7623915 := by
    simpa [prefixWord, tailWord_7623915, baseEnd_7623915] using wordTrace_append hprefix tailTrace_7623915
  have hstable : (prefixWord ++ tailWord_7623915).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7623915).length < 2 ^ (prefixWord ++ tailWord_7623915).sum := by decide
  have hdescent : baseEnd_7623915 < baseStart_7623915 := by decide
  rcases family_descends (prefixWord ++ tailWord_7623915) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7623999 : List Nat := [1, 1, 2, 2, 4, 3, 2, 1, 2, 3, 2]
def baseStart_7623999 : Nat := 118140960795 + 7623999 * 2 ^ 59
def prefixEnd_7623999 : Nat := 4983230072969 + 3 ^ 40 * 7623999 * 2
def baseEnd_7623999 : Nat := 3914775996397621802550373

theorem tailTrace_7623999 : CollatzResearch.WordTrace tailWord_7623999 prefixEnd_7623999 3914775996397621802550373 := by
  unfold tailWord_7623999
  simp only [CollatzResearch.WordTrace]
  refine ⟨278070087906561173210795051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185380058604374115473863367 278070087906561173210795051)
  ·
    refine ⟨417105131859841759816192577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 278070087906561173210795051 417105131859841759816192577)
    ·
      refine ⟨312828848894881319862144433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 417105131859841759816192577 312828848894881319862144433)
      ·
        refine ⟨234621636671160989896608325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 312828848894881319862144433 234621636671160989896608325)
        ·
          refine ⟨43991556875842685605614061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 234621636671160989896608325 43991556875842685605614061)
          ·
            refine ⟨16496833828441007102105273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43991556875842685605614061 16496833828441007102105273)
            ·
              refine ⟨12372625371330755326578955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16496833828441007102105273 12372625371330755326578955)
              ·
                refine ⟨18558938056996132989868433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12372625371330755326578955 18558938056996132989868433)
                ·
                  refine ⟨13919203542747099742401325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18558938056996132989868433 13919203542747099742401325)
                  ·
                    refine ⟨5219701328530162403400497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13919203542747099742401325 5219701328530162403400497)
                    ·
                      refine ⟨3914775996397621802550373, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5219701328530162403400497 3914775996397621802550373)
                      ·
                        rfl

theorem cell23_7623999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 3, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 3, 2, 1, 2, 3, 2].length) (baseStart_7623999 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7623999 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7623999 prefixEnd_7623999 := by exact prefixLift 7623999
  have htrace : WordTrace (prefixWord ++ tailWord_7623999) baseStart_7623999 baseEnd_7623999 := by
    simpa [prefixWord, tailWord_7623999, baseEnd_7623999] using wordTrace_append hprefix tailTrace_7623999
  have hstable : (prefixWord ++ tailWord_7623999).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7623999).length < 2 ^ (prefixWord ++ tailWord_7623999).sum := by decide
  have hdescent : baseEnd_7623999 < baseStart_7623999 := by decide
  rcases family_descends (prefixWord ++ tailWord_7623999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7624005 : List Nat := [1, 3, 1, 1, 1, 2, 1, 3, 6, 4]
def baseStart_7624005 : Nat := 118140960795 + 7624005 * 2 ^ 59
def prefixEnd_7624005 : Nat := 4983230072969 + 3 ^ 40 * 7624005 * 2
def baseEnd_7624005 : Nat := 1304926359093849593025115

theorem tailTrace_7624005 : CollatzResearch.WordTrace tailWord_7624005 prefixEnd_7624005 1304926359093849593025115 := by
  unfold tailWord_7624005
  simp only [CollatzResearch.WordTrace]
  refine ⟨278070306744539436235513469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185380204496359624157008979 278070306744539436235513469)
  ·
    refine ⟨104276365029202288588317551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 278070306744539436235513469 104276365029202288588317551)
    ·
      refine ⟨156414547543803432882476327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104276365029202288588317551 156414547543803432882476327)
      ·
        refine ⟨234621821315705149323714491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 156414547543803432882476327 234621821315705149323714491)
        ·
          refine ⟨351932731973557723985571737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 234621821315705149323714491 351932731973557723985571737)
          ·
            refine ⟨263949548980168292989178803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 351932731973557723985571737 263949548980168292989178803)
            ·
              refine ⟨395924323470252439483768205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 263949548980168292989178803 395924323470252439483768205)
              ·
                refine ⟨148471621301344664806413077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 395924323470252439483768205 148471621301344664806413077)
                ·
                  refine ⟨6959607248500531162800613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 148471621301344664806413077 6959607248500531162800613)
                  ·
                    refine ⟨1304926359093849593025115, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6959607248500531162800613 1304926359093849593025115)
                    ·
                      rfl

theorem cell23_7624005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 1, 3, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 1, 3, 6, 4].length) (baseStart_7624005 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7624005 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7624005 prefixEnd_7624005 := by exact prefixLift 7624005
  have htrace : WordTrace (prefixWord ++ tailWord_7624005) baseStart_7624005 baseEnd_7624005 := by
    simpa [prefixWord, tailWord_7624005, baseEnd_7624005] using wordTrace_append hprefix tailTrace_7624005
  have hstable : (prefixWord ++ tailWord_7624005).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7624005).length < 2 ^ (prefixWord ++ tailWord_7624005).sum := by decide
  have hdescent : baseEnd_7624005 < baseStart_7624005 := by decide
  rcases family_descends (prefixWord ++ tailWord_7624005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7624023 : List Nat := [1, 1, 3, 2, 3, 4, 2, 2, 1, 1, 3]
def baseStart_7624023 : Nat := 118140960795 + 7624023 * 2 ^ 59
def prefixEnd_7624023 : Nat := 4983230072969 + 3 ^ 40 * 7624023 * 2
def baseEnd_7624023 : Nat := 3914788319933329708650263

theorem tailTrace_7624023 : CollatzResearch.WordTrace tailWord_7624023 prefixEnd_7624023 3914788319933329708650263 := by
  unfold tailWord_7624023
  simp only [CollatzResearch.WordTrace]
  refine ⟨278070963258474225309668723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185380642172316150206445815 278070963258474225309668723)
  ·
    refine ⟨417106444887711337964503085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 278070963258474225309668723 417106444887711337964503085)
    ·
      refine ⟨156414916832891751736688657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 417106444887711337964503085 156414916832891751736688657)
      ·
        refine ⟨117311187624668813802516493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 156414916832891751736688657 117311187624668813802516493)
        ·
          refine ⟨43991695359250805175943685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 117311187624668813802516493 43991695359250805175943685)
          ·
            refine ⟨8248442879859525970489441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 43991695359250805175943685 8248442879859525970489441)
            ·
              refine ⟨6186332159894644477867081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8248442879859525970489441 6186332159894644477867081)
              ·
                refine ⟨4639749119920983358400311, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6186332159894644477867081 4639749119920983358400311)
                ·
                  refine ⟨6959623679881475037600467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4639749119920983358400311 6959623679881475037600467)
                  ·
                    refine ⟨10439435519822212556400701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6959623679881475037600467 10439435519822212556400701)
                    ·
                      refine ⟨3914788319933329708650263, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10439435519822212556400701 3914788319933329708650263)
                      ·
                        rfl

theorem cell23_7624023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 4, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 4, 2, 2, 1, 1, 3].length) (baseStart_7624023 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7624023 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7624023 prefixEnd_7624023 := by exact prefixLift 7624023
  have htrace : WordTrace (prefixWord ++ tailWord_7624023) baseStart_7624023 baseEnd_7624023 := by
    simpa [prefixWord, tailWord_7624023, baseEnd_7624023] using wordTrace_append hprefix tailTrace_7624023
  have hstable : (prefixWord ++ tailWord_7624023).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7624023).length < 2 ^ (prefixWord ++ tailWord_7624023).sum := by decide
  have hdescent : baseEnd_7624023 < baseStart_7624023 := by decide
  rcases family_descends (prefixWord ++ tailWord_7624023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7624032 : List Nat := [2, 1, 1, 3, 4, 1, 1, 2, 3, 2, 3]
def baseStart_7624032 : Nat := 118140960795 + 7624032 * 2 ^ 59
def prefixEnd_7624032 : Nat := 4983230072969 + 3 ^ 40 * 7624032 * 2
def baseEnd_7624032 : Nat := 3914792941259220173437721

theorem tailTrace_7624032 : CollatzResearch.WordTrace tailWord_7624032 prefixEnd_7624032 3914792941259220173437721 := by
  unfold tailWord_7624032
  simp only [CollatzResearch.WordTrace]
  refine ⟨139035645757720809923373175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 185380861010294413231164233 139035645757720809923373175)
  ·
    refine ⟨208553468636581214885059763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139035645757720809923373175 208553468636581214885059763)
    ·
      refine ⟨312830202954871822327589645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 208553468636581214885059763 312830202954871822327589645)
      ·
        refine ⟨117311326108076933372846117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 312830202954871822327589645 117311326108076933372846117)
        ·
          refine ⟨21995873645264425007408647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 117311326108076933372846117 21995873645264425007408647)
          ·
            refine ⟨32993810467896637511112971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21995873645264425007408647 32993810467896637511112971)
            ·
              refine ⟨49490715701844956266669457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32993810467896637511112971 49490715701844956266669457)
              ·
                refine ⟨37118036776383717200002093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49490715701844956266669457 37118036776383717200002093)
                ·
                  refine ⟨13919263791143893950000785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 37118036776383717200002093 13919263791143893950000785)
                  ·
                    refine ⟨10439447843357920462500589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13919263791143893950000785 10439447843357920462500589)
                    ·
                      refine ⟨3914792941259220173437721, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10439447843357920462500589 3914792941259220173437721)
                      ·
                        rfl

theorem cell23_7624032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 1, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 1, 1, 2, 3, 2, 3].length) (baseStart_7624032 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7624032 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7624032 prefixEnd_7624032 := by exact prefixLift 7624032
  have htrace : WordTrace (prefixWord ++ tailWord_7624032) baseStart_7624032 baseEnd_7624032 := by
    simpa [prefixWord, tailWord_7624032, baseEnd_7624032] using wordTrace_append hprefix tailTrace_7624032
  have hstable : (prefixWord ++ tailWord_7624032).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7624032).length < 2 ^ (prefixWord ++ tailWord_7624032).sum := by decide
  have hdescent : baseEnd_7624032 < baseStart_7624032 := by decide
  rcases family_descends (prefixWord ++ tailWord_7624032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7624035 : List Nat := [1, 1, 1, 5, 2, 2, 3, 8]
def baseStart_7624035 : Nat := 118140960795 + 7624035 * 2 ^ 59
def prefixEnd_7624035 : Nat := 4983230072969 + 3 ^ 40 * 7624035 * 2
def baseEnd_7624035 : Nat := 144992388211154950433341

theorem tailTrace_7624035 : CollatzResearch.WordTrace tailWord_7624035 prefixEnd_7624035 144992388211154950433341 := by
  unfold tailWord_7624035
  simp only [CollatzResearch.WordTrace]
  refine ⟨278071400934430751359105559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185380933956287167572737039 278071400934430751359105559)
  ·
    refine ⟨417107101401646127038658339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 278071400934430751359105559 417107101401646127038658339)
    ·
      refine ⟨625660652102469190557987509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 417107101401646127038658339 625660652102469190557987509)
      ·
        refine ⟨58655686134606486614811329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 625660652102469190557987509 58655686134606486614811329)
        ·
          refine ⟨43991764600954864961108497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58655686134606486614811329 43991764600954864961108497)
          ·
            refine ⟨32993823450716148720831373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43991764600954864961108497 32993823450716148720831373)
            ·
              refine ⟨12372683794018555770311765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32993823450716148720831373 12372683794018555770311765)
              ·
                refine ⟨144992388211154950433341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 12372683794018555770311765 144992388211154950433341)
                ·
                  rfl

theorem cell23_7624035_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 2, 3, 8].length) (baseStart_7624035 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7624035 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7624035 prefixEnd_7624035 := by exact prefixLift 7624035
  have htrace : WordTrace (prefixWord ++ tailWord_7624035) baseStart_7624035 baseEnd_7624035 := by
    simpa [prefixWord, tailWord_7624035, baseEnd_7624035] using wordTrace_append hprefix tailTrace_7624035
  have hstable : (prefixWord ++ tailWord_7624035).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7624035).length < 2 ^ (prefixWord ++ tailWord_7624035).sum := by decide
  have hdescent : baseEnd_7624035 < baseStart_7624035 := by decide
  rcases family_descends (prefixWord ++ tailWord_7624035) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7624085 : List Nat := [1, 3, 2, 1, 1, 2, 2, 1, 1, 5, 4]
def baseStart_7624085 : Nat := 118140960795 + 7624085 * 2 ^ 59
def prefixEnd_7624085 : Nat := 4983230072969 + 3 ^ 40 * 7624085 * 2
def baseEnd_7624085 : Nat := 3914820155733908466074977

theorem tailTrace_7624085 : CollatzResearch.WordTrace tailWord_7624085 prefixEnd_7624085 3914820155733908466074977 := by
  unfold tailWord_7624085
  simp only [CollatzResearch.WordTrace]
  refine ⟨278073224584249609898425709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185382149722833073265617139 278073224584249609898425709)
  ·
    refine ⟨104277459219093603711909641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 278073224584249609898425709 104277459219093603711909641)
    ·
      refine ⟨78208094414320202783932231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 104277459219093603711909641 78208094414320202783932231)
      ·
        refine ⟨117312141621480304175898347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78208094414320202783932231 117312141621480304175898347)
        ·
          refine ⟨175968212432220456263847521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 117312141621480304175898347 175968212432220456263847521)
          ·
            refine ⟨131976159324165342197885641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 175968212432220456263847521 131976159324165342197885641)
            ·
              refine ⟨98982119493124006648414231, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 131976159324165342197885641 98982119493124006648414231)
              ·
                refine ⟨148473179239686009972621347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 98982119493124006648414231 148473179239686009972621347)
                ·
                  refine ⟨222709768859529014958932021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 148473179239686009972621347 222709768859529014958932021)
                  ·
                    refine ⟨20879040830580845152399877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 222709768859529014958932021 20879040830580845152399877)
                    ·
                      refine ⟨3914820155733908466074977, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20879040830580845152399877 3914820155733908466074977)
                      ·
                        rfl

theorem cell23_7624085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 2, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 2, 1, 1, 5, 4].length) (baseStart_7624085 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7624085 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7624085 prefixEnd_7624085 := by exact prefixLift 7624085
  have htrace : WordTrace (prefixWord ++ tailWord_7624085) baseStart_7624085 baseEnd_7624085 := by
    simpa [prefixWord, tailWord_7624085, baseEnd_7624085] using wordTrace_append hprefix tailTrace_7624085
  have hstable : (prefixWord ++ tailWord_7624085).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7624085).length < 2 ^ (prefixWord ++ tailWord_7624085).sum := by decide
  have hdescent : baseEnd_7624085 < baseStart_7624085 := by decide
  rcases family_descends (prefixWord ++ tailWord_7624085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7624096 : List Nat := [2, 1, 1, 4, 1, 2, 5, 1, 2, 1, 3]
def baseStart_7624096 : Nat := 118140960795 + 7624096 * 2 ^ 59
def prefixEnd_7624096 : Nat := 4983230072969 + 3 ^ 40 * 7624096 * 2
def baseEnd_7624096 : Nat := 3914825804021107923037427

theorem tailTrace_7624096 : CollatzResearch.WordTrace tailWord_7624096 prefixEnd_7624096 3914825804021107923037427 := by
  unfold tailWord_7624096
  simp only [CollatzResearch.WordTrace]
  refine ⟨139036812893604879388538071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 185382417191473172518050761 139036812893604879388538071)
  ·
    refine ⟨208555219340407319082807107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139036812893604879388538071 208555219340407319082807107)
    ·
      refine ⟨312832829010610978624210661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 208555219340407319082807107 312832829010610978624210661)
      ·
        refine ⟨58656155439489558492039499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 312832829010610978624210661 58656155439489558492039499)
        ·
          refine ⟨87984233159234337738059249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58656155439489558492039499 87984233159234337738059249)
          ·
            refine ⟨65988174869425753303544437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 87984233159234337738059249 65988174869425753303544437)
            ·
              refine ⟨6186391394008664372207291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 65988174869425753303544437 6186391394008664372207291)
              ·
                refine ⟨9279587091012996558310937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6186391394008664372207291 9279587091012996558310937)
                ·
                  refine ⟨6959690318259747418733203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9279587091012996558310937 6959690318259747418733203)
                  ·
                    refine ⟨10439535477389621128099805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6959690318259747418733203 10439535477389621128099805)
                    ·
                      refine ⟨3914825804021107923037427, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10439535477389621128099805 3914825804021107923037427)
                      ·
                        rfl

theorem cell23_7624096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 5, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 5, 1, 2, 1, 3].length) (baseStart_7624096 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7624096 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7624096 prefixEnd_7624096 := by exact prefixLift 7624096
  have htrace : WordTrace (prefixWord ++ tailWord_7624096) baseStart_7624096 baseEnd_7624096 := by
    simpa [prefixWord, tailWord_7624096, baseEnd_7624096] using wordTrace_append hprefix tailTrace_7624096
  have hstable : (prefixWord ++ tailWord_7624096).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7624096).length < 2 ^ (prefixWord ++ tailWord_7624096).sum := by decide
  have hdescent : baseEnd_7624096 < baseStart_7624096 := by decide
  rcases family_descends (prefixWord ++ tailWord_7624096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7624115 : List Nat := [1, 1, 1, 2, 3, 1, 1, 4, 1, 4, 4]
def baseStart_7624115 : Nat := 118140960795 + 7624115 * 2 ^ 59
def prefixEnd_7624115 : Nat := 4983230072969 + 3 ^ 40 * 7624115 * 2
def baseEnd_7624115 : Nat := 3914835560153543348699839

theorem tailTrace_7624115 : CollatzResearch.WordTrace tailWord_7624115 prefixEnd_7624115 3914835560153543348699839 := by
  unfold tailWord_7624115
  simp only [CollatzResearch.WordTrace]
  refine ⟨278074318774140925022017799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185382879182760616681345199 278074318774140925022017799)
  ·
    refine ⟨417111478161211387533026699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 278074318774140925022017799 417111478161211387533026699)
    ·
      refine ⟨625667217241817081299540049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 417111478161211387533026699 625667217241817081299540049)
      ·
        refine ⟨469250412931362810974655037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 625667217241817081299540049 469250412931362810974655037)
        ·
          refine ⟨175968904849261054115495639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 469250412931362810974655037 175968904849261054115495639)
          ·
            refine ⟨263953357273891581173243459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 175968904849261054115495639 263953357273891581173243459)
            ·
              refine ⟨395930035910837371759865189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 263953357273891581173243459 395930035910837371759865189)
              ·
                refine ⟨74236881733282007204974723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 395930035910837371759865189 74236881733282007204974723)
                ·
                  refine ⟨111355322599923010807462085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 74236881733282007204974723 111355322599923010807462085)
                  ·
                    refine ⟨20879122987485564526399141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 111355322599923010807462085 20879122987485564526399141)
                    ·
                      refine ⟨3914835560153543348699839, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20879122987485564526399141 3914835560153543348699839)
                      ·
                        rfl

theorem cell23_7624115_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 1, 4, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 1, 4, 1, 4, 4].length) (baseStart_7624115 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7624115 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7624115 prefixEnd_7624115 := by exact prefixLift 7624115
  have htrace : WordTrace (prefixWord ++ tailWord_7624115) baseStart_7624115 baseEnd_7624115 := by
    simpa [prefixWord, tailWord_7624115, baseEnd_7624115] using wordTrace_append hprefix tailTrace_7624115
  have hstable : (prefixWord ++ tailWord_7624115).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7624115).length < 2 ^ (prefixWord ++ tailWord_7624115).sum := by decide
  have hdescent : baseEnd_7624115 < baseStart_7624115 := by decide
  rcases family_descends (prefixWord ++ tailWord_7624115) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7624119 : List Nat := [1, 1, 3, 1, 3, 2, 1, 1, 6, 2, 2]
def baseStart_7624119 : Nat := 118140960795 + 7624119 * 2 ^ 59
def prefixEnd_7624119 : Nat := 4983230072969 + 3 ^ 40 * 7624119 * 2
def baseEnd_7624119 : Nat := 3914837614076161333049821

theorem tailTrace_7624119 : CollatzResearch.WordTrace tailWord_7624119 prefixEnd_7624119 3914837614076161333049821 := by
  unfold tailWord_7624119
  simp only [CollatzResearch.WordTrace]
  refine ⟨278074464666126433705163411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185382976444084289136775607 278074464666126433705163411)
  ·
    refine ⟨417111696999189650557745117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 278074464666126433705163411 417111696999189650557745117)
    ·
      refine ⟨156416886374696118959154419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 417111696999189650557745117 156416886374696118959154419)
      ·
        refine ⟨234625329562044178438731629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 156416886374696118959154419 234625329562044178438731629)
        ·
          refine ⟨87984498585766566914524361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 234625329562044178438731629 87984498585766566914524361)
          ·
            refine ⟨65988373939324925185893271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 87984498585766566914524361 65988373939324925185893271)
            ·
              refine ⟨98982560908987387778839907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65988373939324925185893271 98982560908987387778839907)
              ·
                refine ⟨148473841363481081668259861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 98982560908987387778839907 148473841363481081668259861)
                ·
                  refine ⟨6959711313913175703199681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 148473841363481081668259861 6959711313913175703199681)
                  ·
                    refine ⟨5219783485434881777399761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6959711313913175703199681 5219783485434881777399761)
                    ·
                      refine ⟨3914837614076161333049821, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5219783485434881777399761 3914837614076161333049821)
                      ·
                        rfl

theorem cell23_7624119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 1, 1, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 1, 1, 6, 2, 2].length) (baseStart_7624119 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7624119 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7624119 prefixEnd_7624119 := by exact prefixLift 7624119
  have htrace : WordTrace (prefixWord ++ tailWord_7624119) baseStart_7624119 baseEnd_7624119 := by
    simpa [prefixWord, tailWord_7624119, baseEnd_7624119] using wordTrace_append hprefix tailTrace_7624119
  have hstable : (prefixWord ++ tailWord_7624119).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7624119).length < 2 ^ (prefixWord ++ tailWord_7624119).sum := by decide
  have hdescent : baseEnd_7624119 < baseStart_7624119 := by decide
  rcases family_descends (prefixWord ++ tailWord_7624119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7624135 : List Nat := [1, 1, 4, 1, 1, 3, 1, 1, 1, 2, 7]
def baseStart_7624135 : Nat := 118140960795 + 7624135 * 2 ^ 59
def prefixEnd_7624135 : Nat := 4983230072969 + 3 ^ 40 * 7624135 * 2
def baseEnd_7624135 : Nat := 3914845829766633270449747

theorem tailTrace_7624135 : CollatzResearch.WordTrace tailWord_7624135 prefixEnd_7624135 3914845829766633270449747 := by
  unfold tailWord_7624135
  simp only [CollatzResearch.WordTrace]
  refine ⟨278075048234068468437745859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185383365489378978958497239 278075048234068468437745859)
  ·
    refine ⟨417112572351102702656618789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 278075048234068468437745859 417112572351102702656618789)
    ·
      refine ⟨78208607315831756748116023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 417112572351102702656618789 78208607315831756748116023)
      ·
        refine ⟨117312910973747635122174035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78208607315831756748116023 117312910973747635122174035)
        ·
          refine ⟨175969366460621452683261053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 117312910973747635122174035 175969366460621452683261053)
          ·
            refine ⟨65988512422733044756222895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 175969366460621452683261053 65988512422733044756222895)
            ·
              refine ⟨98982768634099567134334343, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65988512422733044756222895 98982768634099567134334343)
              ·
                refine ⟨148474152951149350701501515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 98982768634099567134334343 148474152951149350701501515)
                ·
                  refine ⟨222711229426724026052252273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 148474152951149350701501515 222711229426724026052252273)
                  ·
                    refine ⟨167033422070043019539189205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 222711229426724026052252273 167033422070043019539189205)
                    ·
                      refine ⟨3914845829766633270449747, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 167033422070043019539189205 3914845829766633270449747)
                      ·
                        rfl

theorem cell23_7624135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 1, 1, 1, 2, 7].length) (baseStart_7624135 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7624135 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7624135 prefixEnd_7624135 := by exact prefixLift 7624135
  have htrace : WordTrace (prefixWord ++ tailWord_7624135) baseStart_7624135 baseEnd_7624135 := by
    simpa [prefixWord, tailWord_7624135, baseEnd_7624135] using wordTrace_append hprefix tailTrace_7624135
  have hstable : (prefixWord ++ tailWord_7624135).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7624135).length < 2 ^ (prefixWord ++ tailWord_7624135).sum := by decide
  have hdescent : baseEnd_7624135 < baseStart_7624135 := by decide
  rcases family_descends (prefixWord ++ tailWord_7624135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7624136 : List Nat := [2, 1, 3, 1, 3, 1, 2, 4, 2, 2, 2]
def baseStart_7624136 : Nat := 118140960795 + 7624136 * 2 ^ 59
def prefixEnd_7624136 : Nat := 4983230072969 + 3 ^ 40 * 7624136 * 2
def baseEnd_7624136 : Nat := 3914846343247287766537243

theorem tailTrace_7624136 : CollatzResearch.WordTrace tailWord_7624136 prefixEnd_7624136 3914846343247287766537243 := by
  unfold tailWord_7624136
  simp only [CollatzResearch.WordTrace]
  refine ⟨139037542353532422804266131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 185383389804709897072354841 139037542353532422804266131)
  ·
    refine ⟨208556313530298634206399197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139037542353532422804266131 208556313530298634206399197)
    ·
      refine ⟨78208617573861987827399699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 208556313530298634206399197 78208617573861987827399699)
      ·
        refine ⟨117312926360792981741099549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78208617573861987827399699 117312926360792981741099549)
        ·
          refine ⟨43992347385297368152912331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 117312926360792981741099549 43992347385297368152912331)
          ·
            refine ⟨65988521077946052229368497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43992347385297368152912331 65988521077946052229368497)
            ·
              refine ⟨49491390808459539172026373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 65988521077946052229368497 49491390808459539172026373)
              ·
                refine ⟨9279635776586163594754945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 49491390808459539172026373 9279635776586163594754945)
                ·
                  refine ⟨6959726832439622696066209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9279635776586163594754945 6959726832439622696066209)
                  ·
                    refine ⟨5219795124329717022049657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6959726832439622696066209 5219795124329717022049657)
                    ·
                      refine ⟨3914846343247287766537243, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5219795124329717022049657 3914846343247287766537243)
                      ·
                        rfl

theorem cell23_7624136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 2, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 2, 4, 2, 2, 2].length) (baseStart_7624136 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7624136 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7624136 prefixEnd_7624136 := by exact prefixLift 7624136
  have htrace : WordTrace (prefixWord ++ tailWord_7624136) baseStart_7624136 baseEnd_7624136 := by
    simpa [prefixWord, tailWord_7624136, baseEnd_7624136] using wordTrace_append hprefix tailTrace_7624136
  have hstable : (prefixWord ++ tailWord_7624136).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7624136).length < 2 ^ (prefixWord ++ tailWord_7624136).sum := by decide
  have hdescent : baseEnd_7624136 < baseStart_7624136 := by decide
  rcases family_descends (prefixWord ++ tailWord_7624136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7624142 : List Nat := [4, 1, 1, 1, 2, 1, 5, 1, 7]
def baseStart_7624142 : Nat := 118140960795 + 7624142 * 2 ^ 59
def prefixEnd_7624142 : Nat := 4983230072969 + 3 ^ 40 * 7624142 * 2
def baseEnd_7624142 : Nat := 434983269347912749229135

theorem tailTrace_7624142 : CollatzResearch.WordTrace tailWord_7624142 prefixEnd_7624142 434983269347912749229135 := by
  unfold tailWord_7624142
  simp only [CollatzResearch.WordTrace]
  refine ⟨34759412943130388579156335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 185383535696695405755500453 34759412943130388579156335)
  ·
    refine ⟨52139119414695582868734503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34759412943130388579156335 52139119414695582868734503)
    ·
      refine ⟨78208679122043374303101755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52139119414695582868734503 78208679122043374303101755)
      ·
        refine ⟨117313018683065061454652633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78208679122043374303101755 117313018683065061454652633)
        ·
          refine ⟨87984764012298796090989475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 117313018683065061454652633 87984764012298796090989475)
          ·
            refine ⟨131977146018448194136484213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87984764012298796090989475 131977146018448194136484213)
            ·
              refine ⟨12372857439229518200295395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 131977146018448194136484213 12372857439229518200295395)
              ·
                refine ⟨18559286158844277300443093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12372857439229518200295395 18559286158844277300443093)
                ·
                  refine ⟨434983269347912749229135, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18559286158844277300443093 434983269347912749229135)
                  ·
                    rfl

theorem cell23_7624142_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 5, 1, 7].length) (baseStart_7624142 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7624142 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7624142 prefixEnd_7624142 := by exact prefixLift 7624142
  have htrace : WordTrace (prefixWord ++ tailWord_7624142) baseStart_7624142 baseEnd_7624142 := by
    simpa [prefixWord, tailWord_7624142, baseEnd_7624142] using wordTrace_append hprefix tailTrace_7624142
  have hstable : (prefixWord ++ tailWord_7624142).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7624142).length < 2 ^ (prefixWord ++ tailWord_7624142).sum := by decide
  have hdescent : baseEnd_7624142 < baseStart_7624142 := by decide
  rcases family_descends (prefixWord ++ tailWord_7624142) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7624152 : List Nat := [2, 1, 2, 2, 2, 1, 2, 3, 2, 3, 3]
def baseStart_7624152 : Nat := 118140960795 + 7624152 * 2 ^ 59
def prefixEnd_7624152 : Nat := 4983230072969 + 3 ^ 40 * 7624152 * 2
def baseEnd_7624152 : Nat := 3914854558937759703937169

theorem tailTrace_7624152 : CollatzResearch.WordTrace tailWord_7624152 prefixEnd_7624152 3914854558937759703937169 := by
  unfold tailWord_7624152
  simp only [CollatzResearch.WordTrace]
  refine ⟨139037834137503440170557355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 185383778850004586894076473 139037834137503440170557355)
  ·
    refine ⟨208556751206255160255836033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139037834137503440170557355 208556751206255160255836033)
    ·
      refine ⟨156417563404691370191877025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 208556751206255160255836033 156417563404691370191877025)
      ·
        refine ⟨117313172553518527643907769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 156417563404691370191877025 117313172553518527643907769)
        ·
          refine ⟨87984879415138895732930827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 117313172553518527643907769 87984879415138895732930827)
          ·
            refine ⟨131977319122708343599396241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87984879415138895732930827 131977319122708343599396241)
            ·
              refine ⟨98982989342031257699547181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 131977319122708343599396241 98982989342031257699547181)
              ·
                refine ⟨37118621003261721637330193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 98982989342031257699547181 37118621003261721637330193)
                ·
                  refine ⟨27838965752446291227997645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37118621003261721637330193 27838965752446291227997645)
                  ·
                    refine ⟨10439612157167359210499117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27838965752446291227997645 10439612157167359210499117)
                    ·
                      refine ⟨3914854558937759703937169, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10439612157167359210499117 3914854558937759703937169)
                      ·
                        rfl

theorem cell23_7624152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 2, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 2, 3, 2, 3, 3].length) (baseStart_7624152 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7624152 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7624152 prefixEnd_7624152 := by exact prefixLift 7624152
  have htrace : WordTrace (prefixWord ++ tailWord_7624152) baseStart_7624152 baseEnd_7624152 := by
    simpa [prefixWord, tailWord_7624152, baseEnd_7624152] using wordTrace_append hprefix tailTrace_7624152
  have hstable : (prefixWord ++ tailWord_7624152).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7624152).length < 2 ^ (prefixWord ++ tailWord_7624152).sum := by decide
  have hdescent : baseEnd_7624152 < baseStart_7624152 := by decide
  rcases family_descends (prefixWord ++ tailWord_7624152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7624153 : List Nat := [1, 2, 1, 2, 4, 2, 4, 1, 2, 2, 2]
def baseStart_7624153 : Nat := 118140960795 + 7624153 * 2 ^ 59
def prefixEnd_7624153 : Nat := 4983230072969 + 3 ^ 40 * 7624153 * 2
def baseEnd_7624153 : Nat := 3914855072418414200024665

theorem tailTrace_7624153 : CollatzResearch.WordTrace tailWord_7624153 prefixEnd_7624153 3914855072418414200024665 := by
  unfold tailWord_7624153
  simp only [CollatzResearch.WordTrace]
  refine ⟨278075704748003257511901113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185383803165335505007934075 278075704748003257511901113)
  ·
    refine ⟨208556778561002443133925835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 278075704748003257511901113 208556778561002443133925835)
    ·
      refine ⟨312835167841503664700888753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 208556778561002443133925835 312835167841503664700888753)
      ·
        refine ⟨234626375881127748525666565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 312835167841503664700888753 234626375881127748525666565)
        ·
          refine ⟨43992445477711452848562481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 234626375881127748525666565 43992445477711452848562481)
          ·
            refine ⟨32994334108283589636421861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43992445477711452848562481 32994334108283589636421861)
            ·
              refine ⟨6186437645303173056829099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 32994334108283589636421861 6186437645303173056829099)
              ·
                refine ⟨9279656467954759585243649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6186437645303173056829099 9279656467954759585243649)
                ·
                  refine ⟨6959742350966069688932737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9279656467954759585243649 6959742350966069688932737)
                  ·
                    refine ⟨5219806763224552266699553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6959742350966069688932737 5219806763224552266699553)
                    ·
                      refine ⟨3914855072418414200024665, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5219806763224552266699553 3914855072418414200024665)
                      ·
                        rfl

theorem cell23_7624153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 2, 4, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 2, 4, 1, 2, 2, 2].length) (baseStart_7624153 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7624153 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7624153 prefixEnd_7624153 := by exact prefixLift 7624153
  have htrace : WordTrace (prefixWord ++ tailWord_7624153) baseStart_7624153 baseEnd_7624153 := by
    simpa [prefixWord, tailWord_7624153, baseEnd_7624153] using wordTrace_append hprefix tailTrace_7624153
  have hstable : (prefixWord ++ tailWord_7624153).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7624153).length < 2 ^ (prefixWord ++ tailWord_7624153).sum := by decide
  have hdescent : baseEnd_7624153 < baseStart_7624153 := by decide
  rcases family_descends (prefixWord ++ tailWord_7624153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7624193 : List Nat := [1, 2, 4, 1, 4, 2, 2, 2, 5]
def baseStart_7624193 : Nat := 118140960795 + 7624193 * 2 ^ 59
def prefixEnd_7624193 : Nat := 4983230072969 + 3 ^ 40 * 7624193 * 2
def baseEnd_7624193 : Nat := 434986179071621560391609

theorem tailTrace_7624193 : CollatzResearch.WordTrace tailWord_7624193 prefixEnd_7624193 434986179071621560391609 := by
  unfold tailWord_7624193
  simp only [CollatzResearch.WordTrace]
  refine ⟨278077163667858344343357233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185384775778572229562238155 278077163667858344343357233)
  ·
    refine ⟨208557872750893758257517925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 278077163667858344343357233 208557872750893758257517925)
    ·
      refine ⟨39104601140792579673284611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 208557872750893758257517925 39104601140792579673284611)
      ·
        refine ⟨58656901711188869509926917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39104601140792579673284611 58656901711188869509926917)
        ·
          refine ⟨10998169070847913033111297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 58656901711188869509926917 10998169070847913033111297)
          ·
            refine ⟨8248626803135934774833473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10998169070847913033111297 8248626803135934774833473)
            ·
              refine ⟨6186470102351951081125105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8248626803135934774833473 6186470102351951081125105)
              ·
                refine ⟨4639852576763963310843829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6186470102351951081125105 4639852576763963310843829)
                ·
                  refine ⟨434986179071621560391609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4639852576763963310843829 434986179071621560391609)
                  ·
                    rfl

theorem cell23_7624193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 4, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 4, 2, 2, 2, 5].length) (baseStart_7624193 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7624193 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7624193 prefixEnd_7624193 := by exact prefixLift 7624193
  have htrace : WordTrace (prefixWord ++ tailWord_7624193) baseStart_7624193 baseEnd_7624193 := by
    simpa [prefixWord, tailWord_7624193, baseEnd_7624193] using wordTrace_append hprefix tailTrace_7624193
  have hstable : (prefixWord ++ tailWord_7624193).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7624193).length < 2 ^ (prefixWord ++ tailWord_7624193).sum := by decide
  have hdescent : baseEnd_7624193 < baseStart_7624193 := by decide
  rcases family_descends (prefixWord ++ tailWord_7624193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7624209 : List Nat := [1, 2, 2, 1, 1, 2, 5, 1, 2, 4, 2]
def baseStart_7624209 : Nat := 118140960795 + 7624209 * 2 ^ 59
def prefixEnd_7624209 : Nat := 4983230072969 + 3 ^ 40 * 7624209 * 2
def baseEnd_7624209 : Nat := 3914883827335065980924407

theorem tailTrace_7624209 : CollatzResearch.WordTrace tailWord_7624209 prefixEnd_7624209 3914883827335065980924407 := by
  unfold tailWord_7624209
  simp only [CollatzResearch.WordTrace]
  refine ⟨278077747235800379075939681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185385164823866919383959787 278077747235800379075939681)
  ·
    refine ⟨208558310426850284306954761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 278077747235800379075939681 208558310426850284306954761)
    ·
      refine ⟨156418732820137713230216071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 208558310426850284306954761 156418732820137713230216071)
      ·
        refine ⟨234628099230206569845324107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 156418732820137713230216071 234628099230206569845324107)
        ·
          refine ⟨351942148845309854767986161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 234628099230206569845324107 351942148845309854767986161)
          ·
            refine ⟨263956611633982391075989621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 351942148845309854767986161 263956611633982391075989621)
            ·
              refine ⟨24745932340685849163374027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 263956611633982391075989621 24745932340685849163374027)
              ·
                refine ⟨37118898511028773745061041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24745932340685849163374027 37118898511028773745061041)
                ·
                  refine ⟨27839173883271580308795781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37118898511028773745061041 27839173883271580308795781)
                  ·
                    refine ⟨5219845103113421307899209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 27839173883271580308795781 5219845103113421307899209)
                    ·
                      refine ⟨3914883827335065980924407, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5219845103113421307899209 3914883827335065980924407)
                      ·
                        rfl

theorem cell23_7624209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 4, 2].length) (baseStart_7624209 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7624209 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7624209 prefixEnd_7624209 := by exact prefixLift 7624209
  have htrace : WordTrace (prefixWord ++ tailWord_7624209) baseStart_7624209 baseEnd_7624209 := by
    simpa [prefixWord, tailWord_7624209, baseEnd_7624209] using wordTrace_append hprefix tailTrace_7624209
  have hstable : (prefixWord ++ tailWord_7624209).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7624209).length < 2 ^ (prefixWord ++ tailWord_7624209).sum := by decide
  have hdescent : baseEnd_7624209 < baseStart_7624209 := by decide
  rcases family_descends (prefixWord ++ tailWord_7624209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7624249 : List Nat := [1, 2, 1, 5, 1, 2, 3, 2, 6]
def baseStart_7624249 : Nat := 118140960795 + 7624249 * 2 ^ 59
def prefixEnd_7624249 : Nat := 4983230072969 + 3 ^ 40 * 7624249 * 2
def baseEnd_7624249 : Nat := 434989374062360647158247

theorem tailTrace_7624249 : CollatzResearch.WordTrace tailWord_7624249 prefixEnd_7624249 434989374062360647158247 := by
  unfold tailWord_7624249
  simp only [CollatzResearch.WordTrace]
  refine ⟨278079206155655465907395801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185386137437103643938263867 278079206155655465907395801)
  ·
    refine ⟨208559404616741599430546851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 278079206155655465907395801 208559404616741599430546851)
    ·
      refine ⟨312839106925112399145820277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 208559404616741599430546851 312839106925112399145820277)
      ·
        refine ⟨29328666274229287419920651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 312839106925112399145820277 29328666274229287419920651)
        ·
          refine ⟨43992999411343931129880977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29328666274229287419920651 43992999411343931129880977)
          ·
            refine ⟨32994749558507948347410733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43992999411343931129880977 32994749558507948347410733)
            ·
              refine ⟨12373031084440480630279025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32994749558507948347410733 12373031084440480630279025)
              ·
                refine ⟨9279773313330360472709269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12373031084440480630279025 9279773313330360472709269)
                ·
                  refine ⟨434989374062360647158247, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9279773313330360472709269 434989374062360647158247)
                  ·
                    rfl

theorem cell23_7624249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 2, 3, 2, 6].length) (baseStart_7624249 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7624249 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7624249 prefixEnd_7624249 := by exact prefixLift 7624249
  have htrace : WordTrace (prefixWord ++ tailWord_7624249) baseStart_7624249 baseEnd_7624249 := by
    simpa [prefixWord, tailWord_7624249, baseEnd_7624249] using wordTrace_append hprefix tailTrace_7624249
  have hstable : (prefixWord ++ tailWord_7624249).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7624249).length < 2 ^ (prefixWord ++ tailWord_7624249).sum := by decide
  have hdescent : baseEnd_7624249 < baseStart_7624249 := by decide
  rcases family_descends (prefixWord ++ tailWord_7624249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7624276 : List Nat := [2, 4, 1, 1, 1, 2, 1, 4, 3, 1, 3]
def baseStart_7624276 : Nat := 118140960795 + 7624276 * 2 ^ 59
def prefixEnd_7624276 : Nat := 4983230072969 + 3 ^ 40 * 7624276 * 2
def baseEnd_7624276 : Nat := 3914918230538917218786599

theorem tailTrace_7624276 : CollatzResearch.WordTrace tailWord_7624276 prefixEnd_7624276 3914918230538917218786599 := by
  unfold tailWord_7624276
  simp only [CollatzResearch.WordTrace]
  refine ⟨139040095463278824759314341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 185386793951038433012419121 139040095463278824759314341)
  ·
    refine ⟨26070017899364779642371439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 139040095463278824759314341 26070017899364779642371439)
    ·
      refine ⟨39105026849047169463557159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26070017899364779642371439 39105026849047169463557159)
      ·
        refine ⟨58657540273570754195335739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39105026849047169463557159 58657540273570754195335739)
        ·
          refine ⟨87986310410356131293003609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58657540273570754195335739 87986310410356131293003609)
          ·
            refine ⟨65989732807767098469752707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 87986310410356131293003609 65989732807767098469752707)
            ·
              refine ⟨98984599211650647704629061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65989732807767098469752707 98984599211650647704629061)
              ·
                refine ⟨18559612352184496444617949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 98984599211650647704629061 18559612352184496444617949)
                ·
                  refine ⟨6959854632069186166731731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18559612352184496444617949 6959854632069186166731731)
                  ·
                    refine ⟨10439781948103779250097597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6959854632069186166731731 10439781948103779250097597)
                    ·
                      refine ⟨3914918230538917218786599, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10439781948103779250097597 3914918230538917218786599)
                      ·
                        rfl

theorem cell23_7624276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 1, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 1, 4, 3, 1, 3].length) (baseStart_7624276 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7624276 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7624276 prefixEnd_7624276 := by exact prefixLift 7624276
  have htrace : WordTrace (prefixWord ++ tailWord_7624276) baseStart_7624276 baseEnd_7624276 := by
    simpa [prefixWord, tailWord_7624276, baseEnd_7624276] using wordTrace_append hprefix tailTrace_7624276
  have hstable : (prefixWord ++ tailWord_7624276).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7624276).length < 2 ^ (prefixWord ++ tailWord_7624276).sum := by decide
  have hdescent : baseEnd_7624276 < baseStart_7624276 := by decide
  rcases family_descends (prefixWord ++ tailWord_7624276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7624279 : List Nat := [1, 1, 3, 2, 2, 3, 1, 4, 1, 5]
def baseStart_7624279 : Nat := 118140960795 + 7624279 * 2 ^ 59
def prefixEnd_7624279 : Nat := 4983230072969 + 3 ^ 40 * 7624279 * 2
def baseEnd_7624279 : Nat := 1304973256993626902349695

theorem tailTrace_7624279 : CollatzResearch.WordTrace tailWord_7624279 prefixEnd_7624279 1304973256993626902349695 := by
  unfold tailWord_7624279
  simp only [CollatzResearch.WordTrace]
  refine ⟨278080300345546781030987891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185386866897031187353991927 278080300345546781030987891)
  ·
    refine ⟨417120450518320171546481837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 278080300345546781030987891 417120450518320171546481837)
    ·
      refine ⟨156420168944370064329930689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 417120450518320171546481837 156420168944370064329930689)
      ·
        refine ⟨117315126708277548247448017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 156420168944370064329930689 117315126708277548247448017)
        ·
          refine ⟨87986345031208161185586013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 117315126708277548247448017 87986345031208161185586013)
          ·
            refine ⟨32994879386703060444594755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 87986345031208161185586013 32994879386703060444594755)
            ·
              refine ⟨49492319080054590666892133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32994879386703060444594755 49492319080054590666892133)
              ·
                refine ⟨9279809827510235750042275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 49492319080054590666892133 9279809827510235750042275)
                ·
                  refine ⟨13919714741265353625063413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9279809827510235750042275 13919714741265353625063413)
                  ·
                    refine ⟨1304973256993626902349695, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13919714741265353625063413 1304973256993626902349695)
                    ·
                      rfl

theorem cell23_7624279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 3, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 3, 1, 4, 1, 5].length) (baseStart_7624279 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7624279 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7624279 prefixEnd_7624279 := by exact prefixLift 7624279
  have htrace : WordTrace (prefixWord ++ tailWord_7624279) baseStart_7624279 baseEnd_7624279 := by
    simpa [prefixWord, tailWord_7624279, baseEnd_7624279] using wordTrace_append hprefix tailTrace_7624279
  have hstable : (prefixWord ++ tailWord_7624279).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7624279).length < 2 ^ (prefixWord ++ tailWord_7624279).sum := by decide
  have hdescent : baseEnd_7624279 < baseStart_7624279 := by decide
  rcases family_descends (prefixWord ++ tailWord_7624279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7624282 : List Nat := [3, 1, 1, 2, 1, 1, 1, 2, 2, 5, 4]
def baseStart_7624282 : Nat := 118140960795 + 7624282 * 2 ^ 59
def prefixEnd_7624282 : Nat := 4983230072969 + 3 ^ 40 * 7624282 * 2
def baseEnd_7624282 : Nat := 3914921311422844195311571

theorem tailTrace_7624282 : CollatzResearch.WordTrace tailWord_7624282 prefixEnd_7624282 3914921311422844195311571 := by
  unfold tailWord_7624282
  simp only [CollatzResearch.WordTrace]
  refine ⟨69520102441133978135836775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 185386939843023941695564733 69520102441133978135836775)
  ·
    refine ⟨104280153661700967203755163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69520102441133978135836775 104280153661700967203755163)
    ·
      refine ⟨156420230492551450805632745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104280153661700967203755163 156420230492551450805632745)
      ·
        refine ⟨117315172869413588104224559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 156420230492551450805632745 117315172869413588104224559)
        ·
          refine ⟨175972759304120382156336839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 117315172869413588104224559 175972759304120382156336839)
          ·
            refine ⟨263959138956180573234505259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 175972759304120382156336839 263959138956180573234505259)
            ·
              refine ⟨395938708434270859851757889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 263959138956180573234505259 395938708434270859851757889)
              ·
                refine ⟨296954031325703144888818417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 395938708434270859851757889 296954031325703144888818417)
                ·
                  refine ⟨222715523494277358666613813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 296954031325703144888818417 222715523494277358666613813)
                  ·
                    refine ⟨20879580327588502374995045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 222715523494277358666613813 20879580327588502374995045)
                    ·
                      refine ⟨3914921311422844195311571, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20879580327588502374995045 3914921311422844195311571)
                      ·
                        rfl

theorem cell23_7624282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 1, 2, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 1, 2, 2, 5, 4].length) (baseStart_7624282 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7624282 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7624282 prefixEnd_7624282 := by exact prefixLift 7624282
  have htrace : WordTrace (prefixWord ++ tailWord_7624282) baseStart_7624282 baseEnd_7624282 := by
    simpa [prefixWord, tailWord_7624282, baseEnd_7624282] using wordTrace_append hprefix tailTrace_7624282
  have hstable : (prefixWord ++ tailWord_7624282).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7624282).length < 2 ^ (prefixWord ++ tailWord_7624282).sum := by decide
  have hdescent : baseEnd_7624282 < baseStart_7624282 := by decide
  rcases family_descends (prefixWord ++ tailWord_7624282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7624296 : List Nat := [2, 1, 4, 3, 1, 1, 2, 3, 1, 5]
def baseStart_7624296 : Nat := 118140960795 + 7624296 * 2 ^ 59
def prefixEnd_7624296 : Nat := 4983230072969 + 3 ^ 40 * 7624296 * 2
def baseEnd_7624296 : Nat := 1304976166717335713512169

theorem tailTrace_7624296 : CollatzResearch.WordTrace tailWord_7624296 prefixEnd_7624296 1304976166717335713512169 := by
  unfold tailWord_7624296
  simp only [CollatzResearch.WordTrace]
  refine ⟨139040460193242596467178371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 185387280257656795289571161 139040460193242596467178371)
  ·
    refine ⟨208560690289863894700767557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139040460193242596467178371 208560690289863894700767557)
    ·
      refine ⟨39105129429349480256393917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 208560690289863894700767557 39105129429349480256393917)
      ·
        refine ⟨14664423536006055096147719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39105129429349480256393917 14664423536006055096147719)
        ·
          refine ⟨21996635304009082644221579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14664423536006055096147719 21996635304009082644221579)
          ·
            refine ⟨32994952956013623966332369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21996635304009082644221579 32994952956013623966332369)
            ·
              refine ⟨24746214717010217974749277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32994952956013623966332369 24746214717010217974749277)
              ·
                refine ⟨9279830518878831740530979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24746214717010217974749277 9279830518878831740530979)
                ·
                  refine ⟨13919745778318247610796469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9279830518878831740530979 13919745778318247610796469)
                  ·
                    refine ⟨1304976166717335713512169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13919745778318247610796469 1304976166717335713512169)
                    ·
                      rfl

theorem cell23_7624296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 1, 2, 3, 1, 5].length) (baseStart_7624296 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7624296 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7624296 prefixEnd_7624296 := by exact prefixLift 7624296
  have htrace : WordTrace (prefixWord ++ tailWord_7624296) baseStart_7624296 baseEnd_7624296 := by
    simpa [prefixWord, tailWord_7624296, baseEnd_7624296] using wordTrace_append hprefix tailTrace_7624296
  have hstable : (prefixWord ++ tailWord_7624296).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7624296).length < 2 ^ (prefixWord ++ tailWord_7624296).sum := by decide
  have hdescent : baseEnd_7624296 < baseStart_7624296 := by decide
  rcases family_descends (prefixWord ++ tailWord_7624296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7624310 : List Nat := [5, 1, 1, 2, 2, 3, 1, 1, 3, 1, 3]
def baseStart_7624310 : Nat := 118140960795 + 7624310 * 2 ^ 59
def prefixEnd_7624310 : Nat := 4983230072969 + 3 ^ 40 * 7624310 * 2
def baseEnd_7624310 : Nat := 3914935688881170085761443

theorem tailTrace_7624310 : CollatzResearch.WordTrace tailWord_7624310 prefixEnd_7624310 3914935688881170085761443 := by
  unfold tailWord_7624310
  simp only [CollatzResearch.WordTrace]
  refine ⟨17380089438027154582835399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 185387620672289648883577589 17380089438027154582835399)
  ·
    refine ⟨26070134157040731874253099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17380089438027154582835399 26070134157040731874253099)
    ·
      refine ⟨39105201235561097811379649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26070134157040731874253099 39105201235561097811379649)
      ·
        refine ⟨29328900926670823358534737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39105201235561097811379649 29328900926670823358534737)
        ·
          refine ⟨21996675695003117518901053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29328900926670823358534737 21996675695003117518901053)
          ·
            refine ⟨8248753385626169069587895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21996675695003117518901053 8248753385626169069587895)
            ·
              refine ⟨12373130078439253604381843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8248753385626169069587895 12373130078439253604381843)
              ·
                refine ⟨18559695117658880406572765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12373130078439253604381843 18559695117658880406572765)
                ·
                  refine ⟨6959885669122080152464787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18559695117658880406572765 6959885669122080152464787)
                  ·
                    refine ⟨10439828503683120228697181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6959885669122080152464787 10439828503683120228697181)
                    ·
                      refine ⟨3914935688881170085761443, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10439828503683120228697181 3914935688881170085761443)
                      ·
                        rfl

theorem cell23_7624310_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 3, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 3, 1, 1, 3, 1, 3].length) (baseStart_7624310 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7624310 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7624310 prefixEnd_7624310 := by exact prefixLift 7624310
  have htrace : WordTrace (prefixWord ++ tailWord_7624310) baseStart_7624310 baseEnd_7624310 := by
    simpa [prefixWord, tailWord_7624310, baseEnd_7624310] using wordTrace_append hprefix tailTrace_7624310
  have hstable : (prefixWord ++ tailWord_7624310).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7624310).length < 2 ^ (prefixWord ++ tailWord_7624310).sum := by decide
  have hdescent : baseEnd_7624310 < baseStart_7624310 := by decide
  rcases family_descends (prefixWord ++ tailWord_7624310) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7624312 : List Nat := [2, 1, 2, 1, 1, 1, 2, 1, 2, 6, 4]
def baseStart_7624312 : Nat := 118140960795 + 7624312 * 2 ^ 59
def prefixEnd_7624312 : Nat := 4983230072969 + 3 ^ 40 * 7624312 * 2
def baseEnd_7624312 : Nat := 3914936715842479077936433

theorem tailTrace_7624312 : CollatzResearch.WordTrace tailWord_7624312 prefixEnd_7624312 3914936715842479077936433 := by
  unfold tailWord_7624312
  simp only [CollatzResearch.WordTrace]
  refine ⟨139040751977213613833469595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 185387669302951485111292793 139040751977213613833469595)
  ·
    refine ⟨208561127965820420750204393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139040751977213613833469595 208561127965820420750204393)
    ·
      refine ⟨156420845974365315562653295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 208561127965820420750204393 156420845974365315562653295)
      ·
        refine ⟨234631268961547973343979943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 156420845974365315562653295 234631268961547973343979943)
        ·
          refine ⟨351946903442321960015969915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 234631268961547973343979943 351946903442321960015969915)
          ·
            refine ⟨527920355163482940023954873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 351946903442321960015969915 527920355163482940023954873)
            ·
              refine ⟨395940266372612205017966155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 527920355163482940023954873 395940266372612205017966155)
              ·
                refine ⟨593910399558918307526949233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 395940266372612205017966155 593910399558918307526949233)
                ·
                  refine ⟨445432799669188730645211925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 593910399558918307526949233 445432799669188730645211925)
                  ·
                    refine ⟨20879662484493221748994309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 445432799669188730645211925 20879662484493221748994309)
                    ·
                      refine ⟨3914936715842479077936433, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20879662484493221748994309 3914936715842479077936433)
                      ·
                        rfl

theorem cell23_7624312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 1, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 1, 2, 6, 4].length) (baseStart_7624312 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7624312 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7624312 prefixEnd_7624312 := by exact prefixLift 7624312
  have htrace : WordTrace (prefixWord ++ tailWord_7624312) baseStart_7624312 baseEnd_7624312 := by
    simpa [prefixWord, tailWord_7624312, baseEnd_7624312] using wordTrace_append hprefix tailTrace_7624312
  have hstable : (prefixWord ++ tailWord_7624312).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7624312).length < 2 ^ (prefixWord ++ tailWord_7624312).sum := by decide
  have hdescent : baseEnd_7624312 < baseStart_7624312 := by decide
  rcases family_descends (prefixWord ++ tailWord_7624312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7624350 : List Nat := [4, 3, 1, 1, 1, 3, 3, 1, 1, 1, 4]
def baseStart_7624350 : Nat := 118140960795 + 7624350 * 2 ^ 59
def prefixEnd_7624350 : Nat := 4983230072969 + 3 ^ 40 * 7624350 * 2
def baseEnd_7624350 : Nat := 3914956228107349929261259

theorem tailTrace_7624350 : CollatzResearch.WordTrace tailWord_7624350 prefixEnd_7624350 3914956228107349929261259 := by
  unfold tailWord_7624350
  simp only [CollatzResearch.WordTrace]
  refine ⟨34760361241036195019602813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 185388593285526373437881669 34760361241036195019602813)
  ·
    refine ⟨13035135465388573132351055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34760361241036195019602813 13035135465388573132351055)
    ·
      refine ⟨19552703198082859698526583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13035135465388573132351055 19552703198082859698526583)
      ·
        refine ⟨29329054797124289547789875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19552703198082859698526583 29329054797124289547789875)
        ·
          refine ⟨43993582195686434321684813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29329054797124289547789875 43993582195686434321684813)
          ·
            refine ⟨16497593323382412870631805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43993582195686434321684813 16497593323382412870631805)
            ·
              refine ⟨6186597496268404826486927, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16497593323382412870631805 6186597496268404826486927)
              ·
                refine ⟨9279896244402607239730391, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6186597496268404826486927 9279896244402607239730391)
                ·
                  refine ⟨13919844366603910859595587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9279896244402607239730391 13919844366603910859595587)
                  ·
                    refine ⟨20879766549905866289393381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13919844366603910859595587 20879766549905866289393381)
                    ·
                      refine ⟨3914956228107349929261259, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20879766549905866289393381 3914956228107349929261259)
                      ·
                        rfl

theorem cell23_7624350_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 3, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 3, 3, 1, 1, 1, 4].length) (baseStart_7624350 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7624350 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7624350 prefixEnd_7624350 := by exact prefixLift 7624350
  have htrace : WordTrace (prefixWord ++ tailWord_7624350) baseStart_7624350 baseEnd_7624350 := by
    simpa [prefixWord, tailWord_7624350, baseEnd_7624350] using wordTrace_append hprefix tailTrace_7624350
  have hstable : (prefixWord ++ tailWord_7624350).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7624350).length < 2 ^ (prefixWord ++ tailWord_7624350).sum := by decide
  have hdescent : baseEnd_7624350 < baseStart_7624350 := by decide
  rcases family_descends (prefixWord ++ tailWord_7624350) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7624373 : List Nat := [1, 3, 3, 3, 3, 1, 1, 8]
def baseStart_7624373 : Nat := 118140960795 + 7624373 * 2 ^ 59
def prefixEnd_7624373 : Nat := 4983230072969 + 3 ^ 40 * 7624373 * 2
def baseEnd_7624373 : Nat := 144998816228237160713839

theorem tailTrace_7624373 : CollatzResearch.WordTrace tailWord_7624373 prefixEnd_7624373 144998816228237160713839 := by
  unfold tailWord_7624373
  simp only [CollatzResearch.WordTrace]
  refine ⟨278083728807206235084909773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185389152538137490056606515 278083728807206235084909773)
  ·
    refine ⟨104281398302702338156841165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 278083728807206235084909773 104281398302702338156841165)
    ·
      refine ⟨39105524363513376808815437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 104281398302702338156841165 39105524363513376808815437)
      ·
        refine ⟨14664571636317516303305789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39105524363513376808815437 14664571636317516303305789)
        ·
          refine ⟨5499214363619068613739671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14664571636317516303305789 5499214363619068613739671)
          ·
            refine ⟨8248821545428602920609507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5499214363619068613739671 8248821545428602920609507)
            ·
              refine ⟨12373232318142904380914261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8248821545428602920609507 12373232318142904380914261)
              ·
                refine ⟨144998816228237160713839, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 12373232318142904380914261 144998816228237160713839)
                ·
                  rfl

theorem cell23_7624373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 3, 1, 1, 8].length) (baseStart_7624373 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7624373 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7624373 prefixEnd_7624373 := by exact prefixLift 7624373
  have htrace : WordTrace (prefixWord ++ tailWord_7624373) baseStart_7624373 baseEnd_7624373 := by
    simpa [prefixWord, tailWord_7624373, baseEnd_7624373] using wordTrace_append hprefix tailTrace_7624373
  have hstable : (prefixWord ++ tailWord_7624373).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7624373).length < 2 ^ (prefixWord ++ tailWord_7624373).sum := by decide
  have hdescent : baseEnd_7624373 < baseStart_7624373 := by decide
  rcases family_descends (prefixWord ++ tailWord_7624373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7624390 : List Nat := [6, 1, 2, 1, 1, 2, 3, 7]
def baseStart_7624390 : Nat := 118140960795 + 7624390 * 2 ^ 59
def prefixEnd_7624390 : Nat := 4983230072969 + 3 ^ 40 * 7624390 * 2
def baseEnd_7624390 : Nat := 144999139530871473065225

theorem tailTrace_7624390 : CollatzResearch.WordTrace tailWord_7624390 prefixEnd_7624390 144999139530871473065225 := by
  unfold tailWord_7624390
  simp only [CollatzResearch.WordTrace]
  refine ⟨8690135901504520218383707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 185389565898763097992185749 8690135901504520218383707)
  ·
    refine ⟨13035203852256780327575561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8690135901504520218383707 13035203852256780327575561)
    ·
      refine ⟨9776402889192585245681671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13035203852256780327575561 9776402889192585245681671)
      ·
        refine ⟨14664604333788877868522507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9776402889192585245681671 14664604333788877868522507)
        ·
          refine ⟨21996906500683316802783761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14664604333788877868522507 21996906500683316802783761)
          ·
            refine ⟨16497679875512487602087821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21996906500683316802783761 16497679875512487602087821)
            ·
              refine ⟨6186629953317182850782933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16497679875512487602087821 6186629953317182850782933)
              ·
                refine ⟨144999139530871473065225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6186629953317182850782933 144999139530871473065225)
                ·
                  rfl

theorem cell23_7624390_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 2, 3, 7].length) (baseStart_7624390 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7624390 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7624390 prefixEnd_7624390 := by exact prefixLift 7624390
  have htrace : WordTrace (prefixWord ++ tailWord_7624390) baseStart_7624390 baseEnd_7624390 := by
    simpa [prefixWord, tailWord_7624390, baseEnd_7624390] using wordTrace_append hprefix tailTrace_7624390
  have hstable : (prefixWord ++ tailWord_7624390).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7624390).length < 2 ^ (prefixWord ++ tailWord_7624390).sum := by decide
  have hdescent : baseEnd_7624390 < baseStart_7624390 := by decide
  rcases family_descends (prefixWord ++ tailWord_7624390) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7624410 : List Nat := [3, 1, 1, 2, 2, 3, 4, 1, 1, 3, 2]
def baseStart_7624410 : Nat := 118140960795 + 7624410 * 2 ^ 59
def prefixEnd_7624410 : Nat := 4983230072969 + 3 ^ 40 * 7624410 * 2
def baseEnd_7624410 : Nat := 3914987036946619694510983

theorem tailTrace_7624410 : CollatzResearch.WordTrace tailWord_7624410 prefixEnd_7624410 3914987036946619694510983 := by
  unfold tailWord_7624410
  simp only [CollatzResearch.WordTrace]
  refine ⟨69521269577018047601001671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 185390052205381460269337789 69521269577018047601001671)
  ·
    refine ⟨104281904365527071401502507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69521269577018047601001671 104281904365527071401502507)
    ·
      refine ⟨156422856548290607102253761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104281904365527071401502507 156422856548290607102253761)
      ·
        refine ⟨117317142411217955326690321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 156422856548290607102253761 117317142411217955326690321)
        ·
          refine ⟨87987856808413466495017741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 117317142411217955326690321 87987856808413466495017741)
          ·
            refine ⟨32995446303155049935631653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 87987856808413466495017741 32995446303155049935631653)
            ·
              refine ⟨6186646181841571862930935, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 32995446303155049935631653 6186646181841571862930935)
              ·
                refine ⟨9279969272762357794396403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6186646181841571862930935 9279969272762357794396403)
                ·
                  refine ⟨13919953909143536691594605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9279969272762357794396403 13919953909143536691594605)
                  ·
                    refine ⟨5219982715928826259347977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13919953909143536691594605 5219982715928826259347977)
                    ·
                      refine ⟨3914987036946619694510983, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5219982715928826259347977 3914987036946619694510983)
                      ·
                        rfl

theorem cell23_7624410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 3, 4, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 3, 4, 1, 1, 3, 2].length) (baseStart_7624410 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7624410 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7624410 prefixEnd_7624410 := by exact prefixLift 7624410
  have htrace : WordTrace (prefixWord ++ tailWord_7624410) baseStart_7624410 baseEnd_7624410 := by
    simpa [prefixWord, tailWord_7624410, baseEnd_7624410] using wordTrace_append hprefix tailTrace_7624410
  have hstable : (prefixWord ++ tailWord_7624410).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7624410).length < 2 ^ (prefixWord ++ tailWord_7624410).sum := by decide
  have hdescent : baseEnd_7624410 < baseStart_7624410 := by decide
  rcases family_descends (prefixWord ++ tailWord_7624410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7624417 : List Nat := [1, 2, 3, 1, 6, 1, 1, 2, 2, 1, 3]
def baseStart_7624417 : Nat := 118140960795 + 7624417 * 2 ^ 59
def prefixEnd_7624417 : Nat := 4983230072969 + 3 ^ 40 * 7624417 * 2
def baseEnd_7624417 : Nat := 3914990631311201167123451

theorem tailTrace_7624417 : CollatzResearch.WordTrace tailWord_7624417 prefixEnd_7624417 3914990631311201167123451 := by
  unfold tailWord_7624417
  simp only [CollatzResearch.WordTrace]
  refine ⟨278085333619046830599511505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185390222412697887066341003 278085333619046830599511505)
  ·
    refine ⟨208564000214285122949633629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 278085333619046830599511505 208564000214285122949633629)
    ·
      refine ⟨78211500080356921106112611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 208564000214285122949633629 78211500080356921106112611)
      ·
        refine ⟨117317250120535381659168917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78211500080356921106112611 117317250120535381659168917)
        ·
          refine ⟨5499246099400096015273543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 117317250120535381659168917 5499246099400096015273543)
          ·
            refine ⟨8248869149100144022910315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5499246099400096015273543 8248869149100144022910315)
            ·
              refine ⟨12373303723650216034365473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8248869149100144022910315 12373303723650216034365473)
              ·
                refine ⟨9279977792737662025774105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12373303723650216034365473 9279977792737662025774105)
                ·
                  refine ⟨6959983344553246519330579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9279977792737662025774105 6959983344553246519330579)
                  ·
                    refine ⟨10439975016829869778995869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6959983344553246519330579 10439975016829869778995869)
                    ·
                      refine ⟨3914990631311201167123451, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10439975016829869778995869 3914990631311201167123451)
                      ·
                        rfl

theorem cell23_7624417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 6, 1, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 6, 1, 1, 2, 2, 1, 3].length) (baseStart_7624417 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7624417 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7624417 prefixEnd_7624417 := by exact prefixLift 7624417
  have htrace : WordTrace (prefixWord ++ tailWord_7624417) baseStart_7624417 baseEnd_7624417 := by
    simpa [prefixWord, tailWord_7624417, baseEnd_7624417] using wordTrace_append hprefix tailTrace_7624417
  have hstable : (prefixWord ++ tailWord_7624417).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7624417).length < 2 ^ (prefixWord ++ tailWord_7624417).sum := by decide
  have hdescent : baseEnd_7624417 < baseStart_7624417 := by decide
  rcases family_descends (prefixWord ++ tailWord_7624417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7624459 : List Nat := [1, 1, 1, 1, 5, 1, 4, 1, 1, 7]
def baseStart_7624459 : Nat := 118140960795 + 7624459 * 2 ^ 59
def prefixEnd_7624459 : Nat := 4983230072969 + 3 ^ 40 * 7624459 * 2
def baseEnd_7624459 : Nat := 1305004065832896667599419

theorem tailTrace_7624459 : CollatzResearch.WordTrace tailWord_7624459 prefixEnd_7624459 1305004065832896667599419 := by
  unfold tailWord_7624459
  simp only [CollatzResearch.WordTrace]
  refine ⟨278086865484894671772540431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185391243656596447848360287 278086865484894671772540431)
  ·
    refine ⟨417130298227342007658810647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 278086865484894671772540431 417130298227342007658810647)
    ·
      refine ⟨625695447341013011488215971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 417130298227342007658810647 625695447341013011488215971)
      ·
        refine ⟨938543171011519517232323957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 625695447341013011488215971 938543171011519517232323957)
        ·
          refine ⟨87988422282329954740530371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 938543171011519517232323957 87988422282329954740530371)
          ·
            refine ⟨131982633423494932110795557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87988422282329954740530371 131982633423494932110795557)
            ·
              refine ⟨24746743766905299770774167, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 131982633423494932110795557 24746743766905299770774167)
              ·
                refine ⟨37120115650357949656161251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24746743766905299770774167 37120115650357949656161251)
                ·
                  refine ⟨55680173475536924484241877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37120115650357949656161251 55680173475536924484241877)
                  ·
                    refine ⟨1305004065832896667599419, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 55680173475536924484241877 1305004065832896667599419)
                    ·
                      rfl

theorem cell23_7624459_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 4, 1, 1, 7].length) (baseStart_7624459 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7624459 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7624459 prefixEnd_7624459 := by exact prefixLift 7624459
  have htrace : WordTrace (prefixWord ++ tailWord_7624459) baseStart_7624459 baseEnd_7624459 := by
    simpa [prefixWord, tailWord_7624459, baseEnd_7624459] using wordTrace_append hprefix tailTrace_7624459
  have hstable : (prefixWord ++ tailWord_7624459).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7624459).length < 2 ^ (prefixWord ++ tailWord_7624459).sum := by decide
  have hdescent : baseEnd_7624459 < baseStart_7624459 := by decide
  rcases family_descends (prefixWord ++ tailWord_7624459) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7624476 : List Nat := [2, 2, 3, 1, 1, 2, 3, 2, 2, 5]
def baseStart_7624476 : Nat := 118140960795 + 7624476 * 2 ^ 59
def prefixEnd_7624476 : Nat := 4983230072969 + 3 ^ 40 * 7624476 * 2
def baseEnd_7624476 : Nat := 1305006975556605478761893

theorem tailTrace_7624476 : CollatzResearch.WordTrace tailWord_7624476 prefixEnd_7624476 1305006975556605478761893 := by
  unfold tailWord_7624476
  simp only [CollatzResearch.WordTrace]
  refine ⟨139043742762916541837954641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 185391657017222055783939521 139043742762916541837954641)
  ·
    refine ⟨104282807072187406378465981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 139043742762916541837954641 104282807072187406378465981)
    ·
      refine ⟨39106052652070277391924743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 104282807072187406378465981 39106052652070277391924743)
      ·
        refine ⟨58659078978105416087887115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39106052652070277391924743 58659078978105416087887115)
        ·
          refine ⟨87988618467158124131830673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58659078978105416087887115 87988618467158124131830673)
          ·
            refine ⟨65991463850368593098873005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 87988618467158124131830673 65991463850368593098873005)
            ·
              refine ⟨24746798943888222412077377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 65991463850368593098873005 24746798943888222412077377)
              ·
                refine ⟨18560099207916166809058033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24746798943888222412077377 18560099207916166809058033)
                ·
                  refine ⟨13920074405937125106793525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18560099207916166809058033 13920074405937125106793525)
                  ·
                    refine ⟨1305006975556605478761893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13920074405937125106793525 1305006975556605478761893)
                    ·
                      rfl

theorem cell23_7624476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 3, 2, 2, 5].length) (baseStart_7624476 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7624476 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7624476 prefixEnd_7624476 := by exact prefixLift 7624476
  have htrace : WordTrace (prefixWord ++ tailWord_7624476) baseStart_7624476 baseEnd_7624476 := by
    simpa [prefixWord, tailWord_7624476, baseEnd_7624476] using wordTrace_append hprefix tailTrace_7624476
  have hstable : (prefixWord ++ tailWord_7624476).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7624476).length < 2 ^ (prefixWord ++ tailWord_7624476).sum := by decide
  have hdescent : baseEnd_7624476 < baseStart_7624476 := by decide
  rcases family_descends (prefixWord ++ tailWord_7624476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7624519 : List Nat := [1, 1, 4, 1, 2, 1, 2, 1, 10]
def baseStart_7624519 : Nat := 118140960795 + 7624519 * 2 ^ 59
def prefixEnd_7624519 : Nat := 4983230072969 + 3 ^ 40 * 7624519 * 2
def baseEnd_7624519 : Nat := 435004778481995529783109

theorem tailTrace_7624519 : CollatzResearch.WordTrace tailWord_7624519 prefixEnd_7624519 435004778481995529783109 := by
  unfold tailWord_7624519
  simp only [CollatzResearch.WordTrace]
  refine ⟨278089053864677302019724611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185392702576451534679816407 278089053864677302019724611)
  ·
    refine ⟨417133580797015953029586917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 278089053864677302019724611 417133580797015953029586917)
    ·
      refine ⟨78212546399440491193047547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 417133580797015953029586917 78212546399440491193047547)
      ·
        refine ⟨117318819599160736789571321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78212546399440491193047547 117318819599160736789571321)
        ·
          refine ⟨87989114699370552592178491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 117318819599160736789571321 87989114699370552592178491)
          ·
            refine ⟨131983672049055828888267737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87989114699370552592178491 131983672049055828888267737)
            ·
              refine ⟨98987754036791871666200803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 131983672049055828888267737 98987754036791871666200803)
              ·
                refine ⟨148481631055187807499301205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 98987754036791871666200803 148481631055187807499301205)
                ·
                  refine ⟨435004778481995529783109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 148481631055187807499301205 435004778481995529783109)
                  ·
                    rfl

theorem cell23_7624519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 2, 1, 10].length) (baseStart_7624519 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7624519 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7624519 prefixEnd_7624519 := by exact prefixLift 7624519
  have htrace : WordTrace (prefixWord ++ tailWord_7624519) baseStart_7624519 baseEnd_7624519 := by
    simpa [prefixWord, tailWord_7624519, baseEnd_7624519] using wordTrace_append hprefix tailTrace_7624519
  have hstable : (prefixWord ++ tailWord_7624519).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7624519).length < 2 ^ (prefixWord ++ tailWord_7624519).sum := by decide
  have hdescent : baseEnd_7624519 < baseStart_7624519 := by decide
  rcases family_descends (prefixWord ++ tailWord_7624519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7624533 : List Nat := [1, 3, 2, 2, 2, 2, 2, 2, 2, 2, 3]
def baseStart_7624533 : Nat := 118140960795 + 7624533 * 2 ^ 59
def prefixEnd_7624533 : Nat := 4983230072969 + 3 ^ 40 * 7624533 * 2
def baseEnd_7624533 : Nat := 3915050195067122713272917

theorem tailTrace_7624533 : CollatzResearch.WordTrace tailWord_7624533 prefixEnd_7624533 3915050195067122713272917 := by
  unfold tailWord_7624533
  simp only [CollatzResearch.WordTrace]
  refine ⟨278089564486626582410734253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185393042991084388273822835 278089564486626582410734253)
  ·
    refine ⟨104283586682484968404025345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 278089564486626582410734253 104283586682484968404025345)
    ·
      refine ⟨78212690011863726303019009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 104283586682484968404025345 78212690011863726303019009)
      ·
        refine ⟨58659517508897794727264257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78212690011863726303019009 58659517508897794727264257)
        ·
          refine ⟨43994638131673346045448193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58659517508897794727264257 43994638131673346045448193)
          ·
            refine ⟨32995978598755009534086145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43994638131673346045448193 32995978598755009534086145)
            ·
              refine ⟨24746983949066257150564609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32995978598755009534086145 24746983949066257150564609)
              ·
                refine ⟨18560237961799692862923457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24746983949066257150564609 18560237961799692862923457)
                ·
                  refine ⟨13920178471349769647192593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18560237961799692862923457 13920178471349769647192593)
                  ·
                    refine ⟨10440133853512327235394445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13920178471349769647192593 10440133853512327235394445)
                    ·
                      refine ⟨3915050195067122713272917, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10440133853512327235394445 3915050195067122713272917)
                      ·
                        rfl

theorem cell23_7624533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 2, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 2, 2, 2, 2, 2, 3].length) (baseStart_7624533 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7624533 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7624533 prefixEnd_7624533 := by exact prefixLift 7624533
  have htrace : WordTrace (prefixWord ++ tailWord_7624533) baseStart_7624533 baseEnd_7624533 := by
    simpa [prefixWord, tailWord_7624533, baseEnd_7624533] using wordTrace_append hprefix tailTrace_7624533
  have hstable : (prefixWord ++ tailWord_7624533).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7624533).length < 2 ^ (prefixWord ++ tailWord_7624533).sum := by decide
  have hdescent : baseEnd_7624533 < baseStart_7624533 := by decide
  rcases family_descends (prefixWord ++ tailWord_7624533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7624574 : List Nat := [4, 2, 3, 1, 1, 2, 2, 3, 1, 4]
def baseStart_7624574 : Nat := 118140960795 + 7624574 * 2 ^ 59
def prefixEnd_7624574 : Nat := 4983230072969 + 3 ^ 40 * 7624574 * 2
def baseEnd_7624574 : Nat := 1305023749257985684286743

theorem tailTrace_7624574 : CollatzResearch.WordTrace tailWord_7624574 prefixEnd_7624574 1305023749257985684286743 := by
  unfold tailWord_7624574
  simp only [CollatzResearch.WordTrace]
  refine ⟨34761382484934755801622097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 185394039919652030941984517 34761382484934755801622097)
  ·
    refine ⟨26071036863701066851216573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34761382484934755801622097 26071036863701066851216573)
    ·
      refine ⟨9776638823887900069206215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26071036863701066851216573 9776638823887900069206215)
      ·
        refine ⟨14664958235831850103809323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9776638823887900069206215 14664958235831850103809323)
        ·
          refine ⟨21997437353747775155713985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14664958235831850103809323 21997437353747775155713985)
          ·
            refine ⟨16498078015310831366785489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21997437353747775155713985 16498078015310831366785489)
            ·
              refine ⟨12373558511483123525089117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16498078015310831366785489 12373558511483123525089117)
              ·
                refine ⟨4640084441806171321908419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12373558511483123525089117 4640084441806171321908419)
                ·
                  refine ⟨6960126662709256982862629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4640084441806171321908419 6960126662709256982862629)
                  ·
                    refine ⟨1305023749257985684286743, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6960126662709256982862629 1305023749257985684286743)
                    ·
                      rfl

theorem cell23_7624574_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 2, 2, 3, 1, 4].length) (baseStart_7624574 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7624574 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7624574 prefixEnd_7624574 := by exact prefixLift 7624574
  have htrace : WordTrace (prefixWord ++ tailWord_7624574) baseStart_7624574 baseEnd_7624574 := by
    simpa [prefixWord, tailWord_7624574, baseEnd_7624574] using wordTrace_append hprefix tailTrace_7624574
  have hstable : (prefixWord ++ tailWord_7624574).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7624574).length < 2 ^ (prefixWord ++ tailWord_7624574).sum := by decide
  have hdescent : baseEnd_7624574 < baseStart_7624574 := by decide
  rcases family_descends (prefixWord ++ tailWord_7624574) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7624613 : List Nat := [1, 3, 1, 2, 1, 1, 1, 7, 2, 4]
def baseStart_7624613 : Nat := 118140960795 + 7624613 * 2 ^ 59
def prefixEnd_7624613 : Nat := 4983230072969 + 3 ^ 40 * 7624613 * 2
def baseEnd_7624613 : Nat := 1305030424506494133424183

theorem tailTrace_7624613 : CollatzResearch.WordTrace tailWord_7624613 prefixEnd_7624613 1305030424506494133424183 := by
  unfold tailWord_7624613
  simp only [CollatzResearch.WordTrace]
  refine ⟨278092482326336756073646493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185394988217557837382430995 278092482326336756073646493)
  ·
    refine ⟨104284680872376283527617435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 278092482326336756073646493 104284680872376283527617435)
    ·
      refine ⟨156427021308564425291426153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104284680872376283527617435 156427021308564425291426153)
      ·
        refine ⟨117320265981423318968569615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 156427021308564425291426153 117320265981423318968569615)
        ·
          refine ⟨175980398972134978452854423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 117320265981423318968569615 175980398972134978452854423)
          ·
            refine ⟨263970598458202467679281635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 175980398972134978452854423 263970598458202467679281635)
            ·
              refine ⟨395955897687303701518922453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 263970598458202467679281635 395955897687303701518922453)
              ·
                refine ⟨9280216352046180504349745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 395955897687303701518922453 9280216352046180504349745)
                ·
                  refine ⟨6960162264034635378262309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9280216352046180504349745 6960162264034635378262309)
                  ·
                    refine ⟨1305030424506494133424183, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6960162264034635378262309 1305030424506494133424183)
                    ·
                      rfl

theorem cell23_7624613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 1, 7, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 1, 7, 2, 4].length) (baseStart_7624613 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7624613 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7624613 prefixEnd_7624613 := by exact prefixLift 7624613
  have htrace : WordTrace (prefixWord ++ tailWord_7624613) baseStart_7624613 baseEnd_7624613 := by
    simpa [prefixWord, tailWord_7624613, baseEnd_7624613] using wordTrace_append hprefix tailTrace_7624613
  have hstable : (prefixWord ++ tailWord_7624613).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7624613).length < 2 ^ (prefixWord ++ tailWord_7624613).sum := by decide
  have hdescent : baseEnd_7624613 < baseStart_7624613 := by decide
  rcases family_descends (prefixWord ++ tailWord_7624613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7624733 : List Nat := [1, 4, 2, 2, 2, 1, 1, 1, 9]
def baseStart_7624733 : Nat := 118140960795 + 7624733 * 2 ^ 59
def prefixEnd_7624733 : Nat := 4983230072969 + 3 ^ 40 * 7624733 * 2
def baseEnd_7624733 : Nat := 435016987910891325641333

theorem tailTrace_7624733 : CollatzResearch.WordTrace tailWord_7624733 prefixEnd_7624733 435016987910891325641333 := by
  unfold tailWord_7624733
  simp only [CollatzResearch.WordTrace]
  refine ⟨278096859085902016568014853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185397906057268011045343235 278096859085902016568014853)
  ·
    refine ⟨52143161078606628106502785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 278096859085902016568014853 52143161078606628106502785)
    ·
      refine ⟨39107370808954971079877089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52143161078606628106502785 39107370808954971079877089)
      ·
        refine ⟨29330528106716228309907817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39107370808954971079877089 29330528106716228309907817)
        ·
          refine ⟨21997896080037171232430863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29330528106716228309907817 21997896080037171232430863)
          ·
            refine ⟨32996844120055756848646295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21997896080037171232430863 32996844120055756848646295)
            ·
              refine ⟨49495266180083635272969443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32996844120055756848646295 49495266180083635272969443)
              ·
                refine ⟨74242899270125452909454165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49495266180083635272969443 74242899270125452909454165)
                ·
                  refine ⟨435016987910891325641333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 74242899270125452909454165 435016987910891325641333)
                  ·
                    rfl

theorem cell23_7624733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 1, 1, 1, 9].length) (baseStart_7624733 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7624733 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7624733 prefixEnd_7624733 := by exact prefixLift 7624733
  have htrace : WordTrace (prefixWord ++ tailWord_7624733) baseStart_7624733 baseEnd_7624733 := by
    simpa [prefixWord, tailWord_7624733, baseEnd_7624733] using wordTrace_append hprefix tailTrace_7624733
  have hstable : (prefixWord ++ tailWord_7624733).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7624733).length < 2 ^ (prefixWord ++ tailWord_7624733).sum := by decide
  have hdescent : baseEnd_7624733 < baseStart_7624733 := by decide
  rcases family_descends (prefixWord ++ tailWord_7624733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7624761 : List Nat := [1, 2, 1, 5, 3, 2, 1, 2, 2, 2, 2]
def baseStart_7624761 : Nat := 118140960795 + 7624761 * 2 ^ 59
def prefixEnd_7624761 : Nat := 4983230072969 + 3 ^ 40 * 7624761 * 2
def baseEnd_7624761 : Nat := 3915167268656347821221869

theorem tailTrace_7624761 : CollatzResearch.WordTrace tailWord_7624761 prefixEnd_7624761 3915167268656347821221869 := by
  unfold tailWord_7624761
  simp only [CollatzResearch.WordTrace]
  refine ⟨278097880329800577350034137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185398586886533718233356091 278097880329800577350034137)
  ·
    refine ⟨208573410247350433012525603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 278097880329800577350034137 208573410247350433012525603)
    ·
      refine ⟨312860115371025649518788405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 208573410247350433012525603 312860115371025649518788405)
      ·
        refine ⟨29330635816033654642386413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 312860115371025649518788405 29330635816033654642386413)
        ·
          refine ⟨10998988431012620490894905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29330635816033654642386413 10998988431012620490894905)
          ·
            refine ⟨8249241323259465368171179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10998988431012620490894905 8249241323259465368171179)
            ·
              refine ⟨12373861984889198052256769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8249241323259465368171179 12373861984889198052256769)
              ·
                refine ⟨9280396488666898539192577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12373861984889198052256769 9280396488666898539192577)
                ·
                  refine ⟨6960297366500173904394433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9280396488666898539192577 6960297366500173904394433)
                  ·
                    refine ⟨5220223024875130428295825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6960297366500173904394433 5220223024875130428295825)
                    ·
                      refine ⟨3915167268656347821221869, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5220223024875130428295825 3915167268656347821221869)
                      ·
                        rfl

theorem cell23_7624761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 3, 2, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 3, 2, 1, 2, 2, 2, 2].length) (baseStart_7624761 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7624761 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7624761 prefixEnd_7624761 := by exact prefixLift 7624761
  have htrace : WordTrace (prefixWord ++ tailWord_7624761) baseStart_7624761 baseEnd_7624761 := by
    simpa [prefixWord, tailWord_7624761, baseEnd_7624761] using wordTrace_append hprefix tailTrace_7624761
  have hstable : (prefixWord ++ tailWord_7624761).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7624761).length < 2 ^ (prefixWord ++ tailWord_7624761).sum := by decide
  have hdescent : baseEnd_7624761 < baseStart_7624761 := by decide
  rcases family_descends (prefixWord ++ tailWord_7624761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7624783 : List Nat := [1, 1, 2, 1, 1, 2, 2, 4, 4, 1, 4]
def baseStart_7624783 : Nat := 118140960795 + 7624783 * 2 ^ 59
def prefixEnd_7624783 : Nat := 4983230072969 + 3 ^ 40 * 7624783 * 2
def baseEnd_7624783 : Nat := 3915178565230746735146767

theorem tailTrace_7624783 : CollatzResearch.WordTrace tailWord_7624783 prefixEnd_7624783 3915178565230746735146767 := by
  unfold tailWord_7624783
  simp only [CollatzResearch.WordTrace]
  refine ⟨278098682735720875107335003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185399121823813916738223335 278098682735720875107335003)
  ·
    refine ⟨417148024103581312661002505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 278098682735720875107335003 417148024103581312661002505)
    ·
      refine ⟨312861018077685984495751879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 417148024103581312661002505 312861018077685984495751879)
      ·
        refine ⟨469291527116528976743627819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 312861018077685984495751879 469291527116528976743627819)
        ·
          refine ⟨703937290674793465115441729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 469291527116528976743627819 703937290674793465115441729)
          ·
            refine ⟨527952968006095098836581297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 703937290674793465115441729 527952968006095098836581297)
            ·
              refine ⟨395964726004571324127435973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 527952968006095098836581297 395964726004571324127435973)
              ·
                refine ⟨74243386125857123273894245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 395964726004571324127435973 74243386125857123273894245)
                ·
                  refine ⟨13920634898598210613855171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 74243386125857123273894245 13920634898598210613855171)
                  ·
                    refine ⟨20880952347897315920782757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13920634898598210613855171 20880952347897315920782757)
                    ·
                      refine ⟨3915178565230746735146767, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20880952347897315920782757 3915178565230746735146767)
                      ·
                        rfl

theorem cell23_7624783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 2, 4, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 2, 4, 4, 1, 4].length) (baseStart_7624783 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7624783 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7624783 prefixEnd_7624783 := by exact prefixLift 7624783
  have htrace : WordTrace (prefixWord ++ tailWord_7624783) baseStart_7624783 baseEnd_7624783 := by
    simpa [prefixWord, tailWord_7624783, baseEnd_7624783] using wordTrace_append hprefix tailTrace_7624783
  have hstable : (prefixWord ++ tailWord_7624783).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7624783).length < 2 ^ (prefixWord ++ tailWord_7624783).sum := by decide
  have hdescent : baseEnd_7624783 < baseStart_7624783 := by decide
  rcases family_descends (prefixWord ++ tailWord_7624783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7624823 : List Nat := [1, 1, 3, 1, 1, 5, 2, 1, 8]
def baseStart_7624823 : Nat := 118140960795 + 7624823 * 2 ^ 59
def prefixEnd_7624823 : Nat := 4983230072969 + 3 ^ 40 * 7624823 * 2
def baseEnd_7624823 : Nat := 435022122717436286516287

theorem tailTrace_7624823 : CollatzResearch.WordTrace tailWord_7624823 prefixEnd_7624823 435022122717436286516287 := by
  unfold tailWord_7624823
  simp only [CollatzResearch.WordTrace]
  refine ⟨278100141655575961938791123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185400094437050641292527415 278100141655575961938791123)
  ·
    refine ⟨417150212483363942908186685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 278100141655575961938791123 417150212483363942908186685)
    ·
      refine ⟨156431329681261478590570007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 417150212483363942908186685 156431329681261478590570007)
      ·
        refine ⟨234646994521892217885855011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 156431329681261478590570007 234646994521892217885855011)
        ·
          refine ⟨351970491782838326828782517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 234646994521892217885855011 351970491782838326828782517)
          ·
            refine ⟨32997233604641093140198361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 351970491782838326828782517 32997233604641093140198361)
            ·
              refine ⟨24747925203480819855148771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32997233604641093140198361 24747925203480819855148771)
              ·
                refine ⟨37121887805221229782723157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24747925203480819855148771 37121887805221229782723157)
                ·
                  refine ⟨435022122717436286516287, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 37121887805221229782723157 435022122717436286516287)
                  ·
                    rfl

theorem cell23_7624823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 5, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 5, 2, 1, 8].length) (baseStart_7624823 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7624823 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7624823 prefixEnd_7624823 := by exact prefixLift 7624823
  have htrace : WordTrace (prefixWord ++ tailWord_7624823) baseStart_7624823 baseEnd_7624823 := by
    simpa [prefixWord, tailWord_7624823, baseEnd_7624823] using wordTrace_append hprefix tailTrace_7624823
  have hstable : (prefixWord ++ tailWord_7624823).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7624823).length < 2 ^ (prefixWord ++ tailWord_7624823).sum := by decide
  have hdescent : baseEnd_7624823 < baseStart_7624823 := by decide
  rcases family_descends (prefixWord ++ tailWord_7624823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7624874 : List Nat := [3, 1, 5, 1, 2, 1, 2, 2, 6]
def baseStart_7624874 : Nat := 118140960795 + 7624874 * 2 ^ 59
def prefixEnd_7624874 : Nat := 4983230072969 + 3 ^ 40 * 7624874 * 2
def baseEnd_7624874 : Nat := 435025032441145097678761

theorem tailTrace_7624874 : CollatzResearch.WordTrace tailWord_7624874 prefixEnd_7624874 435025032441145097678761 := by
  unfold tailWord_7624874
  simp only [CollatzResearch.WordTrace]
  refine ⟨69525500444597799412224419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 185401334518927465099265117 69525500444597799412224419)
  ·
    refine ⟨104288250666896699118336629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69525500444597799412224419 104288250666896699118336629)
    ·
      refine ⟨9777023500021565542344059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 104288250666896699118336629 9777023500021565542344059)
      ·
        refine ⟨14665535250032348313516089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9777023500021565542344059 14665535250032348313516089)
        ·
          refine ⟨10999151437524261235137067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14665535250032348313516089 10999151437524261235137067)
          ·
            refine ⟨16498727156286391852705601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10999151437524261235137067 16498727156286391852705601)
            ·
              refine ⟨12374045367214793889529201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16498727156286391852705601 12374045367214793889529201)
              ·
                refine ⟨9280534025411095417146901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12374045367214793889529201 9280534025411095417146901)
                ·
                  refine ⟨435025032441145097678761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9280534025411095417146901 435025032441145097678761)
                  ·
                    rfl

theorem cell23_7624874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 2, 1, 2, 2, 6].length) (baseStart_7624874 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7624874 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7624874 prefixEnd_7624874 := by exact prefixLift 7624874
  have htrace : WordTrace (prefixWord ++ tailWord_7624874) baseStart_7624874 baseEnd_7624874 := by
    simpa [prefixWord, tailWord_7624874, baseEnd_7624874] using wordTrace_append hprefix tailTrace_7624874
  have hstable : (prefixWord ++ tailWord_7624874).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7624874).length < 2 ^ (prefixWord ++ tailWord_7624874).sum := by decide
  have hdescent : baseEnd_7624874 < baseStart_7624874 := by decide
  rcases family_descends (prefixWord ++ tailWord_7624874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7624878 : List Nat := [4, 1, 4, 2, 1, 1, 1, 4, 1, 4]
def baseStart_7624878 : Nat := 118140960795 + 7624878 * 2 ^ 59
def prefixEnd_7624878 : Nat := 4983230072969 + 3 ^ 40 * 7624878 * 2
def baseEnd_7624878 : Nat := 1305075781964307954486277

theorem tailTrace_7624878 : CollatzResearch.WordTrace tailWord_7624878 prefixEnd_7624878 1305075781964307954486277 := by
  unfold tailWord_7624878
  simp only [CollatzResearch.WordTrace]
  refine ⟨34762768458797088291505411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 185401431780251137554695525 34762768458797088291505411)
  ·
    refine ⟨52144152688195632437258117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34762768458797088291505411 52144152688195632437258117)
    ·
      refine ⟨9777028629036681081985897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 52144152688195632437258117 9777028629036681081985897)
      ·
        refine ⟨7332771471777510811489423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9777028629036681081985897 7332771471777510811489423)
        ·
          refine ⟨10999157207666266217234135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7332771471777510811489423 10999157207666266217234135)
          ·
            refine ⟨16498735811499399325851203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10999157207666266217234135 16498735811499399325851203)
            ·
              refine ⟨24748103717249098988776805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16498735811499399325851203 24748103717249098988776805)
              ·
                refine ⟨4640269446984206060395651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24748103717249098988776805 4640269446984206060395651)
                ·
                  refine ⟨6960404170476309090593477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4640269446984206060395651 6960404170476309090593477)
                  ·
                    refine ⟨1305075781964307954486277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6960404170476309090593477 1305075781964307954486277)
                    ·
                      rfl

theorem cell23_7624878_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 1, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 1, 1, 1, 4, 1, 4].length) (baseStart_7624878 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7624878 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7624878 prefixEnd_7624878 := by exact prefixLift 7624878
  have htrace : WordTrace (prefixWord ++ tailWord_7624878) baseStart_7624878 baseEnd_7624878 := by
    simpa [prefixWord, tailWord_7624878, baseEnd_7624878] using wordTrace_append hprefix tailTrace_7624878
  have hstable : (prefixWord ++ tailWord_7624878).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7624878).length < 2 ^ (prefixWord ++ tailWord_7624878).sum := by decide
  have hdescent : baseEnd_7624878 < baseStart_7624878 := by decide
  rcases family_descends (prefixWord ++ tailWord_7624878) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7624883 : List Nat := [1, 1, 1, 2, 3, 2, 1, 1, 5, 6]
def baseStart_7624883 : Nat := 118140960795 + 7624883 * 2 ^ 59
def prefixEnd_7624883 : Nat := 4983230072969 + 3 ^ 40 * 7624883 * 2
def baseEnd_7624883 : Nat := 1305076637765398781298769

theorem tailTrace_7624883 : CollatzResearch.WordTrace tailWord_7624883 prefixEnd_7624883 1305076637765398781298769 := by
  unfold tailWord_7624883
  simp only [CollatzResearch.WordTrace]
  refine ⟨278102330035358592185975303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185401553356905728123983535 278102330035358592185975303)
  ·
    refine ⟨417153495053037888278962955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 278102330035358592185975303 417153495053037888278962955)
    ·
      refine ⟨625730242579556832418444433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 417153495053037888278962955 625730242579556832418444433)
      ·
        refine ⟨469297681934667624313833325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 625730242579556832418444433 469297681934667624313833325)
        ·
          refine ⟨175986630725500359117687497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 469297681934667624313833325 175986630725500359117687497)
          ·
            refine ⟨131989973044125269338265623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 175986630725500359117687497 131989973044125269338265623)
            ·
              refine ⟨197984959566187904007398435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 131989973044125269338265623 197984959566187904007398435)
              ·
                refine ⟨296977439349281856011097653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 197984959566187904007398435 296977439349281856011097653)
                ·
                  refine ⟨27841634938995174001040405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 296977439349281856011097653 27841634938995174001040405)
                  ·
                    refine ⟨1305076637765398781298769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27841634938995174001040405 1305076637765398781298769)
                    ·
                      rfl

theorem cell23_7624883_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 1, 1, 5, 6].length) (baseStart_7624883 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7624883 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7624883 prefixEnd_7624883 := by exact prefixLift 7624883
  have htrace : WordTrace (prefixWord ++ tailWord_7624883) baseStart_7624883 baseEnd_7624883 := by
    simpa [prefixWord, tailWord_7624883, baseEnd_7624883] using wordTrace_append hprefix tailTrace_7624883
  have hstable : (prefixWord ++ tailWord_7624883).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7624883).length < 2 ^ (prefixWord ++ tailWord_7624883).sum := by decide
  have hdescent : baseEnd_7624883 < baseStart_7624883 := by decide
  rcases family_descends (prefixWord ++ tailWord_7624883) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7624890 : List Nat := [3, 1, 1, 1, 2, 2, 3, 2, 3, 1, 4]
def baseStart_7624890 : Nat := 118140960795 + 7624890 * 2 ^ 59
def prefixEnd_7624890 : Nat := 4983230072969 + 3 ^ 40 * 7624890 * 2
def baseEnd_7624890 : Nat := 3915233507660777816508775

theorem tailTrace_7624890 : CollatzResearch.WordTrace tailWord_7624890 prefixEnd_7624890 3915233507660777816508775 := by
  unfold tailWord_7624890
  simp only [CollatzResearch.WordTrace]
  refine ⟨69525646336583308095370031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 185401723564222154920986749 69525646336583308095370031)
  ·
    refine ⟨104288469504874962143055047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69525646336583308095370031 104288469504874962143055047)
    ·
      refine ⟨156432704257312443214582571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104288469504874962143055047 156432704257312443214582571)
      ·
        refine ⟨234649056385968664821873857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 156432704257312443214582571 234649056385968664821873857)
        ·
          refine ⟨175986792289476498616405393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 234649056385968664821873857 175986792289476498616405393)
          ·
            refine ⟨131990094217107373962304045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 175986792289476498616405393 131990094217107373962304045)
            ·
              refine ⟨49496285331415265235864017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 131990094217107373962304045 49496285331415265235864017)
              ·
                refine ⟨37122213998561448926898013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49496285331415265235864017 37122213998561448926898013)
                ·
                  refine ⟨13920830249460543347586755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 37122213998561448926898013 13920830249460543347586755)
                  ·
                    refine ⟨20881245374190815021380133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13920830249460543347586755 20881245374190815021380133)
                    ·
                      refine ⟨3915233507660777816508775, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20881245374190815021380133 3915233507660777816508775)
                      ·
                        rfl

theorem cell23_7624890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 3, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 3, 2, 3, 1, 4].length) (baseStart_7624890 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7624890 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7624890 prefixEnd_7624890 := by exact prefixLift 7624890
  have htrace : WordTrace (prefixWord ++ tailWord_7624890) baseStart_7624890 baseEnd_7624890 := by
    simpa [prefixWord, tailWord_7624890, baseEnd_7624890] using wordTrace_append hprefix tailTrace_7624890
  have hstable : (prefixWord ++ tailWord_7624890).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7624890).length < 2 ^ (prefixWord ++ tailWord_7624890).sum := by decide
  have hdescent : baseEnd_7624890 < baseStart_7624890 := by decide
  rcases family_descends (prefixWord ++ tailWord_7624890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7624913 : List Nat := [1, 2, 2, 1, 2, 2, 2, 11]
def baseStart_7624913 : Nat := 118140960795 + 7624913 * 2 ^ 59
def prefixEnd_7624913 : Nat := 4983230072969 + 3 ^ 40 * 7624913 * 2
def baseEnd_7624913 : Nat := 145009085841327082463747

theorem tailTrace_7624913 : CollatzResearch.WordTrace tailWord_7624913 prefixEnd_7624913 145009085841327082463747 := by
  unfold tailWord_7624913
  simp only [CollatzResearch.WordTrace]
  refine ⟨278103424225249907309567393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185402282816833271539711595 278103424225249907309567393)
  ·
    refine ⟨208577568168937430482175545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 278103424225249907309567393 208577568168937430482175545)
    ·
      refine ⟨156433176126703072861631659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 208577568168937430482175545 156433176126703072861631659)
      ·
        refine ⟨234649764190054609292447489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 156433176126703072861631659 234649764190054609292447489)
        ·
          refine ⟨175987323142540956969335617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 234649764190054609292447489 175987323142540956969335617)
          ·
            refine ⟨131990492356905717727001713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 175987323142540956969335617 131990492356905717727001713)
            ·
              refine ⟨98992869267679288295251285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 131990492356905717727001713 98992869267679288295251285)
              ·
                refine ⟨145009085841327082463747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 98992869267679288295251285 145009085841327082463747)
                ·
                  rfl

theorem cell23_7624913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 2, 11].length) (baseStart_7624913 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7624913 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7624913 prefixEnd_7624913 := by exact prefixLift 7624913
  have htrace : WordTrace (prefixWord ++ tailWord_7624913) baseStart_7624913 baseEnd_7624913 := by
    simpa [prefixWord, tailWord_7624913, baseEnd_7624913] using wordTrace_append hprefix tailTrace_7624913
  have hstable : (prefixWord ++ tailWord_7624913).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7624913).length < 2 ^ (prefixWord ++ tailWord_7624913).sum := by decide
  have hdescent : baseEnd_7624913 < baseStart_7624913 := by decide
  rcases family_descends (prefixWord ++ tailWord_7624913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7624918 : List Nat := [5, 2, 1, 2, 1, 1, 1, 5, 1, 1, 3]
def baseStart_7624918 : Nat := 118140960795 + 7624918 * 2 ^ 59
def prefixEnd_7624918 : Nat := 4983230072969 + 3 ^ 40 * 7624918 * 2
def baseEnd_7624918 : Nat := 3915247885119103706958647

theorem tailTrace_7624918 : CollatzResearch.WordTrace tailWord_7624918 prefixEnd_7624918 3915247885119103706958647 := by
  unfold tailWord_7624918
  simp only [CollatzResearch.WordTrace]
  refine ⟨17381475411889487072718713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 185402404393487862108999605 17381475411889487072718713)
  ·
    refine ⟨13036106558917115304539035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17381475411889487072718713 13036106558917115304539035)
    ·
      refine ⟨19554159838375672956808553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13036106558917115304539035 19554159838375672956808553)
      ·
        refine ⟨14665619878781754717606415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19554159838375672956808553 14665619878781754717606415)
        ·
          refine ⟨21998429818172632076409623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14665619878781754717606415 21998429818172632076409623)
          ·
            refine ⟨32997644727258948114614435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21998429818172632076409623 32997644727258948114614435)
            ·
              refine ⟨49496467090888422171921653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32997644727258948114614435 49496467090888422171921653)
              ·
                refine ⟨4640293789770789578617655, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 49496467090888422171921653 4640293789770789578617655)
                ·
                  refine ⟨6960440684656184367926483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4640293789770789578617655 6960440684656184367926483)
                  ·
                    refine ⟨10440661026984276551889725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6960440684656184367926483 10440661026984276551889725)
                    ·
                      refine ⟨3915247885119103706958647, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10440661026984276551889725 3915247885119103706958647)
                      ·
                        rfl

theorem cell23_7624918_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 1, 1, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 1, 1, 5, 1, 1, 3].length) (baseStart_7624918 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7624918 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7624918 prefixEnd_7624918 := by exact prefixLift 7624918
  have htrace : WordTrace (prefixWord ++ tailWord_7624918) baseStart_7624918 baseEnd_7624918 := by
    simpa [prefixWord, tailWord_7624918, baseEnd_7624918] using wordTrace_append hprefix tailTrace_7624918
  have hstable : (prefixWord ++ tailWord_7624918).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7624918).length < 2 ^ (prefixWord ++ tailWord_7624918).sum := by decide
  have hdescent : baseEnd_7624918 < baseStart_7624918 := by decide
  rcases family_descends (prefixWord ++ tailWord_7624918) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7624964 : List Nat := [2, 3, 2, 2, 3, 2, 2, 7]
def baseStart_7624964 : Nat := 118140960795 + 7624964 * 2 ^ 59
def prefixEnd_7624964 : Nat := 4983230072969 + 3 ^ 40 * 7624964 * 2
def baseEnd_7624964 : Nat := 145010055749230019517905

theorem tailTrace_7624964 : CollatzResearch.WordTrace tailWord_7624964 prefixEnd_7624964 145010055749230019517905 := by
  unfold tailWord_7624964
  simp only [CollatzResearch.WordTrace]
  refine ⟨139052642174032571509836973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 185403522898710095346449297 139052642174032571509836973)
  ·
    refine ⟨52144740815262214316188865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 139052642174032571509836973 52144740815262214316188865)
    ·
      refine ⟨39108555611446660737141649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52144740815262214316188865 39108555611446660737141649)
      ·
        refine ⟨29331416708584995552856237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39108555611446660737141649 29331416708584995552856237)
        ·
          refine ⟨10999281265719373332321089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29331416708584995552856237 10999281265719373332321089)
          ·
            refine ⟨8249460949289529999240817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10999281265719373332321089 8249460949289529999240817)
            ·
              refine ⟨6187095711967147499430613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8249460949289529999240817 6187095711967147499430613)
              ·
                refine ⟨145010055749230019517905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6187095711967147499430613 145010055749230019517905)
                ·
                  rfl

theorem cell23_7624964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 3, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 3, 2, 2, 7].length) (baseStart_7624964 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7624964 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7624964 prefixEnd_7624964 := by exact prefixLift 7624964
  have htrace : WordTrace (prefixWord ++ tailWord_7624964) baseStart_7624964 baseEnd_7624964 := by
    simpa [prefixWord, tailWord_7624964, baseEnd_7624964] using wordTrace_append hprefix tailTrace_7624964
  have hstable : (prefixWord ++ tailWord_7624964).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7624964).length < 2 ^ (prefixWord ++ tailWord_7624964).sum := by decide
  have hdescent : baseEnd_7624964 < baseStart_7624964 := by decide
  rcases family_descends (prefixWord ++ tailWord_7624964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7624970 : List Nat := [3, 1, 2, 2, 1, 1, 3, 1, 2, 2, 5]
def baseStart_7624970 : Nat := 118140960795 + 7624970 * 2 ^ 59
def prefixEnd_7624970 : Nat := 4983230072969 + 3 ^ 40 * 7624970 * 2
def baseEnd_7624970 : Nat := 3915274586113137503508407

theorem tailTrace_7624970 : CollatzResearch.WordTrace tailWord_7624970 prefixEnd_7624970 3915274586113137503508407 := by
  unfold tailWord_7624970
  simp only [CollatzResearch.WordTrace]
  refine ⟨69526375796510851511098091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 185403668790695604029594909 69526375796510851511098091)
  ·
    refine ⟨104289563694766277266647137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69526375796510851511098091 104289563694766277266647137)
    ·
      refine ⟨78217172771074707949985353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 104289563694766277266647137 78217172771074707949985353)
      ·
        refine ⟨58662879578306030962489015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78217172771074707949985353 58662879578306030962489015)
        ·
          refine ⟨87994319367459046443733523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58662879578306030962489015 87994319367459046443733523)
          ·
            refine ⟨131991479051188569665600285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87994319367459046443733523 131991479051188569665600285)
            ·
              refine ⟨49496804644195713624600107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 131991479051188569665600285 49496804644195713624600107)
              ·
                refine ⟨74245206966293570436900161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49496804644195713624600107 74245206966293570436900161)
                ·
                  refine ⟨55683905224720177827675121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 74245206966293570436900161 55683905224720177827675121)
                  ·
                    refine ⟨41762928918540133370756341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 55683905224720177827675121 41762928918540133370756341)
                    ·
                      refine ⟨3915274586113137503508407, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41762928918540133370756341 3915274586113137503508407)
                      ·
                        rfl

theorem cell23_7624970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 3, 1, 2, 2, 5].length) (baseStart_7624970 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7624970 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7624970 prefixEnd_7624970 := by exact prefixLift 7624970
  have htrace : WordTrace (prefixWord ++ tailWord_7624970) baseStart_7624970 baseEnd_7624970 := by
    simpa [prefixWord, tailWord_7624970, baseEnd_7624970] using wordTrace_append hprefix tailTrace_7624970
  have hstable : (prefixWord ++ tailWord_7624970).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7624970).length < 2 ^ (prefixWord ++ tailWord_7624970).sum := by decide
  have hdescent : baseEnd_7624970 < baseStart_7624970 := by decide
  rcases family_descends (prefixWord ++ tailWord_7624970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7624984 : List Nat := [2, 1, 2, 3, 1, 2, 1, 5, 1, 3, 2]
def baseStart_7624984 : Nat := 118140960795 + 7624984 * 2 ^ 59
def prefixEnd_7624984 : Nat := 4983230072969 + 3 ^ 40 * 7624984 * 2
def baseEnd_7624984 : Nat := 3915281774842300448733343

theorem tailTrace_7624984 : CollatzResearch.WordTrace tailWord_7624984 prefixEnd_7624984 3915281774842300448733343 := by
  unfold tailWord_7624984
  simp only [CollatzResearch.WordTrace]
  refine ⟨139053006903996343217701003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 185404009205328457623601337 139053006903996343217701003)
  ·
    refine ⟨208579510355994514826551505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139053006903996343217701003 208579510355994514826551505)
    ·
      refine ⟨156434632766995886119913629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 208579510355994514826551505 156434632766995886119913629)
      ·
        refine ⟨58662987287623457294967611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 156434632766995886119913629 58662987287623457294967611)
        ·
          refine ⟨87994480931435185942451417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58662987287623457294967611 87994480931435185942451417)
          ·
            refine ⟨65995860698576389456838563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 87994480931435185942451417 65995860698576389456838563)
            ·
              refine ⟨98993791047864584185257845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65995860698576389456838563 98993791047864584185257845)
              ·
                refine ⟨9280667910737304767367923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 98993791047864584185257845 9280667910737304767367923)
                ·
                  refine ⟨13921001866105957151051885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9280667910737304767367923 13921001866105957151051885)
                  ·
                    refine ⟨5220375699789733931644457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13921001866105957151051885 5220375699789733931644457)
                    ·
                      refine ⟨3915281774842300448733343, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5220375699789733931644457 3915281774842300448733343)
                      ·
                        rfl

theorem cell23_7624984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 1, 5, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 1, 5, 1, 3, 2].length) (baseStart_7624984 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7624984 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7624984 prefixEnd_7624984 := by exact prefixLift 7624984
  have htrace : WordTrace (prefixWord ++ tailWord_7624984) baseStart_7624984 baseEnd_7624984 := by
    simpa [prefixWord, tailWord_7624984, baseEnd_7624984] using wordTrace_append hprefix tailTrace_7624984
  have hstable : (prefixWord ++ tailWord_7624984).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7624984).length < 2 ^ (prefixWord ++ tailWord_7624984).sum := by decide
  have hdescent : baseEnd_7624984 < baseStart_7624984 := by decide
  rcases family_descends (prefixWord ++ tailWord_7624984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7625017 : List Nat := [1, 2, 1, 6, 1, 1, 1, 2, 2, 1, 5]
def baseStart_7625017 : Nat := 118140960795 + 7625017 * 2 ^ 59
def prefixEnd_7625017 : Nat := 4983230072969 + 3 ^ 40 * 7625017 * 2
def baseEnd_7625017 : Nat := 3915298719703898819620691

theorem tailTrace_7625017 : CollatzResearch.WordTrace tailWord_7625017 prefixEnd_7625017 3915298719703898819620691 := by
  unfold tailWord_7625017
  simp only [CollatzResearch.WordTrace]
  refine ⟨278107217416873133071353305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185404811611248755380902203 278107217416873133071353305)
  ·
    refine ⟨208580413062654849803514979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 278107217416873133071353305 208580413062654849803514979)
    ·
      refine ⟨312870619593982274705272469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 208580413062654849803514979 312870619593982274705272469)
      ·
        refine ⟨14665810293467919126809647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 312870619593982274705272469 14665810293467919126809647)
        ·
          refine ⟨21998715440201878690214471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14665810293467919126809647 21998715440201878690214471)
          ·
            refine ⟨32998073160302818035321707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21998715440201878690214471 32998073160302818035321707)
            ·
              refine ⟨49497109740454227052982561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32998073160302818035321707 49497109740454227052982561)
              ·
                refine ⟨37122832305340670289736921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49497109740454227052982561 37122832305340670289736921)
                ·
                  refine ⟨27842124229005502717302691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37122832305340670289736921 27842124229005502717302691)
                  ·
                    refine ⟨41763186343508254075954037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27842124229005502717302691 41763186343508254075954037)
                    ·
                      refine ⟨3915298719703898819620691, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41763186343508254075954037 3915298719703898819620691)
                      ·
                        rfl

theorem cell23_7625017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 1, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 1, 1, 2, 2, 1, 5].length) (baseStart_7625017 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7625017 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7625017 prefixEnd_7625017 := by exact prefixLift 7625017
  have htrace : WordTrace (prefixWord ++ tailWord_7625017) baseStart_7625017 baseEnd_7625017 := by
    simpa [prefixWord, tailWord_7625017, baseEnd_7625017] using wordTrace_append hprefix tailTrace_7625017
  have hstable : (prefixWord ++ tailWord_7625017).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7625017).length < 2 ^ (prefixWord ++ tailWord_7625017).sum := by decide
  have hdescent : baseEnd_7625017 < baseStart_7625017 := by decide
  rcases family_descends (prefixWord ++ tailWord_7625017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7625020 : List Nat := [2, 2, 2, 2, 1, 2, 2, 1, 9]
def baseStart_7625020 : Nat := 118140960795 + 7625020 * 2 ^ 59
def prefixEnd_7625020 : Nat := 4983230072969 + 3 ^ 40 * 7625020 * 2
def baseEnd_7625020 : Nat := 435033362238429145320353

theorem tailTrace_7625020 : CollatzResearch.WordTrace tailWord_7625020 prefixEnd_7625020 435033362238429145320353 := by
  unfold tailWord_7625020
  simp only [CollatzResearch.WordTrace]
  refine ⟨139053663417931132291856257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 185404884557241509722475009 139053663417931132291856257)
  ·
    refine ⟨104290247563448349218892193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 139053663417931132291856257 104290247563448349218892193)
    ·
      refine ⟨78217685672586261914169145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 104290247563448349218892193 78217685672586261914169145)
      ·
        refine ⟨58663264254439696435626859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78217685672586261914169145 58663264254439696435626859)
        ·
          refine ⟨87994896381659544653440289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58663264254439696435626859 87994896381659544653440289)
          ·
            refine ⟨65996172286244658490080217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 87994896381659544653440289 65996172286244658490080217)
            ·
              refine ⟨49497129214683493867560163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 65996172286244658490080217 49497129214683493867560163)
              ·
                refine ⟨74245693822025240801340245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49497129214683493867560163 74245693822025240801340245)
                ·
                  refine ⟨435033362238429145320353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 74245693822025240801340245 435033362238429145320353)
                  ·
                    rfl

theorem cell23_7625020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 2, 1, 9].length) (baseStart_7625020 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7625020 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7625020 prefixEnd_7625020 := by exact prefixLift 7625020
  have htrace : WordTrace (prefixWord ++ tailWord_7625020) baseStart_7625020 baseEnd_7625020 := by
    simpa [prefixWord, tailWord_7625020, baseEnd_7625020] using wordTrace_append hprefix tailTrace_7625020
  have hstable : (prefixWord ++ tailWord_7625020).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7625020).length < 2 ^ (prefixWord ++ tailWord_7625020).sum := by decide
  have hdescent : baseEnd_7625020 < baseStart_7625020 := by decide
  rcases family_descends (prefixWord ++ tailWord_7625020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7625047 : List Nat := [1, 1, 3, 2, 3, 1, 2, 2, 2, 3, 3]
def baseStart_7625047 : Nat := 118140960795 + 7625047 * 2 ^ 59
def prefixEnd_7625047 : Nat := 4983230072969 + 3 ^ 40 * 7625047 * 2
def baseEnd_7625047 : Nat := 3915314124123533702245553

theorem tailTrace_7625047 : CollatzResearch.WordTrace tailWord_7625047 prefixEnd_7625047 3915314124123533702245553 := by
  unfold tailWord_7625047
  simp only [CollatzResearch.WordTrace]
  refine ⟨278108311606764448194945395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185405541071176298796630263 278108311606764448194945395)
  ·
    refine ⟨417162467410146672292418093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 278108311606764448194945395 417162467410146672292418093)
    ·
      refine ⟨156435925278805002109656785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 417162467410146672292418093 156435925278805002109656785)
      ·
        refine ⟨117326943959103751582242589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 156435925278805002109656785 117326943959103751582242589)
        ·
          refine ⟨43997603984663906843340971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 117326943959103751582242589 43997603984663906843340971)
          ·
            refine ⟨65996405976995860265011457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43997603984663906843340971 65996405976995860265011457)
            ·
              refine ⟨49497304482746895198758593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 65996405976995860265011457 49497304482746895198758593)
              ·
                refine ⟨37122978362060171399068945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49497304482746895198758593 37122978362060171399068945)
                ·
                  refine ⟨27842233771545128549301709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37122978362060171399068945 27842233771545128549301709)
                  ·
                    refine ⟨10440837664329423205988141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27842233771545128549301709 10440837664329423205988141)
                    ·
                      refine ⟨3915314124123533702245553, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10440837664329423205988141 3915314124123533702245553)
                      ·
                        rfl

theorem cell23_7625047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 2, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 2, 2, 2, 3, 3].length) (baseStart_7625047 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7625047 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7625047 prefixEnd_7625047 := by exact prefixLift 7625047
  have htrace : WordTrace (prefixWord ++ tailWord_7625047) baseStart_7625047 baseEnd_7625047 := by
    simpa [prefixWord, tailWord_7625047, baseEnd_7625047] using wordTrace_append hprefix tailTrace_7625047
  have hstable : (prefixWord ++ tailWord_7625047).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7625047).length < 2 ^ (prefixWord ++ tailWord_7625047).sum := by decide
  have hdescent : baseEnd_7625047 < baseStart_7625047 := by decide
  rcases family_descends (prefixWord ++ tailWord_7625047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7625050 : List Nat := [3, 1, 1, 2, 1, 2, 1, 2, 3, 7]
def baseStart_7625050 : Nat := 118140960795 + 7625050 * 2 ^ 59
def prefixEnd_7625050 : Nat := 4983230072969 + 3 ^ 40 * 7625050 * 2
def baseEnd_7625050 : Nat := 1305105221521832396836013

theorem tailTrace_7625050 : CollatzResearch.WordTrace tailWord_7625050 prefixEnd_7625050 1305105221521832396836013 := by
  unfold tailWord_7625050
  simp only [CollatzResearch.WordTrace]
  refine ⟨69527105256438394926826151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 185405614017169053138203069 69527105256438394926826151)
  ·
    refine ⟨104290657884657592390239227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69527105256438394926826151 104290657884657592390239227)
    ·
      refine ⟨156435986826986388585358841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104290657884657592390239227 156435986826986388585358841)
      ·
        refine ⟨117326990120239791439019131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 156435986826986388585358841 117326990120239791439019131)
        ·
          refine ⟨175990485180359687158528697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 117326990120239791439019131 175990485180359687158528697)
          ·
            refine ⟨131992863885269765368896523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 175990485180359687158528697 131992863885269765368896523)
            ·
              refine ⟨197989295827904648053344785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 131992863885269765368896523 197989295827904648053344785)
              ·
                refine ⟨148491971870928486040008589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 197989295827904648053344785 148491971870928486040008589)
                ·
                  refine ⟨55684489451598182265003221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 148491971870928486040008589 55684489451598182265003221)
                  ·
                    refine ⟨1305105221521832396836013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 55684489451598182265003221 1305105221521832396836013)
                    ·
                      rfl

theorem cell23_7625050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 1, 2, 3, 7].length) (baseStart_7625050 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7625050 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7625050 prefixEnd_7625050 := by exact prefixLift 7625050
  have htrace : WordTrace (prefixWord ++ tailWord_7625050) baseStart_7625050 baseEnd_7625050 := by
    simpa [prefixWord, tailWord_7625050, baseEnd_7625050] using wordTrace_append hprefix tailTrace_7625050
  have hstable : (prefixWord ++ tailWord_7625050).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7625050).length < 2 ^ (prefixWord ++ tailWord_7625050).sum := by decide
  have hdescent : baseEnd_7625050 < baseStart_7625050 := by decide
  rcases family_descends (prefixWord ++ tailWord_7625050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7625064 : List Nat := [2, 1, 4, 2, 2, 2, 1, 1, 2, 3, 3]
def baseStart_7625064 : Nat := 118140960795 + 7625064 * 2 ^ 59
def prefixEnd_7625064 : Nat := 4983230072969 + 3 ^ 40 * 7625064 * 2
def baseEnd_7625064 : Nat := 3915322853294660135732975

theorem tailTrace_7625064 : CollatzResearch.WordTrace tailWord_7625064 prefixEnd_7625064 3915322853294660135732975 := by
  unfold tailWord_7625064
  simp only [CollatzResearch.WordTrace]
  refine ⟨139054465823851430049157123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 185405954431801906732209497 139054465823851430049157123)
  ·
    refine ⟨208581698735777145073735685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139054465823851430049157123 208581698735777145073735685)
    ·
      refine ⟨39109068512958214701325441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 208581698735777145073735685 39109068512958214701325441)
      ·
        refine ⟨29331801384718661025994081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39109068512958214701325441 29331801384718661025994081)
        ·
          refine ⟨21998851038538995769495561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29331801384718661025994081 21998851038538995769495561)
          ·
            refine ⟨16499138278904246827121671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21998851038538995769495561 16499138278904246827121671)
            ·
              refine ⟨24748707418356370240682507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16499138278904246827121671 24748707418356370240682507)
              ·
                refine ⟨37123061127534555361023761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24748707418356370240682507 37123061127534555361023761)
                ·
                  refine ⟨27842295845650916520767821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37123061127534555361023761 27842295845650916520767821)
                  ·
                    refine ⟨10440860942119093695287933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27842295845650916520767821 10440860942119093695287933)
                    ·
                      refine ⟨3915322853294660135732975, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10440860942119093695287933 3915322853294660135732975)
                      ·
                        rfl

theorem cell23_7625064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 2, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 2, 1, 1, 2, 3, 3].length) (baseStart_7625064 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7625064 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7625064 prefixEnd_7625064 := by exact prefixLift 7625064
  have htrace : WordTrace (prefixWord ++ tailWord_7625064) baseStart_7625064 baseEnd_7625064 := by
    simpa [prefixWord, tailWord_7625064, baseEnd_7625064] using wordTrace_append hprefix tailTrace_7625064
  have hstable : (prefixWord ++ tailWord_7625064).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7625064).length < 2 ^ (prefixWord ++ tailWord_7625064).sum := by decide
  have hdescent : baseEnd_7625064 < baseStart_7625064 := by decide
  rcases family_descends (prefixWord ++ tailWord_7625064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7625114 : List Nat := [3, 1, 1, 4, 1, 2, 1, 3, 3, 4]
def baseStart_7625114 : Nat := 118140960795 + 7625114 * 2 ^ 59
def prefixEnd_7625114 : Nat := 4983230072969 + 3 ^ 40 * 7625114 * 2
def baseEnd_7625114 : Nat := 1305116175775794980035915

theorem tailTrace_7625114 : CollatzResearch.WordTrace tailWord_7625114 prefixEnd_7625114 1305116175775794980035915 := by
  unfold tailWord_7625114
  simp only [CollatzResearch.WordTrace]
  refine ⟨69527688824380429659408599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 185407170198347812425089597 69527688824380429659408599)
  ·
    refine ⟨104291533236570644489112899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69527688824380429659408599 104291533236570644489112899)
    ·
      refine ⟨156437299854855966733669349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104291533236570644489112899 156437299854855966733669349)
      ·
        refine ⟨29331993722785493762563003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 156437299854855966733669349 29331993722785493762563003)
        ·
          refine ⟨43997990584178240643844505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29331993722785493762563003 43997990584178240643844505)
          ·
            refine ⟨32998492938133680482883379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43997990584178240643844505 32998492938133680482883379)
            ·
              refine ⟨49497739407200520724325069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32998492938133680482883379 49497739407200520724325069)
              ·
                refine ⟨18561652277700195271621901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 49497739407200520724325069 18561652277700195271621901)
                ·
                  refine ⟨6960619604137573226858213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18561652277700195271621901 6960619604137573226858213)
                  ·
                    refine ⟨1305116175775794980035915, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6960619604137573226858213 1305116175775794980035915)
                    ·
                      rfl

theorem cell23_7625114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 2, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 2, 1, 3, 3, 4].length) (baseStart_7625114 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7625114 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7625114 prefixEnd_7625114 := by exact prefixLift 7625114
  have htrace : WordTrace (prefixWord ++ tailWord_7625114) baseStart_7625114 baseEnd_7625114 := by
    simpa [prefixWord, tailWord_7625114, baseEnd_7625114] using wordTrace_append hprefix tailTrace_7625114
  have hstable : (prefixWord ++ tailWord_7625114).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7625114).length < 2 ^ (prefixWord ++ tailWord_7625114).sum := by decide
  have hdescent : baseEnd_7625114 < baseStart_7625114 := by decide
  rcases family_descends (prefixWord ++ tailWord_7625114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7625148 : List Nat := [2, 2, 2, 4, 1, 1, 3, 3, 1, 4]
def baseStart_7625148 : Nat := 118140960795 + 7625148 * 2 ^ 59
def prefixEnd_7625148 : Nat := 4983230072969 + 3 ^ 40 * 7625148 * 2
def baseEnd_7625148 : Nat := 1305121995223212602360863

theorem tailTrace_7625148 : CollatzResearch.WordTrace tailWord_7625148 prefixEnd_7625148 1305121995223212602360863 := by
  unfold tailWord_7625148
  simp only [CollatzResearch.WordTrace]
  refine ⟨139055997689699271222186049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 185407996919599028296248065 139055997689699271222186049)
  ·
    refine ⟨104291998267274453416639537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 139055997689699271222186049 104291998267274453416639537)
    ·
      refine ⟨78218998700455840062479653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 104291998267274453416639537 78218998700455840062479653)
      ·
        refine ⟨14666062256335470011714935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 78218998700455840062479653 14666062256335470011714935)
        ·
          refine ⟨21999093384503205017572403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14666062256335470011714935 21999093384503205017572403)
          ·
            refine ⟨32998640076754807526358605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21999093384503205017572403 32998640076754807526358605)
            ·
              refine ⟨12374490028783052822384477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32998640076754807526358605 12374490028783052822384477)
              ·
                refine ⟨4640433760793644808394179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12374490028783052822384477 4640433760793644808394179)
                ·
                  refine ⟨6960650641190467212591269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4640433760793644808394179 6960650641190467212591269)
                  ·
                    refine ⟨1305121995223212602360863, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6960650641190467212591269 1305121995223212602360863)
                    ·
                      rfl

theorem cell23_7625148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 1, 3, 3, 1, 4].length) (baseStart_7625148 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7625148 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7625148 prefixEnd_7625148 := by exact prefixLift 7625148
  have htrace : WordTrace (prefixWord ++ tailWord_7625148) baseStart_7625148 baseEnd_7625148 := by
    simpa [prefixWord, tailWord_7625148, baseEnd_7625148] using wordTrace_append hprefix tailTrace_7625148
  have hstable : (prefixWord ++ tailWord_7625148).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7625148).length < 2 ^ (prefixWord ++ tailWord_7625148).sum := by decide
  have hdescent : baseEnd_7625148 < baseStart_7625148 := by decide
  rcases family_descends (prefixWord ++ tailWord_7625148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7625181 : List Nat := [1, 4, 3, 1, 1, 1, 1, 2, 4, 3, 2]
def baseStart_7625181 : Nat := 118140960795 + 7625181 * 2 ^ 59
def prefixEnd_7625181 : Nat := 4983230072969 + 3 ^ 40 * 7625181 * 2
def baseEnd_7625181 : Nat := 3915382930531236177969937

theorem tailTrace_7625181 : CollatzResearch.WordTrace tailWord_7625181 prefixEnd_7625181 3915382930531236177969937 := by
  unfold tailWord_7625181
  simp only [CollatzResearch.WordTrace]
  refine ⟨278113198988278989080323397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185408799325519326053548931 278113198988278989080323397)
  ·
    refine ⟨52146224810302310452560637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 278113198988278989080323397 52146224810302310452560637)
    ·
      refine ⟨19554834303863366419710239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 52146224810302310452560637 19554834303863366419710239)
      ·
        refine ⟨29332251455795049629565359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19554834303863366419710239 29332251455795049629565359)
        ·
          refine ⟨43998377183692574444348039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29332251455795049629565359 43998377183692574444348039)
          ·
            refine ⟨65997565775538861666522059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43998377183692574444348039 65997565775538861666522059)
            ·
              refine ⟨98996348663308292499783089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65997565775538861666522059 98996348663308292499783089)
              ·
                refine ⟨74247261497481219374837317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 98996348663308292499783089 74247261497481219374837317)
                ·
                  refine ⟨13921361530777728632781997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 74247261497481219374837317 13921361530777728632781997)
                  ·
                    refine ⟨5220510574041648237293249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13921361530777728632781997 5220510574041648237293249)
                    ·
                      refine ⟨3915382930531236177969937, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5220510574041648237293249 3915382930531236177969937)
                      ·
                        rfl

theorem cell23_7625181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 1, 2, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 1, 2, 4, 3, 2].length) (baseStart_7625181 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7625181 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7625181 prefixEnd_7625181 := by exact prefixLift 7625181
  have htrace : WordTrace (prefixWord ++ tailWord_7625181) baseStart_7625181 baseEnd_7625181 := by
    simpa [prefixWord, tailWord_7625181, baseEnd_7625181] using wordTrace_append hprefix tailTrace_7625181
  have hstable : (prefixWord ++ tailWord_7625181).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7625181).length < 2 ^ (prefixWord ++ tailWord_7625181).sum := by decide
  have hdescent : baseEnd_7625181 < baseStart_7625181 := by decide
  rcases family_descends (prefixWord ++ tailWord_7625181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7625198 : List Nat := [4, 1, 2, 1, 2, 3, 2, 1, 2, 3, 2]
def baseStart_7625198 : Nat := 118140960795 + 7625198 * 2 ^ 59
def prefixEnd_7625198 : Nat := 4983230072969 + 3 ^ 40 * 7625198 * 2
def baseEnd_7625198 : Nat := 3915391659702362611457359

theorem tailTrace_7625198 : CollatzResearch.WordTrace tailWord_7625198 prefixEnd_7625198 3915391659702362611457359 := by
  unfold tailWord_7625198
  simp only [CollatzResearch.WordTrace]
  refine ⟨34764227378652175122961531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 185409212686144933989128165 34764227378652175122961531)
  ·
    refine ⟨52146341067978262684442297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34764227378652175122961531 52146341067978262684442297)
    ·
      refine ⟨39109755800983697013331723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52146341067978262684442297 39109755800983697013331723)
      ·
        refine ⟨58664633701475545519997585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39109755800983697013331723 58664633701475545519997585)
        ·
          refine ⟨43998475276106659139998189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58664633701475545519997585 43998475276106659139998189)
          ·
            refine ⟨16499428228539997177499321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43998475276106659139998189 16499428228539997177499321)
            ·
              refine ⟨12374571171404997883124491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16499428228539997177499321 12374571171404997883124491)
              ·
                refine ⟨18561856757107496824686737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12374571171404997883124491 18561856757107496824686737)
                ·
                  refine ⟨13921392567830622618515053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18561856757107496824686737 13921392567830622618515053)
                  ·
                    refine ⟨5220522212936483481943145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13921392567830622618515053 5220522212936483481943145)
                    ·
                      refine ⟨3915391659702362611457359, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5220522212936483481943145 3915391659702362611457359)
                      ·
                        rfl

theorem cell23_7625198_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 3, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 3, 2, 1, 2, 3, 2].length) (baseStart_7625198 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7625198 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7625198 prefixEnd_7625198 := by exact prefixLift 7625198
  have htrace : WordTrace (prefixWord ++ tailWord_7625198) baseStart_7625198 baseEnd_7625198 := by
    simpa [prefixWord, tailWord_7625198, baseEnd_7625198] using wordTrace_append hprefix tailTrace_7625198
  have hstable : (prefixWord ++ tailWord_7625198).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7625198).length < 2 ^ (prefixWord ++ tailWord_7625198).sum := by decide
  have hdescent : baseEnd_7625198 < baseStart_7625198 := by decide
  rcases family_descends (prefixWord ++ tailWord_7625198) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7625217 : List Nat := [1, 2, 4, 1, 3, 12]
def baseStart_7625217 : Nat := 118140960795 + 7625217 * 2 ^ 59
def prefixEnd_7625217 : Nat := 4983230072969 + 3 ^ 40 * 7625217 * 2
def baseEnd_7625217 : Nat := 16112763028126740893497

theorem tailTrace_7625217 : CollatzResearch.WordTrace tailWord_7625217 prefixEnd_7625217 16112763028126740893497 := by
  unfold tailWord_7625217
  simp only [CollatzResearch.WordTrace]
  refine ⟨278114512016148567228633905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185409674677432378152422603 278114512016148567228633905)
  ·
    refine ⟨208585884012111425421475429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 278114512016148567228633905 208585884012111425421475429)
    ·
      refine ⟨39109853252270892266526643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 208585884012111425421475429 39109853252270892266526643)
      ·
        refine ⟨58664779878406338399789965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39109853252270892266526643 58664779878406338399789965)
        ·
          refine ⟨21999292454402376899921237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 58664779878406338399789965 21999292454402376899921237)
          ·
            refine ⟨16112763028126740893497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 12 21999292454402376899921237 16112763028126740893497)
            ·
              rfl

theorem cell23_7625217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 12].length) (baseStart_7625217 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7625217 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7625217 prefixEnd_7625217 := by exact prefixLift 7625217
  have htrace : WordTrace (prefixWord ++ tailWord_7625217) baseStart_7625217 baseEnd_7625217 := by
    simpa [prefixWord, tailWord_7625217, baseEnd_7625217] using wordTrace_append hprefix tailTrace_7625217
  have hstable : (prefixWord ++ tailWord_7625217).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7625217).length < 2 ^ (prefixWord ++ tailWord_7625217).sum := by decide
  have hdescent : baseEnd_7625217 < baseStart_7625217 := by decide
  rcases family_descends (prefixWord ++ tailWord_7625217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7625247 : List Nat := [1, 1, 2, 4, 1, 1, 1, 1, 4, 7]
def baseStart_7625247 : Nat := 118140960795 + 7625247 * 2 ^ 59
def prefixEnd_7625247 : Nat := 4983230072969 + 3 ^ 40 * 7625247 * 2
def baseEnd_7625247 : Nat := 1305138940084810973248211

theorem tailTrace_7625247 : CollatzResearch.WordTrace tailWord_7625247 prefixEnd_7625247 1305138940084810973248211 := by
  unfold tailWord_7625247
  simp only [CollatzResearch.WordTrace]
  refine ⟨278115606206039882352225995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185410404137359921568150663 278115606206039882352225995)
  ·
    refine ⟨417173409309059823528338993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 278115606206039882352225995 417173409309059823528338993)
    ·
      refine ⟨312880056981794867646254245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 417173409309059823528338993 312880056981794867646254245)
      ·
        refine ⟨58665010684086537683672671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 312880056981794867646254245 58665010684086537683672671)
        ·
          refine ⟨87997516026129806525509007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58665010684086537683672671 87997516026129806525509007)
          ·
            refine ⟨131996274039194709788263511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87997516026129806525509007 131996274039194709788263511)
            ·
              refine ⟨197994411058792064682395267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 131996274039194709788263511 197994411058792064682395267)
              ·
                refine ⟨296991616588188097023592901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 197994411058792064682395267 296991616588188097023592901)
                ·
                  refine ⟨55685928110285268191923669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 296991616588188097023592901 55685928110285268191923669)
                  ·
                    refine ⟨1305138940084810973248211, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 55685928110285268191923669 1305138940084810973248211)
                    ·
                      rfl

theorem cell23_7625247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 1, 1, 4, 7].length) (baseStart_7625247 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7625247 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7625247 prefixEnd_7625247 := by exact prefixLift 7625247
  have htrace : WordTrace (prefixWord ++ tailWord_7625247) baseStart_7625247 baseEnd_7625247 := by
    simpa [prefixWord, tailWord_7625247, baseEnd_7625247] using wordTrace_append hprefix tailTrace_7625247
  have hstable : (prefixWord ++ tailWord_7625247).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7625247).length < 2 ^ (prefixWord ++ tailWord_7625247).sum := by decide
  have hdescent : baseEnd_7625247 < baseStart_7625247 := by decide
  rcases family_descends (prefixWord ++ tailWord_7625247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7625262 : List Nat := [4, 1, 3, 1, 4, 1, 2, 1, 1, 1, 4]
def baseStart_7625262 : Nat := 118140960795 + 7625262 * 2 ^ 59
def prefixEnd_7625262 : Nat := 4983230072969 + 3 ^ 40 * 7625262 * 2
def baseEnd_7625262 : Nat := 3915424522464250361057065

theorem tailTrace_7625262 : CollatzResearch.WordTrace tailWord_7625262 prefixEnd_7625262 3915424522464250361057065 := by
  unfold tailWord_7625262
  simp only [CollatzResearch.WordTrace]
  refine ⟨34764519162623192489252755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 185410768867323693276014693 34764519162623192489252755)
  ·
    refine ⟨52146778743934788733879133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34764519162623192489252755 52146778743934788733879133)
    ·
      refine ⟨19555042028975545775204675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 52146778743934788733879133 19555042028975545775204675)
      ·
        refine ⟨29332563043463318662807013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19555042028975545775204675 29332563043463318662807013)
        ·
          refine ⟨5499855570649372249276315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 29332563043463318662807013 5499855570649372249276315)
          ·
            refine ⟨8249783355974058373914473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5499855570649372249276315 8249783355974058373914473)
            ·
              refine ⟨6187337516980543780435855, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8249783355974058373914473 6187337516980543780435855)
              ·
                refine ⟨9281006275470815670653783, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6187337516980543780435855 9281006275470815670653783)
                ·
                  refine ⟨13921509413206223505980675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9281006275470815670653783 13921509413206223505980675)
                  ·
                    refine ⟨20882264119809335258971013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13921509413206223505980675 20882264119809335258971013)
                    ·
                      refine ⟨3915424522464250361057065, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20882264119809335258971013 3915424522464250361057065)
                      ·
                        rfl

theorem cell23_7625262_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 4, 1, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 4, 1, 2, 1, 1, 1, 4].length) (baseStart_7625262 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7625262 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7625262 prefixEnd_7625262 := by exact prefixLift 7625262
  have htrace : WordTrace (prefixWord ++ tailWord_7625262) baseStart_7625262 baseEnd_7625262 := by
    simpa [prefixWord, tailWord_7625262, baseEnd_7625262] using wordTrace_append hprefix tailTrace_7625262
  have hstable : (prefixWord ++ tailWord_7625262).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7625262).length < 2 ^ (prefixWord ++ tailWord_7625262).sum := by decide
  have hdescent : baseEnd_7625262 < baseStart_7625262 := by decide
  rcases family_descends (prefixWord ++ tailWord_7625262) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7625294 : List Nat := [4, 1, 1, 1, 1, 2, 4, 1, 2, 6]
def baseStart_7625294 : Nat := 118140960795 + 7625294 * 2 ^ 59
def prefixEnd_7625294 : Nat := 4983230072969 + 3 ^ 40 * 7625294 * 2
def baseEnd_7625294 : Nat := 1305146984615064745285639

theorem tailTrace_7625294 : CollatzResearch.WordTrace tailWord_7625294 prefixEnd_7625294 1305146984615064745285639 := by
  unfold tailWord_7625294
  simp only [CollatzResearch.WordTrace]
  refine ⟨34764665054608701172398367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 185411546957913072919457957 34764665054608701172398367)
  ·
    refine ⟨52146997581913051758597551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34764665054608701172398367 52146997581913051758597551)
    ·
      refine ⟨78220496372869577637896327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52146997581913051758597551 78220496372869577637896327)
      ·
        refine ⟨117330744559304366456844491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78220496372869577637896327 117330744559304366456844491)
        ·
          refine ⟨175996116838956549685266737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 117330744559304366456844491 175996116838956549685266737)
          ·
            refine ⟨131997087629217412263950053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 175996116838956549685266737 131997087629217412263950053)
            ·
              refine ⟨24749453930478264799490635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 131997087629217412263950053 24749453930478264799490635)
              ·
                refine ⟨37124180895717397199235953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24749453930478264799490635 37124180895717397199235953)
                ·
                  refine ⟨27843135671788047899426965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37124180895717397199235953 27843135671788047899426965)
                  ·
                    refine ⟨1305146984615064745285639, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27843135671788047899426965 1305146984615064745285639)
                    ·
                      rfl

theorem cell23_7625294_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 4, 1, 2, 6].length) (baseStart_7625294 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7625294 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7625294 prefixEnd_7625294 := by exact prefixLift 7625294
  have htrace : WordTrace (prefixWord ++ tailWord_7625294) baseStart_7625294 baseEnd_7625294 := by
    simpa [prefixWord, tailWord_7625294, baseEnd_7625294] using wordTrace_append hprefix tailTrace_7625294
  have hstable : (prefixWord ++ tailWord_7625294).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7625294).length < 2 ^ (prefixWord ++ tailWord_7625294).sum := by decide
  have hdescent : baseEnd_7625294 < baseStart_7625294 := by decide
  rcases family_descends (prefixWord ++ tailWord_7625294) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7625304 : List Nat := [2, 1, 2, 2, 1, 2, 2, 2, 2, 4, 3]
def baseStart_7625304 : Nat := 118140960795 + 7625304 * 2 ^ 59
def prefixEnd_7625304 : Nat := 4983230072969 + 3 ^ 40 * 7625304 * 2
def baseEnd_7625304 : Nat := 3915446088651739196731871

theorem tailTrace_7625304 : CollatzResearch.WordTrace tailWord_7625304 prefixEnd_7625304 3915446088651739196731871 := by
  unfold tailWord_7625304
  simp only [CollatzResearch.WordTrace]
  refine ⟨139058842583416690543525483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 185411790111222254058033977 139058842583416690543525483)
  ·
    refine ⟨208588263875125035815288225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139058842583416690543525483 208588263875125035815288225)
    ·
      refine ⟨156441197906343776861466169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 208588263875125035815288225 156441197906343776861466169)
      ·
        refine ⟨117330898429757832646099627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 156441197906343776861466169 117330898429757832646099627)
        ·
          refine ⟨175996347644636748969149441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 117330898429757832646099627 175996347644636748969149441)
          ·
            refine ⟨131997260733477561726862081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 175996347644636748969149441 131997260733477561726862081)
            ·
              refine ⟨98997945550108171295146561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 131997260733477561726862081 98997945550108171295146561)
              ·
                refine ⟨74248459162581128471359921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 98997945550108171295146561 74248459162581128471359921)
                ·
                  refine ⟨55686344371935846353519941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 74248459162581128471359921 55686344371935846353519941)
                  ·
                    refine ⟨10441189569737971191284989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 55686344371935846353519941 10441189569737971191284989)
                    ·
                      refine ⟨3915446088651739196731871, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10441189569737971191284989 3915446088651739196731871)
                      ·
                        rfl

theorem cell23_7625304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 2, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 2, 2, 2, 4, 3].length) (baseStart_7625304 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7625304 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7625304 prefixEnd_7625304 := by exact prefixLift 7625304
  have htrace : WordTrace (prefixWord ++ tailWord_7625304) baseStart_7625304 baseEnd_7625304 := by
    simpa [prefixWord, tailWord_7625304, baseEnd_7625304] using wordTrace_append hprefix tailTrace_7625304
  have hstable : (prefixWord ++ tailWord_7625304).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7625304).length < 2 ^ (prefixWord ++ tailWord_7625304).sum := by decide
  have hdescent : baseEnd_7625304 < baseStart_7625304 := by decide
  rcases family_descends (prefixWord ++ tailWord_7625304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7625391 : List Nat := [1, 1, 2, 1, 2, 5, 2, 2, 2, 1, 4]
def baseStart_7625391 : Nat := 118140960795 + 7625391 * 2 ^ 59
def prefixEnd_7625391 : Nat := 4983230072969 + 3 ^ 40 * 7625391 * 2
def baseEnd_7625391 : Nat := 3915490761468680356343971

theorem tailTrace_7625391 : CollatzResearch.WordTrace tailWord_7625391 prefixEnd_7625391 3915490761468680356343971 := by
  unfold tailWord_7625391
  simp only [CollatzResearch.WordTrace]
  refine ⟨278120858317518194945468027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185413905545012129963645351 278120858317518194945468027)
  ·
    refine ⟨417181287476277292418202041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 278120858317518194945468027 417181287476277292418202041)
    ·
      refine ⟨312885965607207969313651531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 417181287476277292418202041 312885965607207969313651531)
      ·
        refine ⟨469328948410811953970477297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 312885965607207969313651531 469328948410811953970477297)
        ·
          refine ⟨351996711308108965477857973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 469328948410811953970477297 351996711308108965477857973)
          ·
            refine ⟨32999691685135215513549185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 351996711308108965477857973 32999691685135215513549185)
            ·
              refine ⟨24749768763851411635161889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32999691685135215513549185 24749768763851411635161889)
              ·
                refine ⟨18562326572888558726371417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24749768763851411635161889 18562326572888558726371417)
                ·
                  refine ⟨13921744929666419044778563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18562326572888558726371417 13921744929666419044778563)
                  ·
                    refine ⟨20882617394499628567167845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13921744929666419044778563 20882617394499628567167845)
                    ·
                      refine ⟨3915490761468680356343971, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20882617394499628567167845 3915490761468680356343971)
                      ·
                        rfl

theorem cell23_7625391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 5, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 5, 2, 2, 2, 1, 4].length) (baseStart_7625391 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7625391 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7625391 prefixEnd_7625391 := by exact prefixLift 7625391
  have htrace : WordTrace (prefixWord ++ tailWord_7625391) baseStart_7625391 baseEnd_7625391 := by
    simpa [prefixWord, tailWord_7625391, baseEnd_7625391] using wordTrace_append hprefix tailTrace_7625391
  have hstable : (prefixWord ++ tailWord_7625391).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7625391).length < 2 ^ (prefixWord ++ tailWord_7625391).sum := by decide
  have hdescent : baseEnd_7625391 < baseStart_7625391 := by decide
  rcases family_descends (prefixWord ++ tailWord_7625391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7625394 : List Nat := [3, 2, 1, 1, 1, 2, 1, 1, 1, 5, 5]
def baseStart_7625394 : Nat := 118140960795 + 7625394 * 2 ^ 59
def prefixEnd_7625394 : Nat := 4983230072969 + 3 ^ 40 * 7625394 * 2
def baseEnd_7625394 : Nat := 3915492301910643844606457

theorem tailTrace_7625394 : CollatzResearch.WordTrace tailWord_7625394 prefixEnd_7625394 3915492301910643844606457 := by
  unfold tailWord_7625394
  simp only [CollatzResearch.WordTrace]
  refine ⟨69530241934126831614456809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 185413978491004884305218157 69530241934126831614456809)
  ·
    refine ⟨52147681450595123710842607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69530241934126831614456809 52147681450595123710842607)
    ·
      refine ⟨78221522175892685566263911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52147681450595123710842607 78221522175892685566263911)
      ·
        refine ⟨117332283263839028349395867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78221522175892685566263911 117332283263839028349395867)
        ·
          refine ⟨175998424895758542524093801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 117332283263839028349395867 175998424895758542524093801)
          ·
            refine ⟨131998818671818906893070351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 175998424895758542524093801 131998818671818906893070351)
            ·
              refine ⟨197998228007728360339605527, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 131998818671818906893070351 197998228007728360339605527)
              ·
                refine ⟨296997342011592540509408291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 197998228007728360339605527 296997342011592540509408291)
                ·
                  refine ⟨445496013017388810764112437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 296997342011592540509408291 445496013017388810764112437)
                  ·
                    refine ⟨41765251220380201009135541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 445496013017388810764112437 41765251220380201009135541)
                    ·
                      refine ⟨3915492301910643844606457, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41765251220380201009135541 3915492301910643844606457)
                      ·
                        rfl

theorem cell23_7625394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 1, 1, 1, 5, 5].length) (baseStart_7625394 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7625394 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7625394 prefixEnd_7625394 := by exact prefixLift 7625394
  have htrace : WordTrace (prefixWord ++ tailWord_7625394) baseStart_7625394 baseEnd_7625394 := by
    simpa [prefixWord, tailWord_7625394, baseEnd_7625394] using wordTrace_append hprefix tailTrace_7625394
  have hstable : (prefixWord ++ tailWord_7625394).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7625394).length < 2 ^ (prefixWord ++ tailWord_7625394).sum := by decide
  have hdescent : baseEnd_7625394 < baseStart_7625394 := by decide
  rcases family_descends (prefixWord ++ tailWord_7625394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7625401 : List Nat := [1, 2, 1, 4, 1, 1, 1, 5, 3, 4]
def baseStart_7625401 : Nat := 118140960795 + 7625401 * 2 ^ 59
def prefixEnd_7625401 : Nat := 4983230072969 + 3 ^ 40 * 7625401 * 2
def baseEnd_7625401 : Nat := 1305165298758408439072975

theorem tailTrace_7625401 : CollatzResearch.WordTrace tailWord_7625401 prefixEnd_7625401 1305165298758408439072975 := by
  unfold tailWord_7625401
  simp only [CollatzResearch.WordTrace]
  refine ⟨278121223047481966653332057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185414148698321311102221371 278121223047481966653332057)
  ·
    refine ⟨208590917285611474989999043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 278121223047481966653332057 208590917285611474989999043)
    ·
      refine ⟨312886375928417212484998565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 208590917285611474989999043 312886375928417212484998565)
      ·
        refine ⟨58666195486578227340937231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 312886375928417212484998565 58666195486578227340937231)
        ·
          refine ⟨87999293229867341011405847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58666195486578227340937231 87999293229867341011405847)
          ·
            refine ⟨131998939844801011517108771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87999293229867341011405847 131998939844801011517108771)
            ·
              refine ⟨197998409767201517275663157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 131998939844801011517108771 197998409767201517275663157)
              ·
                refine ⟨18562350915675142244593421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 197998409767201517275663157 18562350915675142244593421)
                ·
                  refine ⟨6960881593378178341722533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18562350915675142244593421 6960881593378178341722533)
                  ·
                    refine ⟨1305165298758408439072975, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6960881593378178341722533 1305165298758408439072975)
                    ·
                      rfl

theorem cell23_7625401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 1, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 1, 5, 3, 4].length) (baseStart_7625401 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7625401 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7625401 prefixEnd_7625401 := by exact prefixLift 7625401
  have htrace : WordTrace (prefixWord ++ tailWord_7625401) baseStart_7625401 baseEnd_7625401 := by
    simpa [prefixWord, tailWord_7625401, baseEnd_7625401] using wordTrace_append hprefix tailTrace_7625401
  have hstable : (prefixWord ++ tailWord_7625401).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7625401).length < 2 ^ (prefixWord ++ tailWord_7625401).sum := by decide
  have hdescent : baseEnd_7625401 < baseStart_7625401 := by decide
  rcases family_descends (prefixWord ++ tailWord_7625401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7625408 : List Nat := [2, 1, 1, 2, 4, 3, 1, 1, 2, 4, 2]
def baseStart_7625408 : Nat := 118140960795 + 7625408 * 2 ^ 59
def prefixEnd_7625408 : Nat := 4983230072969 + 3 ^ 40 * 7625408 * 2
def baseEnd_7625408 : Nat := 3915499490639806789831393

theorem tailTrace_7625408 : CollatzResearch.WordTrace tailWord_7625408 prefixEnd_7625408 3915499490639806789831393 := by
  unfold tailWord_7625408
  simp only [CollatzResearch.WordTrace]
  refine ⟨139060739179228303424418439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 185414318905637737899224585 139060739179228303424418439)
  ·
    refine ⟨208591108768842455136627659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139060739179228303424418439 208591108768842455136627659)
    ·
      refine ⟨312886663153263682704941489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 208591108768842455136627659 312886663153263682704941489)
      ·
        refine ⟨234664997364947762028706117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 312886663153263682704941489 234664997364947762028706117)
        ·
          refine ⟨43999687005927705380382397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 234664997364947762028706117 43999687005927705380382397)
          ·
            refine ⟨16499882627222889517643399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43999687005927705380382397 16499882627222889517643399)
            ·
              refine ⟨24749823940834334276465099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16499882627222889517643399 24749823940834334276465099)
              ·
                refine ⟨37124735911251501414697649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24749823940834334276465099 37124735911251501414697649)
                ·
                  refine ⟨27843551933438626061023237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37124735911251501414697649 27843551933438626061023237)
                  ·
                    refine ⟨5220665987519742386441857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 27843551933438626061023237 5220665987519742386441857)
                    ·
                      refine ⟨3915499490639806789831393, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5220665987519742386441857 3915499490639806789831393)
                      ·
                        rfl

theorem cell23_7625408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 3, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 3, 1, 1, 2, 4, 2].length) (baseStart_7625408 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7625408 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7625408 prefixEnd_7625408 := by exact prefixLift 7625408
  have htrace : WordTrace (prefixWord ++ tailWord_7625408) baseStart_7625408 baseEnd_7625408 := by
    simpa [prefixWord, tailWord_7625408, baseEnd_7625408] using wordTrace_append hprefix tailTrace_7625408
  have hstable : (prefixWord ++ tailWord_7625408).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7625408).length < 2 ^ (prefixWord ++ tailWord_7625408).sum := by decide
  have hdescent : baseEnd_7625408 < baseStart_7625408 := by decide
  rcases family_descends (prefixWord ++ tailWord_7625408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7625418 : List Nat := [3, 1, 2, 1, 4, 2, 1, 2, 3, 4]
def baseStart_7625418 : Nat := 118140960795 + 7625418 * 2 ^ 59
def prefixEnd_7625418 : Nat := 4983230072969 + 3 ^ 40 * 7625418 * 2
def baseEnd_7625418 : Nat := 1305168208482117250235449

theorem tailTrace_7625418 : CollatzResearch.WordTrace tailWord_7625418 prefixEnd_7625418 1305168208482117250235449 := by
  unfold tailWord_7625418
  simp only [CollatzResearch.WordTrace]
  refine ⟨69530460772105094639175227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 185414562058946919037800605 69530460772105094639175227)
  ·
    refine ⟨104295691158157641958762841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69530460772105094639175227 104295691158157641958762841)
    ·
      refine ⟨78221768368618231469072131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 104295691158157641958762841 78221768368618231469072131)
      ·
        refine ⟨117332652552927347203608197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78221768368618231469072131 117332652552927347203608197)
        ·
          refine ⟨21999872353673877600676537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 117332652552927347203608197 21999872353673877600676537)
          ·
            refine ⟨16499904265255408200507403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21999872353673877600676537 16499904265255408200507403)
            ·
              refine ⟨24749856397883112300761105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16499904265255408200507403 24749856397883112300761105)
              ·
                refine ⟨18562392298412334225570829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24749856397883112300761105 18562392298412334225570829)
                ·
                  refine ⟨6960897111904625334589061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18562392298412334225570829 6960897111904625334589061)
                  ·
                    refine ⟨1305168208482117250235449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6960897111904625334589061 1305168208482117250235449)
                    ·
                      rfl

theorem cell23_7625418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 2, 1, 2, 3, 4].length) (baseStart_7625418 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7625418 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7625418 prefixEnd_7625418 := by exact prefixLift 7625418
  have htrace : WordTrace (prefixWord ++ tailWord_7625418) baseStart_7625418 baseEnd_7625418 := by
    simpa [prefixWord, tailWord_7625418, baseEnd_7625418] using wordTrace_append hprefix tailTrace_7625418
  have hstable : (prefixWord ++ tailWord_7625418).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7625418).length < 2 ^ (prefixWord ++ tailWord_7625418).sum := by decide
  have hdescent : baseEnd_7625418 < baseStart_7625418 := by decide
  rcases family_descends (prefixWord ++ tailWord_7625418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7625468 : List Nat := [2, 2, 2, 1, 3, 2, 1, 2, 1, 5, 2]
def baseStart_7625468 : Nat := 118140960795 + 7625468 * 2 ^ 59
def prefixEnd_7625468 : Nat := 4983230072969 + 3 ^ 40 * 7625468 * 2
def baseEnd_7625468 : Nat := 3915530299479076555081117

theorem tailTrace_7625468 : CollatzResearch.WordTrace tailWord_7625468 prefixEnd_7625468 3915530299479076555081117 := by
  unfold tailWord_7625468
  simp only [CollatzResearch.WordTrace]
  refine ⟨139061833369119618548010529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 185415777825492824730680705 139061833369119618548010529)
  ·
    refine ⟨104296375026839713911007897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 139061833369119618548010529 104296375026839713911007897)
    ·
      refine ⟨78222281270129785433255923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 104296375026839713911007897 78222281270129785433255923)
      ·
        refine ⟨117333421905194678149883885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78222281270129785433255923 117333421905194678149883885)
        ·
          refine ⟨44000033214448004306206457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 117333421905194678149883885 44000033214448004306206457)
          ·
            refine ⟨33000024910836003229654843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44000033214448004306206457 33000024910836003229654843)
            ·
              refine ⟨49500037366254004844482265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33000024910836003229654843 49500037366254004844482265)
              ·
                refine ⟨37125028024690503633361699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49500037366254004844482265 37125028024690503633361699)
                ·
                  refine ⟨55687542037035755450042549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37125028024690503633361699 55687542037035755450042549)
                  ·
                    refine ⟨5220707065972102073441489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 55687542037035755450042549 5220707065972102073441489)
                    ·
                      refine ⟨3915530299479076555081117, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5220707065972102073441489 3915530299479076555081117)
                      ·
                        rfl

theorem cell23_7625468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 2, 1, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 2, 1, 2, 1, 5, 2].length) (baseStart_7625468 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7625468 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7625468 prefixEnd_7625468 := by exact prefixLift 7625468
  have htrace : WordTrace (prefixWord ++ tailWord_7625468) baseStart_7625468 baseEnd_7625468 := by
    simpa [prefixWord, tailWord_7625468, baseEnd_7625468] using wordTrace_append hprefix tailTrace_7625468
  have hstable : (prefixWord ++ tailWord_7625468).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7625468).length < 2 ^ (prefixWord ++ tailWord_7625468).sum := by decide
  have hdescent : baseEnd_7625468 < baseStart_7625468 := by decide
  rcases family_descends (prefixWord ++ tailWord_7625468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7625481 : List Nat := [1, 2, 1, 1, 3, 2, 2, 3, 3, 1, 4]
def baseStart_7625481 : Nat := 118140960795 + 7625481 * 2 ^ 59
def prefixEnd_7625481 : Nat := 4983230072969 + 3 ^ 40 * 7625481 * 2
def baseEnd_7625481 : Nat := 3915536974727585004218557

theorem tailTrace_7625481 : CollatzResearch.WordTrace tailWord_7625481 prefixEnd_7625481 3915536974727585004218557 := by
  unfold tailWord_7625481
  simp only [CollatzResearch.WordTrace]
  refine ⟨278124140887192140316244297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185416093924794760210829531 278124140887192140316244297)
  ·
    refine ⟨208593105665394105237183223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 278124140887192140316244297 208593105665394105237183223)
    ·
      refine ⟨312889658498091157855774835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 208593105665394105237183223 312889658498091157855774835)
      ·
        refine ⟨469334487747136736783662253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 312889658498091157855774835 469334487747136736783662253)
        ·
          refine ⟨176000432905176276293873345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 469334487747136736783662253 176000432905176276293873345)
          ·
            refine ⟨132000324678882207220405009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 176000432905176276293873345 132000324678882207220405009)
            ·
              refine ⟨99000243509161655415303757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 132000324678882207220405009 99000243509161655415303757)
              ·
                refine ⟨37125091315935620780738909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 99000243509161655415303757 37125091315935620780738909)
                ·
                  refine ⟨13921909243475857792777091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 37125091315935620780738909 13921909243475857792777091)
                  ·
                    refine ⟨20882863865213786689165637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13921909243475857792777091 20882863865213786689165637)
                    ·
                      refine ⟨3915536974727585004218557, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20882863865213786689165637 3915536974727585004218557)
                      ·
                        rfl

theorem cell23_7625481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 2, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 2, 3, 3, 1, 4].length) (baseStart_7625481 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7625481 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7625481 prefixEnd_7625481 := by exact prefixLift 7625481
  have htrace : WordTrace (prefixWord ++ tailWord_7625481) baseStart_7625481 baseEnd_7625481 := by
    simpa [prefixWord, tailWord_7625481, baseEnd_7625481] using wordTrace_append hprefix tailTrace_7625481
  have hstable : (prefixWord ++ tailWord_7625481).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7625481).length < 2 ^ (prefixWord ++ tailWord_7625481).sum := by decide
  have hdescent : baseEnd_7625481 < baseStart_7625481 := by decide
  rcases family_descends (prefixWord ++ tailWord_7625481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7625491 : List Nat := [1, 1, 1, 2, 1, 3, 3, 1, 6, 4]
def baseStart_7625491 : Nat := 118140960795 + 7625491 * 2 ^ 59
def prefixEnd_7625491 : Nat := 4983230072969 + 3 ^ 40 * 7625491 * 2
def baseEnd_7625491 : Nat := 1305180703178043321697837

theorem tailTrace_7625491 : CollatzResearch.WordTrace tailWord_7625491 prefixEnd_7625491 1305180703178043321697837 := by
  unfold tailWord_7625491
  simp only [CollatzResearch.WordTrace]
  refine ⟨278124505617155912024108327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185416337078103941349405551 278124505617155912024108327)
  ·
    refine ⟨417186758425733868036162491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 278124505617155912024108327 417186758425733868036162491)
    ·
      refine ⟨625780137638600802054243737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 417186758425733868036162491 625780137638600802054243737)
      ·
        refine ⟨469335103228950601540682803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 625780137638600802054243737 469335103228950601540682803)
        ·
          refine ⟨704002654843425902311024205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 469335103228950601540682803 704002654843425902311024205)
          ·
            refine ⟨264000995566284713366634077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 704002654843425902311024205 264000995566284713366634077)
            ·
              refine ⟨99000373337356767512487779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 264000995566284713366634077 99000373337356767512487779)
              ·
                refine ⟨148500560006035151268731669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 99000373337356767512487779 148500560006035151268731669)
                ·
                  refine ⟨6960963750282897715721797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 148500560006035151268731669 6960963750282897715721797)
                  ·
                    refine ⟨1305180703178043321697837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6960963750282897715721797 1305180703178043321697837)
                    ·
                      rfl

theorem cell23_7625491_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 3, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 3, 1, 6, 4].length) (baseStart_7625491 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7625491 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7625491 prefixEnd_7625491 := by exact prefixLift 7625491
  have htrace : WordTrace (prefixWord ++ tailWord_7625491) baseStart_7625491 baseEnd_7625491 := by
    simpa [prefixWord, tailWord_7625491, baseEnd_7625491] using wordTrace_append hprefix tailTrace_7625491
  have hstable : (prefixWord ++ tailWord_7625491).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7625491).length < 2 ^ (prefixWord ++ tailWord_7625491).sum := by decide
  have hdescent : baseEnd_7625491 < baseStart_7625491 := by decide
  rcases family_descends (prefixWord ++ tailWord_7625491) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7625498 : List Nat := [3, 1, 1, 3, 2, 1, 1, 5, 1, 1, 4]
def baseStart_7625498 : Nat := 118140960795 + 7625498 * 2 ^ 59
def prefixEnd_7625498 : Nat := 4983230072969 + 3 ^ 40 * 7625498 * 2
def baseEnd_7625498 : Nat := 3915545703898711437705979

theorem tailTrace_7625498 : CollatzResearch.WordTrace tailWord_7625498 prefixEnd_7625498 3915545703898711437705979 := by
  unfold tailWord_7625498
  simp only [CollatzResearch.WordTrace]
  refine ⟨69531190232032638054903287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 185416507285420368146408765 69531190232032638054903287)
  ·
    refine ⟨104296785348048957082354931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69531190232032638054903287 104296785348048957082354931)
    ·
      refine ⟨156445178022073435623532397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104296785348048957082354931 156445178022073435623532397)
      ·
        refine ⟨58666941758277538358824649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 156445178022073435623532397 58666941758277538358824649)
        ·
          refine ⟨44000206318708153769118487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58666941758277538358824649 44000206318708153769118487)
          ·
            refine ⟨66000309478062230653677731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44000206318708153769118487 66000309478062230653677731)
            ·
              refine ⟨99000464217093345980516597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66000309478062230653677731 99000464217093345980516597)
              ·
                refine ⟨9281293520352501185673431, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 99000464217093345980516597 9281293520352501185673431)
                ·
                  refine ⟨13921940280528751778510147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9281293520352501185673431 13921940280528751778510147)
                  ·
                    refine ⟨20882910420793127667765221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13921940280528751778510147 20882910420793127667765221)
                    ·
                      refine ⟨3915545703898711437705979, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20882910420793127667765221 3915545703898711437705979)
                      ·
                        rfl

theorem cell23_7625498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 1, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 1, 5, 1, 1, 4].length) (baseStart_7625498 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7625498 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7625498 prefixEnd_7625498 := by exact prefixLift 7625498
  have htrace : WordTrace (prefixWord ++ tailWord_7625498) baseStart_7625498 baseEnd_7625498 := by
    simpa [prefixWord, tailWord_7625498, baseEnd_7625498] using wordTrace_append hprefix tailTrace_7625498
  have hstable : (prefixWord ++ tailWord_7625498).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7625498).length < 2 ^ (prefixWord ++ tailWord_7625498).sum := by decide
  have hdescent : baseEnd_7625498 < baseStart_7625498 := by decide
  rcases family_descends (prefixWord ++ tailWord_7625498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7625521 : List Nat := [1, 2, 2, 3, 2, 1, 4, 8]
def baseStart_7625521 : Nat := 118140960795 + 7625521 * 2 ^ 59
def prefixEnd_7625521 : Nat := 4983230072969 + 3 ^ 40 * 7625521 * 2
def baseEnd_7625521 : Nat := 145020648664954253619199

theorem tailTrace_7625521 : CollatzResearch.WordTrace tailWord_7625521 prefixEnd_7625521 145020648664954253619199 := by
  unfold tailWord_7625521
  simp only [CollatzResearch.WordTrace]
  refine ⟨278125599807047227147700417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185417066538031484765133611 278125599807047227147700417)
  ·
    refine ⟨208594199855285420360775313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 278125599807047227147700417 208594199855285420360775313)
    ·
      refine ⟨156445649891464065270581485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 208594199855285420360775313 156445649891464065270581485)
      ·
        refine ⟨58667118709299024476468057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 156445649891464065270581485 58667118709299024476468057)
        ·
          refine ⟨44000339031974268357351043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58667118709299024476468057 44000339031974268357351043)
          ·
            refine ⟨66000508547961402536026565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44000339031974268357351043 66000508547961402536026565)
            ·
              refine ⟨12375095352742762975504981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 66000508547961402536026565 12375095352742762975504981)
              ·
                refine ⟨145020648664954253619199, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 12375095352742762975504981 145020648664954253619199)
                ·
                  rfl

theorem cell23_7625521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 4, 8].length) (baseStart_7625521 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7625521 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7625521 prefixEnd_7625521 := by exact prefixLift 7625521
  have htrace : WordTrace (prefixWord ++ tailWord_7625521) baseStart_7625521 baseEnd_7625521 := by
    simpa [prefixWord, tailWord_7625521, baseEnd_7625521] using wordTrace_append hprefix tailTrace_7625521
  have hstable : (prefixWord ++ tailWord_7625521).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7625521).length < 2 ^ (prefixWord ++ tailWord_7625521).sum := by decide
  have hdescent : baseEnd_7625521 < baseStart_7625521 := by decide
  rcases family_descends (prefixWord ++ tailWord_7625521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7625525 : List Nat := [1, 3, 3, 1, 3, 2, 1, 3, 2, 4]
def baseStart_7625525 : Nat := 118140960795 + 7625525 * 2 ^ 59
def prefixEnd_7625525 : Nat := 4983230072969 + 3 ^ 40 * 7625525 * 2
def baseEnd_7625525 : Nat := 1305186522625460944022785

theorem tailTrace_7625525 : CollatzResearch.WordTrace tailWord_7625525 prefixEnd_7625525 1305186522625460944022785 := by
  unfold tailWord_7625525
  simp only [CollatzResearch.WordTrace]
  refine ⟨278125745699032735830846029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185417163799355157220564019 278125745699032735830846029)
  ·
    refine ⟨104297154637137275936567261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 278125745699032735830846029 104297154637137275936567261)
    ·
      refine ⟨39111432988926478476212723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 104297154637137275936567261 39111432988926478476212723)
      ·
        refine ⟨58667149483389717714319085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39111432988926478476212723 58667149483389717714319085)
        ·
          refine ⟨22000181056271144142869657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 58667149483389717714319085 22000181056271144142869657)
          ·
            refine ⟨16500135792203358107152243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22000181056271144142869657 16500135792203358107152243)
            ·
              refine ⟨24750203688305037160728365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16500135792203358107152243 24750203688305037160728365)
              ·
                refine ⟨9281326383114388935273137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24750203688305037160728365 9281326383114388935273137)
                ·
                  refine ⟨6960994787335791701454853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9281326383114388935273137 6960994787335791701454853)
                  ·
                    refine ⟨1305186522625460944022785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6960994787335791701454853 1305186522625460944022785)
                    ·
                      rfl

theorem cell23_7625525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 2, 1, 3, 2, 4].length) (baseStart_7625525 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7625525 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7625525 prefixEnd_7625525 := by exact prefixLift 7625525
  have htrace : WordTrace (prefixWord ++ tailWord_7625525) baseStart_7625525 baseEnd_7625525 := by
    simpa [prefixWord, tailWord_7625525, baseEnd_7625525] using wordTrace_append hprefix tailTrace_7625525
  have hstable : (prefixWord ++ tailWord_7625525).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7625525).length < 2 ^ (prefixWord ++ tailWord_7625525).sum := by decide
  have hdescent : baseEnd_7625525 < baseStart_7625525 := by decide
  rcases family_descends (prefixWord ++ tailWord_7625525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7625535 : List Nat := [1, 1, 2, 2, 5, 1, 3, 2, 1, 2, 3]
def baseStart_7625535 : Nat := 118140960795 + 7625535 * 2 ^ 59
def prefixEnd_7625535 : Nat := 4983230072969 + 3 ^ 40 * 7625535 * 2
def baseEnd_7625535 : Nat := 3915564702682927792943309

theorem tailTrace_7625535 : CollatzResearch.WordTrace tailWord_7625535 prefixEnd_7625535 3915564702682927792943309 := by
  unfold tailWord_7625535
  simp only [CollatzResearch.WordTrace]
  refine ⟨278126110428996507538710059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185417406952664338359140039 278126110428996507538710059)
  ·
    refine ⟨417189165643494761308065089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 278126110428996507538710059 417189165643494761308065089)
    ·
      refine ⟨312891874232621070981048817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 417189165643494761308065089 312891874232621070981048817)
      ·
        refine ⟨234668905674465803235786613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 312891874232621070981048817 234668905674465803235786613)
        ·
          refine ⟨22000209906981169053354995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 234668905674465803235786613 22000209906981169053354995)
          ·
            refine ⟨33000314860471753580032493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22000209906981169053354995 33000314860471753580032493)
            ·
              refine ⟨12375118072676907592512185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33000314860471753580032493 12375118072676907592512185)
              ·
                refine ⟨9281338554507680694384139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12375118072676907592512185 9281338554507680694384139)
                ·
                  refine ⟨13922007831761521041576209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9281338554507680694384139 13922007831761521041576209)
                  ·
                    refine ⟨10441505873821140781182157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13922007831761521041576209 10441505873821140781182157)
                    ·
                      refine ⟨3915564702682927792943309, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10441505873821140781182157 3915564702682927792943309)
                      ·
                        rfl

theorem cell23_7625535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 1, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 1, 3, 2, 1, 2, 3].length) (baseStart_7625535 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7625535 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7625535 prefixEnd_7625535 := by exact prefixLift 7625535
  have htrace : WordTrace (prefixWord ++ tailWord_7625535) baseStart_7625535 baseEnd_7625535 := by
    simpa [prefixWord, tailWord_7625535, baseEnd_7625535] using wordTrace_append hprefix tailTrace_7625535
  have hstable : (prefixWord ++ tailWord_7625535).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7625535).length < 2 ^ (prefixWord ++ tailWord_7625535).sum := by decide
  have hdescent : baseEnd_7625535 < baseStart_7625535 := by decide
  rcases family_descends (prefixWord ++ tailWord_7625535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7625542 : List Nat := [6, 1, 1, 2, 2, 1, 1, 2, 1, 6]
def baseStart_7625542 : Nat := 118140960795 + 7625542 * 2 ^ 59
def prefixEnd_7625542 : Nat := 4983230072969 + 3 ^ 40 * 7625542 * 2
def baseEnd_7625542 : Nat := 1305189432349169755185259

theorem tailTrace_7625542 : CollatzResearch.WordTrace tailWord_7625542 prefixEnd_7625542 1305189432349169755185259 := by
  unfold tailWord_7625542
  simp only [CollatzResearch.WordTrace]
  refine ⟨8691448929374098366694215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 185417577159980765156143253 8691448929374098366694215)
  ·
    refine ⟨13037173394061147550041323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8691448929374098366694215 13037173394061147550041323)
    ·
      refine ⟨19555760091091721325061985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13037173394061147550041323 19555760091091721325061985)
      ·
        refine ⟨14666820068318790993796489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19555760091091721325061985 14666820068318790993796489)
        ·
          refine ⟨11000115051239093245347367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14666820068318790993796489 11000115051239093245347367)
          ·
            refine ⟨16500172576858639868021051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11000115051239093245347367 16500172576858639868021051)
            ·
              refine ⟨24750258865287959802031577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16500172576858639868021051 24750258865287959802031577)
              ·
                refine ⟨18562694148965969851523683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24750258865287959802031577 18562694148965969851523683)
                ·
                  refine ⟨27844041223448954777285525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18562694148965969851523683 27844041223448954777285525)
                  ·
                    refine ⟨1305189432349169755185259, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27844041223448954777285525 1305189432349169755185259)
                    ·
                      rfl

theorem cell23_7625542_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 2, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 2, 1, 1, 2, 1, 6].length) (baseStart_7625542 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7625542 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7625542 prefixEnd_7625542 := by exact prefixLift 7625542
  have htrace : WordTrace (prefixWord ++ tailWord_7625542) baseStart_7625542 baseEnd_7625542 := by
    simpa [prefixWord, tailWord_7625542, baseEnd_7625542] using wordTrace_append hprefix tailTrace_7625542
  have hstable : (prefixWord ++ tailWord_7625542).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7625542).length < 2 ^ (prefixWord ++ tailWord_7625542).sum := by decide
  have hdescent : baseEnd_7625542 < baseStart_7625542 := by decide
  rcases family_descends (prefixWord ++ tailWord_7625542) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7625548 : List Nat := [2, 2, 1, 3, 3, 1, 1, 1, 3, 3, 3]
def baseStart_7625548 : Nat := 118140960795 + 7625548 * 2 ^ 59
def prefixEnd_7625548 : Nat := 4983230072969 + 3 ^ 40 * 7625548 * 2
def baseEnd_7625548 : Nat := 3915571377931436242080749

theorem tailTrace_7625548 : CollatzResearch.WordTrace tailWord_7625548 prefixEnd_7625548 3915571377931436242080749 := by
  unfold tailWord_7625548
  simp only [CollatzResearch.WordTrace]
  refine ⟨139063292288974705379466649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 185417723051966273839288865 139063292288974705379466649)
  ·
    refine ⟨104297469216731029034599987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 139063292288974705379466649 104297469216731029034599987)
    ·
      refine ⟨156446203825096543551899981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104297469216731029034599987 156446203825096543551899981)
      ·
        refine ⟨58667326434411203831962493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 156446203825096543551899981 58667326434411203831962493)
        ·
          refine ⟨22000247412904201436985935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 58667326434411203831962493 22000247412904201436985935)
          ·
            refine ⟨33000371119356302155478903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22000247412904201436985935 33000371119356302155478903)
            ·
              refine ⟨49500556679034453233218355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33000371119356302155478903 49500556679034453233218355)
              ·
                refine ⟨74250835018551679849827533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49500556679034453233218355 74250835018551679849827533)
                ·
                  refine ⟨27844063131956879943685325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 74250835018551679849827533 27844063131956879943685325)
                  ·
                    refine ⟨10441523674483829978881997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27844063131956879943685325 10441523674483829978881997)
                    ·
                      refine ⟨3915571377931436242080749, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10441523674483829978881997 3915571377931436242080749)
                      ·
                        rfl

theorem cell23_7625548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 1, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 1, 1, 1, 3, 3, 3].length) (baseStart_7625548 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7625548 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7625548 prefixEnd_7625548 := by exact prefixLift 7625548
  have htrace : WordTrace (prefixWord ++ tailWord_7625548) baseStart_7625548 baseEnd_7625548 := by
    simpa [prefixWord, tailWord_7625548, baseEnd_7625548] using wordTrace_append hprefix tailTrace_7625548
  have hstable : (prefixWord ++ tailWord_7625548).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7625548).length < 2 ^ (prefixWord ++ tailWord_7625548).sum := by decide
  have hdescent : baseEnd_7625548 < baseStart_7625548 := by decide
  rcases family_descends (prefixWord ++ tailWord_7625548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7625549 : List Nat := [1, 6, 1, 2, 2, 1, 3, 1, 1, 1, 4]
def baseStart_7625549 : Nat := 118140960795 + 7625549 * 2 ^ 59
def prefixEnd_7625549 : Nat := 4983230072969 + 3 ^ 40 * 7625549 * 2
def baseEnd_7625549 : Nat := 3915571891412090738168245

theorem tailTrace_7625549 : CollatzResearch.WordTrace tailWord_7625549 prefixEnd_7625549 3915571891412090738168245 := by
  unfold tailWord_7625549
  simp only [CollatzResearch.WordTrace]
  refine ⟨278126621050945787929719701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185417747367297191953146467 278126621050945787929719701)
  ·
    refine ⟨13037185361763083809205611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 278126621050945787929719701 13037185361763083809205611)
    ·
      refine ⟨19555778042644625713808417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13037185361763083809205611 19555778042644625713808417)
      ·
        refine ⟨14666833531983469285356313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19555778042644625713808417 14666833531983469285356313)
        ·
          refine ⟨11000125148987601964017235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14666833531983469285356313 11000125148987601964017235)
          ·
            refine ⟨16500187723481402946025853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11000125148987601964017235 16500187723481402946025853)
            ·
              refine ⟨6187570396305526104759695, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16500187723481402946025853 6187570396305526104759695)
              ·
                refine ⟨9281355594458289157139543, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6187570396305526104759695 9281355594458289157139543)
                ·
                  refine ⟨13922033391687433735709315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9281355594458289157139543 13922033391687433735709315)
                  ·
                    refine ⟨20883050087531150603563973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13922033391687433735709315 20883050087531150603563973)
                    ·
                      refine ⟨3915571891412090738168245, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20883050087531150603563973 3915571891412090738168245)
                      ·
                        rfl

theorem cell23_7625549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 2, 1, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 2, 1, 3, 1, 1, 1, 4].length) (baseStart_7625549 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7625549 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7625549 prefixEnd_7625549 := by exact prefixLift 7625549
  have htrace : WordTrace (prefixWord ++ tailWord_7625549) baseStart_7625549 baseEnd_7625549 := by
    simpa [prefixWord, tailWord_7625549, baseEnd_7625549] using wordTrace_append hprefix tailTrace_7625549
  have hstable : (prefixWord ++ tailWord_7625549).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7625549).length < 2 ^ (prefixWord ++ tailWord_7625549).sum := by decide
  have hdescent : baseEnd_7625549 < baseStart_7625549 := by decide
  rcases family_descends (prefixWord ++ tailWord_7625549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7625575 : List Nat := [1, 1, 5, 1, 2, 2, 1, 2, 3, 3, 2]
def baseStart_7625575 : Nat := 118140960795 + 7625575 * 2 ^ 59
def prefixEnd_7625575 : Nat := 4983230072969 + 3 ^ 40 * 7625575 * 2
def baseEnd_7625575 : Nat := 3915585241909107636443125

theorem tailTrace_7625575 : CollatzResearch.WordTrace tailWord_7625575 prefixEnd_7625575 3915585241909107636443125 := by
  unfold tailWord_7625575
  simp only [CollatzResearch.WordTrace]
  refine ⟨278127569348851594370166179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185418379565901062913444119 278127569348851594370166179)
  ·
    refine ⟨417191354023277391555249269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 278127569348851594370166179 417191354023277391555249269)
    ·
      refine ⟨39111689439682255458304619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 417191354023277391555249269 39111689439682255458304619)
      ·
        refine ⟨58667534159523383187456929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39111689439682255458304619 58667534159523383187456929)
        ·
          refine ⟨44000650619642537390592697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58667534159523383187456929 44000650619642537390592697)
          ·
            refine ⟨33000487964731903042944523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44000650619642537390592697 33000487964731903042944523)
            ·
              refine ⟨49500731947097854564416785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33000487964731903042944523 49500731947097854564416785)
              ·
                refine ⟨37125548960323390923312589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49500731947097854564416785 37125548960323390923312589)
                ·
                  refine ⟨13922080860121271596242221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 37125548960323390923312589 13922080860121271596242221)
                  ·
                    refine ⟨5220780322545476848590833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13922080860121271596242221 5220780322545476848590833)
                    ·
                      refine ⟨3915585241909107636443125, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5220780322545476848590833 3915585241909107636443125)
                      ·
                        rfl

theorem cell23_7625575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 2, 1, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 2, 1, 2, 3, 3, 2].length) (baseStart_7625575 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7625575 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7625575 prefixEnd_7625575 := by exact prefixLift 7625575
  have htrace : WordTrace (prefixWord ++ tailWord_7625575) baseStart_7625575 baseEnd_7625575 := by
    simpa [prefixWord, tailWord_7625575, baseEnd_7625575] using wordTrace_append hprefix tailTrace_7625575
  have hstable : (prefixWord ++ tailWord_7625575).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7625575).length < 2 ^ (prefixWord ++ tailWord_7625575).sum := by decide
  have hdescent : baseEnd_7625575 < baseStart_7625575 := by decide
  rcases family_descends (prefixWord ++ tailWord_7625575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7625582 : List Nat := [4, 1, 2, 3, 2, 1, 2, 1, 1, 3, 3]
def baseStart_7625582 : Nat := 118140960795 + 7625582 * 2 ^ 59
def prefixEnd_7625582 : Nat := 4983230072969 + 3 ^ 40 * 7625582 * 2
def baseEnd_7625582 : Nat := 3915588836273689109055593

theorem tailTrace_7625582 : CollatzResearch.WordTrace tailWord_7625582 prefixEnd_7625582 3915588836273689109055593 := by
  unfold tailWord_7625582
  simp only [CollatzResearch.WordTrace]
  refine ⟨34765978082478279320708875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 185418549773217489710447333 34765978082478279320708875)
  ·
    refine ⟨52148967123717418981063313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34765978082478279320708875 52148967123717418981063313)
    ·
      refine ⟨39111725342788064235797485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52148967123717418981063313 39111725342788064235797485)
      ·
        refine ⟨14666897003545524088424057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39111725342788064235797485 14666897003545524088424057)
        ·
          refine ⟨11000172752659143066318043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14666897003545524088424057 11000172752659143066318043)
          ·
            refine ⟨16500259128988714599477065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11000172752659143066318043 16500259128988714599477065)
            ·
              refine ⟨12375194346741535949607799, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16500259128988714599477065 12375194346741535949607799)
              ·
                refine ⟨18562791520112303924411699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12375194346741535949607799 18562791520112303924411699)
                ·
                  refine ⟨27844187280168455886617549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18562791520112303924411699 27844187280168455886617549)
                  ·
                    refine ⟨10441570230063170957481581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27844187280168455886617549 10441570230063170957481581)
                    ·
                      refine ⟨3915588836273689109055593, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10441570230063170957481581 3915588836273689109055593)
                      ·
                        rfl

theorem cell23_7625582_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 2, 1, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 2, 1, 2, 1, 1, 3, 3].length) (baseStart_7625582 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7625582 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7625582 prefixEnd_7625582 := by exact prefixLift 7625582
  have htrace : WordTrace (prefixWord ++ tailWord_7625582) baseStart_7625582 baseEnd_7625582 := by
    simpa [prefixWord, tailWord_7625582, baseEnd_7625582] using wordTrace_append hprefix tailTrace_7625582
  have hstable : (prefixWord ++ tailWord_7625582).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7625582).length < 2 ^ (prefixWord ++ tailWord_7625582).sum := by decide
  have hdescent : baseEnd_7625582 < baseStart_7625582 := by decide
  rcases family_descends (prefixWord ++ tailWord_7625582) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7625591 : List Nat := [1, 1, 3, 1, 1, 2, 1, 3, 4, 1, 5]
def baseStart_7625591 : Nat := 118140960795 + 7625591 * 2 ^ 59
def prefixEnd_7625591 : Nat := 4983230072969 + 3 ^ 40 * 7625591 * 2
def baseEnd_7625591 : Nat := 3915593457599579573843051

theorem tailTrace_7625591 : CollatzResearch.WordTrace tailWord_7625591 prefixEnd_7625591 3915593457599579573843051 := by
  unfold tailWord_7625591
  simp only [CollatzResearch.WordTrace]
  refine ⟨278128152916793629102748627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185418768611195752735165751 278128152916793629102748627)
  ·
    refine ⟨417192229375190443654122941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 278128152916793629102748627 417192229375190443654122941)
    ·
      refine ⟨156447086015696416370296103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 417192229375190443654122941 156447086015696416370296103)
      ·
        refine ⟨234670629023544624555444155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 156447086015696416370296103 234670629023544624555444155)
        ·
          refine ⟨352005943535316936833166233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 234670629023544624555444155 352005943535316936833166233)
          ·
            refine ⟨264004457651487702624874675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 352005943535316936833166233 264004457651487702624874675)
            ·
              refine ⟨396006686477231553937312013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 264004457651487702624874675 396006686477231553937312013)
              ·
                refine ⟨148502507428961832726492005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 396006686477231553937312013 148502507428961832726492005)
                ·
                  refine ⟨27844220142930343636217251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 148502507428961832726492005 27844220142930343636217251)
                  ·
                    refine ⟨41766330214395515454325877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27844220142930343636217251 41766330214395515454325877)
                    ·
                      refine ⟨3915593457599579573843051, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41766330214395515454325877 3915593457599579573843051)
                      ·
                        rfl

theorem cell23_7625591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 1, 3, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 1, 3, 4, 1, 5].length) (baseStart_7625591 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7625591 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7625591 prefixEnd_7625591 := by exact prefixLift 7625591
  have htrace : WordTrace (prefixWord ++ tailWord_7625591) baseStart_7625591 baseEnd_7625591 := by
    simpa [prefixWord, tailWord_7625591, baseEnd_7625591] using wordTrace_append hprefix tailTrace_7625591
  have hstable : (prefixWord ++ tailWord_7625591).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7625591).length < 2 ^ (prefixWord ++ tailWord_7625591).sum := by decide
  have hdescent : baseEnd_7625591 < baseStart_7625591 := by decide
  rcases family_descends (prefixWord ++ tailWord_7625591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7625605 : List Nat := [1, 3, 1, 1, 3, 3, 2, 2, 1, 4, 2]
def baseStart_7625605 : Nat := 118140960795 + 7625605 * 2 ^ 59
def prefixEnd_7625605 : Nat := 4983230072969 + 3 ^ 40 * 7625605 * 2
def baseEnd_7625605 : Nat := 3915600646328742519067987

theorem tailTrace_7625605 : CollatzResearch.WordTrace tailWord_7625605 prefixEnd_7625605 3915600646328742519067987 := by
  unfold tailWord_7625605
  simp only [CollatzResearch.WordTrace]
  refine ⟨278128663538742909493758269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185419109025828606329172179 278128663538742909493758269)
  ·
    refine ⟨104298248827028591060159351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 278128663538742909493758269 104298248827028591060159351)
    ·
      refine ⟨156447373240542886590239027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104298248827028591060159351 156447373240542886590239027)
      ·
        refine ⟨234671059860814329885358541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 156447373240542886590239027 234671059860814329885358541)
        ·
          refine ⟨88001647447805373707009453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 234671059860814329885358541 88001647447805373707009453)
          ·
            refine ⟨33000617792927015140128545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 88001647447805373707009453 33000617792927015140128545)
            ·
              refine ⟨24750463344695261355096409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33000617792927015140128545 24750463344695261355096409)
              ·
                refine ⟨18562847508521446016322307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24750463344695261355096409 18562847508521446016322307)
                ·
                  refine ⟨27844271262782169024483461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18562847508521446016322307 27844271262782169024483461)
                  ·
                    refine ⟨5220800861771656692090649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 27844271262782169024483461 5220800861771656692090649)
                    ·
                      refine ⟨3915600646328742519067987, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5220800861771656692090649 3915600646328742519067987)
                      ·
                        rfl

theorem cell23_7625605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 3, 2, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 3, 2, 2, 1, 4, 2].length) (baseStart_7625605 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7625605 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7625605 prefixEnd_7625605 := by exact prefixLift 7625605
  have htrace : WordTrace (prefixWord ++ tailWord_7625605) baseStart_7625605 baseEnd_7625605 := by
    simpa [prefixWord, tailWord_7625605, baseEnd_7625605] using wordTrace_append hprefix tailTrace_7625605
  have hstable : (prefixWord ++ tailWord_7625605).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7625605).length < 2 ^ (prefixWord ++ tailWord_7625605).sum := by decide
  have hdescent : baseEnd_7625605 < baseStart_7625605 := by decide
  rcases family_descends (prefixWord ++ tailWord_7625605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7625609 : List Nat := [1, 2, 1, 1, 5, 4, 2, 1, 1, 3, 2]
def baseStart_7625609 : Nat := 118140960795 + 7625609 * 2 ^ 59
def prefixEnd_7625609 : Nat := 4983230072969 + 3 ^ 40 * 7625609 * 2
def baseEnd_7625609 : Nat := 3915602700251360503417969

theorem tailTrace_7625609 : CollatzResearch.WordTrace tailWord_7625609 prefixEnd_7625609 3915602700251360503417969 := by
  unfold tailWord_7625609
  simp only [CollatzResearch.WordTrace]
  refine ⟨278128809430728418176903881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185419206287152278784602587 278128809430728418176903881)
  ·
    refine ⟨208596607073046313632677911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 278128809430728418176903881 208596607073046313632677911)
    ·
      refine ⟨312894910609569470449016867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 208596607073046313632677911 312894910609569470449016867)
      ·
        refine ⟨469342365914354205673525301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 312894910609569470449016867 469342365914354205673525301)
        ·
          refine ⟨44000846804470706781892997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 469342365914354205673525301 44000846804470706781892997)
          ·
            refine ⟨8250158775838257521604937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 44000846804470706781892997 8250158775838257521604937)
            ·
              refine ⟨6187619081878693141203703, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8250158775838257521604937 6187619081878693141203703)
              ·
                refine ⟨9281428622818039711805555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6187619081878693141203703 9281428622818039711805555)
                ·
                  refine ⟨13922142934227059567708333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9281428622818039711805555 13922142934227059567708333)
                  ·
                    refine ⟨5220803600335147337890625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13922142934227059567708333 5220803600335147337890625)
                    ·
                      refine ⟨3915602700251360503417969, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5220803600335147337890625 3915602700251360503417969)
                      ·
                        rfl

theorem cell23_7625609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 4, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 4, 2, 1, 1, 3, 2].length) (baseStart_7625609 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7625609 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7625609 prefixEnd_7625609 := by exact prefixLift 7625609
  have htrace : WordTrace (prefixWord ++ tailWord_7625609) baseStart_7625609 baseEnd_7625609 := by
    simpa [prefixWord, tailWord_7625609, baseEnd_7625609] using wordTrace_append hprefix tailTrace_7625609
  have hstable : (prefixWord ++ tailWord_7625609).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7625609).length < 2 ^ (prefixWord ++ tailWord_7625609).sum := by decide
  have hdescent : baseEnd_7625609 < baseStart_7625609 := by decide
  rcases family_descends (prefixWord ++ tailWord_7625609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7625639 : List Nat := [1, 1, 6, 1, 3, 2, 1, 1, 1, 4, 2]
def baseStart_7625639 : Nat := 118140960795 + 7625639 * 2 ^ 59
def prefixEnd_7625639 : Nat := 4983230072969 + 3 ^ 40 * 7625639 * 2
def baseEnd_7625639 : Nat := 3915618104670995386042831

theorem tailTrace_7625639 : CollatzResearch.WordTrace tailWord_7625639 prefixEnd_7625639 3915618104670995386042831 := by
  unfold tailWord_7625639
  simp only [CollatzResearch.WordTrace]
  refine ⟨278129903620619733300495971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185419935747079822200330647 278129903620619733300495971)
  ·
    refine ⟨417194855430929599950743957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 278129903620619733300495971 417194855430929599950743957)
    ·
      refine ⟨19556008848324824997691123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 417194855430929599950743957 19556008848324824997691123)
      ·
        refine ⟨29334013272487237496536685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19556008848324824997691123 29334013272487237496536685)
        ·
          refine ⟨11000254977182714061201257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29334013272487237496536685 11000254977182714061201257)
          ·
            refine ⟨8250191232887035545900943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11000254977182714061201257 8250191232887035545900943)
            ·
              refine ⟨12375286849330553318851415, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8250191232887035545900943 12375286849330553318851415)
              ·
                refine ⟨18562930273995829978277123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12375286849330553318851415 18562930273995829978277123)
                ·
                  refine ⟨27844395410993744967415685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18562930273995829978277123 27844395410993744967415685)
                  ·
                    refine ⟨5220824139561327181390441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 27844395410993744967415685 5220824139561327181390441)
                    ·
                      refine ⟨3915618104670995386042831, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5220824139561327181390441 3915618104670995386042831)
                      ·
                        rfl

theorem cell23_7625639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 3, 2, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 3, 2, 1, 1, 1, 4, 2].length) (baseStart_7625639 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7625639 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7625639 prefixEnd_7625639 := by exact prefixLift 7625639
  have htrace : WordTrace (prefixWord ++ tailWord_7625639) baseStart_7625639 baseEnd_7625639 := by
    simpa [prefixWord, tailWord_7625639, baseEnd_7625639] using wordTrace_append hprefix tailTrace_7625639
  have hstable : (prefixWord ++ tailWord_7625639).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7625639).length < 2 ^ (prefixWord ++ tailWord_7625639).sum := by decide
  have hdescent : baseEnd_7625639 < baseStart_7625639 := by decide
  rcases family_descends (prefixWord ++ tailWord_7625639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7625641 : List Nat := [1, 2, 1, 1, 1, 1, 5, 1, 3, 7]
def baseStart_7625641 : Nat := 118140960795 + 7625641 * 2 ^ 59
def prefixEnd_7625641 : Nat := 4983230072969 + 3 ^ 40 * 7625641 * 2
def baseEnd_7625641 : Nat := 1305206377210768126072607

theorem tailTrace_7625641 : CollatzResearch.WordTrace tailWord_7625641 prefixEnd_7625641 1305206377210768126072607 := by
  unfold tailWord_7625641
  simp only [CollatzResearch.WordTrace]
  refine ⟨278129976566612487642068777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185419984377741658428045851 278129976566612487642068777)
  ·
    refine ⟨208597482424959365731551583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 278129976566612487642068777 208597482424959365731551583)
    ·
      refine ⟨312896223637439048597327375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 208597482424959365731551583 312896223637439048597327375)
      ·
        refine ⟨469344335456158572895991063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 312896223637439048597327375 469344335456158572895991063)
        ·
          refine ⟨704016503184237859343986595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 469344335456158572895991063 704016503184237859343986595)
          ·
            refine ⟨1056024754776356789015979893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 704016503184237859343986595 1056024754776356789015979893)
            ·
              refine ⟨99002320760283448970248115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1056024754776356789015979893 99002320760283448970248115)
              ·
                refine ⟨148503481140425173455372173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 99002320760283448970248115 148503481140425173455372173)
                ·
                  refine ⟨55688805427659440045764565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 148503481140425173455372173 55688805427659440045764565)
                  ·
                    refine ⟨1305206377210768126072607, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 55688805427659440045764565 1305206377210768126072607)
                    ·
                      rfl

theorem cell23_7625641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 5, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 5, 1, 3, 7].length) (baseStart_7625641 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7625641 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7625641 prefixEnd_7625641 := by exact prefixLift 7625641
  have htrace : WordTrace (prefixWord ++ tailWord_7625641) baseStart_7625641 baseEnd_7625641 := by
    simpa [prefixWord, tailWord_7625641, baseEnd_7625641] using wordTrace_append hprefix tailTrace_7625641
  have hstable : (prefixWord ++ tailWord_7625641).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7625641).length < 2 ^ (prefixWord ++ tailWord_7625641).sum := by decide
  have hdescent : baseEnd_7625641 < baseStart_7625641 := by decide
  rcases family_descends (prefixWord ++ tailWord_7625641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7625651 : List Nat := [1, 1, 1, 2, 3, 1, 2, 1, 3, 1, 7]
def baseStart_7625651 : Nat := 118140960795 + 7625651 * 2 ^ 59
def prefixEnd_7625651 : Nat := 4983230072969 + 3 ^ 40 * 7625651 * 2
def baseEnd_7625651 : Nat := 3915624266438849339092775

theorem tailTrace_7625651 : CollatzResearch.WordTrace tailWord_7625651 prefixEnd_7625651 3915624266438849339092775 := by
  unfold tailWord_7625651
  simp only [CollatzResearch.WordTrace]
  refine ⟨278130341296576259349932807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185420227531050839566621871 278130341296576259349932807)
  ·
    refine ⟨417195511944864389024899211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 278130341296576259349932807 417195511944864389024899211)
    ·
      refine ⟨625793267917296583537348817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 417195511944864389024899211 625793267917296583537348817)
      ·
        refine ⟨469344950937972437653011613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 625793267917296583537348817 469344950937972437653011613)
        ·
          refine ⟨176004356601739664119879355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 469344950937972437653011613 176004356601739664119879355)
          ·
            refine ⟨264006534902609496179819033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 176004356601739664119879355 264006534902609496179819033)
            ·
              refine ⟨198004901176957122134864275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 264006534902609496179819033 198004901176957122134864275)
              ·
                refine ⟨297007351765435683202296413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 198004901176957122134864275 297007351765435683202296413)
                ·
                  refine ⟨111377756912038381200861155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 297007351765435683202296413 111377756912038381200861155)
                  ·
                    refine ⟨167066635368057571801291733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 111377756912038381200861155 167066635368057571801291733)
                    ·
                      refine ⟨3915624266438849339092775, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 167066635368057571801291733 3915624266438849339092775)
                      ·
                        rfl

theorem cell23_7625651_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 2, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 2, 1, 3, 1, 7].length) (baseStart_7625651 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7625651 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7625651 prefixEnd_7625651 := by exact prefixLift 7625651
  have htrace : WordTrace (prefixWord ++ tailWord_7625651) baseStart_7625651 baseEnd_7625651 := by
    simpa [prefixWord, tailWord_7625651, baseEnd_7625651] using wordTrace_append hprefix tailTrace_7625651
  have hstable : (prefixWord ++ tailWord_7625651).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7625651).length < 2 ^ (prefixWord ++ tailWord_7625651).sum := by decide
  have hdescent : baseEnd_7625651 < baseStart_7625651 := by decide
  rcases family_descends (prefixWord ++ tailWord_7625651) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7625658 : List Nat := [3, 1, 1, 1, 2, 1, 4, 3, 2, 5]
def baseStart_7625658 : Nat := 118140960795 + 7625658 * 2 ^ 59
def prefixEnd_7625658 : Nat := 4983230072969 + 3 ^ 40 * 7625658 * 2
def baseEnd_7625658 : Nat := 1305209286934476937235081

theorem tailTrace_7625658 : CollatzResearch.WordTrace tailWord_7625658 prefixEnd_7625658 1305209286934476937235081 := by
  unfold tailWord_7625658
  simp only [CollatzResearch.WordTrace]
  refine ⟨69532649151887724886359407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 185420397738367266363625085 69532649151887724886359407)
  ·
    refine ⟨104298973727831587329539111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69532649151887724886359407 104298973727831587329539111)
    ·
      refine ⟨156448460591747380994308667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104298973727831587329539111 156448460591747380994308667)
      ·
        refine ⟨234672690887621071491463001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 156448460591747380994308667 234672690887621071491463001)
        ·
          refine ⟨176004518165715803618597251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 234672690887621071491463001 176004518165715803618597251)
          ·
            refine ⟨264006777248573705427895877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 176004518165715803618597251 264006777248573705427895877)
            ·
              refine ⟨49501270734107569767730477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 264006777248573705427895877 49501270734107569767730477)
              ·
                refine ⟨18562976525290338662898929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 49501270734107569767730477 18562976525290338662898929)
                ·
                  refine ⟨13922232393967753997174197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18562976525290338662898929 13922232393967753997174197)
                  ·
                    refine ⟨1305209286934476937235081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13922232393967753997174197 1305209286934476937235081)
                    ·
                      rfl

theorem cell23_7625658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 4, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 4, 3, 2, 5].length) (baseStart_7625658 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7625658 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7625658 prefixEnd_7625658 := by exact prefixLift 7625658
  have htrace : WordTrace (prefixWord ++ tailWord_7625658) baseStart_7625658 baseEnd_7625658 := by
    simpa [prefixWord, tailWord_7625658, baseEnd_7625658] using wordTrace_append hprefix tailTrace_7625658
  have hstable : (prefixWord ++ tailWord_7625658).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7625658).length < 2 ^ (prefixWord ++ tailWord_7625658).sum := by decide
  have hdescent : baseEnd_7625658 < baseStart_7625658 := by decide
  rcases family_descends (prefixWord ++ tailWord_7625658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7625685 : List Nat := [1, 3, 2, 3, 3, 1, 1, 1, 1, 2, 5]
def baseStart_7625685 : Nat := 118140960795 + 7625685 * 2 ^ 59
def prefixEnd_7625685 : Nat := 4983230072969 + 3 ^ 40 * 7625685 * 2
def baseEnd_7625685 : Nat := 3915641724781102206067619

theorem tailTrace_7625685 : CollatzResearch.WordTrace tailWord_7625685 prefixEnd_7625685 3915641724781102206067619 := by
  unfold tailWord_7625685
  simp only [CollatzResearch.WordTrace]
  refine ⟨278131581378453083156670509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185421054252302055437780339 278131581378453083156670509)
  ·
    refine ⟨104299343016919906183751441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 278131581378453083156670509 104299343016919906183751441)
    ·
      refine ⟨78224507262689929637813581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 104299343016919906183751441 78224507262689929637813581)
      ·
        refine ⟨29334190223508723614180093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 78224507262689929637813581 29334190223508723614180093)
        ·
          refine ⟨11000321333815771355317535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29334190223508723614180093 11000321333815771355317535)
          ·
            refine ⟨16500482000723657032976303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11000321333815771355317535 16500482000723657032976303)
            ·
              refine ⟨24750723001085485549464455, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16500482000723657032976303 24750723001085485549464455)
              ·
                refine ⟨37126084501628228324196683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24750723001085485549464455 37126084501628228324196683)
                ·
                  refine ⟨55689126752442342486295025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37126084501628228324196683 55689126752442342486295025)
                  ·
                    refine ⟨41766845064331756864721269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 55689126752442342486295025 41766845064331756864721269)
                    ·
                      refine ⟨3915641724781102206067619, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41766845064331756864721269 3915641724781102206067619)
                      ·
                        rfl

theorem cell23_7625685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 3, 1, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 3, 1, 1, 1, 1, 2, 5].length) (baseStart_7625685 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7625685 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7625685 prefixEnd_7625685 := by exact prefixLift 7625685
  have htrace : WordTrace (prefixWord ++ tailWord_7625685) baseStart_7625685 baseEnd_7625685 := by
    simpa [prefixWord, tailWord_7625685, baseEnd_7625685] using wordTrace_append hprefix tailTrace_7625685
  have hstable : (prefixWord ++ tailWord_7625685).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7625685).length < 2 ^ (prefixWord ++ tailWord_7625685).sum := by decide
  have hdescent : baseEnd_7625685 < baseStart_7625685 := by decide
  rcases family_descends (prefixWord ++ tailWord_7625685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7625728 : List Nat := [2, 1, 1, 2, 1, 1, 1, 2, 4, 5, 3]
def baseStart_7625728 : Nat := 118140960795 + 7625728 * 2 ^ 59
def prefixEnd_7625728 : Nat := 4983230072969 + 3 ^ 40 * 7625728 * 2
def baseEnd_7625728 : Nat := 3915663804449245537829921

theorem tailTrace_7625728 : CollatzResearch.WordTrace tailWord_7625728 prefixEnd_7625728 3915663804449245537829921 := by
  unfold tailWord_7625728
  simp only [CollatzResearch.WordTrace]
  refine ⟨139066574858648650750242919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 185422099811531534333657225 139066574858648650750242919)
  ·
    refine ⟨208599862287972976125364379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139066574858648650750242919 208599862287972976125364379)
    ·
      refine ⟨312899793431959464188046569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 208599862287972976125364379 312899793431959464188046569)
      ·
        refine ⟨234674845073969598141034927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 312899793431959464188046569 234674845073969598141034927)
        ·
          refine ⟨352012267610954397211552391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 234674845073969598141034927 352012267610954397211552391)
          ·
            refine ⟨528018401416431595817328587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 352012267610954397211552391 528018401416431595817328587)
            ·
              refine ⟨792027602124647393725992881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 528018401416431595817328587 792027602124647393725992881)
              ·
                refine ⟨594020701593485545294494661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 792027602124647393725992881 594020701593485545294494661)
                ·
                  refine ⟨111378881548778539742717749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 594020701593485545294494661 111378881548778539742717749)
                  ·
                    refine ⟨10441770145197988100879789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 111378881548778539742717749 10441770145197988100879789)
                    ·
                      refine ⟨3915663804449245537829921, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10441770145197988100879789 3915663804449245537829921)
                      ·
                        rfl

theorem cell23_7625728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 2, 4, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 2, 4, 5, 3].length) (baseStart_7625728 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7625728 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7625728 prefixEnd_7625728 := by exact prefixLift 7625728
  have htrace : WordTrace (prefixWord ++ tailWord_7625728) baseStart_7625728 baseEnd_7625728 := by
    simpa [prefixWord, tailWord_7625728, baseEnd_7625728] using wordTrace_append hprefix tailTrace_7625728
  have hstable : (prefixWord ++ tailWord_7625728).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7625728).length < 2 ^ (prefixWord ++ tailWord_7625728).sum := by decide
  have hdescent : baseEnd_7625728 < baseStart_7625728 := by decide
  rcases family_descends (prefixWord ++ tailWord_7625728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7625735 : List Nat := [1, 1, 4, 3, 1, 1, 4, 2, 6]
def baseStart_7625735 : Nat := 118140960795 + 7625735 * 2 ^ 59
def prefixEnd_7625735 : Nat := 4983230072969 + 3 ^ 40 * 7625735 * 2
def baseEnd_7625735 : Nat := 435074155423758556715821

theorem tailTrace_7625735 : CollatzResearch.WordTrace tailWord_7625735 prefixEnd_7625735 435074155423758556715821 := by
  unfold tailWord_7625735
  simp only [CollatzResearch.WordTrace]
  refine ⟨278133405028271941695990659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185422270018847961130660439 278133405028271941695990659)
  ·
    refine ⟨417200107542407912543985989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 278133405028271941695990659 417200107542407912543985989)
    ·
      refine ⟨78225020164201483601997373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 417200107542407912543985989 78225020164201483601997373)
      ·
        refine ⟨29334382561575556350749015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 78225020164201483601997373 29334382561575556350749015)
        ·
          refine ⟨44001573842363334526123523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29334382561575556350749015 44001573842363334526123523)
          ·
            refine ⟨66002360763545001789185285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44001573842363334526123523 66002360763545001789185285)
            ·
              refine ⟨12375442643164687835472241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 66002360763545001789185285 12375442643164687835472241)
              ·
                refine ⟨9281581982373515876604181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12375442643164687835472241 9281581982373515876604181)
                ·
                  refine ⟨435074155423758556715821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9281581982373515876604181 435074155423758556715821)
                  ·
                    rfl

theorem cell23_7625735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 4, 2, 6].length) (baseStart_7625735 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7625735 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7625735 prefixEnd_7625735 := by exact prefixLift 7625735
  have htrace : WordTrace (prefixWord ++ tailWord_7625735) baseStart_7625735 baseEnd_7625735 := by
    simpa [prefixWord, tailWord_7625735, baseEnd_7625735] using wordTrace_append hprefix tailTrace_7625735
  have hstable : (prefixWord ++ tailWord_7625735).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7625735).length < 2 ^ (prefixWord ++ tailWord_7625735).sum := by decide
  have hdescent : baseEnd_7625735 < baseStart_7625735 := by decide
  rcases family_descends (prefixWord ++ tailWord_7625735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7625739 : List Nat := [1, 1, 1, 1, 6, 2, 4, 2, 1, 4]
def baseStart_7625739 : Nat := 118140960795 + 7625739 * 2 ^ 59
def prefixEnd_7625739 : Nat := 4983230072969 + 3 ^ 40 * 7625739 * 2
def baseEnd_7625739 : Nat := 1305223150912148331597457

theorem tailTrace_7625739 : CollatzResearch.WordTrace tailWord_7625739 prefixEnd_7625739 1305223150912148331597457 := by
  unfold tailWord_7625739
  simp only [CollatzResearch.WordTrace]
  refine ⟨278133550920257450379136271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185422367280171633586090847 278133550920257450379136271)
  ·
    refine ⟨417200326380386175568704407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 278133550920257450379136271 417200326380386175568704407)
    ·
      refine ⟨625800489570579263353056611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 417200326380386175568704407 625800489570579263353056611)
      ·
        refine ⟨938700734355868895029584917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 625800489570579263353056611 938700734355868895029584917)
        ·
          refine ⟨44001596922931354454511793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 938700734355868895029584917 44001596922931354454511793)
          ·
            refine ⟨33001197692198515840883845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44001596922931354454511793 33001197692198515840883845)
            ·
              refine ⟨6187724567287221720165721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 33001197692198515840883845 6187724567287221720165721)
              ·
                refine ⟨4640793425465416290124291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6187724567287221720165721 4640793425465416290124291)
                ·
                  refine ⟨6961190138198124435186437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4640793425465416290124291 6961190138198124435186437)
                  ·
                    refine ⟨1305223150912148331597457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6961190138198124435186437 1305223150912148331597457)
                    ·
                      rfl

theorem cell23_7625739_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 2, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 2, 4, 2, 1, 4].length) (baseStart_7625739 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7625739 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7625739 prefixEnd_7625739 := by exact prefixLift 7625739
  have htrace : WordTrace (prefixWord ++ tailWord_7625739) baseStart_7625739 baseEnd_7625739 := by
    simpa [prefixWord, tailWord_7625739, baseEnd_7625739] using wordTrace_append hprefix tailTrace_7625739
  have hstable : (prefixWord ++ tailWord_7625739).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7625739).length < 2 ^ (prefixWord ++ tailWord_7625739).sum := by decide
  have hdescent : baseEnd_7625739 < baseStart_7625739 := by decide
  rcases family_descends (prefixWord ++ tailWord_7625739) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7625745 : List Nat := [1, 2, 2, 1, 1, 2, 1, 2, 7, 1, 3]
def baseStart_7625745 : Nat := 118140960795 + 7625745 * 2 ^ 59
def prefixEnd_7625745 : Nat := 4983230072969 + 3 ^ 40 * 7625745 * 2
def baseEnd_7625745 : Nat := 3915672533620371971317343

theorem tailTrace_7625745 : CollatzResearch.WordTrace tailWord_7625745 prefixEnd_7625745 3915672533620371971317343 := by
  unfold tailWord_7625745
  simp only [CollatzResearch.WordTrace]
  refine ⟨278133769758235713403854689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185422513172157142269236459 278133769758235713403854689)
  ·
    refine ⟨208600327318676785052891017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 278133769758235713403854689 208600327318676785052891017)
    ·
      refine ⟨156450245489007588789668263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 208600327318676785052891017 156450245489007588789668263)
      ·
        refine ⟨234675368233511383184502395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 156450245489007588789668263 234675368233511383184502395)
        ·
          refine ⟨352013052350267074776753593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 234675368233511383184502395 352013052350267074776753593)
          ·
            refine ⟨264009789262700306082565195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 352013052350267074776753593 264009789262700306082565195)
            ·
              refine ⟨396014683894050459123847793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 264009789262700306082565195 396014683894050459123847793)
              ·
                refine ⟨297011012920537844342885845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 396014683894050459123847793 297011012920537844342885845)
                ·
                  refine ⟨6961195615325105726786387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 297011012920537844342885845 6961195615325105726786387)
                  ·
                    refine ⟨10441793422987658590179581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6961195615325105726786387 10441793422987658590179581)
                    ·
                      refine ⟨3915672533620371971317343, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10441793422987658590179581 3915672533620371971317343)
                      ·
                        rfl

theorem cell23_7625745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 1, 2, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 1, 2, 7, 1, 3].length) (baseStart_7625745 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7625745 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7625745 prefixEnd_7625745 := by exact prefixLift 7625745
  have htrace : WordTrace (prefixWord ++ tailWord_7625745) baseStart_7625745 baseEnd_7625745 := by
    simpa [prefixWord, tailWord_7625745, baseEnd_7625745] using wordTrace_append hprefix tailTrace_7625745
  have hstable : (prefixWord ++ tailWord_7625745).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7625745).length < 2 ^ (prefixWord ++ tailWord_7625745).sum := by decide
  have hdescent : baseEnd_7625745 < baseStart_7625745 := by decide
  rcases family_descends (prefixWord ++ tailWord_7625745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7625762 : List Nat := [3, 3, 1, 1, 1, 3, 1, 1, 5, 1, 3]
def baseStart_7625762 : Nat := 118140960795 + 7625762 * 2 ^ 59
def prefixEnd_7625762 : Nat := 4983230072969 + 3 ^ 40 * 7625762 * 2
def baseEnd_7625762 : Nat := 3915681262791498404804765

theorem tailTrace_7625762 : CollatzResearch.WordTrace tailWord_7625762 prefixEnd_7625762 3915681262791498404804765 := by
  unfold tailWord_7625762
  simp only [CollatzResearch.WordTrace]
  refine ⟨69533597449793531326805885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 185422926532782750204815693 69533597449793531326805885)
  ·
    refine ⟨26075099043672574247552207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 69533597449793531326805885 26075099043672574247552207)
    ·
      refine ⟨39112648565508861371328311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26075099043672574247552207 39112648565508861371328311)
      ·
        refine ⟨58668972848263292056992467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39112648565508861371328311 58668972848263292056992467)
        ·
          refine ⟨88003459272394938085488701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58668972848263292056992467 88003459272394938085488701)
          ·
            refine ⟨33001297227148101782058263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 88003459272394938085488701 33001297227148101782058263)
            ·
              refine ⟨49501945840722152673087395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33001297227148101782058263 49501945840722152673087395)
              ·
                refine ⟨74252918761083229009631093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49501945840722152673087395 74252918761083229009631093)
                ·
                  refine ⟨6961211133851552719652915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 74252918761083229009631093 6961211133851552719652915)
                  ·
                    refine ⟨10441816700777329079479373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6961211133851552719652915 10441816700777329079479373)
                    ·
                      refine ⟨3915681262791498404804765, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10441816700777329079479373 3915681262791498404804765)
                      ·
                        rfl

theorem cell23_7625762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 3, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 3, 1, 1, 5, 1, 3].length) (baseStart_7625762 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7625762 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7625762 prefixEnd_7625762 := by exact prefixLift 7625762
  have htrace : WordTrace (prefixWord ++ tailWord_7625762) baseStart_7625762 baseEnd_7625762 := by
    simpa [prefixWord, tailWord_7625762, baseEnd_7625762] using wordTrace_append hprefix tailTrace_7625762
  have hstable : (prefixWord ++ tailWord_7625762).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7625762).length < 2 ^ (prefixWord ++ tailWord_7625762).sum := by decide
  have hdescent : baseEnd_7625762 < baseStart_7625762 := by decide
  rcases family_descends (prefixWord ++ tailWord_7625762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7625765 : List Nat := [1, 3, 1, 2, 2, 2, 2, 4, 1, 5]
def baseStart_7625765 : Nat := 118140960795 + 7625765 * 2 ^ 59
def prefixEnd_7625765 : Nat := 4983230072969 + 3 ^ 40 * 7625765 * 2
def baseEnd_7625765 : Nat := 1305227601077820631022417

theorem tailTrace_7625765 : CollatzResearch.WordTrace tailWord_7625765 prefixEnd_7625765 1305227601077820631022417 := by
  unfold tailWord_7625765
  simp only [CollatzResearch.WordTrace]
  refine ⟨278134499218163256819582749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185422999478775504546388499 278134499218163256819582749)
  ·
    refine ⟨104300437206811221307343531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 278134499218163256819582749 104300437206811221307343531)
    ·
      refine ⟨156450655810216831961015297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104300437206811221307343531 156450655810216831961015297)
      ·
        refine ⟨117337991857662623970761473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 156450655810216831961015297 117337991857662623970761473)
        ·
          refine ⟨88003493893246967978071105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 117337991857662623970761473 88003493893246967978071105)
          ·
            refine ⟨66002620419935225983553329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 88003493893246967978071105 66002620419935225983553329)
            ·
              refine ⟨49501965314951419487664997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 66002620419935225983553329 49501965314951419487664997)
              ·
                refine ⟨9281618496553391153937187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 49501965314951419487664997 9281618496553391153937187)
                ·
                  refine ⟨13922427744830086730905781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9281618496553391153937187 13922427744830086730905781)
                  ·
                    refine ⟨1305227601077820631022417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13922427744830086730905781 1305227601077820631022417)
                    ·
                      rfl

theorem cell23_7625765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 2, 4, 1, 5].length) (baseStart_7625765 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7625765 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7625765 prefixEnd_7625765 := by exact prefixLift 7625765
  have htrace : WordTrace (prefixWord ++ tailWord_7625765) baseStart_7625765 baseEnd_7625765 := by
    simpa [prefixWord, tailWord_7625765, baseEnd_7625765] using wordTrace_append hprefix tailTrace_7625765
  have hstable : (prefixWord ++ tailWord_7625765).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7625765).length < 2 ^ (prefixWord ++ tailWord_7625765).sum := by decide
  have hdescent : baseEnd_7625765 < baseStart_7625765 := by decide
  rcases family_descends (prefixWord ++ tailWord_7625765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7625795 : List Nat := [1, 1, 1, 3, 1, 2, 5, 1, 4, 4]
def baseStart_7625795 : Nat := 118140960795 + 7625795 * 2 ^ 59
def prefixEnd_7625795 : Nat := 4983230072969 + 3 ^ 40 * 7625795 * 2
def baseEnd_7625795 : Nat := 1305232735884365591897371

theorem tailTrace_7625795 : CollatzResearch.WordTrace tailWord_7625795 prefixEnd_7625795 1305232735884365591897371 := by
  unfold tailWord_7625795
  simp only [CollatzResearch.WordTrace]
  refine ⟨278135593408054571943174839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185423728938703047962116559 278135593408054571943174839)
  ·
    refine ⟨417203390112081857914762259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 278135593408054571943174839 417203390112081857914762259)
    ·
      refine ⟨625805085168122786872143389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 417203390112081857914762259 625805085168122786872143389)
      ·
        refine ⟨234676906938046045077053771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 625805085168122786872143389 234676906938046045077053771)
        ·
          refine ⟨352015360407069067615580657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 234676906938046045077053771 352015360407069067615580657)
          ·
            refine ⟨264011520305301800711685493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 352015360407069067615580657 264011520305301800711685493)
            ·
              refine ⟨24751080028622043816720515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 264011520305301800711685493 24751080028622043816720515)
              ·
                refine ⟨37126620042933065725080773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24751080028622043816720515 37126620042933065725080773)
                ·
                  refine ⟨6961241258049949823452645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 37126620042933065725080773 6961241258049949823452645)
                  ·
                    refine ⟨1305232735884365591897371, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6961241258049949823452645 1305232735884365591897371)
                    ·
                      rfl

theorem cell23_7625795_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 5, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 5, 1, 4, 4].length) (baseStart_7625795 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7625795 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7625795 prefixEnd_7625795 := by exact prefixLift 7625795
  have htrace : WordTrace (prefixWord ++ tailWord_7625795) baseStart_7625795 baseEnd_7625795 := by
    simpa [prefixWord, tailWord_7625795, baseEnd_7625795] using wordTrace_append hprefix tailTrace_7625795
  have hstable : (prefixWord ++ tailWord_7625795).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7625795).length < 2 ^ (prefixWord ++ tailWord_7625795).sum := by decide
  have hdescent : baseEnd_7625795 < baseStart_7625795 := by decide
  rcases family_descends (prefixWord ++ tailWord_7625795) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7625812 : List Nat := [2, 4, 1, 1, 1, 1, 2, 5, 2, 4]
def baseStart_7625812 : Nat := 118140960795 + 7625812 * 2 ^ 59
def prefixEnd_7625812 : Nat := 4983230072969 + 3 ^ 40 * 7625812 * 2
def baseEnd_7625812 : Nat := 1305235645608074403059845

theorem tailTrace_7625812 : CollatzResearch.WordTrace tailWord_7625812 prefixEnd_7625812 1305235645608074403059845 := by
  unfold tailWord_7625812
  simp only [CollatzResearch.WordTrace]
  refine ⟨139068106724496491923271845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 185424142299328655897695793 139068106724496491923271845)
  ·
    refine ⟨26075270010843092235613471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 139068106724496491923271845 26075270010843092235613471)
    ·
      refine ⟨39112905016264638353420207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26075270010843092235613471 39112905016264638353420207)
      ·
        refine ⟨58669357524396957530130311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39112905016264638353420207 58669357524396957530130311)
        ·
          refine ⟨88004036286595436295195467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58669357524396957530130311 88004036286595436295195467)
          ·
            refine ⟨132006054429893154442793201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88004036286595436295195467 132006054429893154442793201)
            ·
              refine ⟨99004540822419865832094901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 132006054429893154442793201 99004540822419865832094901)
              ·
                refine ⟨9281675702101862421758897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 99004540822419865832094901 9281675702101862421758897)
                ·
                  refine ⟨6961256776576396816319173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9281675702101862421758897 6961256776576396816319173)
                  ·
                    refine ⟨1305235645608074403059845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6961256776576396816319173 1305235645608074403059845)
                    ·
                      rfl

theorem cell23_7625812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 2, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 2, 5, 2, 4].length) (baseStart_7625812 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7625812 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7625812 prefixEnd_7625812 := by exact prefixLift 7625812
  have htrace : WordTrace (prefixWord ++ tailWord_7625812) baseStart_7625812 baseEnd_7625812 := by
    simpa [prefixWord, tailWord_7625812, baseEnd_7625812] using wordTrace_append hprefix tailTrace_7625812
  have hstable : (prefixWord ++ tailWord_7625812).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7625812).length < 2 ^ (prefixWord ++ tailWord_7625812).sum := by decide
  have hdescent : baseEnd_7625812 < baseStart_7625812 := by decide
  rcases family_descends (prefixWord ++ tailWord_7625812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7625825 : List Nat := [1, 2, 3, 1, 1, 2, 6, 7]
def baseStart_7625825 : Nat := 118140960795 + 7625825 * 2 ^ 59
def prefixEnd_7625825 : Nat := 4983230072969 + 3 ^ 40 * 7625825 * 2
def baseEnd_7625825 : Nat := 145026430076767839196925

theorem tailTrace_7625825 : CollatzResearch.WordTrace tailWord_7625825 prefixEnd_7625825 145026430076767839196925 := by
  unfold tailWord_7625825
  simp only [CollatzResearch.WordTrace]
  refine ⟨278136687597945887066766929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185424458398630591377844619 278136687597945887066766929)
  ·
    refine ⟨208602515698459415300075197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 278136687597945887066766929 208602515698459415300075197)
    ·
      refine ⟨78225943386922280737528199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 208602515698459415300075197 78225943386922280737528199)
      ·
        refine ⟨117338915080383421106292299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78225943386922280737528199 117338915080383421106292299)
        ·
          refine ⟨176008372620575131659438449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 117338915080383421106292299 176008372620575131659438449)
          ·
            refine ⟨132006279465431348744578837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 176008372620575131659438449 132006279465431348744578837)
            ·
              refine ⟨6187794349942094472402133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 132006279465431348744578837 6187794349942094472402133)
              ·
                refine ⟨145026430076767839196925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6187794349942094472402133 145026430076767839196925)
                ·
                  rfl

theorem cell23_7625825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 6, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 6, 7].length) (baseStart_7625825 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7625825 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7625825 prefixEnd_7625825 := by exact prefixLift 7625825
  have htrace : WordTrace (prefixWord ++ tailWord_7625825) baseStart_7625825 baseEnd_7625825 := by
    simpa [prefixWord, tailWord_7625825, baseEnd_7625825] using wordTrace_append hprefix tailTrace_7625825
  have hstable : (prefixWord ++ tailWord_7625825).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7625825).length < 2 ^ (prefixWord ++ tailWord_7625825).sum := by decide
  have hdescent : baseEnd_7625825 < baseStart_7625825 := by decide
  rcases family_descends (prefixWord ++ tailWord_7625825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7625852 : List Nat := [2, 2, 2, 1, 1, 3, 1, 3, 4, 1, 3]
def baseStart_7625852 : Nat := 118140960795 + 7625852 * 2 ^ 59
def prefixEnd_7625852 : Nat := 4983230072969 + 3 ^ 40 * 7625852 * 2
def baseEnd_7625852 : Nat := 3915727476050403052679351

theorem tailTrace_7625852 : CollatzResearch.WordTrace tailWord_7625852 prefixEnd_7625852 3915727476050403052679351 := by
  unfold tailWord_7625852
  simp only [CollatzResearch.WordTrace]
  refine ⟨139068836184424035338999905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 185425114912565380451999873 139068836184424035338999905)
  ·
    refine ⟨104301627138318026504249929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 139068836184424035338999905 104301627138318026504249929)
    ·
      refine ⟨78226220353738519878187447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 104301627138318026504249929 78226220353738519878187447)
      ·
        refine ⟨117339330530607779817281171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78226220353738519878187447 117339330530607779817281171)
        ·
          refine ⟨176008995795911669725921757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 117339330530607779817281171 176008995795911669725921757)
          ·
            refine ⟨66003373423466876147220659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 176008995795911669725921757 66003373423466876147220659)
            ·
              refine ⟨99005060135200314220830989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66003373423466876147220659 99005060135200314220830989)
              ·
                refine ⟨37126897550700117832811621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 99005060135200314220830989 37126897550700117832811621)
                ·
                  refine ⟨6961293290756272093652179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 37126897550700117832811621 6961293290756272093652179)
                  ·
                    refine ⟨10441939936134408140478269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6961293290756272093652179 10441939936134408140478269)
                    ·
                      refine ⟨3915727476050403052679351, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10441939936134408140478269 3915727476050403052679351)
                      ·
                        rfl

theorem cell23_7625852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 1, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 1, 3, 4, 1, 3].length) (baseStart_7625852 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7625852 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7625852 prefixEnd_7625852 := by exact prefixLift 7625852
  have htrace : WordTrace (prefixWord ++ tailWord_7625852) baseStart_7625852 baseEnd_7625852 := by
    simpa [prefixWord, tailWord_7625852, baseEnd_7625852] using wordTrace_append hprefix tailTrace_7625852
  have hstable : (prefixWord ++ tailWord_7625852).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7625852).length < 2 ^ (prefixWord ++ tailWord_7625852).sum := by decide
  have hdescent : baseEnd_7625852 < baseStart_7625852 := by decide
  rcases family_descends (prefixWord ++ tailWord_7625852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7625853 : List Nat := [1, 4, 1, 1, 3, 1, 5, 2, 1, 2, 2]
def baseStart_7625853 : Nat := 118140960795 + 7625853 * 2 ^ 59
def prefixEnd_7625853 : Nat := 4983230072969 + 3 ^ 40 * 7625853 * 2
def baseEnd_7625853 : Nat := 3915727989531057548766847

theorem tailTrace_7625853 : CollatzResearch.WordTrace tailWord_7625853 prefixEnd_7625853 3915727989531057548766847 := by
  unfold tailWord_7625853
  simp only [CollatzResearch.WordTrace]
  refine ⟨278137708841844447848786213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185425139227896298565857475 278137708841844447848786213)
  ·
    refine ⟨52150820407845833971647415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 278137708841844447848786213 52150820407845833971647415)
    ·
      refine ⟨78226230611768750957471123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52150820407845833971647415 78226230611768750957471123)
      ·
        refine ⟨117339345917653126436206685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78226230611768750957471123 117339345917653126436206685)
        ·
          refine ⟨44002254719119922413577507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 117339345917653126436206685 44002254719119922413577507)
          ·
            refine ⟨66003382078679883620366261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44002254719119922413577507 66003382078679883620366261)
            ·
              refine ⟨6187817069876239089409337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 66003382078679883620366261 6187817069876239089409337)
              ·
                refine ⟨4640862802407179317057003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6187817069876239089409337 4640862802407179317057003)
                ·
                  refine ⟨6961294203610768975585505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4640862802407179317057003 6961294203610768975585505)
                  ·
                    refine ⟨5220970652708076731689129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6961294203610768975585505 5220970652708076731689129)
                    ·
                      refine ⟨3915727989531057548766847, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5220970652708076731689129 3915727989531057548766847)
                      ·
                        rfl

theorem cell23_7625853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 5, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 5, 2, 1, 2, 2].length) (baseStart_7625853 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7625853 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7625853 prefixEnd_7625853 := by exact prefixLift 7625853
  have htrace : WordTrace (prefixWord ++ tailWord_7625853) baseStart_7625853 baseEnd_7625853 := by
    simpa [prefixWord, tailWord_7625853, baseEnd_7625853] using wordTrace_append hprefix tailTrace_7625853
  have hstable : (prefixWord ++ tailWord_7625853).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7625853).length < 2 ^ (prefixWord ++ tailWord_7625853).sum := by decide
  have hdescent : baseEnd_7625853 < baseStart_7625853 := by decide
  rcases family_descends (prefixWord ++ tailWord_7625853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7625879 : List Nat := [1, 1, 3, 3, 3, 2, 1, 1, 3, 3, 2]
def baseStart_7625879 : Nat := 118140960795 + 7625879 * 2 ^ 59
def prefixEnd_7625879 : Nat := 4983230072969 + 3 ^ 40 * 7625879 * 2
def baseEnd_7625879 : Nat := 3915741340028074447041727

theorem tailTrace_7625879 : CollatzResearch.WordTrace tailWord_7625879 prefixEnd_7625879 3915741340028074447041727 := by
  unfold tailWord_7625879
  simp only [CollatzResearch.WordTrace]
  refine ⟨278138657139750254289232691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185425771426500169526155127 278138657139750254289232691)
  ·
    refine ⟨417207985709625381433849037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 278138657139750254289232691 417207985709625381433849037)
    ·
      refine ⟨156452994641109518037693389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 417207985709625381433849037 156452994641109518037693389)
      ·
        refine ⟨58669872990416069264135021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 156452994641109518037693389 58669872990416069264135021)
        ·
          refine ⟨22001202371406025974050633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 58669872990416069264135021 22001202371406025974050633)
          ·
            refine ⟨16500901778554519480537975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22001202371406025974050633 16500901778554519480537975)
            ·
              refine ⟨24751352667831779220806963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16500901778554519480537975 24751352667831779220806963)
              ·
                refine ⟨37127029001747668831210445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24751352667831779220806963 37127029001747668831210445)
                ·
                  refine ⟨13922635875655375811703917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 37127029001747668831210445 13922635875655375811703917)
                  ·
                    refine ⟨5220988453370765929388969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13922635875655375811703917 5220988453370765929388969)
                    ·
                      refine ⟨3915741340028074447041727, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5220988453370765929388969 3915741340028074447041727)
                      ·
                        rfl

theorem cell23_7625879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 2, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 2, 1, 1, 3, 3, 2].length) (baseStart_7625879 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7625879 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7625879 prefixEnd_7625879 := by exact prefixLift 7625879
  have htrace : WordTrace (prefixWord ++ tailWord_7625879) baseStart_7625879 baseEnd_7625879 := by
    simpa [prefixWord, tailWord_7625879, baseEnd_7625879] using wordTrace_append hprefix tailTrace_7625879
  have hstable : (prefixWord ++ tailWord_7625879).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7625879).length < 2 ^ (prefixWord ++ tailWord_7625879).sum := by decide
  have hdescent : baseEnd_7625879 < baseStart_7625879 := by decide
  rcases family_descends (prefixWord ++ tailWord_7625879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7626019 : List Nat := [1, 1, 1, 4, 2, 4, 1, 2, 2, 2, 3]
def baseStart_7626019 : Nat := 118140960795 + 7626019 * 2 ^ 59
def prefixEnd_7626019 : Nat := 4983230072969 + 3 ^ 40 * 7626019 * 2
def baseEnd_7626019 : Nat := 3915813227319703899291083

theorem tailTrace_7626019 : CollatzResearch.WordTrace tailWord_7626019 prefixEnd_7626019 3915813227319703899291083 := by
  unfold tailWord_7626019
  simp only [CollatzResearch.WordTrace]
  refine ⟨278143763359243058199329111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185429175572828705466219407 278143763359243058199329111)
  ·
    refine ⟨417215645038864587298993667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 278143763359243058199329111 417215645038864587298993667)
    ·
      refine ⟨625823467558296880948490501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 417215645038864587298993667 625823467558296880948490501)
      ·
        refine ⟨117341900167180665177841969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 625823467558296880948490501 117341900167180665177841969)
        ·
          refine ⟨88006425125385498883381477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 117341900167180665177841969 88006425125385498883381477)
          ·
            refine ⟨16501204711009781040634027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 88006425125385498883381477 16501204711009781040634027)
            ·
              refine ⟨24751807066514671560951041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16501204711009781040634027 24751807066514671560951041)
              ·
                refine ⟨18563855299886003670713281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24751807066514671560951041 18563855299886003670713281)
                ·
                  refine ⟨13922891474914502753034961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18563855299886003670713281 13922891474914502753034961)
                  ·
                    refine ⟨10442168606185877064776221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13922891474914502753034961 10442168606185877064776221)
                    ·
                      refine ⟨3915813227319703899291083, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10442168606185877064776221 3915813227319703899291083)
                      ·
                        rfl

theorem cell23_7626019_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 4, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 4, 1, 2, 2, 2, 3].length) (baseStart_7626019 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7626019 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7626019 prefixEnd_7626019 := by exact prefixLift 7626019
  have htrace : WordTrace (prefixWord ++ tailWord_7626019) baseStart_7626019 baseEnd_7626019 := by
    simpa [prefixWord, tailWord_7626019, baseEnd_7626019] using wordTrace_append hprefix tailTrace_7626019
  have hstable : (prefixWord ++ tailWord_7626019).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7626019).length < 2 ^ (prefixWord ++ tailWord_7626019).sum := by decide
  have hdescent : baseEnd_7626019 < baseStart_7626019 := by decide
  rcases family_descends (prefixWord ++ tailWord_7626019) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7626025 : List Nat := [1, 2, 1, 1, 1, 1, 1, 2, 5, 2, 6]
def baseStart_7626025 : Nat := 118140960795 + 7626025 * 2 ^ 59
def prefixEnd_7626025 : Nat := 4983230072969 + 3 ^ 40 * 7626025 * 2
def baseEnd_7626025 : Nat := 3915816308203630875816055

theorem tailTrace_7626025 : CollatzResearch.WordTrace tailWord_7626025 prefixEnd_7626025 3915816308203630875816055 := by
  unfold tailWord_7626025
  simp only [CollatzResearch.WordTrace]
  refine ⟨278143982197221321224047529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185429321464814214149365019 278143982197221321224047529)
  ·
    refine ⟨208607986647915990918035647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 278143982197221321224047529 208607986647915990918035647)
    ·
      refine ⟨312911979971873986377053471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 208607986647915990918035647 312911979971873986377053471)
      ·
        refine ⟨469367969957810979565580207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 312911979971873986377053471 469367969957810979565580207)
        ·
          refine ⟨704051954936716469348370311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 469367969957810979565580207 704051954936716469348370311)
          ·
            refine ⟨1056077932405074704022555467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 704051954936716469348370311 1056077932405074704022555467)
            ·
              refine ⟨1584116898607612056033833201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1056077932405074704022555467 1584116898607612056033833201)
              ·
                refine ⟨1188087673955709042025374901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1584116898607612056033833201 1188087673955709042025374901)
                ·
                  refine ⟨111383219433347722689878897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1188087673955709042025374901 111383219433347722689878897)
                  ·
                    refine ⟨83537414575010792017409173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 111383219433347722689878897 83537414575010792017409173)
                    ·
                      refine ⟨3915816308203630875816055, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 83537414575010792017409173 3915816308203630875816055)
                      ·
                        rfl

theorem cell23_7626025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 2, 5, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 2, 5, 2, 6].length) (baseStart_7626025 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7626025 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7626025 prefixEnd_7626025 := by exact prefixLift 7626025
  have htrace : WordTrace (prefixWord ++ tailWord_7626025) baseStart_7626025 baseEnd_7626025 := by
    simpa [prefixWord, tailWord_7626025, baseEnd_7626025] using wordTrace_append hprefix tailTrace_7626025
  have hstable : (prefixWord ++ tailWord_7626025).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7626025).length < 2 ^ (prefixWord ++ tailWord_7626025).sum := by decide
  have hdescent : baseEnd_7626025 < baseStart_7626025 := by decide
  rcases family_descends (prefixWord ++ tailWord_7626025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7626026 : List Nat := [3, 1, 4, 2, 1, 1, 3, 1, 3, 4]
def baseStart_7626026 : Nat := 118140960795 + 7626026 * 2 ^ 59
def prefixEnd_7626026 : Nat := 4983230072969 + 3 ^ 40 * 7626026 * 2
def baseEnd_7626026 : Nat := 1305272273894761790634517

theorem tailTrace_7626026 : CollatzResearch.WordTrace tailWord_7626026 prefixEnd_7626026 1305272273894761790634517 := by
  unfold tailWord_7626026
  simp only [CollatzResearch.WordTrace]
  refine ⟨69536004667554424598708483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 185429345780145132263222621 69536004667554424598708483)
  ·
    refine ⟨104304007001331636898062725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69536004667554424598708483 104304007001331636898062725)
    ·
      refine ⟨19557001312749681918386761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 104304007001331636898062725 19557001312749681918386761)
      ·
        refine ⟨14667750984562261438790071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19557001312749681918386761 14667750984562261438790071)
        ·
          refine ⟨22001626476843392158185107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14667750984562261438790071 22001626476843392158185107)
          ·
            refine ⟨33002439715265088237277661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22001626476843392158185107 33002439715265088237277661)
            ·
              refine ⟨12375914893224408088979123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33002439715265088237277661 12375914893224408088979123)
              ·
                refine ⟨18563872339836612133468685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12375914893224408088979123 18563872339836612133468685)
                ·
                  refine ⟨6961452127438729550050757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18563872339836612133468685 6961452127438729550050757)
                  ·
                    refine ⟨1305272273894761790634517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6961452127438729550050757 1305272273894761790634517)
                    ·
                      rfl

theorem cell23_7626026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 1, 3, 1, 3, 4].length) (baseStart_7626026 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7626026 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7626026 prefixEnd_7626026 := by exact prefixLift 7626026
  have htrace : WordTrace (prefixWord ++ tailWord_7626026) baseStart_7626026 baseEnd_7626026 := by
    simpa [prefixWord, tailWord_7626026, baseEnd_7626026] using wordTrace_append hprefix tailTrace_7626026
  have hstable : (prefixWord ++ tailWord_7626026).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7626026).length < 2 ^ (prefixWord ++ tailWord_7626026).sum := by decide
  have hdescent : baseEnd_7626026 < baseStart_7626026 := by decide
  rcases family_descends (prefixWord ++ tailWord_7626026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7626077 : List Nat := [1, 4, 5, 1, 1, 1, 1, 4, 1, 4]
def baseStart_7626077 : Nat := 118140960795 + 7626077 * 2 ^ 59
def prefixEnd_7626077 : Nat := 4983230072969 + 3 ^ 40 * 7626077 * 2
def baseEnd_7626077 : Nat := 1305281003065888224121939

theorem tailTrace_7626077 : CollatzResearch.WordTrace tailWord_7626077 prefixEnd_7626077 1305281003065888224121939 := by
  unfold tailWord_7626077
  simp only [CollatzResearch.WordTrace]
  refine ⟨278145878793032934104940485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185430585862021956069960323 278145878793032934104940485)
  ·
    refine ⟨52152352273693675144676341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 278145878793032934104940485 52152352273693675144676341)
    ·
      refine ⟨4889283025658782044813407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 52152352273693675144676341 4889283025658782044813407)
      ·
        refine ⟨7333924538488173067220111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4889283025658782044813407 7333924538488173067220111)
        ·
          refine ⟨11000886807732259600830167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7333924538488173067220111 11000886807732259600830167)
          ·
            refine ⟨16501330211598389401245251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11000886807732259600830167 16501330211598389401245251)
            ·
              refine ⟨24751995317397584101867877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16501330211598389401245251 24751995317397584101867877)
              ·
                refine ⟨4640999122012047019100227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24751995317397584101867877 4640999122012047019100227)
                ·
                  refine ⟨6961498683018070528650341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4640999122012047019100227 6961498683018070528650341)
                  ·
                    refine ⟨1305281003065888224121939, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6961498683018070528650341 1305281003065888224121939)
                    ·
                      rfl

theorem cell23_7626077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 1, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 1, 1, 1, 4, 1, 4].length) (baseStart_7626077 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7626077 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7626077 prefixEnd_7626077 := by exact prefixLift 7626077
  have htrace : WordTrace (prefixWord ++ tailWord_7626077) baseStart_7626077 baseEnd_7626077 := by
    simpa [prefixWord, tailWord_7626077, baseEnd_7626077] using wordTrace_append hprefix tailTrace_7626077
  have hstable : (prefixWord ++ tailWord_7626077).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7626077).length < 2 ^ (prefixWord ++ tailWord_7626077).sum := by decide
  have hdescent : baseEnd_7626077 < baseStart_7626077 := by decide
  rcases family_descends (prefixWord ++ tailWord_7626077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7626083 : List Nat := [1, 1, 1, 5, 2, 3, 1, 4, 1, 1, 3]
def baseStart_7626083 : Nat := 118140960795 + 7626083 * 2 ^ 59
def prefixEnd_7626083 : Nat := 4983230072969 + 3 ^ 40 * 7626083 * 2
def baseEnd_7626083 : Nat := 3915846090081591648890789

theorem tailTrace_7626083 : CollatzResearch.WordTrace tailWord_7626083 prefixEnd_7626083 3915846090081591648890789 := by
  unfold tailWord_7626083
  simp only [CollatzResearch.WordTrace]
  refine ⟨278146097631011197129658903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185430731754007464753105935 278146097631011197129658903)
  ·
    refine ⟨417219146446516795694488355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 278146097631011197129658903 417219146446516795694488355)
    ·
      refine ⟨625828719669775193541732533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 417219146446516795694488355 625828719669775193541732533)
      ·
        refine ⟨58671442469041424394537425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 625828719669775193541732533 58671442469041424394537425)
        ·
          refine ⟨44003581851781068295903069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58671442469041424394537425 44003581851781068295903069)
          ·
            refine ⟨16501343194417900610963651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 44003581851781068295903069 16501343194417900610963651)
            ·
              refine ⟨24752014791626850916445477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16501343194417900610963651 24752014791626850916445477)
              ·
                refine ⟨4641002773430034546833527, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24752014791626850916445477 4641002773430034546833527)
                ·
                  refine ⟨6961504160145051820250291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4641002773430034546833527 6961504160145051820250291)
                  ·
                    refine ⟨10442256240217577730375437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6961504160145051820250291 10442256240217577730375437)
                    ·
                      refine ⟨3915846090081591648890789, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10442256240217577730375437 3915846090081591648890789)
                      ·
                        rfl

theorem cell23_7626083_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 3, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 3, 1, 4, 1, 1, 3].length) (baseStart_7626083 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7626083 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7626083 prefixEnd_7626083 := by exact prefixLift 7626083
  have htrace : WordTrace (prefixWord ++ tailWord_7626083) baseStart_7626083 baseEnd_7626083 := by
    simpa [prefixWord, tailWord_7626083, baseEnd_7626083] using wordTrace_append hprefix tailTrace_7626083
  have hstable : (prefixWord ++ tailWord_7626083).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7626083).length < 2 ^ (prefixWord ++ tailWord_7626083).sum := by decide
  have hdescent : baseEnd_7626083 < baseStart_7626083 := by decide
  rcases family_descends (prefixWord ++ tailWord_7626083) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7626106 : List Nat := [3, 1, 1, 1, 1, 1, 2, 6, 3, 2, 2]
def baseStart_7626106 : Nat := 118140960795 + 7626106 * 2 ^ 59
def prefixEnd_7626106 : Nat := 4983230072969 + 3 ^ 40 * 7626106 * 2
def baseEnd_7626106 : Nat := 3915857900136645058903183

theorem tailTrace_7626106 : CollatzResearch.WordTrace tailWord_7626106 prefixEnd_7626106 3915857900136645058903183 := by
  unfold tailWord_7626106
  simp only [CollatzResearch.WordTrace]
  refine ⟨69536734127481968014436543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 185431291006618581371830781 69536734127481968014436543)
  ·
    refine ⟨104305101191222952021654815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69536734127481968014436543 104305101191222952021654815)
    ·
      refine ⟨156457651786834428032482223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104305101191222952021654815 156457651786834428032482223)
      ·
        refine ⟨234686477680251642048723335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 156457651786834428032482223 234686477680251642048723335)
        ·
          refine ⟨352029716520377463073085003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 234686477680251642048723335 352029716520377463073085003)
          ·
            refine ⟨528044574780566194609627505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 352029716520377463073085003 528044574780566194609627505)
            ·
              refine ⟨396033431085424645957220629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 528044574780566194609627505 396033431085424645957220629)
              ·
                refine ⟨18564067082129280279244717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 396033431085424645957220629 18564067082129280279244717)
                ·
                  refine ⟨6961525155798480104716769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18564067082129280279244717 6961525155798480104716769)
                  ·
                    refine ⟨5221143866848860078537577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6961525155798480104716769 5221143866848860078537577)
                    ·
                      refine ⟨3915857900136645058903183, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5221143866848860078537577 3915857900136645058903183)
                      ·
                        rfl

theorem cell23_7626106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 2, 6, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 2, 6, 3, 2, 2].length) (baseStart_7626106 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7626106 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7626106 prefixEnd_7626106 := by exact prefixLift 7626106
  have htrace : WordTrace (prefixWord ++ tailWord_7626106) baseStart_7626106 baseEnd_7626106 := by
    simpa [prefixWord, tailWord_7626106, baseEnd_7626106] using wordTrace_append hprefix tailTrace_7626106
  have hstable : (prefixWord ++ tailWord_7626106).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7626106).length < 2 ^ (prefixWord ++ tailWord_7626106).sum := by decide
  have hdescent : baseEnd_7626106 < baseStart_7626106 := by decide
  rcases family_descends (prefixWord ++ tailWord_7626106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7626109 : List Nat := [1, 4, 1, 1, 2, 2, 1, 3, 3, 2, 3]
def baseStart_7626109 : Nat := 118140960795 + 7626109 * 2 ^ 59
def prefixEnd_7626109 : Nat := 4983230072969 + 3 ^ 40 * 7626109 * 2
def baseEnd_7626109 : Nat := 3915859440578608547165669

theorem tailTrace_7626109 : CollatzResearch.WordTrace tailWord_7626109 prefixEnd_7626109 3915859440578608547165669 := by
  unfold tailWord_7626109
  simp only [CollatzResearch.WordTrace]
  refine ⟨278147045928917003570105381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185431363952611335713403587 278147045928917003570105381)
  ·
    refine ⟨52152571111671938169394759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 278147045928917003570105381 52152571111671938169394759)
    ·
      refine ⟨78228856667507907254092139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52152571111671938169394759 78228856667507907254092139)
      ·
        refine ⟨117343285001261860881138209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78228856667507907254092139 117343285001261860881138209)
        ·
          refine ⟨88007463750946395660853657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 117343285001261860881138209 88007463750946395660853657)
          ·
            refine ⟨66005597813209796745640243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 88007463750946395660853657 66005597813209796745640243)
            ·
              refine ⟨99008396719814695118460365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66005597813209796745640243 99008396719814695118460365)
              ·
                refine ⟨37128148769930510669422637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 99008396719814695118460365 37128148769930510669422637)
                ·
                  refine ⟨13923055788723941501033489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 37128148769930510669422637 13923055788723941501033489)
                  ·
                    refine ⟨10442291841542956125775117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13923055788723941501033489 10442291841542956125775117)
                    ·
                      refine ⟨3915859440578608547165669, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10442291841542956125775117 3915859440578608547165669)
                      ·
                        rfl

theorem cell23_7626109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 1, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 1, 3, 3, 2, 3].length) (baseStart_7626109 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7626109 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7626109 prefixEnd_7626109 := by exact prefixLift 7626109
  have htrace : WordTrace (prefixWord ++ tailWord_7626109) baseStart_7626109 baseEnd_7626109 := by
    simpa [prefixWord, tailWord_7626109, baseEnd_7626109] using wordTrace_append hprefix tailTrace_7626109
  have hstable : (prefixWord ++ tailWord_7626109).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7626109).length < 2 ^ (prefixWord ++ tailWord_7626109).sum := by decide
  have hdescent : baseEnd_7626109 < baseStart_7626109 := by decide
  rcases family_descends (prefixWord ++ tailWord_7626109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7626110 : List Nat := [4, 2, 3, 2, 1, 1, 1, 1, 1, 5, 2]
def baseStart_7626110 : Nat := 118140960795 + 7626110 * 2 ^ 59
def prefixEnd_7626110 : Nat := 4983230072969 + 3 ^ 40 * 7626110 * 2
def baseEnd_7626110 : Nat := 3915859954059263043253165

theorem tailTrace_7626110 : CollatzResearch.WordTrace tailWord_7626110 prefixEnd_7626110 3915859954059263043253165 := by
  unfold tailWord_7626110
  simp only [CollatzResearch.WordTrace]
  refine ⟨34768385300239172592611473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 185431388267942253827261189 34768385300239172592611473)
  ·
    refine ⟨26076288975179379444458605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34768385300239172592611473 26076288975179379444458605)
    ·
      refine ⟨9778608365692267291671977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26076288975179379444458605 9778608365692267291671977)
      ·
        refine ⟨7333956274269200468753983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9778608365692267291671977 7333956274269200468753983)
        ·
          refine ⟨11000934411403800703130975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7333956274269200468753983 11000934411403800703130975)
          ·
            refine ⟨16501401617105701054696463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11000934411403800703130975 16501401617105701054696463)
            ·
              refine ⟨24752102425658551582044695, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16501401617105701054696463 24752102425658551582044695)
              ·
                refine ⟨37128153638487827373067043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24752102425658551582044695 37128153638487827373067043)
                ·
                  refine ⟨55692230457731741059600565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37128153638487827373067043 55692230457731741059600565)
                  ·
                    refine ⟨5221146605412350724337553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 55692230457731741059600565 5221146605412350724337553)
                    ·
                      refine ⟨3915859954059263043253165, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5221146605412350724337553 3915859954059263043253165)
                      ·
                        rfl

theorem cell23_7626110_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 1, 1, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 1, 1, 1, 1, 1, 5, 2].length) (baseStart_7626110 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7626110 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7626110 prefixEnd_7626110 := by exact prefixLift 7626110
  have htrace : WordTrace (prefixWord ++ tailWord_7626110) baseStart_7626110 baseEnd_7626110 := by
    simpa [prefixWord, tailWord_7626110, baseEnd_7626110] using wordTrace_append hprefix tailTrace_7626110
  have hstable : (prefixWord ++ tailWord_7626110).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7626110).length < 2 ^ (prefixWord ++ tailWord_7626110).sum := by decide
  have hdescent : baseEnd_7626110 < baseStart_7626110 := by decide
  rcases family_descends (prefixWord ++ tailWord_7626110) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7626119 : List Nat := [1, 1, 4, 2, 2, 2, 2, 2, 1, 2, 4]
def baseStart_7626119 : Nat := 118140960795 + 7626119 * 2 ^ 59
def prefixEnd_7626119 : Nat := 4983230072969 + 3 ^ 40 * 7626119 * 2
def baseEnd_7626119 : Nat := 3915864575385153508040623

theorem tailTrace_7626119 : CollatzResearch.WordTrace tailWord_7626119 prefixEnd_7626119 3915864575385153508040623 := by
  unfold tailWord_7626119
  simp only [CollatzResearch.WordTrace]
  refine ⟨278147410658880775277969411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185431607105920516851979607 278147410658880775277969411)
  ·
    refine ⟨417221115988321162916954117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 278147410658880775277969411 417221115988321162916954117)
    ·
      refine ⟨78228959247810218046928897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 417221115988321162916954117 78228959247810218046928897)
      ·
        refine ⟨58671719435857663535196673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78228959247810218046928897 58671719435857663535196673)
        ·
          refine ⟨44003789576893247651397505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58671719435857663535196673 44003789576893247651397505)
          ·
            refine ⟨33002842182669935738548129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44003789576893247651397505 33002842182669935738548129)
            ·
              refine ⟨24752131637002451803911097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33002842182669935738548129 24752131637002451803911097)
              ·
                refine ⟨18564098727751838852933323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24752131637002451803911097 18564098727751838852933323)
                ·
                  refine ⟨27846148091627758279399985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18564098727751838852933323 27846148091627758279399985)
                  ·
                    refine ⟨20884611068720818709549989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27846148091627758279399985 20884611068720818709549989)
                    ·
                      refine ⟨3915864575385153508040623, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20884611068720818709549989 3915864575385153508040623)
                      ·
                        rfl

theorem cell23_7626119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 2, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 2, 2, 2, 1, 2, 4].length) (baseStart_7626119 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7626119 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7626119 prefixEnd_7626119 := by exact prefixLift 7626119
  have htrace : WordTrace (prefixWord ++ tailWord_7626119) baseStart_7626119 baseEnd_7626119 := by
    simpa [prefixWord, tailWord_7626119, baseEnd_7626119] using wordTrace_append hprefix tailTrace_7626119
  have hstable : (prefixWord ++ tailWord_7626119).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7626119).length < 2 ^ (prefixWord ++ tailWord_7626119).sum := by decide
  have hdescent : baseEnd_7626119 < baseStart_7626119 := by decide
  rcases family_descends (prefixWord ++ tailWord_7626119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7626139 : List Nat := [1, 1, 1, 1, 1, 1, 2, 1, 10, 1, 3]
def baseStart_7626139 : Nat := 118140960795 + 7626139 * 2 ^ 59
def prefixEnd_7626139 : Nat := 4983230072969 + 3 ^ 40 * 7626139 * 2
def baseEnd_7626139 : Nat := 3915874844998243429790531

theorem tailTrace_7626139 : CollatzResearch.WordTrace tailWord_7626139 prefixEnd_7626139 3915874844998243429790531 := by
  unfold tailWord_7626139
  simp only [CollatzResearch.WordTrace]
  refine ⟨278148140118808318693697471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185432093412538879129131647 278148140118808318693697471)
  ·
    refine ⟨417222210178212478040546207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 278148140118808318693697471 417222210178212478040546207)
    ·
      refine ⟨625833315267318717060819311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 417222210178212478040546207 625833315267318717060819311)
      ·
        refine ⟨938749972900978075591228967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 625833315267318717060819311 938749972900978075591228967)
        ·
          refine ⟨1408124959351467113386843451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 938749972900978075591228967 1408124959351467113386843451)
          ·
            refine ⟨2112187439027200670080265177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1408124959351467113386843451 2112187439027200670080265177)
            ·
              refine ⟨1584140579270400502560198883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2112187439027200670080265177 1584140579270400502560198883)
              ·
                refine ⟨2376210868905600753840298325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1584140579270400502560198883 2376210868905600753840298325)
                ·
                  refine ⟨6961555279996877208516499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 2376210868905600753840298325 6961555279996877208516499)
                  ·
                    refine ⟨10442332919995315812774749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6961555279996877208516499 10442332919995315812774749)
                    ·
                      refine ⟨3915874844998243429790531, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10442332919995315812774749 3915874844998243429790531)
                      ·
                        rfl

theorem cell23_7626139_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 10, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 10, 1, 3].length) (baseStart_7626139 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7626139 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7626139 prefixEnd_7626139 := by exact prefixLift 7626139
  have htrace : WordTrace (prefixWord ++ tailWord_7626139) baseStart_7626139 baseEnd_7626139 := by
    simpa [prefixWord, tailWord_7626139, baseEnd_7626139] using wordTrace_append hprefix tailTrace_7626139
  have hstable : (prefixWord ++ tailWord_7626139).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7626139).length < 2 ^ (prefixWord ++ tailWord_7626139).sum := by decide
  have hdescent : baseEnd_7626139 < baseStart_7626139 := by decide
  rcases family_descends (prefixWord ++ tailWord_7626139) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7626149 : List Nat := [1, 3, 1, 2, 1, 1, 2, 1, 2, 7, 2]
def baseStart_7626149 : Nat := 118140960795 + 7626149 * 2 ^ 59
def prefixEnd_7626149 : Nat := 4983230072969 + 3 ^ 40 * 7626149 * 2
def baseEnd_7626149 : Nat := 3915879979804788390665485

theorem tailTrace_7626149 : CollatzResearch.WordTrace tailWord_7626149 prefixEnd_7626149 3915879979804788390665485 := by
  unfold tailWord_7626149
  simp only [CollatzResearch.WordTrace]
  refine ⟨278148504848772090401561501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185432336565848060267707667 278148504848772090401561501)
  ·
    refine ⟨104305689318289533900585563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 278148504848772090401561501 104305689318289533900585563)
    ·
      refine ⟨156458533977434300850878345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104305689318289533900585563 156458533977434300850878345)
      ·
        refine ⟨117343900483075725638158759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 156458533977434300850878345 117343900483075725638158759)
        ·
          refine ⟨176015850724613588457238139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 117343900483075725638158759 176015850724613588457238139)
          ·
            refine ⟨264023776086920382685857209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 176015850724613588457238139 264023776086920382685857209)
            ·
              refine ⟨198017832065190287014392907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 264023776086920382685857209 198017832065190287014392907)
              ·
                refine ⟨297026748097785430521589361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 198017832065190287014392907 297026748097785430521589361)
                ·
                  refine ⟨222770061073339072891192021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 297026748097785430521589361 222770061073339072891192021)
                  ·
                    refine ⟨5221173306406384520887313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 222770061073339072891192021 5221173306406384520887313)
                    ·
                      refine ⟨3915879979804788390665485, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5221173306406384520887313 3915879979804788390665485)
                      ·
                        rfl

theorem cell23_7626149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 2, 1, 2, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 2, 1, 2, 7, 2].length) (baseStart_7626149 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7626149 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7626149 prefixEnd_7626149 := by exact prefixLift 7626149
  have htrace : WordTrace (prefixWord ++ tailWord_7626149) baseStart_7626149 baseEnd_7626149 := by
    simpa [prefixWord, tailWord_7626149, baseEnd_7626149] using wordTrace_append hprefix tailTrace_7626149
  have hstable : (prefixWord ++ tailWord_7626149).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7626149).length < 2 ^ (prefixWord ++ tailWord_7626149).sum := by decide
  have hdescent : baseEnd_7626149 < baseStart_7626149 := by decide
  rcases family_descends (prefixWord ++ tailWord_7626149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7626156 : List Nat := [2, 2, 1, 1, 1, 1, 4, 5, 2, 1, 3]
def baseStart_7626156 : Nat := 118140960795 + 7626156 * 2 ^ 59
def prefixEnd_7626156 : Nat := 4983230072969 + 3 ^ 40 * 7626156 * 2
def baseEnd_7626156 : Nat := 3915883574169369863277953

theorem tailTrace_7626156 : CollatzResearch.WordTrace tailWord_7626156 prefixEnd_7626156 3915883574169369863277953 := by
  unfold tailWord_7626156
  simp only [CollatzResearch.WordTrace]
  refine ⟨139074380079873365298533161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 185432506773164487064710881 139074380079873365298533161)
  ·
    refine ⟨104305785059905023973899871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 139074380079873365298533161 104305785059905023973899871)
    ·
      refine ⟨156458677589857535960849807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104305785059905023973899871 156458677589857535960849807)
      ·
        refine ⟨234688016384786303941274711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 156458677589857535960849807 234688016384786303941274711)
        ·
          refine ⟨352032024577179455911912067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 234688016384786303941274711 352032024577179455911912067)
          ·
            refine ⟨528048036865769183867868101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 352032024577179455911912067 528048036865769183867868101)
            ·
              refine ⟨99009006912331721975225269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 528048036865769183867868101 99009006912331721975225269)
              ·
                refine ⟨9282094398031098935177369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 99009006912331721975225269 9282094398031098935177369)
                ·
                  refine ⟨6961570798523324201383027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9282094398031098935177369 6961570798523324201383027)
                  ·
                    refine ⟨10442356197784986302074541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6961570798523324201383027 10442356197784986302074541)
                    ·
                      refine ⟨3915883574169369863277953, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10442356197784986302074541 3915883574169369863277953)
                      ·
                        rfl

theorem cell23_7626156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 2, 1, 3].length) (baseStart_7626156 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7626156 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7626156 prefixEnd_7626156 := by exact prefixLift 7626156
  have htrace : WordTrace (prefixWord ++ tailWord_7626156) baseStart_7626156 baseEnd_7626156 := by
    simpa [prefixWord, tailWord_7626156, baseEnd_7626156] using wordTrace_append hprefix tailTrace_7626156
  have hstable : (prefixWord ++ tailWord_7626156).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7626156).length < 2 ^ (prefixWord ++ tailWord_7626156).sum := by decide
  have hdescent : baseEnd_7626156 < baseStart_7626156 := by decide
  rcases family_descends (prefixWord ++ tailWord_7626156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7626162 : List Nat := [3, 2, 1, 1, 1, 1, 2, 1, 1, 2, 8]
def baseStart_7626162 : Nat := 118140960795 + 7626162 * 2 ^ 59
def prefixEnd_7626162 : Nat := 4983230072969 + 3 ^ 40 * 7626162 * 2
def baseEnd_7626162 : Nat := 3915886655053296839802925

theorem tailTrace_7626162 : CollatzResearch.WordTrace tailWord_7626162 prefixEnd_7626162 3915886655053296839802925 := by
  unfold tailWord_7626162
  simp only [CollatzResearch.WordTrace]
  refine ⟨69537244749431248405446185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 185432652665149995747856493 69537244749431248405446185)
  ·
    refine ⟨52152933562073436304084639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69537244749431248405446185 52152933562073436304084639)
    ·
      refine ⟨78229400343110154456126959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52152933562073436304084639 78229400343110154456126959)
      ·
        refine ⟨117344100514665231684190439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78229400343110154456126959 117344100514665231684190439)
        ·
          refine ⟨176016150771997847526285659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 117344100514665231684190439 176016150771997847526285659)
          ·
            refine ⟨264024226157996771289428489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 176016150771997847526285659 264024226157996771289428489)
            ·
              refine ⟨198018169618497578467071367, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 264024226157996771289428489 198018169618497578467071367)
              ·
                refine ⟨297027254427746367700607051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 198018169618497578467071367 297027254427746367700607051)
                ·
                  refine ⟨445540881641619551550910577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 297027254427746367700607051 445540881641619551550910577)
                  ·
                    refine ⟨334155661231214663663182933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 445540881641619551550910577 334155661231214663663182933)
                    ·
                      refine ⟨3915886655053296839802925, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 334155661231214663663182933 3915886655053296839802925)
                      ·
                        rfl

theorem cell23_7626162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 2, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 2, 1, 1, 2, 8].length) (baseStart_7626162 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7626162 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7626162 prefixEnd_7626162 := by exact prefixLift 7626162
  have htrace : WordTrace (prefixWord ++ tailWord_7626162) baseStart_7626162 baseEnd_7626162 := by
    simpa [prefixWord, tailWord_7626162, baseEnd_7626162] using wordTrace_append hprefix tailTrace_7626162
  have hstable : (prefixWord ++ tailWord_7626162).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7626162).length < 2 ^ (prefixWord ++ tailWord_7626162).sum := by decide
  have hdescent : baseEnd_7626162 < baseStart_7626162 := by decide
  rcases family_descends (prefixWord ++ tailWord_7626162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7626249 : List Nat := [1, 2, 1, 1, 3, 1, 3, 4, 2, 5]
def baseStart_7626249 : Nat := 118140960795 + 7626249 * 2 ^ 59
def prefixEnd_7626249 : Nat := 4983230072969 + 3 ^ 40 * 7626249 * 2
def baseEnd_7626249 : Nat := 1305310442623412666471675

theorem tailTrace_7626249 : CollatzResearch.WordTrace tailWord_7626249 prefixEnd_7626249 1305310442623412666471675 := by
  unfold tailWord_7626249
  simp only [CollatzResearch.WordTrace]
  refine ⟨278152152148409807480201801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185434768098939871653467867 278152152148409807480201801)
  ·
    refine ⟨208614114111307355610151351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 278152152148409807480201801 208614114111307355610151351)
    ·
      refine ⟨312921171166961033415227027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 208614114111307355610151351 312921171166961033415227027)
      ·
        refine ⟨469381756750441550122840541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 312921171166961033415227027 469381756750441550122840541)
        ·
          refine ⟨176018158781415581296065203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 469381756750441550122840541 176018158781415581296065203)
          ·
            refine ⟨264027238172123371944097805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 176018158781415581296065203 264027238172123371944097805)
            ·
              refine ⟨99010214314546264479036677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 264027238172123371944097805 99010214314546264479036677)
              ·
                refine ⟨18564415183977424589819377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 99010214314546264479036677 18564415183977424589819377)
                ·
                  refine ⟨13923311387983068442364533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18564415183977424589819377 13923311387983068442364533)
                  ·
                    refine ⟨1305310442623412666471675, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13923311387983068442364533 1305310442623412666471675)
                    ·
                      rfl

theorem cell23_7626249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 3, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 3, 4, 2, 5].length) (baseStart_7626249 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7626249 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7626249 prefixEnd_7626249 := by exact prefixLift 7626249
  have htrace : WordTrace (prefixWord ++ tailWord_7626249) baseStart_7626249 baseEnd_7626249 := by
    simpa [prefixWord, tailWord_7626249, baseEnd_7626249] using wordTrace_append hprefix tailTrace_7626249
  have hstable : (prefixWord ++ tailWord_7626249).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7626249).length < 2 ^ (prefixWord ++ tailWord_7626249).sum := by decide
  have hdescent : baseEnd_7626249 < baseStart_7626249 := by decide
  rcases family_descends (prefixWord ++ tailWord_7626249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7626259 : List Nat := [1, 1, 1, 2, 1, 6, 2, 1, 1, 2, 5]
def baseStart_7626259 : Nat := 118140960795 + 7626259 * 2 ^ 59
def prefixEnd_7626259 : Nat := 4983230072969 + 3 ^ 40 * 7626259 * 2
def baseEnd_7626259 : Nat := 3915936462676782960289979

theorem tailTrace_7626259 : CollatzResearch.WordTrace tailWord_7626259 prefixEnd_7626259 3915936462676782960289979 := by
  unfold tailWord_7626259
  simp only [CollatzResearch.WordTrace]
  refine ⟨278152516878373579188065831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185435011252249052792043887 278152516878373579188065831)
  ·
    refine ⟨417228775317560368782098747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 278152516878373579188065831 417228775317560368782098747)
    ·
      refine ⟨625843162976340553173148121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 417228775317560368782098747 625843162976340553173148121)
      ·
        refine ⟨469382372232255414879861091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 625843162976340553173148121 469382372232255414879861091)
        ·
          refine ⟨704073558348383122319791637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 469382372232255414879861091 704073558348383122319791637)
          ·
            refine ⟨33003448047580458858740233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 704073558348383122319791637 33003448047580458858740233)
            ·
              refine ⟨24752586035685344144055175, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33003448047580458858740233 24752586035685344144055175)
              ·
                refine ⟨37128879053528016216082763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24752586035685344144055175 37128879053528016216082763)
                ·
                  refine ⟨55693318580292024324124145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37128879053528016216082763 55693318580292024324124145)
                  ·
                    refine ⟨41769988935219018243093109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 55693318580292024324124145 41769988935219018243093109)
                    ·
                      refine ⟨3915936462676782960289979, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41769988935219018243093109 3915936462676782960289979)
                      ·
                        rfl

theorem cell23_7626259_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 6, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 6, 2, 1, 1, 2, 5].length) (baseStart_7626259 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7626259 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7626259 prefixEnd_7626259 := by exact prefixLift 7626259
  have htrace : WordTrace (prefixWord ++ tailWord_7626259) baseStart_7626259 baseEnd_7626259 := by
    simpa [prefixWord, tailWord_7626259, baseEnd_7626259] using wordTrace_append hprefix tailTrace_7626259
  have hstable : (prefixWord ++ tailWord_7626259).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7626259).length < 2 ^ (prefixWord ++ tailWord_7626259).sum := by decide
  have hdescent : baseEnd_7626259 < baseStart_7626259 := by decide
  rcases family_descends (prefixWord ++ tailWord_7626259) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7626309 : List Nat := [1, 3, 1, 1, 1, 4, 3, 1, 8]
def baseStart_7626309 : Nat := 118140960795 + 7626309 * 2 ^ 59
def prefixEnd_7626309 : Nat := 4983230072969 + 3 ^ 40 * 7626309 * 2
def baseEnd_7626309 : Nat := 435106904078834196073861

theorem tailTrace_7626309 : CollatzResearch.WordTrace tailWord_7626309 prefixEnd_7626309 435106904078834196073861 := by
  unfold tailWord_7626309
  simp only [CollatzResearch.WordTrace]
  refine ⟨278154340528192437727385981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185436227018794958484923987 278154340528192437727385981)
  ·
    refine ⟨104307877698072164147769743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 278154340528192437727385981 104307877698072164147769743)
    ·
      refine ⟨156461816547108246221654615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104307877698072164147769743 156461816547108246221654615)
      ·
        refine ⟨234692724820662369332481923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 156461816547108246221654615 234692724820662369332481923)
        ·
          refine ⟨352039087230993553998722885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 234692724820662369332481923 352039087230993553998722885)
          ·
            refine ⟨66007328855811291374760541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 352039087230993553998722885 66007328855811291374760541)
            ·
              refine ⟨24752748320929234265535203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 66007328855811291374760541 24752748320929234265535203)
              ·
                refine ⟨37129122481393851398302805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24752748320929234265535203 37129122481393851398302805)
                ·
                  refine ⟨435106904078834196073861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 37129122481393851398302805 435106904078834196073861)
                  ·
                    rfl

theorem cell23_7626309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 3, 1, 8].length) (baseStart_7626309 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7626309 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7626309 prefixEnd_7626309 := by exact prefixLift 7626309
  have htrace : WordTrace (prefixWord ++ tailWord_7626309) baseStart_7626309 baseEnd_7626309 := by
    simpa [prefixWord, tailWord_7626309, baseEnd_7626309] using wordTrace_append hprefix tailTrace_7626309
  have hstable : (prefixWord ++ tailWord_7626309).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7626309).length < 2 ^ (prefixWord ++ tailWord_7626309).sum := by decide
  have hdescent : baseEnd_7626309 < baseStart_7626309 := by decide
  rcases family_descends (prefixWord ++ tailWord_7626309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7626363 : List Nat := [1, 1, 1, 1, 1, 4, 5, 2, 2, 3, 2]
def baseStart_7626363 : Nat := 118140960795 + 7626363 * 2 ^ 59
def prefixEnd_7626363 : Nat := 4983230072969 + 3 ^ 40 * 7626363 * 2
def baseEnd_7626363 : Nat := 3915989864664850553389501

theorem tailTrace_7626363 : CollatzResearch.WordTrace tailWord_7626363 prefixEnd_7626363 3915989864664850553389501 := by
  unfold tailWord_7626363
  simp only [CollatzResearch.WordTrace]
  refine ⟨278156310069996804949851743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185437540046664536633234495 278156310069996804949851743)
  ·
    refine ⟨417234465104995207424777615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 278156310069996804949851743 417234465104995207424777615)
    ·
      refine ⟨625851697657492811137166423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 417234465104995207424777615 625851697657492811137166423)
      ·
        refine ⟨938777546486239216705749635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 625851697657492811137166423 938777546486239216705749635)
        ·
          refine ⟨1408166319729358825058624453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 938777546486239216705749635 1408166319729358825058624453)
          ·
            refine ⟨264031184949254779698492085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1408166319729358825058624453 264031184949254779698492085)
            ·
              refine ⟨24752923588992635596733633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 264031184949254779698492085 24752923588992635596733633)
              ·
                refine ⟨18564692691744476697550225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24752923588992635596733633 18564692691744476697550225)
                ·
                  refine ⟨13923519518808357523162669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18564692691744476697550225 13923519518808357523162669)
                  ·
                    refine ⟨5221319819553134071186001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13923519518808357523162669 5221319819553134071186001)
                    ·
                      refine ⟨3915989864664850553389501, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5221319819553134071186001 3915989864664850553389501)
                      ·
                        rfl

theorem cell23_7626363_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 5, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 5, 2, 2, 3, 2].length) (baseStart_7626363 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7626363 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7626363 prefixEnd_7626363 := by exact prefixLift 7626363
  have htrace : WordTrace (prefixWord ++ tailWord_7626363) baseStart_7626363 baseEnd_7626363 := by
    simpa [prefixWord, tailWord_7626363, baseEnd_7626363] using wordTrace_append hprefix tailTrace_7626363
  have hstable : (prefixWord ++ tailWord_7626363).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7626363).length < 2 ^ (prefixWord ++ tailWord_7626363).sum := by decide
  have hdescent : baseEnd_7626363 < baseStart_7626363 := by decide
  rcases family_descends (prefixWord ++ tailWord_7626363) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7626409 : List Nat := [1, 2, 1, 1, 1, 1, 2, 2, 1, 4, 7]
def baseStart_7626409 : Nat := 118140960795 + 7626409 * 2 ^ 59
def prefixEnd_7626409 : Nat := 4983230072969 + 3 ^ 40 * 7626409 * 2
def baseEnd_7626409 : Nat := 3916013484774957373414289

theorem tailTrace_7626409 : CollatzResearch.WordTrace tailWord_7626409 prefixEnd_7626409 3916013484774957373414289 := by
  unfold tailWord_7626409
  simp only [CollatzResearch.WordTrace]
  refine ⟨278157987827830154806026281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185438658551886769870684187 278157987827830154806026281)
  ·
    refine ⟨208618490870872616104519711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 278157987827830154806026281 208618490870872616104519711)
    ·
      refine ⟨312927736306308924156779567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 208618490870872616104519711 312927736306308924156779567)
      ·
        refine ⟨469391604459463386235169351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 312927736306308924156779567 469391604459463386235169351)
        ·
          refine ⟨704087406689195079352754027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 469391604459463386235169351 704087406689195079352754027)
          ·
            refine ⟨1056131110033792619029131041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 704087406689195079352754027 1056131110033792619029131041)
            ·
              refine ⟨792098332525344464271848281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1056131110033792619029131041 792098332525344464271848281)
              ·
                refine ⟨594073749394008348203886211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 792098332525344464271848281 594073749394008348203886211)
                ·
                  refine ⟨891110624091012522305829317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 594073749394008348203886211 891110624091012522305829317)
                  ·
                    refine ⟨167083242017064847932342997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 891110624091012522305829317 167083242017064847932342997)
                    ·
                      refine ⟨3916013484774957373414289, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 167083242017064847932342997 3916013484774957373414289)
                      ·
                        rfl

theorem cell23_7626409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 2, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 2, 1, 4, 7].length) (baseStart_7626409 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7626409 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7626409 prefixEnd_7626409 := by exact prefixLift 7626409
  have htrace : WordTrace (prefixWord ++ tailWord_7626409) baseStart_7626409 baseEnd_7626409 := by
    simpa [prefixWord, tailWord_7626409, baseEnd_7626409] using wordTrace_append hprefix tailTrace_7626409
  have hstable : (prefixWord ++ tailWord_7626409).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7626409).length < 2 ^ (prefixWord ++ tailWord_7626409).sum := by decide
  have hdescent : baseEnd_7626409 < baseStart_7626409 := by decide
  rcases family_descends (prefixWord ++ tailWord_7626409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7626421 : List Nat := [1, 3, 3, 3, 2, 2, 2, 2, 1, 1, 3]
def baseStart_7626421 : Nat := 118140960795 + 7626421 * 2 ^ 59
def prefixEnd_7626421 : Nat := 4983230072969 + 3 ^ 40 * 7626421 * 2
def baseEnd_7626421 : Nat := 3916019646542811326464235

theorem tailTrace_7626421 : CollatzResearch.WordTrace tailWord_7626421 prefixEnd_7626421 3916019646542811326464235 := by
  unfold tailWord_7626421
  simp only [CollatzResearch.WordTrace]
  refine ⟨278158425503786680855463117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185438950335857787236975411 278158425503786680855463117)
  ·
    refine ⟨104309409563920005320798669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 278158425503786680855463117 104309409563920005320798669)
    ·
      refine ⟨39116028586470001995299501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 104309409563920005320798669 39116028586470001995299501)
      ·
        refine ⟨14668510719926250748237313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39116028586470001995299501 14668510719926250748237313)
        ·
          refine ⟨11001383039944688061177985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14668510719926250748237313 11001383039944688061177985)
          ·
            refine ⟨8251037279958516045883489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11001383039944688061177985 8251037279958516045883489)
            ·
              refine ⟨6188277959968887034412617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8251037279958516045883489 6188277959968887034412617)
              ·
                refine ⟨4641208469976665275809463, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6188277959968887034412617 4641208469976665275809463)
                ·
                  refine ⟨6961812704964997913714195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4641208469976665275809463 6961812704964997913714195)
                  ·
                    refine ⟨10442719057447496870571293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6961812704964997913714195 10442719057447496870571293)
                    ·
                      refine ⟨3916019646542811326464235, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10442719057447496870571293 3916019646542811326464235)
                      ·
                        rfl

theorem cell23_7626421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 2, 2, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 2, 2, 2, 2, 1, 1, 3].length) (baseStart_7626421 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7626421 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7626421 prefixEnd_7626421 := by exact prefixLift 7626421
  have htrace : WordTrace (prefixWord ++ tailWord_7626421) baseStart_7626421 baseEnd_7626421 := by
    simpa [prefixWord, tailWord_7626421, baseEnd_7626421] using wordTrace_append hprefix tailTrace_7626421
  have hstable : (prefixWord ++ tailWord_7626421).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7626421).length < 2 ^ (prefixWord ++ tailWord_7626421).sum := by decide
  have hdescent : baseEnd_7626421 < baseStart_7626421 := by decide
  rcases family_descends (prefixWord ++ tailWord_7626421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7626446 : List Nat := [4, 1, 1, 1, 3, 1, 1, 2, 2, 7]
def baseStart_7626446 : Nat := 118140960795 + 7626446 * 2 ^ 59
def prefixEnd_7626446 : Nat := 4983230072969 + 3 ^ 40 * 7626446 * 2
def baseEnd_7626446 : Nat := 1305344161186391242883873

theorem tailTrace_7626446 : CollatzResearch.WordTrace tailWord_7626446 prefixEnd_7626446 1305344161186391242883873 := by
  unfold tailWord_7626446
  simp only [CollatzResearch.WordTrace]
  refine ⟨34769917166087013765640399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 185439558219130740083415461 34769917166087013765640399)
  ·
    refine ⟨52154875749130520648460599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34769917166087013765640399 52154875749130520648460599)
    ·
      refine ⟨78232313623695780972690899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52154875749130520648460599 78232313623695780972690899)
      ·
        refine ⟨117348470435543671459036349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78232313623695780972690899 117348470435543671459036349)
        ·
          refine ⟨44005676413328876797138631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 117348470435543671459036349 44005676413328876797138631)
          ·
            refine ⟨66008514619993315195707947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44005676413328876797138631 66008514619993315195707947)
            ·
              refine ⟨99012771929989972793561921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66008514619993315195707947 99012771929989972793561921)
              ·
                refine ⟨74259578947492479595171441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 99012771929989972793561921 74259578947492479595171441)
                ·
                  refine ⟨55694684210619359696378581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 74259578947492479595171441 55694684210619359696378581)
                  ·
                    refine ⟨1305344161186391242883873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 55694684210619359696378581 1305344161186391242883873)
                    ·
                      rfl

theorem cell23_7626446_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 1, 2, 2, 7].length) (baseStart_7626446 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7626446 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7626446 prefixEnd_7626446 := by exact prefixLift 7626446
  have htrace : WordTrace (prefixWord ++ tailWord_7626446) baseStart_7626446 baseEnd_7626446 := by
    simpa [prefixWord, tailWord_7626446, baseEnd_7626446] using wordTrace_append hprefix tailTrace_7626446
  have hstable : (prefixWord ++ tailWord_7626446).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7626446).length < 2 ^ (prefixWord ++ tailWord_7626446).sum := by decide
  have hdescent : baseEnd_7626446 < baseStart_7626446 := by decide
  rcases family_descends (prefixWord ++ tailWord_7626446) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7626456 : List Nat := [2, 1, 2, 2, 3, 1, 2, 1, 2, 2, 5]
def baseStart_7626456 : Nat := 118140960795 + 7626456 * 2 ^ 59
def prefixEnd_7626456 : Nat := 4983230072969 + 3 ^ 40 * 7626456 * 2
def baseEnd_7626456 : Nat := 3916037618365718689526573

theorem tailTrace_7626456 : CollatzResearch.WordTrace tailWord_7626456 prefixEnd_7626456 3916037618365718689526573 := by
  unfold tailWord_7626456
  simp only [CollatzResearch.WordTrace]
  refine ⟨139079851029329940916493611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 185439801372439921221991481 139079851029329940916493611)
  ·
    refine ⟨208619776543994911374740417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139079851029329940916493611 208619776543994911374740417)
    ·
      refine ⟨156464832407996183531055313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 208619776543994911374740417 156464832407996183531055313)
      ·
        refine ⟨117348624305997137648291485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 156464832407996183531055313 117348624305997137648291485)
        ·
          refine ⟨44005734114748926618109307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 117348624305997137648291485 44005734114748926618109307)
          ·
            refine ⟨66008601172123389927163961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44005734114748926618109307 66008601172123389927163961)
            ·
              refine ⟨49506450879092542445372971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 66008601172123389927163961 49506450879092542445372971)
              ·
                refine ⟨74259676318638813668059457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49506450879092542445372971 74259676318638813668059457)
                ·
                  refine ⟨55694757238979110251044593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 74259676318638813668059457 55694757238979110251044593)
                  ·
                    refine ⟨41771067929234332688283445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 55694757238979110251044593 41771067929234332688283445)
                    ·
                      refine ⟨3916037618365718689526573, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41771067929234332688283445 3916037618365718689526573)
                      ·
                        rfl

theorem cell23_7626456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 2, 1, 2, 2, 5].length) (baseStart_7626456 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7626456 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7626456 prefixEnd_7626456 := by exact prefixLift 7626456
  have htrace : WordTrace (prefixWord ++ tailWord_7626456) baseStart_7626456 baseEnd_7626456 := by
    simpa [prefixWord, tailWord_7626456, baseEnd_7626456] using wordTrace_append hprefix tailTrace_7626456
  have hstable : (prefixWord ++ tailWord_7626456).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7626456).length < 2 ^ (prefixWord ++ tailWord_7626456).sum := by decide
  have hdescent : baseEnd_7626456 < baseStart_7626456 := by decide
  rcases family_descends (prefixWord ++ tailWord_7626456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7626461 : List Nat := [1, 4, 3, 3, 2, 1, 2, 1, 1, 1, 4]
def baseStart_7626461 : Nat := 118140960795 + 7626461 * 2 ^ 59
def prefixEnd_7626461 : Nat := 4983230072969 + 3 ^ 40 * 7626461 * 2
def baseEnd_7626461 : Nat := 3916040185768991169964051

theorem tailTrace_7626461 : CollatzResearch.WordTrace tailWord_7626461 prefixEnd_7626461 3916040185768991169964051 := by
  unfold tailWord_7626461
  simp only [CollatzResearch.WordTrace]
  refine ⟨278159884423641767686919237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185439922949094511791279491 278159884423641767686919237)
  ·
    refine ⟨52154978329432831441297357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 278159884423641767686919237 52154978329432831441297357)
    ·
      refine ⟨19558116873537311790486509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 52154978329432831441297357 19558116873537311790486509)
      ·
        refine ⟨7334293827576491921432441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19558116873537311790486509 7334293827576491921432441)
        ·
          refine ⟨5500720370682368941074331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7334293827576491921432441 5500720370682368941074331)
          ·
            refine ⟨8251080556023553411611497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5500720370682368941074331 8251080556023553411611497)
            ·
              refine ⟨6188310417017665058708623, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8251080556023553411611497 6188310417017665058708623)
              ·
                refine ⟨9282465625526497588062935, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6188310417017665058708623 9282465625526497588062935)
                ·
                  refine ⟨13923698438289746382094403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9282465625526497588062935 13923698438289746382094403)
                  ·
                    refine ⟨20885547657434619573141605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13923698438289746382094403 20885547657434619573141605)
                    ·
                      refine ⟨3916040185768991169964051, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20885547657434619573141605 3916040185768991169964051)
                      ·
                        rfl

theorem cell23_7626461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 2, 1, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 2, 1, 2, 1, 1, 1, 4].length) (baseStart_7626461 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7626461 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7626461 prefixEnd_7626461 := by exact prefixLift 7626461
  have htrace : WordTrace (prefixWord ++ tailWord_7626461) baseStart_7626461 baseEnd_7626461 := by
    simpa [prefixWord, tailWord_7626461, baseEnd_7626461] using wordTrace_append hprefix tailTrace_7626461
  have hstable : (prefixWord ++ tailWord_7626461).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7626461).length < 2 ^ (prefixWord ++ tailWord_7626461).sum := by decide
  have hdescent : baseEnd_7626461 < baseStart_7626461 := by decide
  rcases family_descends (prefixWord ++ tailWord_7626461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7626476 : List Nat := [2, 2, 1, 1, 2, 2, 3, 2, 2, 6]
def baseStart_7626476 : Nat := 118140960795 + 7626476 * 2 ^ 59
def prefixEnd_7626476 : Nat := 4983230072969 + 3 ^ 40 * 7626476 * 2
def baseEnd_7626476 : Nat := 1305349295992936203758827

theorem tailTrace_7626476 : CollatzResearch.WordTrace tailWord_7626476 prefixEnd_7626476 1305349295992936203758827 := by
  unfold tailWord_7626476
  simp only [CollatzResearch.WordTrace]
  refine ⟨139080215759293712624357641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 185440287679058283499143521 139080215759293712624357641)
  ·
    refine ⟨104310161819470284468268231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 139080215759293712624357641 104310161819470284468268231)
    ·
      refine ⟨156465242729205426702402347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104310161819470284468268231 156465242729205426702402347)
      ·
        refine ⟨234697864093808140053603521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 156465242729205426702402347 234697864093808140053603521)
        ·
          refine ⟨176023398070356105040202641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 234697864093808140053603521 176023398070356105040202641)
          ·
            refine ⟨132017548552767078780151981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 176023398070356105040202641 132017548552767078780151981)
            ·
              refine ⟨49506580707287654542556993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 132017548552767078780151981 49506580707287654542556993)
              ·
                refine ⟨37129935530465740906917745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49506580707287654542556993 37129935530465740906917745)
                ·
                  refine ⟨27847451647849305680188309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37129935530465740906917745 27847451647849305680188309)
                  ·
                    refine ⟨1305349295992936203758827, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27847451647849305680188309 1305349295992936203758827)
                    ·
                      rfl

theorem cell23_7626476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 6].length) (baseStart_7626476 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7626476 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7626476 prefixEnd_7626476 := by exact prefixLift 7626476
  have htrace : WordTrace (prefixWord ++ tailWord_7626476) baseStart_7626476 baseEnd_7626476 := by
    simpa [prefixWord, tailWord_7626476, baseEnd_7626476] using wordTrace_append hprefix tailTrace_7626476
  have hstable : (prefixWord ++ tailWord_7626476).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7626476).length < 2 ^ (prefixWord ++ tailWord_7626476).sum := by decide
  have hdescent : baseEnd_7626476 < baseStart_7626476 := by decide
  rcases family_descends (prefixWord ++ tailWord_7626476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7626477 : List Nat := [1, 5, 1, 2, 1, 2, 3, 2, 2, 1, 3]
def baseStart_7626477 : Nat := 118140960795 + 7626477 * 2 ^ 59
def prefixEnd_7626477 : Nat := 4983230072969 + 3 ^ 40 * 7626477 * 2
def baseEnd_7626477 : Nat := 3916048401459463107363977

theorem tailTrace_7626477 : CollatzResearch.WordTrace tailWord_7626477 prefixEnd_7626477 3916048401459463107363977 := by
  unfold tailWord_7626477
  simp only [CollatzResearch.WordTrace]
  refine ⟨278160467991583802419501685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185440311994389201613001123 278160467991583802419501685)
  ·
    refine ⟨26077543874210981476828283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 278160467991583802419501685 26077543874210981476828283)
    ·
      refine ⟨39116315811316472215242425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26077543874210981476828283 39116315811316472215242425)
      ·
        refine ⟨29337236858487354161431819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39116315811316472215242425 29337236858487354161431819)
        ·
          refine ⟨44005855287731031242147729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29337236858487354161431819 44005855287731031242147729)
          ·
            refine ⟨33004391465798273431610797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44005855287731031242147729 33004391465798273431610797)
            ·
              refine ⟨12376646799674352536854049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33004391465798273431610797 12376646799674352536854049)
              ·
                refine ⟨9282485099755764402640537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12376646799674352536854049 9282485099755764402640537)
                ·
                  refine ⟨6961863824816823301980403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9282485099755764402640537 6961863824816823301980403)
                  ·
                    refine ⟨10442795737225234952970605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6961863824816823301980403 10442795737225234952970605)
                    ·
                      refine ⟨3916048401459463107363977, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10442795737225234952970605 3916048401459463107363977)
                      ·
                        rfl

theorem cell23_7626477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 2, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 2, 3, 2, 2, 1, 3].length) (baseStart_7626477 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7626477 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7626477 prefixEnd_7626477 := by exact prefixLift 7626477
  have htrace : WordTrace (prefixWord ++ tailWord_7626477) baseStart_7626477 baseEnd_7626477 := by
    simpa [prefixWord, tailWord_7626477, baseEnd_7626477] using wordTrace_append hprefix tailTrace_7626477
  have hstable : (prefixWord ++ tailWord_7626477).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7626477).length < 2 ^ (prefixWord ++ tailWord_7626477).sum := by decide
  have hdescent : baseEnd_7626477 < baseStart_7626477 := by decide
  rcases family_descends (prefixWord ++ tailWord_7626477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7626483 : List Nat := [1, 1, 1, 2, 2, 3, 2, 2, 3, 4, 2]
def baseStart_7626483 : Nat := 118140960795 + 7626483 * 2 ^ 59
def prefixEnd_7626483 : Nat := 4983230072969 + 3 ^ 40 * 7626483 * 2
def baseEnd_7626483 : Nat := 3916051482343390083888949

theorem tailTrace_7626483 : CollatzResearch.WordTrace tailWord_7626483 prefixEnd_7626483 3916051482343390083888949 := by
  unfold tailWord_7626483
  simp only [CollatzResearch.WordTrace]
  refine ⟨278160686829562065444220103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185440457886374710296146735 278160686829562065444220103)
  ·
    refine ⟨417241030244343098166330155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 278160686829562065444220103 417241030244343098166330155)
    ·
      refine ⟨625861545366514647249495233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 417241030244343098166330155 625861545366514647249495233)
      ·
        refine ⟨469396159024885985437121425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 625861545366514647249495233 469396159024885985437121425)
        ·
          refine ⟨352047119268664489077841069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 469396159024885985437121425 352047119268664489077841069)
          ·
            refine ⟨132017669725749183404190401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 352047119268664489077841069 132017669725749183404190401)
            ·
              refine ⟨99013252294311887553142801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 132017669725749183404190401 99013252294311887553142801)
              ·
                refine ⟨74259939220733915664857101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 99013252294311887553142801 74259939220733915664857101)
                ·
                  refine ⟨27847477207775218374321413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 74259939220733915664857101 27847477207775218374321413)
                  ·
                    refine ⟨5221401976457853445185265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 27847477207775218374321413 5221401976457853445185265)
                    ·
                      refine ⟨3916051482343390083888949, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5221401976457853445185265 3916051482343390083888949)
                      ·
                        rfl

theorem cell23_7626483_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 2, 2, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 2, 2, 3, 4, 2].length) (baseStart_7626483 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7626483 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7626483 prefixEnd_7626483 := by exact prefixLift 7626483
  have htrace : WordTrace (prefixWord ++ tailWord_7626483) baseStart_7626483 baseEnd_7626483 := by
    simpa [prefixWord, tailWord_7626483, baseEnd_7626483] using wordTrace_append hprefix tailTrace_7626483
  have hstable : (prefixWord ++ tailWord_7626483).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7626483).length < 2 ^ (prefixWord ++ tailWord_7626483).sum := by decide
  have hdescent : baseEnd_7626483 < baseStart_7626483 := by decide
  rcases family_descends (prefixWord ++ tailWord_7626483) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7626494 : List Nat := [4, 2, 2, 1, 4, 1, 1, 1, 1, 3, 3]
def baseStart_7626494 : Nat := 118140960795 + 7626494 * 2 ^ 59
def prefixEnd_7626494 : Nat := 4983230072969 + 3 ^ 40 * 7626494 * 2
def baseEnd_7626494 : Nat := 3916057130630589540851399

theorem tailTrace_7626494 : CollatzResearch.WordTrace tailWord_7626494 prefixEnd_7626494 3916057130630589540851399 := by
  unfold tailWord_7626494
  simp only [CollatzResearch.WordTrace]
  refine ⟨34770136004065276790358817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 185440725355014809548580357 34770136004065276790358817)
  ·
    refine ⟨26077602003048957592769113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34770136004065276790358817 26077602003048957592769113)
    ·
      refine ⟨19558201502286718194576835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26077602003048957592769113 19558201502286718194576835)
      ·
        refine ⟨29337302253430077291865253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19558201502286718194576835 29337302253430077291865253)
        ·
          refine ⟨5500744172518139492224735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 29337302253430077291865253 5500744172518139492224735)
          ·
            refine ⟨8251116258777209238337103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5500744172518139492224735 8251116258777209238337103)
            ·
              refine ⟨12376674388165813857505655, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8251116258777209238337103 12376674388165813857505655)
              ·
                refine ⟨18565011582248720786258483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12376674388165813857505655 18565011582248720786258483)
                ·
                  refine ⟨27847517373373081179387725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18565011582248720786258483 27847517373373081179387725)
                  ·
                    refine ⟨10442819015014905442270397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27847517373373081179387725 10442819015014905442270397)
                    ·
                      refine ⟨3916057130630589540851399, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10442819015014905442270397 3916057130630589540851399)
                      ·
                        rfl

theorem cell23_7626494_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 4, 1, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 4, 1, 1, 1, 1, 3, 3].length) (baseStart_7626494 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7626494 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7626494 prefixEnd_7626494 := by exact prefixLift 7626494
  have htrace : WordTrace (prefixWord ++ tailWord_7626494) baseStart_7626494 baseEnd_7626494 := by
    simpa [prefixWord, tailWord_7626494, baseEnd_7626494] using wordTrace_append hprefix tailTrace_7626494
  have hstable : (prefixWord ++ tailWord_7626494).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7626494).length < 2 ^ (prefixWord ++ tailWord_7626494).sum := by decide
  have hdescent : baseEnd_7626494 < baseStart_7626494 := by decide
  rcases family_descends (prefixWord ++ tailWord_7626494) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7626543 : List Nat := [1, 1, 2, 1, 2, 1, 2, 3, 1, 7, 2]
def baseStart_7626543 : Nat := 118140960795 + 7626543 * 2 ^ 59
def prefixEnd_7626543 : Nat := 4983230072969 + 3 ^ 40 * 7626543 * 2
def baseEnd_7626543 : Nat := 3916082291182659849138673

theorem tailTrace_7626543 : CollatzResearch.WordTrace tailWord_7626543 prefixEnd_7626543 3916082291182659849138673 := by
  unfold tailWord_7626543
  simp only [CollatzResearch.WordTrace]
  refine ⟨278162875209344695691404283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185441916806229797127602855 278162875209344695691404283)
  ·
    refine ⟨417244312814017043537106425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 278162875209344695691404283 417244312814017043537106425)
    ·
      refine ⟨312933234610512782652829819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 417244312814017043537106425 312933234610512782652829819)
      ·
        refine ⟨469399851915769173979244729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 312933234610512782652829819 469399851915769173979244729)
        ·
          refine ⟨352049888936826880484433547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 469399851915769173979244729 352049888936826880484433547)
          ·
            refine ⟨528074833405240320726650321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 352049888936826880484433547 528074833405240320726650321)
            ·
              refine ⟨396056125053930240544987741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 528074833405240320726650321 396056125053930240544987741)
              ·
                refine ⟨148521046895223840204370403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 396056125053930240544987741 148521046895223840204370403)
                ·
                  refine ⟨222781570342835760306555605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 148521046895223840204370403 222781570342835760306555605)
                  ·
                    refine ⟨5221443054910213132184897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 222781570342835760306555605 5221443054910213132184897)
                    ·
                      refine ⟨3916082291182659849138673, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5221443054910213132184897 3916082291182659849138673)
                      ·
                        rfl

theorem cell23_7626543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 2, 3, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 2, 3, 1, 7, 2].length) (baseStart_7626543 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7626543 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7626543 prefixEnd_7626543 := by exact prefixLift 7626543
  have htrace : WordTrace (prefixWord ++ tailWord_7626543) baseStart_7626543 baseEnd_7626543 := by
    simpa [prefixWord, tailWord_7626543, baseEnd_7626543] using wordTrace_append hprefix tailTrace_7626543
  have hstable : (prefixWord ++ tailWord_7626543).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7626543).length < 2 ^ (prefixWord ++ tailWord_7626543).sum := by decide
  have hdescent : baseEnd_7626543 < baseStart_7626543 := by decide
  rcases family_descends (prefixWord ++ tailWord_7626543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7626600 : List Nat := [2, 1, 4, 2, 1, 1, 2, 3, 3, 4]
def baseStart_7626600 : Nat := 118140960795 + 7626600 * 2 ^ 59
def prefixEnd_7626600 : Nat := 4983230072969 + 3 ^ 40 * 7626600 * 2
def baseEnd_7626600 : Nat := 1305370519859988708708637

theorem tailTrace_7626600 : CollatzResearch.WordTrace tailWord_7626600 prefixEnd_7626600 1305370519859988708708637 := by
  unfold tailWord_7626600
  simp only [CollatzResearch.WordTrace]
  refine ⟨139082477085069097213114627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 185443302780092129617486169 139082477085069097213114627)
  ·
    refine ⟨208623715627603645819671941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139082477085069097213114627 208623715627603645819671941)
    ·
      refine ⟨39116946680175683591188489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 208623715627603645819671941 39116946680175683591188489)
      ·
        refine ⟨29337710010131762693391367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39116946680175683591188489 29337710010131762693391367)
        ·
          refine ⟨44006565015197644040087051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29337710010131762693391367 44006565015197644040087051)
          ·
            refine ⟨66009847522796466060130577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44006565015197644040087051 66009847522796466060130577)
            ·
              refine ⟨49507385642097349545097933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 66009847522796466060130577 49507385642097349545097933)
              ·
                refine ⟨18565269615786506079411725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 49507385642097349545097933 18565269615786506079411725)
                ·
                  refine ⟨6961976105919939779779397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18565269615786506079411725 6961976105919939779779397)
                  ·
                    refine ⟨1305370519859988708708637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6961976105919939779779397 1305370519859988708708637)
                    ·
                      rfl

theorem cell23_7626600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 2, 3, 3, 4].length) (baseStart_7626600 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7626600 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7626600 prefixEnd_7626600 := by exact prefixLift 7626600
  have htrace : WordTrace (prefixWord ++ tailWord_7626600) baseStart_7626600 baseEnd_7626600 := by
    simpa [prefixWord, tailWord_7626600, baseEnd_7626600] using wordTrace_append hprefix tailTrace_7626600
  have hstable : (prefixWord ++ tailWord_7626600).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7626600).length < 2 ^ (prefixWord ++ tailWord_7626600).sum := by decide
  have hdescent : baseEnd_7626600 < baseStart_7626600 := by decide
  rcases family_descends (prefixWord ++ tailWord_7626600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7626627 : List Nat := [1, 1, 1, 3, 4, 4, 1, 1, 2, 2, 3]
def baseStart_7626627 : Nat := 118140960795 + 7626627 * 2 ^ 59
def prefixEnd_7626627 : Nat := 4983230072969 + 3 ^ 40 * 7626627 * 2
def baseEnd_7626627 : Nat := 3916125423557637520488287

theorem tailTrace_7626627 : CollatzResearch.WordTrace tailWord_7626627 prefixEnd_7626627 3916125423557637520488287 := by
  unfold tailWord_7626627
  simp only [CollatzResearch.WordTrace]
  refine ⟨278165938941040378037462135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185443959294026918691641423 278165938941040378037462135)
  ·
    refine ⟨417248908411560567056193203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 278165938941040378037462135 417248908411560567056193203)
    ·
      refine ⟨625873362617340850584289805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 417248908411560567056193203 625873362617340850584289805)
      ·
        refine ⟨234702510981502818969108677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 625873362617340850584289805 234702510981502818969108677)
        ·
          refine ⟨44006720809031778556707877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 234702510981502818969108677 44006720809031778556707877)
          ·
            refine ⟨8251260151693458479382727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 44006720809031778556707877 8251260151693458479382727)
            ·
              refine ⟨12376890227540187719074091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8251260151693458479382727 12376890227540187719074091)
              ·
                refine ⟨18565335341310281578611137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12376890227540187719074091 18565335341310281578611137)
                ·
                  refine ⟨13924001505982711183958353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18565335341310281578611137 13924001505982711183958353)
                  ·
                    refine ⟨10443001129487033387968765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13924001505982711183958353 10443001129487033387968765)
                    ·
                      refine ⟨3916125423557637520488287, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10443001129487033387968765 3916125423557637520488287)
                      ·
                        rfl

theorem cell23_7626627_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 4, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 4, 1, 1, 2, 2, 3].length) (baseStart_7626627 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7626627 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7626627 prefixEnd_7626627 := by exact prefixLift 7626627
  have htrace : WordTrace (prefixWord ++ tailWord_7626627) baseStart_7626627 baseEnd_7626627 := by
    simpa [prefixWord, tailWord_7626627, baseEnd_7626627] using wordTrace_append hprefix tailTrace_7626627
  have hstable : (prefixWord ++ tailWord_7626627).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7626627).length < 2 ^ (prefixWord ++ tailWord_7626627).sum := by decide
  have hdescent : baseEnd_7626627 < baseStart_7626627 := by decide
  rcases family_descends (prefixWord ++ tailWord_7626627) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7626677 : List Nat := [1, 3, 3, 2, 1, 3, 2, 2, 1, 5]
def baseStart_7626677 : Nat := 118140960795 + 7626677 * 2 ^ 59
def prefixEnd_7626677 : Nat := 4983230072969 + 3 ^ 40 * 7626677 * 2
def baseEnd_7626677 : Nat := 1305383699196787441621019

theorem tailTrace_7626677 : CollatzResearch.WordTrace tailWord_7626677 prefixEnd_7626677 1305383699196787441621019 := by
  unfold tailWord_7626677
  simp only [CollatzResearch.WordTrace]
  refine ⟨278167762590859236576782285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185445175060572824384521523 278167762590859236576782285)
  ·
    refine ⟨104312910971572213716293357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 278167762590859236576782285 104312910971572213716293357)
    ·
      refine ⟨39117341614339580143610009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 104312910971572213716293357 39117341614339580143610009)
      ·
        refine ⟨29338006210754685107707507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39117341614339580143610009 29338006210754685107707507)
        ·
          refine ⟨44007009316132027661561261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29338006210754685107707507 44007009316132027661561261)
          ·
            refine ⟨16502628493549510373085473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 44007009316132027661561261 16502628493549510373085473)
            ·
              refine ⟨12376971370162132779814105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16502628493549510373085473 12376971370162132779814105)
              ·
                refine ⟨9282728527621599584860579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12376971370162132779814105 9282728527621599584860579)
                ·
                  refine ⟨13924092791432399377290869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9282728527621599584860579 13924092791432399377290869)
                  ·
                    refine ⟨1305383699196787441621019, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13924092791432399377290869 1305383699196787441621019)
                    ·
                      rfl

theorem cell23_7626677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 3, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 3, 2, 2, 1, 5].length) (baseStart_7626677 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7626677 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7626677 prefixEnd_7626677 := by exact prefixLift 7626677
  have htrace : WordTrace (prefixWord ++ tailWord_7626677) baseStart_7626677 baseEnd_7626677 := by
    simpa [prefixWord, tailWord_7626677, baseEnd_7626677] using wordTrace_append hprefix tailTrace_7626677
  have hstable : (prefixWord ++ tailWord_7626677).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7626677).length < 2 ^ (prefixWord ++ tailWord_7626677).sum := by decide
  have hdescent : baseEnd_7626677 < baseStart_7626677 := by decide
  rcases family_descends (prefixWord ++ tailWord_7626677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7626680 : List Nat := [2, 1, 2, 1, 2, 3, 1, 1, 2, 6, 2]
def baseStart_7626680 : Nat := 118140960795 + 7626680 * 2 ^ 59
def prefixEnd_7626680 : Nat := 4983230072969 + 3 ^ 40 * 7626680 * 2
def baseEnd_7626680 : Nat := 3916152638032325813125543

theorem tailTrace_7626680 : CollatzResearch.WordTrace tailWord_7626680 prefixEnd_7626680 3916152638032325813125543 := by
  unfold tailWord_7626680
  simp only [CollatzResearch.WordTrace]
  refine ⟨139083936004924184044570747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 185445248006565578726094329 139083936004924184044570747)
  ·
    refine ⟨208625904007386276066856121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139083936004924184044570747 208625904007386276066856121)
    ·
      refine ⟨156469428005539707050142091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 208625904007386276066856121 156469428005539707050142091)
      ·
        refine ⟨234704142008309560575213137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 156469428005539707050142091 234704142008309560575213137)
        ·
          refine ⟨176028106506232170431409853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 234704142008309560575213137 176028106506232170431409853)
          ·
            refine ⟨66010539939837063911778695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 176028106506232170431409853 66010539939837063911778695)
            ·
              refine ⟨99015809909755595867668043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66010539939837063911778695 99015809909755595867668043)
              ·
                refine ⟨148523714864633393801502065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 99015809909755595867668043 148523714864633393801502065)
                ·
                  refine ⟨111392786148475045351126549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 148523714864633393801502065 111392786148475045351126549)
                  ·
                    refine ⟨5221536850709767750834057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 111392786148475045351126549 5221536850709767750834057)
                    ·
                      refine ⟨3916152638032325813125543, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5221536850709767750834057 3916152638032325813125543)
                      ·
                        rfl

theorem cell23_7626680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 1, 1, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 1, 1, 2, 6, 2].length) (baseStart_7626680 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7626680 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7626680 prefixEnd_7626680 := by exact prefixLift 7626680
  have htrace : WordTrace (prefixWord ++ tailWord_7626680) baseStart_7626680 baseEnd_7626680 := by
    simpa [prefixWord, tailWord_7626680, baseEnd_7626680] using wordTrace_append hprefix tailTrace_7626680
  have hstable : (prefixWord ++ tailWord_7626680).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7626680).length < 2 ^ (prefixWord ++ tailWord_7626680).sum := by decide
  have hdescent : baseEnd_7626680 < baseStart_7626680 := by decide
  rcases family_descends (prefixWord ++ tailWord_7626680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7626700 : List Nat := [2, 2, 1, 4, 1, 2, 1, 3, 1, 1, 5]
def baseStart_7626700 : Nat := 118140960795 + 7626700 * 2 ^ 59
def prefixEnd_7626700 : Nat := 4983230072969 + 3 ^ 40 * 7626700 * 2
def baseEnd_7626700 : Nat := 3916162907645415734875451

theorem tailTrace_7626700 : CollatzResearch.WordTrace tailWord_7626700 prefixEnd_7626700 3916162907645415734875451 := by
  unfold tailWord_7626700
  simp only [CollatzResearch.WordTrace]
  refine ⟨139084300734887955752434777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 185445734313183941003246369 139084300734887955752434777)
  ·
    refine ⟨104313225551165966814326083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 139084300734887955752434777 104313225551165966814326083)
    ·
      refine ⟨156469838326748950221489125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104313225551165966814326083 156469838326748950221489125)
      ·
        refine ⟨29338094686265428166529211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 156469838326748950221489125 29338094686265428166529211)
        ·
          refine ⟨44007142029398142249793817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29338094686265428166529211 44007142029398142249793817)
          ·
            refine ⟨33005356522048606687345363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44007142029398142249793817 33005356522048606687345363)
            ·
              refine ⟨49508034783072910031018045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33005356522048606687345363 49508034783072910031018045)
              ·
                refine ⟨18565513043652341261631767, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 49508034783072910031018045 18565513043652341261631767)
                ·
                  refine ⟨27848269565478511892447651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18565513043652341261631767 27848269565478511892447651)
                  ·
                    refine ⟨41772404348217767838671477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27848269565478511892447651 41772404348217767838671477)
                    ·
                      refine ⟨3916162907645415734875451, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41772404348217767838671477 3916162907645415734875451)
                      ·
                        rfl

theorem cell23_7626700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 2, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 2, 1, 3, 1, 1, 5].length) (baseStart_7626700 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7626700 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7626700 prefixEnd_7626700 := by exact prefixLift 7626700
  have htrace : WordTrace (prefixWord ++ tailWord_7626700) baseStart_7626700 baseEnd_7626700 := by
    simpa [prefixWord, tailWord_7626700, baseEnd_7626700] using wordTrace_append hprefix tailTrace_7626700
  have hstable : (prefixWord ++ tailWord_7626700).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7626700).length < 2 ^ (prefixWord ++ tailWord_7626700).sum := by decide
  have hdescent : baseEnd_7626700 < baseStart_7626700 := by decide
  rcases family_descends (prefixWord ++ tailWord_7626700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7626734 : List Nat := [4, 1, 2, 1, 3, 1, 3, 2, 1, 2, 3]
def baseStart_7626734 : Nat := 118140960795 + 7626734 * 2 ^ 59
def prefixEnd_7626734 : Nat := 4983230072969 + 3 ^ 40 * 7626734 * 2
def baseEnd_7626734 : Nat := 3916180365987668601850295

theorem tailTrace_7626734 : CollatzResearch.WordTrace tailWord_7626734 prefixEnd_7626734 3916180365987668601850295 := by
  unfold tailWord_7626734
  simp only [CollatzResearch.WordTrace]
  refine ⟨34771230193956591913950907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 185446561034435156874404837 34771230193956591913950907)
  ·
    refine ⟨52156845290934887870926361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34771230193956591913950907 52156845290934887870926361)
    ·
      refine ⟨39117633968201165903194771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52156845290934887870926361 39117633968201165903194771)
      ·
        refine ⟨58676450952301748854792157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39117633968201165903194771 58676450952301748854792157)
        ·
          refine ⟨22003669107113155820547059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 58676450952301748854792157 22003669107113155820547059)
          ·
            refine ⟨33005503660669733730820589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22003669107113155820547059 33005503660669733730820589)
            ·
              refine ⟨12377063872751150149057721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33005503660669733730820589 12377063872751150149057721)
              ·
                refine ⟨9282797904563362611793291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12377063872751150149057721 9282797904563362611793291)
                ·
                  refine ⟨13924196856845043917689937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9282797904563362611793291 13924196856845043917689937)
                  ·
                    refine ⟨10443147642633782938267453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13924196856845043917689937 10443147642633782938267453)
                    ·
                      refine ⟨3916180365987668601850295, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10443147642633782938267453 3916180365987668601850295)
                      ·
                        rfl

theorem cell23_7626734_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 1, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 1, 3, 2, 1, 2, 3].length) (baseStart_7626734 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7626734 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7626734 prefixEnd_7626734 := by exact prefixLift 7626734
  have htrace : WordTrace (prefixWord ++ tailWord_7626734) baseStart_7626734 baseEnd_7626734 := by
    simpa [prefixWord, tailWord_7626734, baseEnd_7626734] using wordTrace_append hprefix tailTrace_7626734
  have hstable : (prefixWord ++ tailWord_7626734).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7626734).length < 2 ^ (prefixWord ++ tailWord_7626734).sum := by decide
  have hdescent : baseEnd_7626734 < baseStart_7626734 := by decide
  rcases family_descends (prefixWord ++ tailWord_7626734) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7626764 : List Nat := [2, 2, 1, 2, 3, 1, 4, 2, 2, 1, 3]
def baseStart_7626764 : Nat := 118140960795 + 7626764 * 2 ^ 59
def prefixEnd_7626764 : Nat := 4983230072969 + 3 ^ 40 * 7626764 * 2
def baseEnd_7626764 : Nat := 3916195770407303484475157

theorem tailTrace_7626764 : CollatzResearch.WordTrace tailWord_7626764 prefixEnd_7626764 3916195770407303484475157 := by
  unfold tailWord_7626764
  simp only [CollatzResearch.WordTrace]
  refine ⟨139085467870772025217599673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 185447290494362700290132897 139085467870772025217599673)
  ·
    refine ⟨104314100903079018913199755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 139085467870772025217599673 104314100903079018913199755)
    ·
      refine ⟨156471151354618528369799633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104314100903079018913199755 156471151354618528369799633)
      ·
        refine ⟨117353363515963896277349725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 156471151354618528369799633 117353363515963896277349725)
        ·
          refine ⟨44007511318486461104006147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 117353363515963896277349725 44007511318486461104006147)
          ·
            refine ⟨66011266977729691656009221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44007511318486461104006147 66011266977729691656009221)
            ·
              refine ⟨12377112558324317185501729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 66011266977729691656009221 12377112558324317185501729)
              ·
                refine ⟨9282834418743237889126297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12377112558324317185501729 9282834418743237889126297)
                ·
                  refine ⟨6962125814057428416844723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9282834418743237889126297 6962125814057428416844723)
                  ·
                    refine ⟨10443188721086142625267085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6962125814057428416844723 10443188721086142625267085)
                    ·
                      refine ⟨3916195770407303484475157, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10443188721086142625267085 3916195770407303484475157)
                      ·
                        rfl

theorem cell23_7626764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 4, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 4, 2, 2, 1, 3].length) (baseStart_7626764 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7626764 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7626764 prefixEnd_7626764 := by exact prefixLift 7626764
  have htrace : WordTrace (prefixWord ++ tailWord_7626764) baseStart_7626764 baseEnd_7626764 := by
    simpa [prefixWord, tailWord_7626764, baseEnd_7626764] using wordTrace_append hprefix tailTrace_7626764
  have hstable : (prefixWord ++ tailWord_7626764).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7626764).length < 2 ^ (prefixWord ++ tailWord_7626764).sum := by decide
  have hdescent : baseEnd_7626764 < baseStart_7626764 := by decide
  rcases family_descends (prefixWord ++ tailWord_7626764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7626780 : List Nat := [2, 2, 3, 1, 3, 1, 1, 1, 1, 8]
def baseStart_7626780 : Nat := 118140960795 + 7626780 * 2 ^ 59
def prefixEnd_7626780 : Nat := 4983230072969 + 3 ^ 40 * 7626780 * 2
def baseEnd_7626780 : Nat := 1305401328699258473958361

theorem tailTrace_7626780 : CollatzResearch.WordTrace tailWord_7626780 prefixEnd_7626780 1305401328699258473958361 := by
  unfold tailWord_7626780
  simp only [CollatzResearch.WordTrace]
  refine ⟨139085759654743042583890897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 185447679539657390111854529 139085759654743042583890897)
  ·
    refine ⟨104314319741057281937918173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 139085759654743042583890897 104314319741057281937918173)
    ·
      refine ⟨39117869902896480726719315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 104314319741057281937918173 39117869902896480726719315)
      ·
        refine ⟨58676804854344721090078973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39117869902896480726719315 58676804854344721090078973)
        ·
          refine ⟨22003801820379270408779615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 58676804854344721090078973 22003801820379270408779615)
          ·
            refine ⟨33005702730568905613169423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22003801820379270408779615 33005702730568905613169423)
            ·
              refine ⟨49508554095853358419754135, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33005702730568905613169423 49508554095853358419754135)
              ·
                refine ⟨74262831143780037629631203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49508554095853358419754135 74262831143780037629631203)
                ·
                  refine ⟨111394246715670056444446805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 74262831143780037629631203 111394246715670056444446805)
                  ·
                    refine ⟨1305401328699258473958361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 111394246715670056444446805 1305401328699258473958361)
                    ·
                      rfl

theorem cell23_7626780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 1, 1, 1, 1, 8].length) (baseStart_7626780 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7626780 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7626780 prefixEnd_7626780 := by exact prefixLift 7626780
  have htrace : WordTrace (prefixWord ++ tailWord_7626780) baseStart_7626780 baseEnd_7626780 := by
    simpa [prefixWord, tailWord_7626780, baseEnd_7626780] using wordTrace_append hprefix tailTrace_7626780
  have hstable : (prefixWord ++ tailWord_7626780).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7626780).length < 2 ^ (prefixWord ++ tailWord_7626780).sum := by decide
  have hdescent : baseEnd_7626780 < baseStart_7626780 := by decide
  rcases family_descends (prefixWord ++ tailWord_7626780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7626808 : List Nat := [2, 1, 2, 1, 6, 2, 2, 1, 1, 3, 2]
def baseStart_7626808 : Nat := 118140960795 + 7626808 * 2 ^ 59
def prefixEnd_7626808 : Nat := 4983230072969 + 3 ^ 40 * 7626808 * 2
def baseEnd_7626808 : Nat := 3916218363556101312324955

theorem tailTrace_7626808 : CollatzResearch.WordTrace tailWord_7626808 prefixEnd_7626808 3916218363556101312324955 := by
  unfold tailWord_7626808
  simp only [CollatzResearch.WordTrace]
  refine ⟨139086270276692322974900539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 185448360368923097299867385 139086270276692322974900539)
  ·
    refine ⟨208629405415038484462350809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139086270276692322974900539 208629405415038484462350809)
    ·
      refine ⟨156472054061278863346763107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 208629405415038484462350809 156472054061278863346763107)
      ·
        refine ⟨234708081091918295020144661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 156472054061278863346763107 234708081091918295020144661)
        ·
          refine ⟨11001941301183670079069281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 234708081091918295020144661 11001941301183670079069281)
          ·
            refine ⟨8251455975887752559301961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11001941301183670079069281 8251455975887752559301961)
            ·
              refine ⟨6188591981915814419476471, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8251455975887752559301961 6188591981915814419476471)
              ·
                refine ⟨9282887972873721629214707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6188591981915814419476471 9282887972873721629214707)
                ·
                  refine ⟨13924331959310582443822061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9282887972873721629214707 13924331959310582443822061)
                  ·
                    refine ⟨5221624484741468416433273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13924331959310582443822061 5221624484741468416433273)
                    ·
                      refine ⟨3916218363556101312324955, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5221624484741468416433273 3916218363556101312324955)
                      ·
                        rfl

theorem cell23_7626808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 6, 2, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 6, 2, 2, 1, 1, 3, 2].length) (baseStart_7626808 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7626808 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7626808 prefixEnd_7626808 := by exact prefixLift 7626808
  have htrace : WordTrace (prefixWord ++ tailWord_7626808) baseStart_7626808 baseEnd_7626808 := by
    simpa [prefixWord, tailWord_7626808, baseEnd_7626808] using wordTrace_append hprefix tailTrace_7626808
  have hstable : (prefixWord ++ tailWord_7626808).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7626808).length < 2 ^ (prefixWord ++ tailWord_7626808).sum := by decide
  have hdescent : baseEnd_7626808 < baseStart_7626808 := by decide
  rcases family_descends (prefixWord ++ tailWord_7626808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7626817 : List Nat := [1, 2, 5, 1, 2, 1, 1, 2, 2, 2, 4]
def baseStart_7626817 : Nat := 118140960795 + 7626817 * 2 ^ 59
def prefixEnd_7626817 : Nat := 4983230072969 + 3 ^ 40 * 7626817 * 2
def baseEnd_7626817 : Nat := 3916222984881991777112413

theorem tailTrace_7626817 : CollatzResearch.WordTrace tailWord_7626817 prefixEnd_7626817 3916222984881991777112413 := by
  unfold tailWord_7626817
  simp only [CollatzResearch.WordTrace]
  refine ⟨278172868810352040486878705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185448579206901360324585803 278172868810352040486878705)
  ·
    refine ⟨208629651607764030365159029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 278172868810352040486878705 208629651607764030365159029)
    ·
      refine ⟨19559029838227877846733659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 208629651607764030365159029 19559029838227877846733659)
      ·
        refine ⟨29338544757341816770100489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19559029838227877846733659 29338544757341816770100489)
        ·
          refine ⟨22003908568006362577575367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29338544757341816770100489 22003908568006362577575367)
          ·
            refine ⟨33005862852009543866363051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22003908568006362577575367 33005862852009543866363051)
            ·
              refine ⟨49508794278014315799544577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33005862852009543866363051 49508794278014315799544577)
              ·
                refine ⟨37131595708510736849658433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49508794278014315799544577 37131595708510736849658433)
                ·
                  refine ⟨27848696781383052637243825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37131595708510736849658433 27848696781383052637243825)
                  ·
                    refine ⟨20886522586037289477932869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27848696781383052637243825 20886522586037289477932869)
                    ·
                      refine ⟨3916222984881991777112413, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20886522586037289477932869 3916222984881991777112413)
                      ·
                        rfl

theorem cell23_7626817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 1, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 1, 1, 2, 2, 2, 4].length) (baseStart_7626817 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7626817 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7626817 prefixEnd_7626817 := by exact prefixLift 7626817
  have htrace : WordTrace (prefixWord ++ tailWord_7626817) baseStart_7626817 baseEnd_7626817 := by
    simpa [prefixWord, tailWord_7626817, baseEnd_7626817] using wordTrace_append hprefix tailTrace_7626817
  have hstable : (prefixWord ++ tailWord_7626817).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7626817).length < 2 ^ (prefixWord ++ tailWord_7626817).sum := by decide
  have hdescent : baseEnd_7626817 < baseStart_7626817 := by decide
  rcases family_descends (prefixWord ++ tailWord_7626817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7626837 : List Nat := [1, 3, 2, 2, 1, 3, 2, 1, 2, 3, 3]
def baseStart_7626837 : Nat := 118140960795 + 7626837 * 2 ^ 59
def prefixEnd_7626837 : Nat := 4983230072969 + 3 ^ 40 * 7626837 * 2
def baseEnd_7626837 : Nat := 3916233254495081698862321

theorem tailTrace_7626837 : CollatzResearch.WordTrace tailWord_7626837 prefixEnd_7626837 3916233254495081698862321 := by
  unfold tailWord_7626837
  simp only [CollatzResearch.WordTrace]
  refine ⟨278173598270279583902606765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185449065513519722601737843 278173598270279583902606765)
  ·
    refine ⟨104315099351354843963477537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 278173598270279583902606765 104315099351354843963477537)
    ·
      refine ⟨78236324513516132972608153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 104315099351354843963477537 78236324513516132972608153)
      ·
        refine ⟨58677243385137099729456115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78236324513516132972608153 58677243385137099729456115)
        ·
          refine ⟨88015865077705649594184173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58677243385137099729456115 88015865077705649594184173)
          ·
            refine ⟨33005949404139618597819065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 88015865077705649594184173 33005949404139618597819065)
            ·
              refine ⟨24754462053104713948364299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33005949404139618597819065 24754462053104713948364299)
              ·
                refine ⟨37131693079657070922546449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24754462053104713948364299 37131693079657070922546449)
                ·
                  refine ⟨27848769809742803191909837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37131693079657070922546449 27848769809742803191909837)
                  ·
                    refine ⟨10443288678653551196966189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27848769809742803191909837 10443288678653551196966189)
                    ·
                      refine ⟨3916233254495081698862321, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10443288678653551196966189 3916233254495081698862321)
                      ·
                        rfl

theorem cell23_7626837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 3, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 3, 2, 1, 2, 3, 3].length) (baseStart_7626837 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7626837 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7626837 prefixEnd_7626837 := by exact prefixLift 7626837
  have htrace : WordTrace (prefixWord ++ tailWord_7626837) baseStart_7626837 baseEnd_7626837 := by
    simpa [prefixWord, tailWord_7626837, baseEnd_7626837] using wordTrace_append hprefix tailTrace_7626837
  have hstable : (prefixWord ++ tailWord_7626837).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7626837).length < 2 ^ (prefixWord ++ tailWord_7626837).sum := by decide
  have hdescent : baseEnd_7626837 < baseStart_7626837 := by decide
  rcases family_descends (prefixWord ++ tailWord_7626837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7626838 : List Nat := [5, 2, 2, 1, 1, 1, 3, 1, 1, 4, 2]
def baseStart_7626838 : Nat := 118140960795 + 7626838 * 2 ^ 59
def prefixEnd_7626838 : Nat := 4983230072969 + 3 ^ 40 * 7626838 * 2
def baseEnd_7626838 : Nat := 3916233767975736194949817

theorem tailTrace_7626838 : CollatzResearch.WordTrace tailWord_7626838 prefixEnd_7626838 3916233767975736194949817 := by
  unfold tailWord_7626838
  simp only [CollatzResearch.WordTrace]
  refine ⟨17385852171454747567087073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 185449089828850640715595445 17385852171454747567087073)
  ·
    refine ⟨13039389128591060675315305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17385852171454747567087073 13039389128591060675315305)
    ·
      refine ⟨9779541846443295506486479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13039389128591060675315305 9779541846443295506486479)
      ·
        refine ⟨14669312769664943259729719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9779541846443295506486479 14669312769664943259729719)
        ·
          refine ⟨22003969154497414889594579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14669312769664943259729719 22003969154497414889594579)
          ·
            refine ⟨33005953731746122334391869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22003969154497414889594579 33005953731746122334391869)
            ·
              refine ⟨12377232649404795875396951, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33005953731746122334391869 12377232649404795875396951)
              ·
                refine ⟨18565848974107193813095427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12377232649404795875396951 18565848974107193813095427)
                ·
                  refine ⟨27848773461160790719643141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18565848974107193813095427 27848773461160790719643141)
                  ·
                    refine ⟨5221645023967648259933089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 27848773461160790719643141 5221645023967648259933089)
                    ·
                      refine ⟨3916233767975736194949817, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5221645023967648259933089 3916233767975736194949817)
                      ·
                        rfl

theorem cell23_7626838_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 1, 3, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 1, 3, 1, 1, 4, 2].length) (baseStart_7626838 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7626838 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7626838 prefixEnd_7626838 := by exact prefixLift 7626838
  have htrace : WordTrace (prefixWord ++ tailWord_7626838) baseStart_7626838 baseEnd_7626838 := by
    simpa [prefixWord, tailWord_7626838, baseEnd_7626838] using wordTrace_append hprefix tailTrace_7626838
  have hstable : (prefixWord ++ tailWord_7626838).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7626838).length < 2 ^ (prefixWord ++ tailWord_7626838).sum := by decide
  have hdescent : baseEnd_7626838 < baseStart_7626838 := by decide
  rcases family_descends (prefixWord ++ tailWord_7626838) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7626840 : List Nat := [2, 1, 2, 2, 1, 4, 1, 2, 1, 7]
def baseStart_7626840 : Nat := 118140960795 + 7626840 * 2 ^ 59
def prefixEnd_7626840 : Nat := 4983230072969 + 3 ^ 40 * 7626840 * 2
def baseEnd_7626840 : Nat := 1305411598312348395708269

theorem tailTrace_7626840 : CollatzResearch.WordTrace tailWord_7626840 prefixEnd_7626840 1305411598312348395708269 := by
  unfold tailWord_7626840
  simp only [CollatzResearch.WordTrace]
  refine ⟨139086853844634357707482987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 185449138459512476943310649 139086853844634357707482987)
  ·
    refine ⟨208630280766951536561224481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139086853844634357707482987 208630280766951536561224481)
    ·
      refine ⟨156472710575213652420918361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 208630280766951536561224481 156472710575213652420918361)
      ·
        refine ⟨117354532931410239315688771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 156472710575213652420918361 117354532931410239315688771)
        ·
          refine ⟨176031799397115358973533157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 117354532931410239315688771 176031799397115358973533157)
          ·
            refine ⟨33005962386959129807537467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 176031799397115358973533157 33005962386959129807537467)
            ·
              refine ⟨49508943580438694711306201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33005962386959129807537467 49508943580438694711306201)
              ·
                refine ⟨37131707685329021033479651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49508943580438694711306201 37131707685329021033479651)
                ·
                  refine ⟨55697561527993531550219477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37131707685329021033479651 55697561527993531550219477)
                  ·
                    refine ⟨1305411598312348395708269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 55697561527993531550219477 1305411598312348395708269)
                    ·
                      rfl

theorem cell23_7626840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 4, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 4, 1, 2, 1, 7].length) (baseStart_7626840 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7626840 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7626840 prefixEnd_7626840 := by exact prefixLift 7626840
  have htrace : WordTrace (prefixWord ++ tailWord_7626840) baseStart_7626840 baseEnd_7626840 := by
    simpa [prefixWord, tailWord_7626840, baseEnd_7626840] using wordTrace_append hprefix tailTrace_7626840
  have hstable : (prefixWord ++ tailWord_7626840).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7626840).length < 2 ^ (prefixWord ++ tailWord_7626840).sum := by decide
  have hdescent : baseEnd_7626840 < baseStart_7626840 := by decide
  rcases family_descends (prefixWord ++ tailWord_7626840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7626877 : List Nat := [1, 4, 1, 1, 3, 2, 1, 1, 4, 1, 4]
def baseStart_7626877 : Nat := 118140960795 + 7626877 * 2 ^ 59
def prefixEnd_7626877 : Nat := 4983230072969 + 3 ^ 40 * 7626877 * 2
def baseEnd_7626877 : Nat := 3916253793721261542362137

theorem tailTrace_7626877 : CollatzResearch.WordTrace tailWord_7626877 prefixEnd_7626877 3916253793721261542362137 := by
  unfold tailWord_7626877
  simp only [CollatzResearch.WordTrace]
  refine ⟨278175057190134670734062885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185450038126756447156041923 278175057190134670734062885)
  ·
    refine ⟨52157823223150250762636791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 278175057190134670734062885 52157823223150250762636791)
    ·
      refine ⟨78236734834725376143955187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52157823223150250762636791 78236734834725376143955187)
      ·
        refine ⟨117355102252088064215932781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78236734834725376143955187 117355102252088064215932781)
        ·
          refine ⟨44008163344533024080974793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 117355102252088064215932781 44008163344533024080974793)
          ·
            refine ⟨33006122508399768060731095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44008163344533024080974793 33006122508399768060731095)
            ·
              refine ⟨49509183762599652091096643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33006122508399768060731095 49509183762599652091096643)
              ·
                refine ⟨74263775643899478136644965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49509183762599652091096643 74263775643899478136644965)
                ·
                  refine ⟨13924457933231152150620931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 74263775643899478136644965 13924457933231152150620931)
                  ·
                    refine ⟨20886686899846728225931397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13924457933231152150620931 20886686899846728225931397)
                    ·
                      refine ⟨3916253793721261542362137, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20886686899846728225931397 3916253793721261542362137)
                      ·
                        rfl

theorem cell23_7626877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 2, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 2, 1, 1, 4, 1, 4].length) (baseStart_7626877 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7626877 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7626877 prefixEnd_7626877 := by exact prefixLift 7626877
  have htrace : WordTrace (prefixWord ++ tailWord_7626877) baseStart_7626877 baseEnd_7626877 := by
    simpa [prefixWord, tailWord_7626877, baseEnd_7626877] using wordTrace_append hprefix tailTrace_7626877
  have hstable : (prefixWord ++ tailWord_7626877).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7626877).length < 2 ^ (prefixWord ++ tailWord_7626877).sum := by decide
  have hdescent : baseEnd_7626877 < baseStart_7626877 := by decide
  rcases family_descends (prefixWord ++ tailWord_7626877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7626954 : List Nat := [3, 1, 2, 1, 3, 1, 2, 2, 1, 5, 2]
def baseStart_7626954 : Nat := 118140960795 + 7626954 * 2 ^ 59
def prefixEnd_7626954 : Nat := 4983230072969 + 3 ^ 40 * 7626954 * 2
def baseEnd_7626954 : Nat := 3916293331731657741099283

theorem tailTrace_7626954 : CollatzResearch.WordTrace tailWord_7626954 prefixEnd_7626954 3916293331731657741099283 := by
  unfold tailWord_7626954
  simp only [CollatzResearch.WordTrace]
  refine ⟨69544466402713928221153979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 185451910407237141923077277 69544466402713928221153979)
  ·
    refine ⟨104316699604070892331730969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69544466402713928221153979 104316699604070892331730969)
    ·
      refine ⟨78237524703053169248798227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 104316699604070892331730969 78237524703053169248798227)
      ·
        refine ⟨117356287054579753873197341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78237524703053169248798227 117356287054579753873197341)
        ·
          refine ⟨44008607645467407702449003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 117356287054579753873197341 44008607645467407702449003)
          ·
            refine ⟨66012911468201111553673505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44008607645467407702449003 66012911468201111553673505)
            ·
              refine ⟨49509683601150833665255129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 66012911468201111553673505 49509683601150833665255129)
              ·
                refine ⟨37132262700863125248941347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49509683601150833665255129 37132262700863125248941347)
                ·
                  refine ⟨55698394051294687873412021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37132262700863125248941347 55698394051294687873412021)
                  ·
                    refine ⟨5221724442308876988132377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 55698394051294687873412021 5221724442308876988132377)
                    ·
                      refine ⟨3916293331731657741099283, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5221724442308876988132377 3916293331731657741099283)
                      ·
                        rfl

theorem cell23_7626954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 2, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 2, 2, 1, 5, 2].length) (baseStart_7626954 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7626954 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7626954 prefixEnd_7626954 := by exact prefixLift 7626954
  have htrace : WordTrace (prefixWord ++ tailWord_7626954) baseStart_7626954 baseEnd_7626954 := by
    simpa [prefixWord, tailWord_7626954, baseEnd_7626954] using wordTrace_append hprefix tailTrace_7626954
  have hstable : (prefixWord ++ tailWord_7626954).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7626954).length < 2 ^ (prefixWord ++ tailWord_7626954).sum := by decide
  have hdescent : baseEnd_7626954 < baseStart_7626954 := by decide
  rcases family_descends (prefixWord ++ tailWord_7626954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7626977 : List Nat := [1, 2, 3, 1, 3, 1, 1, 4, 1, 6]
def baseStart_7626977 : Nat := 118140960795 + 7626977 * 2 ^ 59
def prefixEnd_7626977 : Nat := 4983230072969 + 3 ^ 40 * 7626977 * 2
def baseEnd_7626977 : Nat := 1305435047262237050370559

theorem tailTrace_7626977 : CollatzResearch.WordTrace tailWord_7626977 prefixEnd_7626977 1305435047262237050370559 := by
  unfold tailWord_7626977
  simp only [CollatzResearch.WordTrace]
  refine ⟨278178704489772387812703185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185452469659848258541802123 278178704489772387812703185)
  ·
    refine ⟨208634028367329290859527389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 278178704489772387812703185 208634028367329290859527389)
    ·
      refine ⟨78237760637748484072322771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 208634028367329290859527389 78237760637748484072322771)
      ·
        refine ⟨117356640956622726108484157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78237760637748484072322771 117356640956622726108484157)
        ·
          refine ⟨44008740358733522290681559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 117356640956622726108484157 44008740358733522290681559)
          ·
            refine ⟨66013110538100283436022339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44008740358733522290681559 66013110538100283436022339)
            ·
              refine ⟨99019665807150425154033509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66013110538100283436022339 99019665807150425154033509)
              ·
                refine ⟨18566187338840704716381283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 99019665807150425154033509 18566187338840704716381283)
                ·
                  refine ⟨27849281008261057074571925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18566187338840704716381283 27849281008261057074571925)
                  ·
                    refine ⟨1305435047262237050370559, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27849281008261057074571925 1305435047262237050370559)
                    ·
                      rfl

theorem cell23_7626977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 1, 4, 1, 6].length) (baseStart_7626977 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7626977 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7626977 prefixEnd_7626977 := by exact prefixLift 7626977
  have htrace : WordTrace (prefixWord ++ tailWord_7626977) baseStart_7626977 baseEnd_7626977 := by
    simpa [prefixWord, tailWord_7626977, baseEnd_7626977] using wordTrace_append hprefix tailTrace_7626977
  have hstable : (prefixWord ++ tailWord_7626977).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7626977).length < 2 ^ (prefixWord ++ tailWord_7626977).sum := by decide
  have hdescent : baseEnd_7626977 < baseStart_7626977 := by decide
  rcases family_descends (prefixWord ++ tailWord_7626977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7626981 : List Nat := [1, 3, 1, 4, 2, 1, 4, 1, 1, 5]
def baseStart_7626981 : Nat := 118140960795 + 7626981 * 2 ^ 59
def prefixEnd_7626981 : Nat := 4983230072969 + 3 ^ 40 * 7626981 * 2
def baseEnd_7626981 : Nat := 1305435731903109711820553

theorem tailTrace_7626981 : CollatzResearch.WordTrace tailWord_7626981 prefixEnd_7626981 1305435731903109711820553 := by
  unfold tailWord_7626981
  simp only [CollatzResearch.WordTrace]
  refine ⟨278178850381757896495848797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185452566921171930997232531 278178850381757896495848797)
  ·
    refine ⟨104317068893159211185943299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 278178850381757896495848797 104317068893159211185943299)
    ·
      refine ⟨156475603339738816778914949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104317068893159211185943299 156475603339738816778914949)
      ·
        refine ⟨29339175626201028146046553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 156475603339738816778914949 29339175626201028146046553)
        ·
          refine ⟨22004381719650771109534915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29339175626201028146046553 22004381719650771109534915)
          ·
            refine ⟨33006572579476156664302373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22004381719650771109534915 33006572579476156664302373)
            ·
              refine ⟨6188732358651779374556695, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 33006572579476156664302373 6188732358651779374556695)
              ·
                refine ⟨9283098537977669061835043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6188732358651779374556695 9283098537977669061835043)
                ·
                  refine ⟨13924647806966503592752565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9283098537977669061835043 13924647806966503592752565)
                  ·
                    refine ⟨1305435731903109711820553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13924647806966503592752565 1305435731903109711820553)
                    ·
                      rfl

theorem cell23_7626981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 1, 4, 1, 1, 5].length) (baseStart_7626981 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7626981 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7626981 prefixEnd_7626981 := by exact prefixLift 7626981
  have htrace : WordTrace (prefixWord ++ tailWord_7626981) baseStart_7626981 baseEnd_7626981 := by
    simpa [prefixWord, tailWord_7626981, baseEnd_7626981] using wordTrace_append hprefix tailTrace_7626981
  have hstable : (prefixWord ++ tailWord_7626981).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7626981).length < 2 ^ (prefixWord ++ tailWord_7626981).sum := by decide
  have hdescent : baseEnd_7626981 < baseStart_7626981 := by decide
  rcases family_descends (prefixWord ++ tailWord_7626981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7626987 : List Nat := [1, 1, 1, 1, 2, 5, 2, 3, 1, 1, 5]
def baseStart_7626987 : Nat := 118140960795 + 7626987 * 2 ^ 59
def prefixEnd_7626987 : Nat := 4983230072969 + 3 ^ 40 * 7626987 * 2
def baseEnd_7626987 : Nat := 3916310276593256111986631

theorem tailTrace_7626987 : CollatzResearch.WordTrace tailWord_7626987 prefixEnd_7626987 3916310276593256111986631 := by
  unfold tailWord_7626987
  simp only [CollatzResearch.WordTrace]
  refine ⟨278179069219736159520567215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185452712813157439680378143 278179069219736159520567215)
  ·
    refine ⟨417268603829604239280850823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 278179069219736159520567215 417268603829604239280850823)
    ·
      refine ⟨625902905744406358921276235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 417268603829604239280850823 625902905744406358921276235)
      ·
        refine ⟨938854358616609538381914353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 625902905744406358921276235 938854358616609538381914353)
        ·
          refine ⟨704140768962457153786435765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 938854358616609538381914353 704140768962457153786435765)
          ·
            refine ⟨66013197090230358167478353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 704140768962457153786435765 66013197090230358167478353)
            ·
              refine ⟨49509897817672768625608765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 66013197090230358167478353 49509897817672768625608765)
              ·
                refine ⟨18566211681627288234603287, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 49509897817672768625608765 18566211681627288234603287)
                ·
                  refine ⟨27849317522440932351904931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18566211681627288234603287 27849317522440932351904931)
                  ·
                    refine ⟨41773976283661398527857397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27849317522440932351904931 41773976283661398527857397)
                    ·
                      refine ⟨3916310276593256111986631, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41773976283661398527857397 3916310276593256111986631)
                      ·
                        rfl

theorem cell23_7626987_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 2, 3, 1, 1, 5].length) (baseStart_7626987 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7626987 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7626987 prefixEnd_7626987 := by exact prefixLift 7626987
  have htrace : WordTrace (prefixWord ++ tailWord_7626987) baseStart_7626987 baseEnd_7626987 := by
    simpa [prefixWord, tailWord_7626987, baseEnd_7626987] using wordTrace_append hprefix tailTrace_7626987
  have hstable : (prefixWord ++ tailWord_7626987).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7626987).length < 2 ^ (prefixWord ++ tailWord_7626987).sum := by decide
  have hdescent : baseEnd_7626987 < baseStart_7626987 := by decide
  rcases family_descends (prefixWord ++ tailWord_7626987) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7627004 : List Nat := [2, 2, 2, 1, 4, 2, 1, 2, 1, 1, 5]
def baseStart_7627004 : Nat := 118140960795 + 7627004 * 2 ^ 59
def prefixEnd_7627004 : Nat := 4983230072969 + 3 ^ 40 * 7627004 * 2
def baseEnd_7627004 : Nat := 3916319005764382545474053

theorem tailTrace_7627004 : CollatzResearch.WordTrace tailWord_7627004 prefixEnd_7627004 3916319005764382545474053 := by
  unfold tailWord_7627004
  simp only [CollatzResearch.WordTrace]
  refine ⟨139089844630337285711968033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 185453126173783047615957377 139089844630337285711968033)
  ·
    refine ⟨104317383472752964283976025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 139089844630337285711968033 104317383472752964283976025)
    ·
      refine ⟨78238037604564723212982019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 104317383472752964283976025 78238037604564723212982019)
      ·
        refine ⟨117357056406847084819473029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78238037604564723212982019 117357056406847084819473029)
        ·
          refine ⟨22004448076283828403651193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 117357056406847084819473029 22004448076283828403651193)
          ·
            refine ⟨16503336057212871302738395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22004448076283828403651193 16503336057212871302738395)
            ·
              refine ⟨24755004085819306954107593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16503336057212871302738395 24755004085819306954107593)
              ·
                refine ⟨18566253064364480215580695, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24755004085819306954107593 18566253064364480215580695)
                ·
                  refine ⟨27849379596546720323371043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18566253064364480215580695 27849379596546720323371043)
                  ·
                    refine ⟨41774069394820080485056565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27849379596546720323371043 41774069394820080485056565)
                    ·
                      refine ⟨3916319005764382545474053, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41774069394820080485056565 3916319005764382545474053)
                      ·
                        rfl

theorem cell23_7627004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 2, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 2, 1, 2, 1, 1, 5].length) (baseStart_7627004 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7627004 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7627004 prefixEnd_7627004 := by exact prefixLift 7627004
  have htrace : WordTrace (prefixWord ++ tailWord_7627004) baseStart_7627004 baseEnd_7627004 := by
    simpa [prefixWord, tailWord_7627004, baseEnd_7627004] using wordTrace_append hprefix tailTrace_7627004
  have hstable : (prefixWord ++ tailWord_7627004).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7627004).length < 2 ^ (prefixWord ++ tailWord_7627004).sum := by decide
  have hdescent : baseEnd_7627004 < baseStart_7627004 := by decide
  rcases family_descends (prefixWord ++ tailWord_7627004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7627011 : List Nat := [1, 1, 1, 3, 2, 3, 5, 1, 2, 4]
def baseStart_7627011 : Nat := 118140960795 + 7627011 * 2 ^ 59
def prefixEnd_7627011 : Nat := 4983230072969 + 3 ^ 40 * 7627011 * 2
def baseEnd_7627011 : Nat := 1305440866709654672695507

theorem tailTrace_7627011 : CollatzResearch.WordTrace tailWord_7627011 prefixEnd_7627011 1305440866709654672695507 := by
  unfold tailWord_7627011
  simp only [CollatzResearch.WordTrace]
  refine ⟨278179944571649211619440887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185453296381099474412960591 278179944571649211619440887)
  ·
    refine ⟨417269916857473817429161331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 278179944571649211619440887 417269916857473817429161331)
    ·
      refine ⟨625904875286210726143741997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 417269916857473817429161331 625904875286210726143741997)
      ·
        refine ⟨234714328232329022303903249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 625904875286210726143741997 234714328232329022303903249)
        ·
          refine ⟨176035746174246766727927437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 234714328232329022303903249 176035746174246766727927437)
          ·
            refine ⟨66013404815342537522972789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 176035746174246766727927437 66013404815342537522972789)
            ·
              refine ⟨6188756701438362892778699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 66013404815342537522972789 6188756701438362892778699)
              ·
                refine ⟨9283135052157544339168049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6188756701438362892778699 9283135052157544339168049)
                ·
                  refine ⟨6962351289118158254376037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9283135052157544339168049 6962351289118158254376037)
                  ·
                    refine ⟨1305440866709654672695507, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6962351289118158254376037 1305440866709654672695507)
                    ·
                      rfl

theorem cell23_7627011_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 5, 1, 2, 4].length) (baseStart_7627011 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7627011 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7627011 prefixEnd_7627011 := by exact prefixLift 7627011
  have htrace : WordTrace (prefixWord ++ tailWord_7627011) baseStart_7627011 baseEnd_7627011 := by
    simpa [prefixWord, tailWord_7627011, baseEnd_7627011] using wordTrace_append hprefix tailTrace_7627011
  have hstable : (prefixWord ++ tailWord_7627011).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7627011).length < 2 ^ (prefixWord ++ tailWord_7627011).sum := by decide
  have hdescent : baseEnd_7627011 < baseStart_7627011 := by decide
  rcases family_descends (prefixWord ++ tailWord_7627011) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7627038 : List Nat := [4, 3, 2, 1, 1, 2, 2, 1, 1, 1, 5]
def baseStart_7627038 : Nat := 118140960795 + 7627038 * 2 ^ 59
def prefixEnd_7627038 : Nat := 4983230072969 + 3 ^ 40 * 7627038 * 2
def baseEnd_7627038 : Nat := 3916336464106635412448897

theorem tailTrace_7627038 : CollatzResearch.WordTrace tailWord_7627038 prefixEnd_7627038 3916336464106635412448897 := by
  unfold tailWord_7627038
  simp only [CollatzResearch.WordTrace]
  refine ⟨34772616167818924403834221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 185453952895034263487115845 34772616167818924403834221)
  ·
    refine ⟨13039731062932096651437833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34772616167818924403834221 13039731062932096651437833)
    ·
      refine ⟨9779798297199072488578375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13039731062932096651437833 9779798297199072488578375)
      ·
        refine ⟨14669697445798608732867563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9779798297199072488578375 14669697445798608732867563)
        ·
          refine ⟨22004546168697913099301345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14669697445798608732867563 22004546168697913099301345)
          ·
            refine ⟨16503409626523434824476009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22004546168697913099301345 16503409626523434824476009)
            ·
              refine ⟨12377557219892576118357007, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16503409626523434824476009 12377557219892576118357007)
              ·
                refine ⟨18566335829838864177535511, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12377557219892576118357007 18566335829838864177535511)
                ·
                  refine ⟨27849503744758296266303267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18566335829838864177535511 27849503744758296266303267)
                  ·
                    refine ⟨41774255617137444399454901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27849503744758296266303267 41774255617137444399454901)
                    ·
                      refine ⟨3916336464106635412448897, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41774255617137444399454901 3916336464106635412448897)
                      ·
                        rfl

theorem cell23_7627038_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 2, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 2, 2, 1, 1, 1, 5].length) (baseStart_7627038 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7627038 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7627038 prefixEnd_7627038 := by exact prefixLift 7627038
  have htrace : WordTrace (prefixWord ++ tailWord_7627038) baseStart_7627038 baseEnd_7627038 := by
    simpa [prefixWord, tailWord_7627038, baseEnd_7627038] using wordTrace_append hprefix tailTrace_7627038
  have hstable : (prefixWord ++ tailWord_7627038).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7627038).length < 2 ^ (prefixWord ++ tailWord_7627038).sum := by decide
  have hdescent : baseEnd_7627038 < baseStart_7627038 := by decide
  rcases family_descends (prefixWord ++ tailWord_7627038) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7627061 : List Nat := [1, 3, 3, 1, 2, 1, 2, 2, 3, 3, 2]
def baseStart_7627061 : Nat := 118140960795 + 7627061 * 2 ^ 59
def prefixEnd_7627061 : Nat := 4983230072969 + 3 ^ 40 * 7627061 * 2
def baseEnd_7627061 : Nat := 3916348274161688822461291

theorem tailTrace_7627061 : CollatzResearch.WordTrace tailWord_7627061 prefixEnd_7627061 3916348274161688822461291 := by
  unfold tailWord_7627061
  simp only [CollatzResearch.WordTrace]
  refine ⟨278181768221468070158761037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185454512147645380105840691 278181768221468070158761037)
  ·
    refine ⟨104318163083050526309535389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 278181768221468070158761037 104318163083050526309535389)
    ·
      refine ⟨39119311156143947366075771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 104318163083050526309535389 39119311156143947366075771)
      ·
        refine ⟨58678966734215921049113657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39119311156143947366075771 58678966734215921049113657)
        ·
          refine ⟨44009225050661940786835243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58678966734215921049113657 44009225050661940786835243)
          ·
            refine ⟨66013837575992911180252865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44009225050661940786835243 66013837575992911180252865)
            ·
              refine ⟨49510378181994683385189649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 66013837575992911180252865 49510378181994683385189649)
              ·
                refine ⟨37132783636496012538892237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49510378181994683385189649 37132783636496012538892237)
                ·
                  refine ⟨13924793863686004702084589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 37132783636496012538892237 13924793863686004702084589)
                  ·
                    refine ⟨5221797698882251763281721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13924793863686004702084589 5221797698882251763281721)
                    ·
                      refine ⟨3916348274161688822461291, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5221797698882251763281721 3916348274161688822461291)
                      ·
                        rfl

theorem cell23_7627061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 2, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 2, 2, 3, 3, 2].length) (baseStart_7627061 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7627061 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7627061 prefixEnd_7627061 := by exact prefixLift 7627061
  have htrace : WordTrace (prefixWord ++ tailWord_7627061) baseStart_7627061 baseEnd_7627061 := by
    simpa [prefixWord, tailWord_7627061, baseEnd_7627061] using wordTrace_append hprefix tailTrace_7627061
  have hstable : (prefixWord ++ tailWord_7627061).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7627061).length < 2 ^ (prefixWord ++ tailWord_7627061).sum := by decide
  have hdescent : baseEnd_7627061 < baseStart_7627061 := by decide
  rcases family_descends (prefixWord ++ tailWord_7627061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7627087 : List Nat := [1, 1, 2, 1, 1, 2, 1, 3, 3, 4, 4]
def baseStart_7627087 : Nat := 118140960795 + 7627087 * 2 ^ 59
def prefixEnd_7627087 : Nat := 4983230072969 + 3 ^ 40 * 7627087 * 2
def baseEnd_7627087 : Nat := 3916361624658705720736171

theorem tailTrace_7627087 : CollatzResearch.WordTrace tailWord_7627087 prefixEnd_7627087 3916361624658705720736171 := by
  unfold tailWord_7627087
  simp only [CollatzResearch.WordTrace]
  refine ⟨278182716519373876599207515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185455144346249251066138343 278182716519373876599207515)
  ·
    refine ⟨417274074779060814898811273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 278182716519373876599207515 417274074779060814898811273)
    ·
      refine ⟨312955556084295611174108455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 417274074779060814898811273 312955556084295611174108455)
      ·
        refine ⟨469433334126443416761162683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 312955556084295611174108455 469433334126443416761162683)
        ·
          refine ⟨704150001189665125141744025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 469433334126443416761162683 704150001189665125141744025)
          ·
            refine ⟨528112500892248843856308019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 704150001189665125141744025 528112500892248843856308019)
            ·
              refine ⟨792168751338373265784462029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 528112500892248843856308019 792168751338373265784462029)
              ·
                refine ⟨297063281751889974669173261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 792168751338373265784462029 297063281751889974669173261)
                ·
                  refine ⟨111398730656958740500939973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 297063281751889974669173261 111398730656958740500939973)
                  ·
                    refine ⟨20887261998179763843926245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 111398730656958740500939973 20887261998179763843926245)
                    ·
                      refine ⟨3916361624658705720736171, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20887261998179763843926245 3916361624658705720736171)
                      ·
                        rfl

theorem cell23_7627087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 3, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 3, 3, 4, 4].length) (baseStart_7627087 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7627087 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7627087 prefixEnd_7627087 := by exact prefixLift 7627087
  have htrace : WordTrace (prefixWord ++ tailWord_7627087) baseStart_7627087 baseEnd_7627087 := by
    simpa [prefixWord, tailWord_7627087, baseEnd_7627087] using wordTrace_append hprefix tailTrace_7627087
  have hstable : (prefixWord ++ tailWord_7627087).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7627087).length < 2 ^ (prefixWord ++ tailWord_7627087).sum := by decide
  have hdescent : baseEnd_7627087 < baseStart_7627087 := by decide
  rcases family_descends (prefixWord ++ tailWord_7627087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7627091 : List Nat := [1, 1, 1, 2, 1, 1, 4, 4, 4, 2, 2]
def baseStart_7627091 : Nat := 118140960795 + 7627091 * 2 ^ 59
def prefixEnd_7627091 : Nat := 4983230072969 + 3 ^ 40 * 7627091 * 2
def baseEnd_7627091 : Nat := 3916363678581323705086153

theorem tailTrace_7627091 : CollatzResearch.WordTrace tailWord_7627091 prefixEnd_7627091 3916363678581323705086153 := by
  unfold tailWord_7627091
  simp only [CollatzResearch.WordTrace]
  refine ⟨278182862411359385282353127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185455241607572923521568751 278182862411359385282353127)
  ·
    refine ⟨417274293617039077923529691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 278182862411359385282353127 417274293617039077923529691)
    ·
      refine ⟨625911440425558616885294537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 417274293617039077923529691 625911440425558616885294537)
      ·
        refine ⟨469433580319168962663970903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 625911440425558616885294537 469433580319168962663970903)
        ·
          refine ⟨704150370478753443995956355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 469433580319168962663970903 704150370478753443995956355)
          ·
            refine ⟨1056225555718130165993934533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 704150370478753443995956355 1056225555718130165993934533)
            ·
              refine ⟨198042291697149406123862725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1056225555718130165993934533 198042291697149406123862725)
              ·
                refine ⟨37132929693215513648224261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 198042291697149406123862725 37132929693215513648224261)
                ·
                  refine ⟨6962424317477908809042049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 37132929693215513648224261 6962424317477908809042049)
                  ·
                    refine ⟨5221818238108431606781537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6962424317477908809042049 5221818238108431606781537)
                    ·
                      refine ⟨3916363678581323705086153, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5221818238108431606781537 3916363678581323705086153)
                      ·
                        rfl

theorem cell23_7627091_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 4, 4, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 4, 4, 4, 2, 2].length) (baseStart_7627091 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7627091 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7627091 prefixEnd_7627091 := by exact prefixLift 7627091
  have htrace : WordTrace (prefixWord ++ tailWord_7627091) baseStart_7627091 baseEnd_7627091 := by
    simpa [prefixWord, tailWord_7627091, baseEnd_7627091] using wordTrace_append hprefix tailTrace_7627091
  have hstable : (prefixWord ++ tailWord_7627091).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7627091).length < 2 ^ (prefixWord ++ tailWord_7627091).sum := by decide
  have hdescent : baseEnd_7627091 < baseStart_7627091 := by decide
  rcases family_descends (prefixWord ++ tailWord_7627091) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7627125 : List Nat := [1, 3, 4, 1, 2, 1, 2, 3, 2, 2, 2]
def baseStart_7627125 : Nat := 118140960795 + 7627125 * 2 ^ 59
def prefixEnd_7627125 : Nat := 4983230072969 + 3 ^ 40 * 7627125 * 2
def baseEnd_7627125 : Nat := 3916381136923576572060997

theorem tailTrace_7627125 : CollatzResearch.WordTrace tailWord_7627125 prefixEnd_7627125 3916381136923576572060997 := by
  unfold tailWord_7627125
  simp only [CollatzResearch.WordTrace]
  refine ⟨278184102493236209089090829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185456068328824139392727219 278184102493236209089090829)
  ·
    refine ⟨104319038434963578408409061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 278184102493236209089090829 104319038434963578408409061)
    ·
      refine ⟨19559819706555670951576699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 104319038434963578408409061 19559819706555670951576699)
      ·
        refine ⟨29339729559833506427365049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19559819706555670951576699 29339729559833506427365049)
        ·
          refine ⟨22004797169875129820523787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29339729559833506427365049 22004797169875129820523787)
          ·
            refine ⟨33007195754812694730785681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22004797169875129820523787 33007195754812694730785681)
            ·
              refine ⟨24755396816109521048089261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33007195754812694730785681 24755396816109521048089261)
              ·
                refine ⟨9283273806041070393033473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24755396816109521048089261 9283273806041070393033473)
                ·
                  refine ⟨6962455354530802794775105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9283273806041070393033473 6962455354530802794775105)
                  ·
                    refine ⟨5221841515898102096081329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6962455354530802794775105 5221841515898102096081329)
                    ·
                      refine ⟨3916381136923576572060997, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5221841515898102096081329 3916381136923576572060997)
                      ·
                        rfl

theorem cell23_7627125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 1, 2, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 1, 2, 3, 2, 2, 2].length) (baseStart_7627125 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7627125 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7627125 prefixEnd_7627125 := by exact prefixLift 7627125
  have htrace : WordTrace (prefixWord ++ tailWord_7627125) baseStart_7627125 baseEnd_7627125 := by
    simpa [prefixWord, tailWord_7627125, baseEnd_7627125] using wordTrace_append hprefix tailTrace_7627125
  have hstable : (prefixWord ++ tailWord_7627125).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7627125).length < 2 ^ (prefixWord ++ tailWord_7627125).sum := by decide
  have hdescent : baseEnd_7627125 < baseStart_7627125 := by decide
  rcases family_descends (prefixWord ++ tailWord_7627125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7627144 : List Nat := [2, 1, 3, 3, 1, 1, 3, 1, 1, 7]
def baseStart_7627144 : Nat := 118140960795 + 7627144 * 2 ^ 59
def prefixEnd_7627144 : Nat := 4983230072969 + 3 ^ 40 * 7627144 * 2
def baseEnd_7627144 : Nat := 1305463631018670665907803

theorem tailTrace_7627144 : CollatzResearch.WordTrace tailWord_7627144 prefixEnd_7627144 1305463631018670665907803 := by
  unfold tailWord_7627144
  simp only [CollatzResearch.WordTrace]
  refine ⟨139092397740083687667016243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 185456530320111583556021657 139092397740083687667016243)
  ·
    refine ⟨208638596610125531500524365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139092397740083687667016243 208638596610125531500524365)
    ·
      refine ⟨78239473728797074312696637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 208638596610125531500524365 78239473728797074312696637)
      ·
        refine ⟨29339802648298902867261239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 78239473728797074312696637 29339802648298902867261239)
        ·
          refine ⟨44009703972448354300891859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29339802648298902867261239 44009703972448354300891859)
          ·
            refine ⟨66014555958672531451337789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44009703972448354300891859 66014555958672531451337789)
            ·
              refine ⟨24755458484502199294251671, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 66014555958672531451337789 24755458484502199294251671)
              ·
                refine ⟨37133187726753298941377507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24755458484502199294251671 37133187726753298941377507)
                ·
                  refine ⟨55699781590129948412066261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37133187726753298941377507 55699781590129948412066261)
                  ·
                    refine ⟨1305463631018670665907803, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 55699781590129948412066261 1305463631018670665907803)
                    ·
                      rfl

theorem cell23_7627144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 3, 1, 1, 7].length) (baseStart_7627144 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7627144 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7627144 prefixEnd_7627144 := by exact prefixLift 7627144
  have htrace : WordTrace (prefixWord ++ tailWord_7627144) baseStart_7627144 baseEnd_7627144 := by
    simpa [prefixWord, tailWord_7627144, baseEnd_7627144] using wordTrace_append hprefix tailTrace_7627144
  have hstable : (prefixWord ++ tailWord_7627144).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7627144).length < 2 ^ (prefixWord ++ tailWord_7627144).sum := by decide
  have hdescent : baseEnd_7627144 < baseStart_7627144 := by decide
  rcases family_descends (prefixWord ++ tailWord_7627144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7627191 : List Nat := [1, 1, 3, 1, 3, 3, 2, 2, 3, 4]
def baseStart_7627191 : Nat := 118140960795 + 7627191 * 2 ^ 59
def prefixEnd_7627191 : Nat := 4983230072969 + 3 ^ 40 * 7627191 * 2
def baseEnd_7627191 : Nat := 1305471675548924437945231

theorem tailTrace_7627191 : CollatzResearch.WordTrace tailWord_7627191 prefixEnd_7627191 1305471675548924437945231 := by
  unfold tailWord_7627191
  simp only [CollatzResearch.WordTrace]
  refine ⟨278186509710997102360993427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185457673140664734907328951 278186509710997102360993427)
  ·
    refine ⟨417279764566495653541490141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 278186509710997102360993427 417279764566495653541490141)
    ·
      refine ⟨156479911712435870078058803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 417279764566495653541490141 156479911712435870078058803)
      ·
        refine ⟨234719867568653805117088205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 156479911712435870078058803 234719867568653805117088205)
        ·
          refine ⟨88019950338245176918908077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 234719867568653805117088205 88019950338245176918908077)
          ·
            refine ⟨33007481376841941344590529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 88019950338245176918908077 33007481376841941344590529)
            ·
              refine ⟨24755611032631456008442897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33007481376841941344590529 24755611032631456008442897)
              ·
                refine ⟨18566708274473592006332173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24755611032631456008442897 18566708274473592006332173)
                ·
                  refine ⟨6962515602927597002374565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18566708274473592006332173 6962515602927597002374565)
                  ·
                    refine ⟨1305471675548924437945231, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6962515602927597002374565 1305471675548924437945231)
                    ·
                      rfl

theorem cell23_7627191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 3, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 3, 2, 2, 3, 4].length) (baseStart_7627191 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7627191 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7627191 prefixEnd_7627191 := by exact prefixLift 7627191
  have htrace : WordTrace (prefixWord ++ tailWord_7627191) baseStart_7627191 baseEnd_7627191 := by
    simpa [prefixWord, tailWord_7627191, baseEnd_7627191] using wordTrace_append hprefix tailTrace_7627191
  have hstable : (prefixWord ++ tailWord_7627191).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7627191).length < 2 ^ (prefixWord ++ tailWord_7627191).sum := by decide
  have hdescent : baseEnd_7627191 < baseStart_7627191 := by decide
  rcases family_descends (prefixWord ++ tailWord_7627191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7627225 : List Nat := [1, 2, 1, 2, 4, 1, 5, 2, 1, 4]
def baseStart_7627225 : Nat := 118140960795 + 7627225 * 2 ^ 59
def prefixEnd_7627225 : Nat := 4983230072969 + 3 ^ 40 * 7627225 * 2
def baseEnd_7627225 : Nat := 1305477494996342060270179

theorem tailTrace_7627225 : CollatzResearch.WordTrace tailWord_7627225 prefixEnd_7627225 1305477494996342060270179 := by
  unfold tailWord_7627225
  simp only [CollatzResearch.WordTrace]
  refine ⟨278187749792873926167731129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185458499861915950778487419 278187749792873926167731129)
  ·
    refine ⟨208640812344655444625798347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 278187749792873926167731129 208640812344655444625798347)
    ·
      refine ⟨312961218516983166938697521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 208640812344655444625798347 312961218516983166938697521)
      ·
        refine ⟨234720913887737375204023141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 312961218516983166938697521 234720913887737375204023141)
        ·
          refine ⟨44010171353950757850754339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 234720913887737375204023141 44010171353950757850754339)
          ·
            refine ⟨66015257030926136776131509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44010171353950757850754339 66015257030926136776131509)
            ·
              refine ⟨6188930346649325322762329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 66015257030926136776131509 6188930346649325322762329)
              ·
                refine ⟨4641697759986993992071747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6188930346649325322762329 4641697759986993992071747)
                ·
                  refine ⟨6962546639980490988107621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4641697759986993992071747 6962546639980490988107621)
                  ·
                    refine ⟨1305477494996342060270179, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6962546639980490988107621 1305477494996342060270179)
                    ·
                      rfl

theorem cell23_7627225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 5, 2, 1, 4].length) (baseStart_7627225 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7627225 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7627225 prefixEnd_7627225 := by exact prefixLift 7627225
  have htrace : WordTrace (prefixWord ++ tailWord_7627225) baseStart_7627225 baseEnd_7627225 := by
    simpa [prefixWord, tailWord_7627225, baseEnd_7627225] using wordTrace_append hprefix tailTrace_7627225
  have hstable : (prefixWord ++ tailWord_7627225).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7627225).length < 2 ^ (prefixWord ++ tailWord_7627225).sum := by decide
  have hdescent : baseEnd_7627225 < baseStart_7627225 := by decide
  rcases family_descends (prefixWord ++ tailWord_7627225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7627241 : List Nat := [1, 2, 1, 1, 1, 2, 1, 6, 1, 5, 2]
def baseStart_7627241 : Nat := 118140960795 + 7627241 * 2 ^ 59
def prefixEnd_7627241 : Nat := 4983230072969 + 3 ^ 40 * 7627241 * 2
def baseEnd_7627241 : Nat := 3916440700679498118210463

theorem tailTrace_7627241 : CollatzResearch.WordTrace tailWord_7627241 prefixEnd_7627241 3916440700679498118210463 := by
  unfold tailWord_7627241
  simp only [CollatzResearch.WordTrace]
  refine ⟨278188333360815960900313577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185458888907210640600209051 278188333360815960900313577)
  ·
    refine ⟨208641250020611970675235183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 278188333360815960900313577 208641250020611970675235183)
    ·
      refine ⟨312961875030917956012852775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 208641250020611970675235183 312961875030917956012852775)
      ·
        refine ⟨469442812546376934019279163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 312961875030917956012852775 469442812546376934019279163)
        ·
          refine ⟨704164218819565401028918745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 469442812546376934019279163 704164218819565401028918745)
          ·
            refine ⟨528123164114674050771689059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 704164218819565401028918745 528123164114674050771689059)
            ·
              refine ⟨792184746172011076157533589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 528123164114674050771689059 792184746172011076157533589)
              ·
                refine ⟨37133659976813019194884387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 792184746172011076157533589 37133659976813019194884387)
                ·
                  refine ⟨55700489965219528792326581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37133659976813019194884387 55700489965219528792326581)
                  ·
                    refine ⟨5221920934239330824280617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 55700489965219528792326581 5221920934239330824280617)
                    ·
                      refine ⟨3916440700679498118210463, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5221920934239330824280617 3916440700679498118210463)
                      ·
                        rfl

theorem cell23_7627241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 6, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 6, 1, 5, 2].length) (baseStart_7627241 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7627241 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7627241 prefixEnd_7627241 := by exact prefixLift 7627241
  have htrace : WordTrace (prefixWord ++ tailWord_7627241) baseStart_7627241 baseEnd_7627241 := by
    simpa [prefixWord, tailWord_7627241, baseEnd_7627241] using wordTrace_append hprefix tailTrace_7627241
  have hstable : (prefixWord ++ tailWord_7627241).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7627241).length < 2 ^ (prefixWord ++ tailWord_7627241).sum := by decide
  have hdescent : baseEnd_7627241 < baseStart_7627241 := by decide
  rcases family_descends (prefixWord ++ tailWord_7627241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7627301 : List Nat := [1, 3, 1, 2, 2, 1, 3, 3, 1, 2, 4]
def baseStart_7627301 : Nat := 118140960795 + 7627301 * 2 ^ 59
def prefixEnd_7627301 : Nat := 4983230072969 + 3 ^ 40 * 7627301 * 2
def baseEnd_7627301 : Nat := 3916471509518767883460187

theorem tailTrace_7627301 : CollatzResearch.WordTrace tailWord_7627301 prefixEnd_7627301 3916471509518767883460187 := by
  unfold tailWord_7627301
  simp only [CollatzResearch.WordTrace]
  refine ⟨278190521740598591147497757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185460347827065727431665171 278190521740598591147497757)
  ·
    refine ⟨104321445652724471680311659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 278190521740598591147497757 104321445652724471680311659)
    ·
      refine ⟨156482168479086707520467489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104321445652724471680311659 156482168479086707520467489)
      ·
        refine ⟨117361626359315030640350617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 156482168479086707520467489 117361626359315030640350617)
        ·
          refine ⟨88021219769486272980262963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 117361626359315030640350617 88021219769486272980262963)
          ·
            refine ⟨132031829654229409470394445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88021219769486272980262963 132031829654229409470394445)
            ·
              refine ⟨49511936120336028551397917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 132031829654229409470394445 49511936120336028551397917)
              ·
                refine ⟨18566976045126010706774219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 49511936120336028551397917 18566976045126010706774219)
                ·
                  refine ⟨27850464067689016060161329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18566976045126010706774219 27850464067689016060161329)
                  ·
                    refine ⟨20887848050766762045120997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27850464067689016060161329 20887848050766762045120997)
                    ·
                      refine ⟨3916471509518767883460187, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20887848050766762045120997 3916471509518767883460187)
                      ·
                        rfl

theorem cell23_7627301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 3, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 3, 3, 1, 2, 4].length) (baseStart_7627301 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7627301 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7627301 prefixEnd_7627301 := by exact prefixLift 7627301
  have htrace : WordTrace (prefixWord ++ tailWord_7627301) baseStart_7627301 baseEnd_7627301 := by
    simpa [prefixWord, tailWord_7627301, baseEnd_7627301] using wordTrace_append hprefix tailTrace_7627301
  have hstable : (prefixWord ++ tailWord_7627301).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7627301).length < 2 ^ (prefixWord ++ tailWord_7627301).sum := by decide
  have hdescent : baseEnd_7627301 < baseStart_7627301 := by decide
  rcases family_descends (prefixWord ++ tailWord_7627301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7627309 : List Nat := [1, 5, 4, 1, 1, 1, 1, 1, 1, 5, 2]
def baseStart_7627309 : Nat := 118140960795 + 7627309 * 2 ^ 59
def prefixEnd_7627309 : Nat := 4983230072969 + 3 ^ 40 * 7627309 * 2
def baseEnd_7627309 : Nat := 3916475617364003852160151

theorem tailTrace_7627309 : CollatzResearch.WordTrace tailWord_7627309 prefixEnd_7627309 3916475617364003852160151 := by
  unfold tailWord_7627309
  simp only [CollatzResearch.WordTrace]
  refine ⟨278190813524569608513788981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185460542349713072342525987 278190813524569608513788981)
  ·
    refine ⟨26080388767928400798167717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 278190813524569608513788981 26080388767928400798167717)
    ·
      refine ⟨4890072893986575149656447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 26080388767928400798167717 4890072893986575149656447)
      ·
        refine ⟨7335109340979862724484671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4890072893986575149656447 7335109340979862724484671)
        ·
          refine ⟨11002664011469794086727007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7335109340979862724484671 11002664011469794086727007)
          ·
            refine ⟨16503996017204691130090511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11002664011469794086727007 16503996017204691130090511)
            ·
              refine ⟨24755994025807036695135767, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16503996017204691130090511 24755994025807036695135767)
              ·
                refine ⟨37133991038710555042703651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24755994025807036695135767 37133991038710555042703651)
                ·
                  refine ⟨55700986558065832564055477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37133991038710555042703651 55700986558065832564055477)
                  ·
                    refine ⟨5221967489818671802880201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 55700986558065832564055477 5221967489818671802880201)
                    ·
                      refine ⟨3916475617364003852160151, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5221967489818671802880201 3916475617364003852160151)
                      ·
                        rfl

theorem cell23_7627309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 1, 1, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 1, 1, 1, 1, 1, 5, 2].length) (baseStart_7627309 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7627309 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7627309 prefixEnd_7627309 := by exact prefixLift 7627309
  have htrace : WordTrace (prefixWord ++ tailWord_7627309) baseStart_7627309 baseEnd_7627309 := by
    simpa [prefixWord, tailWord_7627309, baseEnd_7627309] using wordTrace_append hprefix tailTrace_7627309
  have hstable : (prefixWord ++ tailWord_7627309).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7627309).length < 2 ^ (prefixWord ++ tailWord_7627309).sum := by decide
  have hdescent : baseEnd_7627309 < baseStart_7627309 := by decide
  rcases family_descends (prefixWord ++ tailWord_7627309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7627316 : List Nat := [2, 5, 1, 3, 1, 1, 2, 3, 1, 1, 3]
def baseStart_7627316 : Nat := 118140960795 + 7627316 * 2 ^ 59
def prefixEnd_7627316 : Nat := 4983230072969 + 3 ^ 40 * 7627316 * 2
def baseEnd_7627316 : Nat := 3916479211728585324772619

theorem tailTrace_7627316 : CollatzResearch.WordTrace tailWord_7627316 prefixEnd_7627316 3916479211728585324772619 := by
  unfold tailWord_7627316
  simp only [CollatzResearch.WordTrace]
  refine ⟨139095534417772124354646901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 185460712557029499139529201 139095534417772124354646901)
  ·
    refine ⟨13040206351666136658248147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 139095534417772124354646901 13040206351666136658248147)
    ·
      refine ⟨19560309527499204987372221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13040206351666136658248147 19560309527499204987372221)
      ·
        refine ⟨7335116072812201870264583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19560309527499204987372221 7335116072812201870264583)
        ·
          refine ⟨11002674109218302805396875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7335116072812201870264583 11002674109218302805396875)
          ·
            refine ⟨16504011163827454208095313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11002674109218302805396875 16504011163827454208095313)
            ·
              refine ⟨12378008372870590656071485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16504011163827454208095313 12378008372870590656071485)
              ·
                refine ⟨4641753139826471496026807, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12378008372870590656071485 4641753139826471496026807)
                ·
                  refine ⟨6962629709739707244040211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4641753139826471496026807 6962629709739707244040211)
                  ·
                    refine ⟨10443944564609560866060317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6962629709739707244040211 10443944564609560866060317)
                    ·
                      refine ⟨3916479211728585324772619, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10443944564609560866060317 3916479211728585324772619)
                      ·
                        rfl

theorem cell23_7627316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 1, 1, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 1, 1, 2, 3, 1, 1, 3].length) (baseStart_7627316 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7627316 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7627316 prefixEnd_7627316 := by exact prefixLift 7627316
  have htrace : WordTrace (prefixWord ++ tailWord_7627316) baseStart_7627316 baseEnd_7627316 := by
    simpa [prefixWord, tailWord_7627316, baseEnd_7627316] using wordTrace_append hprefix tailTrace_7627316
  have hstable : (prefixWord ++ tailWord_7627316).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7627316).length < 2 ^ (prefixWord ++ tailWord_7627316).sum := by decide
  have hdescent : baseEnd_7627316 < baseStart_7627316 := by decide
  rcases family_descends (prefixWord ++ tailWord_7627316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7627322 : List Nat := [3, 1, 1, 1, 3, 3, 1, 5, 1, 2, 2]
def baseStart_7627322 : Nat := 118140960795 + 7627322 * 2 ^ 59
def prefixEnd_7627322 : Nat := 4983230072969 + 3 ^ 40 * 7627322 * 2
def baseEnd_7627322 : Nat := 3916482292612512301297591

theorem tailTrace_7627322 : CollatzResearch.WordTrace tailWord_7627322 prefixEnd_7627322 3916482292612512301297591 := by
  unfold tailWord_7627322
  simp only [CollatzResearch.WordTrace]
  refine ⟨69547821918380627933503055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 185460858449015007822674813 69547821918380627933503055)
  ·
    refine ⟨104321732877570941900254583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69547821918380627933503055 104321732877570941900254583)
    ·
      refine ⟨156482599316356412850381875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104321732877570941900254583 156482599316356412850381875)
      ·
        refine ⟨234723898974534619275572813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 156482599316356412850381875 234723898974534619275572813)
        ·
          refine ⟨88021462115450482228339805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 234723898974534619275572813 88021462115450482228339805)
          ·
            refine ⟨33008048293293930835627427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 88021462115450482228339805 33008048293293930835627427)
            ·
              refine ⟨49512072439940896253441141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33008048293293930835627427 49512072439940896253441141)
              ·
                refine ⟨4641756791244459023760107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 49512072439940896253441141 4641756791244459023760107)
                ·
                  refine ⟨6962635186866688535640161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4641756791244459023760107 6962635186866688535640161)
                  ·
                    refine ⟨5221976390150016401730121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6962635186866688535640161 5221976390150016401730121)
                    ·
                      refine ⟨3916482292612512301297591, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5221976390150016401730121 3916482292612512301297591)
                      ·
                        rfl

theorem cell23_7627322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 3, 1, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 3, 1, 5, 1, 2, 2].length) (baseStart_7627322 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7627322 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7627322 prefixEnd_7627322 := by exact prefixLift 7627322
  have htrace : WordTrace (prefixWord ++ tailWord_7627322) baseStart_7627322 baseEnd_7627322 := by
    simpa [prefixWord, tailWord_7627322, baseEnd_7627322] using wordTrace_append hprefix tailTrace_7627322
  have hstable : (prefixWord ++ tailWord_7627322).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7627322).length < 2 ^ (prefixWord ++ tailWord_7627322).sum := by decide
  have hdescent : baseEnd_7627322 < baseStart_7627322 := by decide
  rcases family_descends (prefixWord ++ tailWord_7627322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7627325 : List Nat := [1, 4, 1, 3, 2, 2, 1, 3, 1, 2, 3]
def baseStart_7627325 : Nat := 118140960795 + 7627325 * 2 ^ 59
def prefixEnd_7627325 : Nat := 4983230072969 + 3 ^ 40 * 7627325 * 2
def baseEnd_7627325 : Nat := 3916483833054475789560077

theorem tailTrace_7627325 : CollatzResearch.WordTrace tailWord_7627325 prefixEnd_7627325 3916483833054475789560077 := by
  unfold tailWord_7627325
  simp only [CollatzResearch.WordTrace]
  refine ⟨278191397092511643246371429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185460931395007762164247619 278191397092511643246371429)
  ·
    refine ⟨52160886954845933108694643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 278191397092511643246371429 52160886954845933108694643)
    ·
      refine ⟨78241330432268899663041965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52160886954845933108694643 78241330432268899663041965)
      ·
        refine ⟨29340498912100837373640737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 78241330432268899663041965 29340498912100837373640737)
        ·
          refine ⟨22005374184075628030230553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29340498912100837373640737 22005374184075628030230553)
          ·
            refine ⟨16504030638056721022672915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22005374184075628030230553 16504030638056721022672915)
            ·
              refine ⟨24756045957085081534009373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16504030638056721022672915 24756045957085081534009373)
              ·
                refine ⟨9283517233906905575253515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24756045957085081534009373 9283517233906905575253515)
                ·
                  refine ⟨13925275850860358362880273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9283517233906905575253515 13925275850860358362880273)
                  ·
                    refine ⟨10443956888145268772160205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13925275850860358362880273 10443956888145268772160205)
                    ·
                      refine ⟨3916483833054475789560077, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10443956888145268772160205 3916483833054475789560077)
                      ·
                        rfl

theorem cell23_7627325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 2, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 2, 1, 3, 1, 2, 3].length) (baseStart_7627325 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7627325 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7627325 prefixEnd_7627325 := by exact prefixLift 7627325
  have htrace : WordTrace (prefixWord ++ tailWord_7627325) baseStart_7627325 baseEnd_7627325 := by
    simpa [prefixWord, tailWord_7627325, baseEnd_7627325] using wordTrace_append hprefix tailTrace_7627325
  have hstable : (prefixWord ++ tailWord_7627325).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7627325).length < 2 ^ (prefixWord ++ tailWord_7627325).sum := by decide
  have hdescent : baseEnd_7627325 < baseStart_7627325 := by decide
  rcases family_descends (prefixWord ++ tailWord_7627325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7627362 : List Nat := [3, 3, 2, 3, 1, 2, 2, 7]
def baseStart_7627362 : Nat := 118140960795 + 7627362 * 2 ^ 59
def prefixEnd_7627362 : Nat := 4983230072969 + 3 ^ 40 * 7627362 * 2
def baseEnd_7627362 : Nat := 145055660438470079436941

theorem tailTrace_7627362 : CollatzResearch.WordTrace tailWord_7627362 prefixEnd_7627362 145055660438470079436941 := by
  unfold tailWord_7627362
  simp only [CollatzResearch.WordTrace]
  refine ⟨69548186648344399641367085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 185461831062251732376978893 69548186648344399641367085)
  ·
    refine ⟨26080569993129149865512657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 69548186648344399641367085 26080569993129149865512657)
    ·
      refine ⟨19560427494846862399134493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26080569993129149865512657 19560427494846862399134493)
      ·
        refine ⟨7335160310567573399675435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19560427494846862399134493 7335160310567573399675435)
        ·
          refine ⟨11002740465851360099513153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7335160310567573399675435 11002740465851360099513153)
          ·
            refine ⟨8252055349388520074634865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11002740465851360099513153 8252055349388520074634865)
            ·
              refine ⟨6189041512041390055976149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8252055349388520074634865 6189041512041390055976149)
              ·
                refine ⟨145055660438470079436941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6189041512041390055976149 145055660438470079436941)
                ·
                  rfl

theorem cell23_7627362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 1, 2, 2, 7].length) (baseStart_7627362 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7627362 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7627362 prefixEnd_7627362 := by exact prefixLift 7627362
  have htrace : WordTrace (prefixWord ++ tailWord_7627362) baseStart_7627362 baseEnd_7627362 := by
    simpa [prefixWord, tailWord_7627362, baseEnd_7627362] using wordTrace_append hprefix tailTrace_7627362
  have hstable : (prefixWord ++ tailWord_7627362).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7627362).length < 2 ^ (prefixWord ++ tailWord_7627362).sum := by decide
  have hdescent : baseEnd_7627362 < baseStart_7627362 := by decide
  rcases family_descends (prefixWord ++ tailWord_7627362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7627391 : List Nat := [1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 4]
def baseStart_7627391 : Nat := 118140960795 + 7627391 * 2 ^ 59
def prefixEnd_7627391 : Nat := 4983230072969 + 3 ^ 40 * 7627391 * 2
def baseEnd_7627391 : Nat := 3916517722777672531334773

theorem tailTrace_7627391 : CollatzResearch.WordTrace tailWord_7627391 prefixEnd_7627391 3916517722777672531334773 := by
  unfold tailWord_7627391
  simp only [CollatzResearch.WordTrace]
  refine ⟨278193804310272536518274027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185462536206848357678849351 278193804310272536518274027)
  ·
    refine ⟨417290706465408804777411041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 278193804310272536518274027 417290706465408804777411041)
    ·
      refine ⟨312968029849056603583058281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 417290706465408804777411041 312968029849056603583058281)
      ·
        refine ⟨234726022386792452687293711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 312968029849056603583058281 234726022386792452687293711)
        ·
          refine ⟨352089033580188679030940567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 234726022386792452687293711 352089033580188679030940567)
          ·
            refine ⟨528133550370283018546410851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 352089033580188679030940567 528133550370283018546410851)
            ·
              refine ⟨792200325555424527819616277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 528133550370283018546410851 792200325555424527819616277)
              ·
                refine ⟨37134390260410524741544513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 792200325555424527819616277 37134390260410524741544513)
                ·
                  refine ⟨27850792695307893556158385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37134390260410524741544513 27850792695307893556158385)
                  ·
                    refine ⟨20888094521480920167118789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27850792695307893556158385 20888094521480920167118789)
                    ·
                      refine ⟨3916517722777672531334773, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20888094521480920167118789 3916517722777672531334773)
                      ·
                        rfl

theorem cell23_7627391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 4].length) (baseStart_7627391 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7627391 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7627391 prefixEnd_7627391 := by exact prefixLift 7627391
  have htrace : WordTrace (prefixWord ++ tailWord_7627391) baseStart_7627391 baseEnd_7627391 := by
    simpa [prefixWord, tailWord_7627391, baseEnd_7627391] using wordTrace_append hprefix tailTrace_7627391
  have hstable : (prefixWord ++ tailWord_7627391).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7627391).length < 2 ^ (prefixWord ++ tailWord_7627391).sum := by decide
  have hdescent : baseEnd_7627391 < baseStart_7627391 := by decide
  rcases family_descends (prefixWord ++ tailWord_7627391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7627395 : List Nat := [1, 1, 1, 3, 3, 1, 4, 1, 4, 2, 2]
def baseStart_7627395 : Nat := 118140960795 + 7627395 * 2 ^ 59
def prefixEnd_7627395 : Nat := 4983230072969 + 3 ^ 40 * 7627395 * 2
def baseEnd_7627395 : Nat := 3916519776700290515684755

theorem tailTrace_7627395 : CollatzResearch.WordTrace tailWord_7627395 prefixEnd_7627395 3916519776700290515684755 := by
  unfold tailWord_7627395
  simp only [CollatzResearch.WordTrace]
  refine ⟨278193950202258045201419639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185462633468172030134279759 278193950202258045201419639)
  ·
    refine ⟨417290925303387067802129459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 278193950202258045201419639 417290925303387067802129459)
    ·
      refine ⟨625936387955080601703194189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 417290925303387067802129459 625936387955080601703194189)
      ·
        refine ⟨234726145483155225638697821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 625936387955080601703194189 234726145483155225638697821)
        ·
          refine ⟨88022304556183209614511683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 234726145483155225638697821 88022304556183209614511683)
          ·
            refine ⟨132033456834274814421767525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88022304556183209614511683 132033456834274814421767525)
            ·
              refine ⟨24756273156426527704081411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 132033456834274814421767525 24756273156426527704081411)
              ·
                refine ⟨37134409734639791556122117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24756273156426527704081411 37134409734639791556122117)
                ·
                  refine ⟨6962701825244960916772897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 37134409734639791556122117 6962701825244960916772897)
                  ·
                    refine ⟨5222026368933720687579673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6962701825244960916772897 5222026368933720687579673)
                    ·
                      refine ⟨3916519776700290515684755, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5222026368933720687579673 3916519776700290515684755)
                      ·
                        rfl

theorem cell23_7627395_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 4, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 4, 1, 4, 2, 2].length) (baseStart_7627395 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7627395 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7627395 prefixEnd_7627395 := by exact prefixLift 7627395
  have htrace : WordTrace (prefixWord ++ tailWord_7627395) baseStart_7627395 baseEnd_7627395 := by
    simpa [prefixWord, tailWord_7627395, baseEnd_7627395] using wordTrace_append hprefix tailTrace_7627395
  have hstable : (prefixWord ++ tailWord_7627395).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7627395).length < 2 ^ (prefixWord ++ tailWord_7627395).sum := by decide
  have hdescent : baseEnd_7627395 < baseStart_7627395 := by decide
  rcases family_descends (prefixWord ++ tailWord_7627395) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7627451 : List Nat := [1, 1, 1, 1, 1, 2, 3, 1, 5, 3, 4]
def baseStart_7627451 : Nat := 118140960795 + 7627451 * 2 ^ 59
def prefixEnd_7627451 : Nat := 4983230072969 + 3 ^ 40 * 7627451 * 2
def baseEnd_7627451 : Nat := 3916548531616942296584497

theorem tailTrace_7627451 : CollatzResearch.WordTrace tailWord_7627451 prefixEnd_7627451 3916548531616942296584497 := by
  unfold tailWord_7627451
  simp only [CollatzResearch.WordTrace]
  refine ⟨278195992690055166765458207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185463995126703444510305471 278195992690055166765458207)
  ·
    refine ⟨417293989035082750148187311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 278195992690055166765458207 417293989035082750148187311)
    ·
      refine ⟨625940983552624125222280967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 417293989035082750148187311 625940983552624125222280967)
      ·
        refine ⟨938911475328936187833421451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 625940983552624125222280967 938911475328936187833421451)
        ·
          refine ⟨1408367212993404281750132177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 938911475328936187833421451 1408367212993404281750132177)
          ·
            refine ⟨1056275409745053211312599133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1408367212993404281750132177 1056275409745053211312599133)
            ·
              refine ⟨396103278654394954242224675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1056275409745053211312599133 396103278654394954242224675)
              ·
                refine ⟨594154917981592431363337013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 396103278654394954242224675 594154917981592431363337013)
                ·
                  refine ⟨55702023560774290440312845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 594154917981592431363337013 55702023560774290440312845)
                  ·
                    refine ⟨20888258835290358915117317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 55702023560774290440312845 20888258835290358915117317)
                    ·
                      refine ⟨3916548531616942296584497, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20888258835290358915117317 3916548531616942296584497)
                      ·
                        rfl

theorem cell23_7627451_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 3, 1, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 3, 1, 5, 3, 4].length) (baseStart_7627451 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7627451 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7627451 prefixEnd_7627451 := by exact prefixLift 7627451
  have htrace : WordTrace (prefixWord ++ tailWord_7627451) baseStart_7627451 baseEnd_7627451 := by
    simpa [prefixWord, tailWord_7627451, baseEnd_7627451] using wordTrace_append hprefix tailTrace_7627451
  have hstable : (prefixWord ++ tailWord_7627451).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7627451).length < 2 ^ (prefixWord ++ tailWord_7627451).sum := by decide
  have hdescent : baseEnd_7627451 < baseStart_7627451 := by decide
  rcases family_descends (prefixWord ++ tailWord_7627451) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7627535 : List Nat := [1, 1, 2, 1, 1, 1, 5, 4, 3, 1, 3]
def baseStart_7627535 : Nat := 118140960795 + 7627535 * 2 ^ 59
def prefixEnd_7627535 : Nat := 4983230072969 + 3 ^ 40 * 7627535 * 2
def baseEnd_7627535 : Nat := 3916591663991919967934111

theorem tailTrace_7627535 : CollatzResearch.WordTrace tailWord_7627535 prefixEnd_7627535 3916591663991919967934111 := by
  unfold tailWord_7627535
  simp only [CollatzResearch.WordTrace]
  refine ⟨278199056421750849111516059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185466037614500566074344039 278199056421750849111516059)
  ·
    refine ⟨417298584632626273667274089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 278199056421750849111516059 417298584632626273667274089)
    ·
      refine ⟨312973938474469705250455567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 417298584632626273667274089 312973938474469705250455567)
      ·
        refine ⟨469460907711704557875683351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 312973938474469705250455567 469460907711704557875683351)
        ·
          refine ⟨704191361567556836813525027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 469460907711704557875683351 704191361567556836813525027)
          ·
            refine ⟨1056287042351335255220287541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 704191361567556836813525027 1056287042351335255220287541)
            ·
              refine ⟨99026910220437680176901957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1056287042351335255220287541 99026910220437680176901957)
              ·
                refine ⟨18567545666332065033169117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 99026910220437680176901957 18567545666332065033169117)
                ·
                  refine ⟨6962829624874524387438419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18567545666332065033169117 6962829624874524387438419)
                  ·
                    refine ⟨10444244437311786581157629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6962829624874524387438419 10444244437311786581157629)
                    ·
                      refine ⟨3916591663991919967934111, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10444244437311786581157629 3916591663991919967934111)
                      ·
                        rfl

theorem cell23_7627535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 5, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 5, 4, 3, 1, 3].length) (baseStart_7627535 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7627535 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7627535 prefixEnd_7627535 := by exact prefixLift 7627535
  have htrace : WordTrace (prefixWord ++ tailWord_7627535) baseStart_7627535 baseEnd_7627535 := by
    simpa [prefixWord, tailWord_7627535, baseEnd_7627535] using wordTrace_append hprefix tailTrace_7627535
  have hstable : (prefixWord ++ tailWord_7627535).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7627535).length < 2 ^ (prefixWord ++ tailWord_7627535).sum := by decide
  have hdescent : baseEnd_7627535 < baseStart_7627535 := by decide
  rcases family_descends (prefixWord ++ tailWord_7627535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7627592 : List Nat := [2, 1, 3, 1, 1, 3, 2, 1, 5, 2, 2]
def baseStart_7627592 : Nat := 118140960795 + 7627592 * 2 ^ 59
def prefixEnd_7627592 : Nat := 4983230072969 + 3 ^ 40 * 7627592 * 2
def baseEnd_7627592 : Nat := 3916620932389226244921349

theorem tailTrace_7627592 : CollatzResearch.WordTrace tailWord_7627592 prefixEnd_7627592 3916620932389226244921349 := by
  unfold tailWord_7627592
  simp only [CollatzResearch.WordTrace]
  refine ⟨139100567691272173923170515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 185467423588362898564227353 139100567691272173923170515)
  ·
    refine ⟨208650851536908260884755773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139100567691272173923170515 208650851536908260884755773)
    ·
      refine ⟨78244069326340597831783415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 208650851536908260884755773 78244069326340597831783415)
      ·
        refine ⟨117366103989510896747675123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78244069326340597831783415 117366103989510896747675123)
        ·
          refine ⟨176049155984266345121512685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 117366103989510896747675123 176049155984266345121512685)
          ·
            refine ⟨66018433494099879420567257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 176049155984266345121512685 66018433494099879420567257)
            ·
              refine ⟨49513825120574909565425443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 66018433494099879420567257 49513825120574909565425443)
              ·
                refine ⟨74270737680862364348138165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49513825120574909565425443 74270737680862364348138165)
                ·
                  refine ⟨6962881657580846657637953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 74270737680862364348138165 6962881657580846657637953)
                  ·
                    refine ⟨5222161243185634993228465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6962881657580846657637953 5222161243185634993228465)
                    ·
                      refine ⟨3916620932389226244921349, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5222161243185634993228465 3916620932389226244921349)
                      ·
                        rfl

theorem cell23_7627592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 2, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 2, 1, 5, 2, 2].length) (baseStart_7627592 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7627592 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7627592 prefixEnd_7627592 := by exact prefixLift 7627592
  have htrace : WordTrace (prefixWord ++ tailWord_7627592) baseStart_7627592 baseEnd_7627592 := by
    simpa [prefixWord, tailWord_7627592, baseEnd_7627592] using wordTrace_append hprefix tailTrace_7627592
  have hstable : (prefixWord ++ tailWord_7627592).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7627592).length < 2 ^ (prefixWord ++ tailWord_7627592).sum := by decide
  have hdescent : baseEnd_7627592 < baseStart_7627592 := by decide
  rcases family_descends (prefixWord ++ tailWord_7627592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7627605 : List Nat := [1, 3, 2, 2, 2, 1, 3, 2, 1, 2, 4]
def baseStart_7627605 : Nat := 118140960795 + 7627605 * 2 ^ 59
def prefixEnd_7627605 : Nat := 4983230072969 + 3 ^ 40 * 7627605 * 2
def baseEnd_7627605 : Nat := 3916627607637734694058789

theorem tailTrace_7627605 : CollatzResearch.WordTrace tailWord_7627605 prefixEnd_7627605 3916627607637734694058789 := by
  unfold tailWord_7627605
  simp only [CollatzResearch.WordTrace]
  refine ⟨278201609531497251066564269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185467739687664834044376179 278201609531497251066564269)
  ·
    refine ⟨104325603574311469149961601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 278201609531497251066564269 104325603574311469149961601)
    ·
      refine ⟨78244202680733601862471201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 104325603574311469149961601 78244202680733601862471201)
      ·
        refine ⟨58683152010550201396853401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78244202680733601862471201 58683152010550201396853401)
        ·
          refine ⟨44012364007912651047640051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58683152010550201396853401 44012364007912651047640051)
          ·
            refine ⟨66018546011868976571460077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44012364007912651047640051 66018546011868976571460077)
            ·
              refine ⟨24756954754450866214297529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 66018546011868976571460077 24756954754450866214297529)
              ·
                refine ⟨18567716065838149660723147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24756954754450866214297529 18567716065838149660723147)
                ·
                  refine ⟨27851574098757224491084721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18567716065838149660723147 27851574098757224491084721)
                  ·
                    refine ⟨20888680574067918368313541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27851574098757224491084721 20888680574067918368313541)
                    ·
                      refine ⟨3916627607637734694058789, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20888680574067918368313541 3916627607637734694058789)
                      ·
                        rfl

theorem cell23_7627605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 3, 2, 1, 2, 4].length) (baseStart_7627605 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7627605 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7627605 prefixEnd_7627605 := by exact prefixLift 7627605
  have htrace : WordTrace (prefixWord ++ tailWord_7627605) baseStart_7627605 baseEnd_7627605 := by
    simpa [prefixWord, tailWord_7627605, baseEnd_7627605] using wordTrace_append hprefix tailTrace_7627605
  have hstable : (prefixWord ++ tailWord_7627605).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7627605).length < 2 ^ (prefixWord ++ tailWord_7627605).sum := by decide
  have hdescent : baseEnd_7627605 < baseStart_7627605 := by decide
  rcases family_descends (prefixWord ++ tailWord_7627605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7627612 : List Nat := [2, 2, 4, 2, 1, 1, 3, 1, 1, 1, 5]
def baseStart_7627612 : Nat := 118140960795 + 7627612 * 2 ^ 59
def prefixEnd_7627612 : Nat := 4983230072969 + 3 ^ 40 * 7627612 * 2
def baseEnd_7627612 : Nat := 3916631202002316166671257

theorem tailTrace_7627612 : CollatzResearch.WordTrace tailWord_7627612 prefixEnd_7627612 3916631202002316166671257 := by
  unfold tailWord_7627612
  simp only [CollatzResearch.WordTrace]
  refine ⟨139100932421235945631034545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 185467909894981260841379393 139100932421235945631034545)
  ·
    refine ⟨104325699315926959223275909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 139100932421235945631034545 104325699315926959223275909)
    ·
      refine ⟨19561068621736304854364233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 104325699315926959223275909 19561068621736304854364233)
      ·
        refine ⟨14670801466302228640773175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19561068621736304854364233 14670801466302228640773175)
        ·
          refine ⟨22006202199453342961159763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14670801466302228640773175 22006202199453342961159763)
          ·
            refine ⟨33009303299180014441739645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22006202199453342961159763 33009303299180014441739645)
            ·
              refine ⟨12378488737192505415652367, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33009303299180014441739645 12378488737192505415652367)
              ·
                refine ⟨18567733105788758123478551, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12378488737192505415652367 18567733105788758123478551)
                ·
                  refine ⟨27851599658683137185217827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18567733105788758123478551 27851599658683137185217827)
                  ·
                    refine ⟨41777399488024705777826741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27851599658683137185217827 41777399488024705777826741)
                    ·
                      refine ⟨3916631202002316166671257, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41777399488024705777826741 3916631202002316166671257)
                      ·
                        rfl

theorem cell23_7627612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 1, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 1, 3, 1, 1, 1, 5].length) (baseStart_7627612 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7627612 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7627612 prefixEnd_7627612 := by exact prefixLift 7627612
  have htrace : WordTrace (prefixWord ++ tailWord_7627612) baseStart_7627612 baseEnd_7627612 := by
    simpa [prefixWord, tailWord_7627612, baseEnd_7627612] using wordTrace_append hprefix tailTrace_7627612
  have hstable : (prefixWord ++ tailWord_7627612).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7627612).length < 2 ^ (prefixWord ++ tailWord_7627612).sum := by decide
  have hdescent : baseEnd_7627612 < baseStart_7627612 := by decide
  rcases family_descends (prefixWord ++ tailWord_7627612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7627628 : List Nat := [2, 2, 1, 1, 4, 1, 1, 1, 1, 9]
def baseStart_7627628 : Nat := 118140960795 + 7627628 * 2 ^ 59
def prefixEnd_7627628 : Nat := 4983230072969 + 3 ^ 40 * 7627628 * 2
def baseEnd_7627628 : Nat := 1305546472564262701357061

theorem tailTrace_7627628 : CollatzResearch.WordTrace tailWord_7627628 prefixEnd_7627628 1305546472564262701357061 := by
  unfold tailWord_7627628
  simp only [CollatzResearch.WordTrace]
  refine ⟨139101224205206962997325769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 185468298940275950663101025 139101224205206962997325769)
  ·
    refine ⟨104325918153905222247994327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 139101224205206962997325769 104325918153905222247994327)
    ·
      refine ⟨156488877230857833371991491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104325918153905222247994327 156488877230857833371991491)
      ·
        refine ⟨234733315846286750057987237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 156488877230857833371991491 234733315846286750057987237)
        ·
          refine ⟨44012496721178765635872607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 234733315846286750057987237 44012496721178765635872607)
          ·
            refine ⟨66018745081768148453808911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44012496721178765635872607 66018745081768148453808911)
            ·
              refine ⟨99028117622652222680713367, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66018745081768148453808911 99028117622652222680713367)
              ·
                refine ⟨148542176433978334021070051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 99028117622652222680713367 148542176433978334021070051)
                ·
                  refine ⟨222813264650967501031605077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 148542176433978334021070051 222813264650967501031605077)
                  ·
                    refine ⟨1305546472564262701357061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 222813264650967501031605077 1305546472564262701357061)
                    ·
                      rfl

theorem cell23_7627628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 9].length) (baseStart_7627628 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7627628 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7627628 prefixEnd_7627628 := by exact prefixLift 7627628
  have htrace : WordTrace (prefixWord ++ tailWord_7627628) baseStart_7627628 baseEnd_7627628 := by
    simpa [prefixWord, tailWord_7627628, baseEnd_7627628] using wordTrace_append hprefix tailTrace_7627628
  have hstable : (prefixWord ++ tailWord_7627628).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7627628).length < 2 ^ (prefixWord ++ tailWord_7627628).sum := by decide
  have hdescent : baseEnd_7627628 < baseStart_7627628 := by decide
  rcases family_descends (prefixWord ++ tailWord_7627628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7627669 : List Nat := [1, 3, 2, 1, 1, 5, 1, 3, 1, 3, 2]
def baseStart_7627669 : Nat := 118140960795 + 7627669 * 2 ^ 59
def prefixEnd_7627669 : Nat := 4983230072969 + 3 ^ 40 * 7627669 * 2
def baseEnd_7627669 : Nat := 3916660470399622443658495

theorem tailTrace_7627669 : CollatzResearch.WordTrace tailWord_7627669 prefixEnd_7627669 3916660470399622443658495 := by
  unfold tailWord_7627669
  simp only [CollatzResearch.WordTrace]
  refine ⟨278203943803265389996894061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185469295868843593331262707 278203943803265389996894061)
  ·
    refine ⟨104326478926224521248835273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 278203943803265389996894061 104326478926224521248835273)
    ·
      refine ⟨78244859194668390936626455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 104326478926224521248835273 78244859194668390936626455)
      ·
        refine ⟨117367288792002586404939683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78244859194668390936626455 117367288792002586404939683)
        ·
          refine ⟨176050933188003879607409525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 117367288792002586404939683 176050933188003879607409525)
          ·
            refine ⟨16504774986375363713194643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 176050933188003879607409525 16504774986375363713194643)
            ·
              refine ⟨24757162479563045569791965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16504774986375363713194643 24757162479563045569791965)
              ·
                refine ⟨9283935929836142088671987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24757162479563045569791965 9283935929836142088671987)
                ·
                  refine ⟨13925903894754213133007981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9283935929836142088671987 13925903894754213133007981)
                  ·
                    refine ⟨5222213960532829924877993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13925903894754213133007981 5222213960532829924877993)
                    ·
                      refine ⟨3916660470399622443658495, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5222213960532829924877993 3916660470399622443658495)
                      ·
                        rfl

theorem cell23_7627669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 5, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 5, 1, 3, 1, 3, 2].length) (baseStart_7627669 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7627669 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7627669 prefixEnd_7627669 := by exact prefixLift 7627669
  have htrace : WordTrace (prefixWord ++ tailWord_7627669) baseStart_7627669 baseEnd_7627669 := by
    simpa [prefixWord, tailWord_7627669, baseEnd_7627669] using wordTrace_append hprefix tailTrace_7627669
  have hstable : (prefixWord ++ tailWord_7627669).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7627669).length < 2 ^ (prefixWord ++ tailWord_7627669).sum := by decide
  have hdescent : baseEnd_7627669 < baseStart_7627669 := by decide
  rcases family_descends (prefixWord ++ tailWord_7627669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7627693 : List Nat := [1, 5, 2, 3, 2, 1, 1, 1, 1, 3, 3]
def baseStart_7627693 : Nat := 118140960795 + 7627693 * 2 ^ 59
def prefixEnd_7627693 : Nat := 4983230072969 + 3 ^ 40 * 7627693 * 2
def baseEnd_7627693 : Nat := 3916672793935330349758385

theorem tailTrace_7627693 : CollatzResearch.WordTrace tailWord_7627693 prefixEnd_7627693 3916672793935330349758385 := by
  unfold tailWord_7627693
  simp only [CollatzResearch.WordTrace]
  refine ⟨278204819155178442095767733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185469879436785628063845155 278204819155178442095767733)
  ·
    refine ⟨26081701795797978946478225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 278204819155178442095767733 26081701795797978946478225)
    ·
      refine ⟨19561276346848484209858669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26081701795797978946478225 19561276346848484209858669)
      ·
        refine ⟨7335478630068181578697001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19561276346848484209858669 7335478630068181578697001)
        ·
          refine ⟨5501608972551136184022751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7335478630068181578697001 5501608972551136184022751)
          ·
            refine ⟨8252413458826704276034127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5501608972551136184022751 8252413458826704276034127)
            ·
              refine ⟨12378620188240056414051191, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8252413458826704276034127 12378620188240056414051191)
              ·
                refine ⟨18567930282360084621076787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12378620188240056414051191 18567930282360084621076787)
                ·
                  refine ⟨27851895423540126931615181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18567930282360084621076787 27851895423540126931615181)
                  ·
                    refine ⟨10444460783827547599355693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27851895423540126931615181 10444460783827547599355693)
                    ·
                      refine ⟨3916672793935330349758385, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10444460783827547599355693 3916672793935330349758385)
                      ·
                        rfl

theorem cell23_7627693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 2, 1, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 2, 1, 1, 1, 1, 3, 3].length) (baseStart_7627693 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7627693 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7627693 prefixEnd_7627693 := by exact prefixLift 7627693
  have htrace : WordTrace (prefixWord ++ tailWord_7627693) baseStart_7627693 baseEnd_7627693 := by
    simpa [prefixWord, tailWord_7627693, baseEnd_7627693] using wordTrace_append hprefix tailTrace_7627693
  have hstable : (prefixWord ++ tailWord_7627693).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7627693).length < 2 ^ (prefixWord ++ tailWord_7627693).sum := by decide
  have hdescent : baseEnd_7627693 < baseStart_7627693 := by decide
  rcases family_descends (prefixWord ++ tailWord_7627693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7627705 : List Nat := [1, 2, 1, 4, 2, 2, 2, 2, 7]
def baseStart_7627705 : Nat := 118140960795 + 7627705 * 2 ^ 59
def prefixEnd_7627705 : Nat := 4983230072969 + 3 ^ 40 * 7627705 * 2
def baseEnd_7627705 : Nat := 435186550633687144756481

theorem tailTrace_7627705 : CollatzResearch.WordTrace tailWord_7627705 prefixEnd_7627705 435186550633687144756481 := by
  unfold tailWord_7627705
  simp only [CollatzResearch.WordTrace]
  refine ⟨278205256831134968145204569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185470171220756645430136379 278205256831134968145204569)
  ·
    refine ⟨208653942623351226108903427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 278205256831134968145204569 208653942623351226108903427)
    ·
      refine ⟨312980913935026839163355141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 208653942623351226108903427 312980913935026839163355141)
      ·
        refine ⟨58683921362817532343129089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 312980913935026839163355141 58683921362817532343129089)
        ·
          refine ⟨44012941022113149257346817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58683921362817532343129089 44012941022113149257346817)
          ·
            refine ⟨33009705766584861943010113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44012941022113149257346817 33009705766584861943010113)
            ·
              refine ⟨24757279324938646457257585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33009705766584861943010113 24757279324938646457257585)
              ·
                refine ⟨18567959493703984842943189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24757279324938646457257585 18567959493703984842943189)
                ·
                  refine ⟨435186550633687144756481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18567959493703984842943189 435186550633687144756481)
                  ·
                    rfl

theorem cell23_7627705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 2, 2, 2, 7].length) (baseStart_7627705 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7627705 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7627705 prefixEnd_7627705 := by exact prefixLift 7627705
  have htrace : WordTrace (prefixWord ++ tailWord_7627705) baseStart_7627705 baseEnd_7627705 := by
    simpa [prefixWord, tailWord_7627705, baseEnd_7627705] using wordTrace_append hprefix tailTrace_7627705
  have hstable : (prefixWord ++ tailWord_7627705).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7627705).length < 2 ^ (prefixWord ++ tailWord_7627705).sum := by decide
  have hdescent : baseEnd_7627705 < baseStart_7627705 := by decide
  rcases family_descends (prefixWord ++ tailWord_7627705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7627772 : List Nat := [2, 2, 2, 1, 2, 3, 1, 3, 2, 1, 4]
def baseStart_7627772 : Nat := 118140960795 + 7627772 * 2 ^ 59
def prefixEnd_7627772 : Nat := 4983230072969 + 3 ^ 40 * 7627772 * 2
def baseEnd_7627772 : Nat := 3916713358907035540670521

theorem tailTrace_7627772 : CollatzResearch.WordTrace tailWord_7627772 prefixEnd_7627772 3916713358907035540670521 := by
  unfold tailWord_7627772
  simp only [CollatzResearch.WordTrace]
  refine ⟨139103850260946119293946785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 185471800347928159058595713 139103850260946119293946785)
  ·
    refine ⟨104327887695709589470460089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 139103850260946119293946785 104327887695709589470460089)
    ·
      refine ⟨78245915771782192102845067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 104327887695709589470460089 78245915771782192102845067)
      ·
        refine ⟨117368873657673288154267601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78245915771782192102845067 117368873657673288154267601)
        ·
          refine ⟨88026655243254966115700701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 117368873657673288154267601 88026655243254966115700701)
          ·
            refine ⟨33009995716220612293387763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 88026655243254966115700701 33009995716220612293387763)
            ·
              refine ⟨49514993574330918440081645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33009995716220612293387763 49514993574330918440081645)
              ·
                refine ⟨18568122590374094415030617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 49514993574330918440081645 18568122590374094415030617)
                ·
                  refine ⟨13926091942780570811272963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18568122590374094415030617 13926091942780570811272963)
                  ·
                    refine ⟨20889137914170856216909445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13926091942780570811272963 20889137914170856216909445)
                    ·
                      refine ⟨3916713358907035540670521, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20889137914170856216909445 3916713358907035540670521)
                      ·
                        rfl

theorem cell23_7627772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 3, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 3, 1, 3, 2, 1, 4].length) (baseStart_7627772 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7627772 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7627772 prefixEnd_7627772 := by exact prefixLift 7627772
  have htrace : WordTrace (prefixWord ++ tailWord_7627772) baseStart_7627772 baseEnd_7627772 := by
    simpa [prefixWord, tailWord_7627772, baseEnd_7627772] using wordTrace_append hprefix tailTrace_7627772
  have hstable : (prefixWord ++ tailWord_7627772).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7627772).length < 2 ^ (prefixWord ++ tailWord_7627772).sum := by decide
  have hdescent : baseEnd_7627772 < baseStart_7627772 := by decide
  rcases family_descends (prefixWord ++ tailWord_7627772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7627846 : List Nat := [6, 1, 1, 1, 1, 2, 3, 2, 6]
def baseStart_7627846 : Nat := 118140960795 + 7627846 * 2 ^ 59
def prefixEnd_7627846 : Nat := 4983230072969 + 3 ^ 40 * 7627846 * 2
def baseEnd_7627846 : Nat := 435194595163940916793909

theorem tailTrace_7627846 : CollatzResearch.WordTrace tailWord_7627846 prefixEnd_7627846 435194595163940916793909 := by
  unfold tailWord_7627846
  simp only [CollatzResearch.WordTrace]
  refine ⟨8694074985113254663315231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 185473599682416099484058261 8694074985113254663315231)
  ·
    refine ⟨13041112477669881994972847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8694074985113254663315231 13041112477669881994972847)
    ·
      refine ⟨19561668716504822992459271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13041112477669881994972847 19561668716504822992459271)
      ·
        refine ⟨29342503074757234488688907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19561668716504822992459271 29342503074757234488688907)
        ·
          refine ⟨44013754612135851733033361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29342503074757234488688907 44013754612135851733033361)
          ·
            refine ⟨33010315959101888799775021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44013754612135851733033361 33010315959101888799775021)
            ·
              refine ⟨12378868484663208299915633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33010315959101888799775021 12378868484663208299915633)
              ·
                refine ⟨9284151363497406224936725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12378868484663208299915633 9284151363497406224936725)
                ·
                  refine ⟨435194595163940916793909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9284151363497406224936725 435194595163940916793909)
                  ·
                    rfl

theorem cell23_7627846_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 2, 3, 2, 6].length) (baseStart_7627846 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7627846 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7627846 prefixEnd_7627846 := by exact prefixLift 7627846
  have htrace : WordTrace (prefixWord ++ tailWord_7627846) baseStart_7627846 baseEnd_7627846 := by
    simpa [prefixWord, tailWord_7627846, baseEnd_7627846] using wordTrace_append hprefix tailTrace_7627846
  have hstable : (prefixWord ++ tailWord_7627846).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7627846).length < 2 ^ (prefixWord ++ tailWord_7627846).sum := by decide
  have hdescent : baseEnd_7627846 < baseStart_7627846 := by decide
  rcases family_descends (prefixWord ++ tailWord_7627846) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7627879 : List Nat := [1, 1, 5, 1, 1, 3, 1, 4, 1, 1, 4]
def baseStart_7627879 : Nat := 118140960795 + 7627879 * 2 ^ 59
def prefixEnd_7627879 : Nat := 4983230072969 + 3 ^ 40 * 7627879 * 2
def baseEnd_7627879 : Nat := 3916768301337066622032529

theorem tailTrace_7627879 : CollatzResearch.WordTrace tailWord_7627879 prefixEnd_7627879 3916768301337066622032529 := by
  unfold tailWord_7627879
  simp only [CollatzResearch.WordTrace]
  refine ⟨278211603132504595862038691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185474402088336397241359127 278211603132504595862038691)
  ·
    refine ⟨417317404698756893793058037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 278211603132504595862038691 417317404698756893793058037)
    ·
      refine ⟨39123506690508458793099191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 417317404698756893793058037 39123506690508458793099191)
      ·
        refine ⟨58685260035762688189648787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39123506690508458793099191 58685260035762688189648787)
        ·
          refine ⟨88027890053644032284473181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58685260035762688189648787 88027890053644032284473181)
          ·
            refine ⟨33010458770116512106677443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 88027890053644032284473181 33010458770116512106677443)
            ·
              refine ⟨49515688155174768160016165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33010458770116512106677443 49515688155174768160016165)
              ·
                refine ⟨9284191529095269030003031, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 49515688155174768160016165 9284191529095269030003031)
                ·
                  refine ⟨13926287293642903545004547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9284191529095269030003031 13926287293642903545004547)
                  ·
                    refine ⟨20889430940464355317506821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13926287293642903545004547 20889430940464355317506821)
                    ·
                      refine ⟨3916768301337066622032529, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20889430940464355317506821 3916768301337066622032529)
                      ·
                        rfl

theorem cell23_7627879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 3, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 3, 1, 4, 1, 1, 4].length) (baseStart_7627879 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7627879 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7627879 prefixEnd_7627879 := by exact prefixLift 7627879
  have htrace : WordTrace (prefixWord ++ tailWord_7627879) baseStart_7627879 baseEnd_7627879 := by
    simpa [prefixWord, tailWord_7627879, baseEnd_7627879] using wordTrace_append hprefix tailTrace_7627879
  have hstable : (prefixWord ++ tailWord_7627879).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7627879).length < 2 ^ (prefixWord ++ tailWord_7627879).sum := by decide
  have hdescent : baseEnd_7627879 < baseStart_7627879 := by decide
  rcases family_descends (prefixWord ++ tailWord_7627879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7627913 : List Nat := [1, 2, 1, 1, 4, 5, 1, 1, 3, 2, 2]
def baseStart_7627913 : Nat := 118140960795 + 7627913 * 2 ^ 59
def prefixEnd_7627913 : Nat := 4983230072969 + 3 ^ 40 * 7627913 * 2
def baseEnd_7627913 : Nat := 3916785759679319489007373

theorem tailTrace_7627913 : CollatzResearch.WordTrace tailWord_7627913 prefixEnd_7627913 3916785759679319489007373 := by
  unfold tailWord_7627913
  simp only [CollatzResearch.WordTrace]
  refine ⟨278212843214381419668776393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185475228809587613112517595 278212843214381419668776393)
  ·
    refine ⟨208659632410786064751582295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 278212843214381419668776393 208659632410786064751582295)
    ·
      refine ⟨312989448616179097127373443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 208659632410786064751582295 312989448616179097127373443)
      ·
        refine ⟨469484172924268645691060165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 312989448616179097127373443 469484172924268645691060165)
        ·
          refine ⟨88028282423300371067073781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 469484172924268645691060165 88028282423300371067073781)
          ·
            refine ⟨8252651477184409787538167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 88028282423300371067073781 8252651477184409787538167)
            ·
              refine ⟨12378977215776614681307251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8252651477184409787538167 12378977215776614681307251)
              ·
                refine ⟨18568465823664922021960877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12378977215776614681307251 18568465823664922021960877)
                ·
                  refine ⟨6963174683874345758235329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18568465823664922021960877 6963174683874345758235329)
                  ·
                    refine ⟨5222381012905759318676497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6963174683874345758235329 5222381012905759318676497)
                    ·
                      refine ⟨3916785759679319489007373, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5222381012905759318676497 3916785759679319489007373)
                      ·
                        rfl

theorem cell23_7627913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 5, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 5, 1, 1, 3, 2, 2].length) (baseStart_7627913 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7627913 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7627913 prefixEnd_7627913 := by exact prefixLift 7627913
  have htrace : WordTrace (prefixWord ++ tailWord_7627913) baseStart_7627913 baseEnd_7627913 := by
    simpa [prefixWord, tailWord_7627913, baseEnd_7627913] using wordTrace_append hprefix tailTrace_7627913
  have hstable : (prefixWord ++ tailWord_7627913).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7627913).length < 2 ^ (prefixWord ++ tailWord_7627913).sum := by decide
  have hdescent : baseEnd_7627913 < baseStart_7627913 := by decide
  rcases family_descends (prefixWord ++ tailWord_7627913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7627946 : List Nat := [3, 1, 5, 1, 1, 1, 1, 1, 3, 3, 3]
def baseStart_7627946 : Nat := 118140960795 + 7627946 * 2 ^ 59
def prefixEnd_7627946 : Nat := 4983230072969 + 3 ^ 40 * 7627946 * 2
def baseEnd_7627946 : Nat := 3916802704540917859894721

theorem tailTrace_7627946 : CollatzResearch.WordTrace tailWord_7627946 prefixEnd_7627946 3916802704540917859894721 := by
  unfold tailWord_7627946
  simp only [CollatzResearch.WordTrace]
  refine ⟨69553511705815466576181923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 185476031215507910869818461 69553511705815466576181923)
  ·
    refine ⟨104330267558723199864272885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69553511705815466576181923 104330267558723199864272885)
    ·
      refine ⟨9780962583630299987275583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 104330267558723199864272885 9780962583630299987275583)
      ·
        refine ⟨14671443875445449980913375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9780962583630299987275583 14671443875445449980913375)
        ·
          refine ⟨22007165813168174971370063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14671443875445449980913375 22007165813168174971370063)
          ·
            refine ⟨33010748719752262457055095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22007165813168174971370063 33010748719752262457055095)
            ·
              refine ⟨49516123079628393685582643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33010748719752262457055095 49516123079628393685582643)
              ·
                refine ⟨74274184619442590528373965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49516123079628393685582643 74274184619442590528373965)
                ·
                  refine ⟨27852819232290971448140237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 74274184619442590528373965 27852819232290971448140237)
                  ·
                    refine ⟨10444807212109114293052589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27852819232290971448140237 10444807212109114293052589)
                    ·
                      refine ⟨3916802704540917859894721, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10444807212109114293052589 3916802704540917859894721)
                      ·
                        rfl

theorem cell23_7627946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 1, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 1, 1, 1, 3, 3, 3].length) (baseStart_7627946 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7627946 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7627946 prefixEnd_7627946 := by exact prefixLift 7627946
  have htrace : WordTrace (prefixWord ++ tailWord_7627946) baseStart_7627946 baseEnd_7627946 := by
    simpa [prefixWord, tailWord_7627946, baseEnd_7627946] using wordTrace_append hprefix tailTrace_7627946
  have hstable : (prefixWord ++ tailWord_7627946).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7627946).length < 2 ^ (prefixWord ++ tailWord_7627946).sum := by decide
  have hdescent : baseEnd_7627946 < baseStart_7627946 := by decide
  rcases family_descends (prefixWord ++ tailWord_7627946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7627962 : List Nat := [3, 1, 1, 1, 2, 2, 1, 4, 2, 6]
def baseStart_7627962 : Nat := 118140960795 + 7627962 * 2 ^ 59
def prefixEnd_7627962 : Nat := 4983230072969 + 3 ^ 40 * 7627962 * 2
def baseEnd_7627962 : Nat := 1305603640077129932431549

theorem tailTrace_7627962 : CollatzResearch.WordTrace tailWord_7627962 prefixEnd_7627962 1305603640077129932431549 := by
  unfold tailWord_7627962
  simp only [CollatzResearch.WordTrace]
  refine ⟨69553657597800975259327535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 185476420260802600691540093 69553657597800975259327535)
  ·
    refine ⟨104330486396701462888991303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69553657597800975259327535 104330486396701462888991303)
    ·
      refine ⟨156495729595052194333486955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104330486396701462888991303 156495729595052194333486955)
      ·
        refine ⟨234743594392578291500230433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 156495729595052194333486955 234743594392578291500230433)
        ·
          refine ⟨176057695794433718625172825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 234743594392578291500230433 176057695794433718625172825)
          ·
            refine ⟨132043271845825288968879619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 176057695794433718625172825 132043271845825288968879619)
            ·
              refine ⟨198064907768737933453319429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 132043271845825288968879619 198064907768737933453319429)
              ·
                refine ⟨37137170206638362522497393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 198064907768737933453319429 37137170206638362522497393)
                ·
                  refine ⟨27852877654978771891873045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37137170206638362522497393 27852877654978771891873045)
                  ·
                    refine ⟨1305603640077129932431549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27852877654978771891873045 1305603640077129932431549)
                    ·
                      rfl

theorem cell23_7627962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 1, 4, 2, 6].length) (baseStart_7627962 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7627962 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7627962 prefixEnd_7627962 := by exact prefixLift 7627962
  have htrace : WordTrace (prefixWord ++ tailWord_7627962) baseStart_7627962 baseEnd_7627962 := by
    simpa [prefixWord, tailWord_7627962, baseEnd_7627962] using wordTrace_append hprefix tailTrace_7627962
  have hstable : (prefixWord ++ tailWord_7627962).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7627962).length < 2 ^ (prefixWord ++ tailWord_7627962).sum := by decide
  have hdescent : baseEnd_7627962 < baseStart_7627962 := by decide
  rcases family_descends (prefixWord ++ tailWord_7627962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7627970 : List Nat := [3, 5, 1, 1, 3, 1, 1, 8]
def baseStart_7627970 : Nat := 118140960795 + 7627970 * 2 ^ 59
def prefixEnd_7627970 : Nat := 4983230072969 + 3 ^ 40 * 7627970 * 2
def baseEnd_7627970 : Nat := 145067223262097250592393

theorem tailTrace_7627970 : CollatzResearch.WordTrace tailWord_7627970 prefixEnd_7627970 145067223262097250592393 := by
  unfold tailWord_7627970
  simp only [CollatzResearch.WordTrace]
  refine ⟨69553730543793729600900341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 185476614783449945602400909 69553730543793729600900341)
  ·
    refine ⟨6520662238480662150084407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 69553730543793729600900341 6520662238480662150084407)
    ·
      refine ⟨9780993357720993225126611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6520662238480662150084407 9780993357720993225126611)
      ·
        refine ⟨14671490036581489837689917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9780993357720993225126611 14671490036581489837689917)
        ·
          refine ⟨5501808763718058689133719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14671490036581489837689917 5501808763718058689133719)
          ·
            refine ⟨8252713145577088033700579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5501808763718058689133719 8252713145577088033700579)
            ·
              refine ⟨12379069718365632050550869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8252713145577088033700579 12379069718365632050550869)
              ·
                refine ⟨145067223262097250592393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 12379069718365632050550869 145067223262097250592393)
                ·
                  rfl

theorem cell23_7627970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 3, 1, 1, 8].length) (baseStart_7627970 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7627970 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7627970 prefixEnd_7627970 := by exact prefixLift 7627970
  have htrace : WordTrace (prefixWord ++ tailWord_7627970) baseStart_7627970 baseEnd_7627970 := by
    simpa [prefixWord, tailWord_7627970, baseEnd_7627970] using wordTrace_append hprefix tailTrace_7627970
  have hstable : (prefixWord ++ tailWord_7627970).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7627970).length < 2 ^ (prefixWord ++ tailWord_7627970).sum := by decide
  have hdescent : baseEnd_7627970 < baseStart_7627970 := by decide
  rcases family_descends (prefixWord ++ tailWord_7627970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7628007 : List Nat := [1, 1, 5, 3, 2, 2, 2, 1, 1, 3, 2]
def baseStart_7628007 : Nat := 118140960795 + 7628007 * 2 ^ 59
def prefixEnd_7628007 : Nat := 4983230072969 + 3 ^ 40 * 7628007 * 2
def baseEnd_7628007 : Nat := 3916834026860842121231941

theorem tailTrace_7628007 : CollatzResearch.WordTrace tailWord_7628007 prefixEnd_7628007 3916834026860842121231941 := by
  unfold tailWord_7628007
  simp only [CollatzResearch.WordTrace]
  refine ⟨278216271676040873722698275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185477514450693915815132183 278216271676040873722698275)
  ·
    refine ⟨417324407514061310584047413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 278216271676040873722698275 417324407514061310584047413)
    ·
      refine ⟨39124163204443247867254445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 417324407514061310584047413 39124163204443247867254445)
      ·
        refine ⟨14671561201666217950220417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39124163204443247867254445 14671561201666217950220417)
        ·
          refine ⟨11003670901249663462665313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14671561201666217950220417 11003670901249663462665313)
          ·
            refine ⟨8252753175937247596998985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11003670901249663462665313 8252753175937247596998985)
            ·
              refine ⟨6189564881952935697749239, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8252753175937247596998985 6189564881952935697749239)
              ·
                refine ⟨9284347322929403546623859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6189564881952935697749239 9284347322929403546623859)
                ·
                  refine ⟨13926520984394105319935789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9284347322929403546623859 13926520984394105319935789)
                  ·
                    refine ⟨5222445369147789494975921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13926520984394105319935789 5222445369147789494975921)
                    ·
                      refine ⟨3916834026860842121231941, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5222445369147789494975921 3916834026860842121231941)
                      ·
                        rfl

theorem cell23_7628007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 2, 2, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 2, 2, 2, 1, 1, 3, 2].length) (baseStart_7628007 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7628007 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7628007 prefixEnd_7628007 := by exact prefixLift 7628007
  have htrace : WordTrace (prefixWord ++ tailWord_7628007) baseStart_7628007 baseEnd_7628007 := by
    simpa [prefixWord, tailWord_7628007, baseEnd_7628007] using wordTrace_append hprefix tailTrace_7628007
  have hstable : (prefixWord ++ tailWord_7628007).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7628007).length < 2 ^ (prefixWord ++ tailWord_7628007).sum := by decide
  have hdescent : baseEnd_7628007 < baseStart_7628007 := by decide
  rcases family_descends (prefixWord ++ tailWord_7628007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7628019 : List Nat := [1, 1, 1, 2, 2, 5, 1, 2, 2, 3, 3]
def baseStart_7628019 : Nat := 118140960795 + 7628019 * 2 ^ 59
def prefixEnd_7628019 : Nat := 4983230072969 + 3 ^ 40 * 7628019 * 2
def baseEnd_7628019 : Nat := 3916840188628696074281885

theorem tailTrace_7628019 : CollatzResearch.WordTrace tailWord_7628019 prefixEnd_7628019 3916840188628696074281885 := by
  unfold tailWord_7628019
  simp only [CollatzResearch.WordTrace]
  refine ⟨278216709351997399772135111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185477806234664933181423407 278216709351997399772135111)
  ·
    refine ⟨417325064027996099658202667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 278216709351997399772135111 417325064027996099658202667)
    ·
      refine ⟨625987596041994149487304001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 417325064027996099658202667 625987596041994149487304001)
      ·
        refine ⟨469490697031495612115478001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 625987596041994149487304001 469490697031495612115478001)
        ·
          refine ⟨352118022773621709086608501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 469490697031495612115478001 352118022773621709086608501)
          ·
            refine ⟨33011064635027035226869547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 352118022773621709086608501 33011064635027035226869547)
            ·
              refine ⟨49516596952540552840304321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33011064635027035226869547 49516596952540552840304321)
              ·
                refine ⟨37137447714405414630228241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49516596952540552840304321 37137447714405414630228241)
                ·
                  refine ⟨27853085785804060972671181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37137447714405414630228241 27853085785804060972671181)
                  ·
                    refine ⟨10444907169676522864751693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27853085785804060972671181 10444907169676522864751693)
                    ·
                      refine ⟨3916840188628696074281885, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10444907169676522864751693 3916840188628696074281885)
                      ·
                        rfl

theorem cell23_7628019_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 5, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 5, 1, 2, 2, 3, 3].length) (baseStart_7628019 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7628019 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7628019 prefixEnd_7628019 := by exact prefixLift 7628019
  have htrace : WordTrace (prefixWord ++ tailWord_7628019) baseStart_7628019 baseEnd_7628019 := by
    simpa [prefixWord, tailWord_7628019, baseEnd_7628019] using wordTrace_append hprefix tailTrace_7628019
  have hstable : (prefixWord ++ tailWord_7628019).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7628019).length < 2 ^ (prefixWord ++ tailWord_7628019).sum := by decide
  have hdescent : baseEnd_7628019 < baseStart_7628019 := by decide
  rcases family_descends (prefixWord ++ tailWord_7628019) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7628032 : List Nat := [2, 1, 1, 2, 1, 1, 3, 3, 1, 1, 7]
def baseStart_7628032 : Nat := 118140960795 + 7628032 * 2 ^ 59
def prefixEnd_7628032 : Nat := 4983230072969 + 3 ^ 40 * 7628032 * 2
def baseEnd_7628032 : Nat := 3916846863877204523419325

theorem tailTrace_7628032 : CollatzResearch.WordTrace tailWord_7628032 prefixEnd_7628032 3916846863877204523419325 := by
  unfold tailWord_7628032
  simp only [CollatzResearch.WordTrace]
  refine ⟨139108591750475151496179175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 185478122333966868661572233 139108591750475151496179175)
  ·
    refine ⟨208662887625712727244268763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139108591750475151496179175 208662887625712727244268763)
    ·
      refine ⟨312994331438569090866403145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 208662887625712727244268763 312994331438569090866403145)
      ·
        refine ⟨234745748578926818149802359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 312994331438569090866403145 234745748578926818149802359)
        ·
          refine ⟨352118622868390227224703539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 234745748578926818149802359 352118622868390227224703539)
          ·
            refine ⟨528177934302585340837055309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 352118622868390227224703539 528177934302585340837055309)
            ·
              refine ⟨198066725363469502813895741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 528177934302585340837055309 198066725363469502813895741)
              ·
                refine ⟨74275022011301063555210903, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 198066725363469502813895741 74275022011301063555210903)
                ·
                  refine ⟨111412533016951595332816355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 74275022011301063555210903 111412533016951595332816355)
                  ·
                    refine ⟨167118799525427392999224533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 111412533016951595332816355 167118799525427392999224533)
                    ·
                      refine ⟨3916846863877204523419325, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 167118799525427392999224533 3916846863877204523419325)
                      ·
                        rfl

theorem cell23_7628032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 3, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 3, 3, 1, 1, 7].length) (baseStart_7628032 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7628032 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7628032 prefixEnd_7628032 := by exact prefixLift 7628032
  have htrace : WordTrace (prefixWord ++ tailWord_7628032) baseStart_7628032 baseEnd_7628032 := by
    simpa [prefixWord, tailWord_7628032, baseEnd_7628032] using wordTrace_append hprefix tailTrace_7628032
  have hstable : (prefixWord ++ tailWord_7628032).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7628032).length < 2 ^ (prefixWord ++ tailWord_7628032).sum := by decide
  have hdescent : baseEnd_7628032 < baseStart_7628032 := by decide
  rcases family_descends (prefixWord ++ tailWord_7628032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7628036 : List Nat := [2, 3, 2, 2, 2, 1, 2, 1, 2, 3, 3]
def baseStart_7628036 : Nat := 118140960795 + 7628036 * 2 ^ 59
def prefixEnd_7628036 : Nat := 4983230072969 + 3 ^ 40 * 7628036 * 2
def baseEnd_7628036 : Nat := 3916848917799822507769307

theorem tailTrace_7628036 : CollatzResearch.WordTrace tailWord_7628036 prefixEnd_7628036 3916848917799822507769307 := by
  unfold tailWord_7628036
  simp only [CollatzResearch.WordTrace]
  refine ⟨139108664696467905837751981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 185478219595290541117002641 139108664696467905837751981)
  ·
    refine ⟨52165749261175464689156993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 139108664696467905837751981 52165749261175464689156993)
    ·
      refine ⟨39124311945881598516867745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52165749261175464689156993 39124311945881598516867745)
      ·
        refine ⟨29343233959411198887650809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39124311945881598516867745 29343233959411198887650809)
        ·
          refine ⟨22007425469558399165738107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29343233959411198887650809 22007425469558399165738107)
          ·
            refine ⟨33011138204337598748607161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22007425469558399165738107 33011138204337598748607161)
            ·
              refine ⟨24758353653253199061455371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33011138204337598748607161 24758353653253199061455371)
              ·
                refine ⟨37137530479879798592183057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24758353653253199061455371 37137530479879798592183057)
                ·
                  refine ⟨27853147859909848944137293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37137530479879798592183057 27853147859909848944137293)
                  ·
                    refine ⟨10444930447466193354051485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27853147859909848944137293 10444930447466193354051485)
                    ·
                      refine ⟨3916848917799822507769307, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10444930447466193354051485 3916848917799822507769307)
                      ·
                        rfl

theorem cell23_7628036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 1, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 1, 2, 1, 2, 3, 3].length) (baseStart_7628036 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7628036 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7628036 prefixEnd_7628036 := by exact prefixLift 7628036
  have htrace : WordTrace (prefixWord ++ tailWord_7628036) baseStart_7628036 baseEnd_7628036 := by
    simpa [prefixWord, tailWord_7628036, baseEnd_7628036] using wordTrace_append hprefix tailTrace_7628036
  have hstable : (prefixWord ++ tailWord_7628036).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7628036).length < 2 ^ (prefixWord ++ tailWord_7628036).sum := by decide
  have hdescent : baseEnd_7628036 < baseStart_7628036 := by decide
  rcases family_descends (prefixWord ++ tailWord_7628036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7628059 : List Nat := [1, 1, 1, 1, 1, 1, 5, 5, 2, 1, 4]
def baseStart_7628059 : Nat := 118140960795 + 7628059 * 2 ^ 59
def prefixEnd_7628059 : Nat := 4983230072969 + 3 ^ 40 * 7628059 * 2
def baseEnd_7628059 : Nat := 3916860727854875917781701

theorem tailTrace_7628059 : CollatzResearch.WordTrace tailWord_7628059 prefixEnd_7628059 3916860727854875917781701 := by
  unfold tailWord_7628059
  simp only [CollatzResearch.WordTrace]
  refine ⟨278218168271852486603591231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185478778847901657735727487 278218168271852486603591231)
  ·
    refine ⟨417327252407778729905386847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 278218168271852486603591231 417327252407778729905386847)
    ·
      refine ⟨625990878611668094858080271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 417327252407778729905386847 625990878611668094858080271)
      ·
        refine ⟨938986317917502142287120407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 625990878611668094858080271 938986317917502142287120407)
        ·
          refine ⟨1408479476876253213430680611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 938986317917502142287120407 1408479476876253213430680611)
          ·
            refine ⟨2112719215314379820146020917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1408479476876253213430680611 2112719215314379820146020917)
            ·
              refine ⟨198067426435723108138689461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 2112719215314379820146020917 198067426435723108138689461)
              ·
                refine ⟨18568821228349041388002137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 198067426435723108138689461 18568821228349041388002137)
                ·
                  refine ⟨13926615921261781041001603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18568821228349041388002137 13926615921261781041001603)
                  ·
                    refine ⟨20889923881892671561502405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13926615921261781041001603 20889923881892671561502405)
                    ·
                      refine ⟨3916860727854875917781701, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20889923881892671561502405 3916860727854875917781701)
                      ·
                        rfl

theorem cell23_7628059_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 5, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 5, 5, 2, 1, 4].length) (baseStart_7628059 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7628059 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7628059 prefixEnd_7628059 := by exact prefixLift 7628059
  have htrace : WordTrace (prefixWord ++ tailWord_7628059) baseStart_7628059 baseEnd_7628059 := by
    simpa [prefixWord, tailWord_7628059, baseEnd_7628059] using wordTrace_append hprefix tailTrace_7628059
  have hstable : (prefixWord ++ tailWord_7628059).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7628059).length < 2 ^ (prefixWord ++ tailWord_7628059).sum := by decide
  have hdescent : baseEnd_7628059 < baseStart_7628059 := by decide
  rcases family_descends (prefixWord ++ tailWord_7628059) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7628180 : List Nat := [2, 4, 2, 1, 2, 1, 4, 1, 1, 5]
def baseStart_7628180 : Nat := 118140960795 + 7628180 * 2 ^ 59
def prefixEnd_7628180 : Nat := 4983230072969 + 3 ^ 40 * 7628180 * 2
def baseEnd_7628180 : Nat := 1305640953004689981456215

theorem tailTrace_7628180 : CollatzResearch.WordTrace tailWord_7628180 prefixEnd_7628180 1305640953004689981456215 := by
  unfold tailWord_7628180
  simp only [CollatzResearch.WordTrace]
  refine ⟨139111290752207062134372997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 185481721002942749512497329 139111290752207062134372997)
  ·
    refine ⟨26083367016038824150194937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 139111290752207062134372997 26083367016038824150194937)
    ·
      refine ⟨19562525262029118112646203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26083367016038824150194937 19562525262029118112646203)
      ·
        refine ⟨29343787893043677168969305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19562525262029118112646203 29343787893043677168969305)
        ·
          refine ⟨22007840919782757876726979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29343787893043677168969305 22007840919782757876726979)
          ·
            refine ⟨33011761379674136815090469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22007840919782757876726979 33011761379674136815090469)
            ·
              refine ⟨6189705258688900652829463, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 33011761379674136815090469 6189705258688900652829463)
              ·
                refine ⟨9284557888033350979244195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6189705258688900652829463 9284557888033350979244195)
                ·
                  refine ⟨13926836832050026468866293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9284557888033350979244195 13926836832050026468866293)
                  ·
                    refine ⟨1305640953004689981456215, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13926836832050026468866293 1305640953004689981456215)
                    ·
                      rfl

theorem cell23_7628180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 1, 4, 1, 1, 5].length) (baseStart_7628180 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7628180 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7628180 prefixEnd_7628180 := by exact prefixLift 7628180
  have htrace : WordTrace (prefixWord ++ tailWord_7628180) baseStart_7628180 baseEnd_7628180 := by
    simpa [prefixWord, tailWord_7628180, baseEnd_7628180] using wordTrace_append hprefix tailTrace_7628180
  have hstable : (prefixWord ++ tailWord_7628180).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7628180).length < 2 ^ (prefixWord ++ tailWord_7628180).sum := by decide
  have hdescent : baseEnd_7628180 < baseStart_7628180 := by decide
  rcases family_descends (prefixWord ++ tailWord_7628180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7628183 : List Nat := [1, 1, 3, 3, 1, 1, 1, 1, 7, 2, 2]
def baseStart_7628183 : Nat := 118140960795 + 7628183 * 2 ^ 59
def prefixEnd_7628183 : Nat := 4983230072969 + 3 ^ 40 * 7628183 * 2
def baseEnd_7628183 : Nat := 3916924399456033432631131

theorem tailTrace_7628183 : CollatzResearch.WordTrace tailWord_7628183 prefixEnd_7628183 3916924399456033432631131 := by
  unfold tailWord_7628183
  simp only [CollatzResearch.WordTrace]
  refine ⟨278222690923403255781105203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185481793948935503854070135 278222690923403255781105203)
  ·
    refine ⟨417334036385104883671657805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 278222690923403255781105203 417334036385104883671657805)
    ·
      refine ⟨156500263644414331376871677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 417334036385104883671657805 156500263644414331376871677)
      ·
        refine ⟨58687598866655374266326879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 156500263644414331376871677 58687598866655374266326879)
        ·
          refine ⟨88031398299983061399490319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58687598866655374266326879 88031398299983061399490319)
          ·
            refine ⟨132047097449974592099235479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88031398299983061399490319 132047097449974592099235479)
            ·
              refine ⟨198070646174961888148853219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 132047097449974592099235479 198070646174961888148853219)
              ·
                refine ⟨297105969262442832223279829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 198070646174961888148853219 297105969262442832223279829)
                ·
                  refine ⟨6963421154588503880233121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 297105969262442832223279829 6963421154588503880233121)
                  ·
                    refine ⟨5222565865941377910174841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6963421154588503880233121 5222565865941377910174841)
                    ·
                      refine ⟨3916924399456033432631131, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5222565865941377910174841 3916924399456033432631131)
                      ·
                        rfl

theorem cell23_7628183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 1, 1, 7, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 1, 1, 7, 2, 2].length) (baseStart_7628183 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7628183 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7628183 prefixEnd_7628183 := by exact prefixLift 7628183
  have htrace : WordTrace (prefixWord ++ tailWord_7628183) baseStart_7628183 baseEnd_7628183 := by
    simpa [prefixWord, tailWord_7628183, baseEnd_7628183] using wordTrace_append hprefix tailTrace_7628183
  have hstable : (prefixWord ++ tailWord_7628183).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7628183).length < 2 ^ (prefixWord ++ tailWord_7628183).sum := by decide
  have hdescent : baseEnd_7628183 < baseStart_7628183 := by decide
  rcases family_descends (prefixWord ++ tailWord_7628183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7628186 : List Nat := [3, 1, 1, 4, 1, 1, 2, 3, 1, 1, 5]
def baseStart_7628186 : Nat := 118140960795 + 7628186 * 2 ^ 59
def prefixEnd_7628186 : Nat := 4983230072969 + 3 ^ 40 * 7628186 * 2
def baseEnd_7628186 : Nat := 3916925939897996920893617

theorem tailTrace_7628186 : CollatzResearch.WordTrace tailWord_7628186 prefixEnd_7628186 3916925939897996920893617 := by
  unfold tailWord_7628186
  simp only [CollatzResearch.WordTrace]
  refine ⟨69555700085598096823366103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 185481866894928258195642941 69555700085598096823366103)
  ·
    refine ⟨104333550128397145235049155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69555700085598096823366103 104333550128397145235049155)
    ·
      refine ⟨156500325192595717852573733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104333550128397145235049155 156500325192595717852573733)
      ·
        refine ⟨29343810973611697097357575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 156500325192595717852573733 29343810973611697097357575)
        ·
          refine ⟨44015716460417545646036363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29343810973611697097357575 44015716460417545646036363)
          ·
            refine ⟨66023574690626318469054545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44015716460417545646036363 66023574690626318469054545)
            ·
              refine ⟨49517681017969738851790909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 66023574690626318469054545 49517681017969738851790909)
              ·
                refine ⟨18569130381738652069421591, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 49517681017969738851790909 18569130381738652069421591)
                ·
                  refine ⟨27853695572607978104132387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18569130381738652069421591 27853695572607978104132387)
                  ·
                    refine ⟨41780543358911967156198581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27853695572607978104132387 41780543358911967156198581)
                    ·
                      refine ⟨3916925939897996920893617, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41780543358911967156198581 3916925939897996920893617)
                      ·
                        rfl

theorem cell23_7628186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 2, 3, 1, 1, 5].length) (baseStart_7628186 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7628186 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7628186 prefixEnd_7628186 := by exact prefixLift 7628186
  have htrace : WordTrace (prefixWord ++ tailWord_7628186) baseStart_7628186 baseEnd_7628186 := by
    simpa [prefixWord, tailWord_7628186, baseEnd_7628186] using wordTrace_append hprefix tailTrace_7628186
  have hstable : (prefixWord ++ tailWord_7628186).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7628186).length < 2 ^ (prefixWord ++ tailWord_7628186).sum := by decide
  have hdescent : baseEnd_7628186 < baseStart_7628186 := by decide
  rcases family_descends (prefixWord ++ tailWord_7628186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7628213 : List Nat := [1, 3, 3, 2, 2, 1, 3, 1, 1, 2, 4]
def baseStart_7628213 : Nat := 118140960795 + 7628213 * 2 ^ 59
def prefixEnd_7628213 : Nat := 4983230072969 + 3 ^ 40 * 7628213 * 2
def baseEnd_7628213 : Nat := 3916939803875668315255993

theorem tailTrace_7628213 : CollatzResearch.WordTrace tailWord_7628213 prefixEnd_7628213 3916939803875668315255993 := by
  unfold tailWord_7628213
  simp only [CollatzResearch.WordTrace]
  refine ⟨278223785113294570904697293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185482523408863047269798195 278223785113294570904697293)
  ·
    refine ⟨104333919417485464089261485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 278223785113294570904697293 104333919417485464089261485)
    ·
      refine ⟨39125219781557049033473057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 104333919417485464089261485 39125219781557049033473057)
      ·
        refine ⟨29343914836167786775104793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39125219781557049033473057 29343914836167786775104793)
        ·
          refine ⟨22007936127125840081328595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29343914836167786775104793 22007936127125840081328595)
          ·
            refine ⟨33011904190688760121992893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22007936127125840081328595 33011904190688760121992893)
            ·
              refine ⟨12379464071508285045747335, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33011904190688760121992893 12379464071508285045747335)
              ·
                refine ⟨18569196107262427568621003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12379464071508285045747335 18569196107262427568621003)
                ·
                  refine ⟨27853794160893641352931505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18569196107262427568621003 27853794160893641352931505)
                  ·
                    refine ⟨20890345620670231014698629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27853794160893641352931505 20890345620670231014698629)
                    ·
                      refine ⟨3916939803875668315255993, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20890345620670231014698629 3916939803875668315255993)
                      ·
                        rfl

theorem cell23_7628213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 1, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 1, 3, 1, 1, 2, 4].length) (baseStart_7628213 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7628213 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7628213 prefixEnd_7628213 := by exact prefixLift 7628213
  have htrace : WordTrace (prefixWord ++ tailWord_7628213) baseStart_7628213 baseEnd_7628213 := by
    simpa [prefixWord, tailWord_7628213, baseEnd_7628213] using wordTrace_append hprefix tailTrace_7628213
  have hstable : (prefixWord ++ tailWord_7628213).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7628213).length < 2 ^ (prefixWord ++ tailWord_7628213).sum := by decide
  have hdescent : baseEnd_7628213 < baseStart_7628213 := by decide
  rcases family_descends (prefixWord ++ tailWord_7628213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7628234 : List Nat := [3, 1, 2, 1, 2, 5, 1, 3, 1, 2, 2]
def baseStart_7628234 : Nat := 118140960795 + 7628234 * 2 ^ 59
def prefixEnd_7628234 : Nat := 4983230072969 + 3 ^ 40 * 7628234 * 2
def baseEnd_7628234 : Nat := 3916950586969412733093397

theorem tailTrace_7628234 : CollatzResearch.WordTrace tailWord_7628234 prefixEnd_7628234 3916950586969412733093397 := by
  unfold tailWord_7628234
  simp only [CollatzResearch.WordTrace]
  refine ⟨69556137761554622872802939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 185483034030812327660807837 69556137761554622872802939)
  ·
    refine ⟨104334206642331934309204409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69556137761554622872802939 104334206642331934309204409)
    ·
      refine ⟨78250654981748950731903307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 104334206642331934309204409 78250654981748950731903307)
      ·
        refine ⟨117375982472623426097854961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78250654981748950731903307 117375982472623426097854961)
        ·
          refine ⟨88031986854467569573391221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 117375982472623426097854961 88031986854467569573391221)
          ·
            refine ⟨8252998767606334647505427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 88031986854467569573391221 8252998767606334647505427)
            ·
              refine ⟨12379498151409501971258141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8252998767606334647505427 12379498151409501971258141)
              ·
                refine ⟨4642311806778563239221803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12379498151409501971258141 4642311806778563239221803)
                ·
                  refine ⟨6963467710167844858832705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4642311806778563239221803 6963467710167844858832705)
                  ·
                    refine ⟨5222600782625883644124529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6963467710167844858832705 5222600782625883644124529)
                    ·
                      refine ⟨3916950586969412733093397, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5222600782625883644124529 3916950586969412733093397)
                      ·
                        rfl

theorem cell23_7628234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 5, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 5, 1, 3, 1, 2, 2].length) (baseStart_7628234 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7628234 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7628234 prefixEnd_7628234 := by exact prefixLift 7628234
  have htrace : WordTrace (prefixWord ++ tailWord_7628234) baseStart_7628234 baseEnd_7628234 := by
    simpa [prefixWord, tailWord_7628234, baseEnd_7628234] using wordTrace_append hprefix tailTrace_7628234
  have hstable : (prefixWord ++ tailWord_7628234).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7628234).length < 2 ^ (prefixWord ++ tailWord_7628234).sum := by decide
  have hdescent : baseEnd_7628234 < baseStart_7628234 := by decide
  rcases family_descends (prefixWord ++ tailWord_7628234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7628277 : List Nat := [1, 3, 5, 1, 1, 2, 1, 1, 3, 3, 2]
def baseStart_7628277 : Nat := 118140960795 + 7628277 * 2 ^ 59
def prefixEnd_7628277 : Nat := 4983230072969 + 3 ^ 40 * 7628277 * 2
def baseEnd_7628277 : Nat := 3916972666637556064855699

theorem tailTrace_7628277 : CollatzResearch.WordTrace tailWord_7628277 prefixEnd_7628277 3916972666637556064855699 := by
  unfold tailWord_7628277
  simp only [CollatzResearch.WordTrace]
  refine ⟨278226119385062709835027085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185484079590041806556684723 278226119385062709835027085)
  ·
    refine ⟨104334794769398516188135157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 278226119385062709835027085 104334794769398516188135157)
    ·
      refine ⟨9781387009631110892637671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 104334794769398516188135157 9781387009631110892637671)
      ·
        refine ⟨14672080514446666338956507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9781387009631110892637671 14672080514446666338956507)
        ·
          refine ⟨22008120771669999508434761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14672080514446666338956507 22008120771669999508434761)
          ·
            refine ⟨16506090578752499631326071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22008120771669999508434761 16506090578752499631326071)
            ·
              refine ⟨24759135868128749446989107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16506090578752499631326071 24759135868128749446989107)
              ·
                refine ⟨37138703802193124170483661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24759135868128749446989107 37138703802193124170483661)
                ·
                  refine ⟨13927013925822421563931373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 37138703802193124170483661 13927013925822421563931373)
                  ·
                    refine ⟨5222630222183408086474265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13927013925822421563931373 5222630222183408086474265)
                    ·
                      refine ⟨3916972666637556064855699, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5222630222183408086474265 3916972666637556064855699)
                      ·
                        rfl

theorem cell23_7628277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 2, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 2, 1, 1, 3, 3, 2].length) (baseStart_7628277 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7628277 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7628277 prefixEnd_7628277 := by exact prefixLift 7628277
  have htrace : WordTrace (prefixWord ++ tailWord_7628277) baseStart_7628277 baseEnd_7628277 := by
    simpa [prefixWord, tailWord_7628277, baseEnd_7628277] using wordTrace_append hprefix tailTrace_7628277
  have hstable : (prefixWord ++ tailWord_7628277).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7628277).length < 2 ^ (prefixWord ++ tailWord_7628277).sum := by decide
  have hdescent : baseEnd_7628277 < baseStart_7628277 := by decide
  rcases family_descends (prefixWord ++ tailWord_7628277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7628301 : List Nat := [1, 7, 1, 1, 2, 1, 2, 2, 2, 1, 3]
def baseStart_7628301 : Nat := 118140960795 + 7628301 * 2 ^ 59
def prefixEnd_7628301 : Nat := 4983230072969 + 3 ^ 40 * 7628301 * 2
def baseEnd_7628301 : Nat := 3916984990173263970955589

theorem tailTrace_7628301 : CollatzResearch.WordTrace tailWord_7628301 prefixEnd_7628301 3916984990173263970955589 := by
  unfold tailWord_7628301
  simp only [CollatzResearch.WordTrace]
  refine ⟨278226994736975761933900757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185484663157983841289267171 278226994736975761933900757)
  ·
    refine ⟨6520945189147869420325799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 278226994736975761933900757 6520945189147869420325799)
    ·
      refine ⟨9781417783721804130488699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6520945189147869420325799 9781417783721804130488699)
      ·
        refine ⟨14672126675582706195733049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9781417783721804130488699 14672126675582706195733049)
        ·
          refine ⟨11004095006687029646799787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14672126675582706195733049 11004095006687029646799787)
          ·
            refine ⟨16506142510030544470199681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11004095006687029646799787 16506142510030544470199681)
            ·
              refine ⟨12379606882522908352649761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16506142510030544470199681 12379606882522908352649761)
              ·
                refine ⟨9284705161892181264487321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12379606882522908352649761 9284705161892181264487321)
                ·
                  refine ⟨6963528871419135948365491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9284705161892181264487321 6963528871419135948365491)
                  ·
                    refine ⟨10445293307128703922548237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6963528871419135948365491 10445293307128703922548237)
                    ·
                      refine ⟨3916984990173263970955589, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10445293307128703922548237 3916984990173263970955589)
                      ·
                        rfl

theorem cell23_7628301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 2, 1, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 2, 1, 2, 2, 2, 1, 3].length) (baseStart_7628301 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7628301 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7628301 prefixEnd_7628301 := by exact prefixLift 7628301
  have htrace : WordTrace (prefixWord ++ tailWord_7628301) baseStart_7628301 baseEnd_7628301 := by
    simpa [prefixWord, tailWord_7628301, baseEnd_7628301] using wordTrace_append hprefix tailTrace_7628301
  have hstable : (prefixWord ++ tailWord_7628301).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7628301).length < 2 ^ (prefixWord ++ tailWord_7628301).sum := by decide
  have hdescent : baseEnd_7628301 < baseStart_7628301 := by decide
  rcases family_descends (prefixWord ++ tailWord_7628301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7628307 : List Nat := [1, 1, 1, 2, 1, 7, 2, 2, 2, 2, 2]
def baseStart_7628307 : Nat := 118140960795 + 7628307 * 2 ^ 59
def prefixEnd_7628307 : Nat := 4983230072969 + 3 ^ 40 * 7628307 * 2
def baseEnd_7628307 : Nat := 3916988071057190947480561

theorem tailTrace_7628307 : CollatzResearch.WordTrace tailWord_7628307 prefixEnd_7628307 3916988071057190947480561 := by
  unfold tailWord_7628307
  simp only [CollatzResearch.WordTrace]
  refine ⟨278227213574954024958619175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185484809049969349972412783 278227213574954024958619175)
  ·
    refine ⟨417340820362431037437928763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 278227213574954024958619175 417340820362431037437928763)
    ·
      refine ⟨626011230543646556156893145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 417340820362431037437928763 626011230543646556156893145)
      ·
        refine ⟨469508422907734917117669859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 626011230543646556156893145 469508422907734917117669859)
        ·
          refine ⟨704262634361602375676504789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 469508422907734917117669859 704262634361602375676504789)
          ·
            refine ⟨16506155492850055679918081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 704262634361602375676504789 16506155492850055679918081)
            ·
              refine ⟨12379616619637541759938561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16506155492850055679918081 12379616619637541759938561)
              ·
                refine ⟨9284712464728156319953921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12379616619637541759938561 9284712464728156319953921)
                ·
                  refine ⟨6963534348546117239965441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9284712464728156319953921 6963534348546117239965441)
                  ·
                    refine ⟨5222650761409587929974081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6963534348546117239965441 5222650761409587929974081)
                    ·
                      refine ⟨3916988071057190947480561, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5222650761409587929974081 3916988071057190947480561)
                      ·
                        rfl

theorem cell23_7628307_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 7, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 7, 2, 2, 2, 2, 2].length) (baseStart_7628307 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7628307 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7628307 prefixEnd_7628307 := by exact prefixLift 7628307
  have htrace : WordTrace (prefixWord ++ tailWord_7628307) baseStart_7628307 baseEnd_7628307 := by
    simpa [prefixWord, tailWord_7628307, baseEnd_7628307] using wordTrace_append hprefix tailTrace_7628307
  have hstable : (prefixWord ++ tailWord_7628307).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7628307).length < 2 ^ (prefixWord ++ tailWord_7628307).sum := by decide
  have hdescent : baseEnd_7628307 < baseStart_7628307 := by decide
  rcases family_descends (prefixWord ++ tailWord_7628307) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
