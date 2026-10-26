import V185TrunkScan23Chunk1188

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_7044291 : List Nat := [1, 1, 1, 3, 1, 1, 1, 5, 2, 1, 6]
def baseStart_7044291 : Nat := 118140960795 + 7044291 * 2 ^ 59
def prefixEnd_7044291 : Nat := 4983230072969 + 3 ^ 40 * 7044291 * 2
def baseEnd_7044291 : Nat := 3617107153141003912766401

theorem tailTrace_7044291 : CollatzResearch.WordTrace tailWord_7044291 prefixEnd_7044291 3617107153141003912766401 := by
  unfold tailWord_7044291
  simp only [CollatzResearch.WordTrace]
  refine ⟨256926400122744250966684727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171284266748496167311123151 256926400122744250966684727)
  ·
    refine ⟨385389600184116376450027091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 256926400122744250966684727 385389600184116376450027091)
    ·
      refine ⟨578084400276174564675040637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 385389600184116376450027091 578084400276174564675040637)
      ·
        refine ⟨216781650103565461753140239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 578084400276174564675040637 216781650103565461753140239)
        ·
          refine ⟨325172475155348192629710359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 216781650103565461753140239 325172475155348192629710359)
          ·
            refine ⟨487758712733022288944565539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 325172475155348192629710359 487758712733022288944565539)
            ·
              refine ⟨731638069099533433416848309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 487758712733022288944565539 731638069099533433416848309)
              ·
                refine ⟨68591068978081259382829529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 731638069099533433416848309 68591068978081259382829529)
                ·
                  refine ⟨51443301733560944537122147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 68591068978081259382829529 51443301733560944537122147)
                  ·
                    refine ⟨77164952600341416805683221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 51443301733560944537122147 77164952600341416805683221)
                    ·
                      refine ⟨3617107153141003912766401, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 77164952600341416805683221 3617107153141003912766401)
                      ·
                        rfl

theorem cell23_7044291_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 5, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 5, 2, 1, 6].length) (baseStart_7044291 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7044291 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7044291 prefixEnd_7044291 := by exact prefixLift 7044291
  have htrace : WordTrace (prefixWord ++ tailWord_7044291) baseStart_7044291 baseEnd_7044291 := by
    simpa [prefixWord, tailWord_7044291, baseEnd_7044291] using wordTrace_append hprefix tailTrace_7044291
  have hstable : (prefixWord ++ tailWord_7044291).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7044291).length < 2 ^ (prefixWord ++ tailWord_7044291).sum := by decide
  have hdescent : baseEnd_7044291 < baseStart_7044291 := by decide
  rcases family_descends (prefixWord ++ tailWord_7044291) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7044356 : List Nat := [2, 3, 2, 2, 2, 3, 2, 2, 1, 4]
def baseStart_7044356 : Nat := 118140960795 + 7044356 * 2 ^ 59
def prefixEnd_7044356 : Nat := 4983230072969 + 3 ^ 40 * 7044356 * 2
def baseEnd_7044356 : Nat := 1205713509794515386151201

theorem tailTrace_7044356 : CollatzResearch.WordTrace tailWord_7044356 prefixEnd_7044356 1205713509794515386151201 := by
  unfold tailWord_7044356
  simp only [CollatzResearch.WordTrace]
  refine ⟨128464385433754383533900461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 171285847245005844711867281 128464385433754383533900461)
  ·
    refine ⟨48174144537657893825212673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 128464385433754383533900461 48174144537657893825212673)
    ·
      refine ⟨36130608403243420368909505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48174144537657893825212673 36130608403243420368909505)
      ·
        refine ⟨27097956302432565276682129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36130608403243420368909505 27097956302432565276682129)
        ·
          refine ⟨20323467226824423957511597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27097956302432565276682129 20323467226824423957511597)
          ·
            refine ⟨7621300210059158984066849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20323467226824423957511597 7621300210059158984066849)
            ·
              refine ⟨5715975157544369238050137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7621300210059158984066849 5715975157544369238050137)
              ·
                refine ⟨4286981368158276928537603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5715975157544369238050137 4286981368158276928537603)
                ·
                  refine ⟨6430472052237415392806405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4286981368158276928537603 6430472052237415392806405)
                  ·
                    refine ⟨1205713509794515386151201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6430472052237415392806405 1205713509794515386151201)
                    ·
                      rfl

theorem cell23_7044356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 3, 2, 2, 1, 4].length) (baseStart_7044356 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7044356 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7044356 prefixEnd_7044356 := by exact prefixLift 7044356
  have htrace : WordTrace (prefixWord ++ tailWord_7044356) baseStart_7044356 baseEnd_7044356 := by
    simpa [prefixWord, tailWord_7044356, baseEnd_7044356] using wordTrace_append hprefix tailTrace_7044356
  have hstable : (prefixWord ++ tailWord_7044356).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7044356).length < 2 ^ (prefixWord ++ tailWord_7044356).sum := by decide
  have hdescent : baseEnd_7044356 < baseStart_7044356 := by decide
  rcases family_descends (prefixWord ++ tailWord_7044356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7044385 : List Nat := [1, 2, 3, 2, 1, 1, 1, 6, 1, 1, 4]
def baseStart_7044385 : Nat := 118140960795 + 7044385 * 2 ^ 59
def prefixEnd_7044385 : Nat := 4983230072969 + 3 ^ 40 * 7044385 * 2
def baseEnd_7044385 : Nat := 3617155420322526544990969

theorem tailTrace_7044385 : CollatzResearch.WordTrace tailWord_7044385 prefixEnd_7044385 3617155420322526544990969 := by
  unfold tailWord_7044385
  simp only [CollatzResearch.WordTrace]
  refine ⟨256929828584403705020606609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171286552389602470013737739 256929828584403705020606609)
  ·
    refine ⟨192697371438302778765454957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 256929828584403705020606609 192697371438302778765454957)
    ·
      refine ⟨72261514289363542037045609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 192697371438302778765454957 72261514289363542037045609)
      ·
        refine ⟨54196135717022656527784207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72261514289363542037045609 54196135717022656527784207)
        ·
          refine ⟨81294203575533984791676311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54196135717022656527784207 81294203575533984791676311)
          ·
            refine ⟨121941305363300977187514467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81294203575533984791676311 121941305363300977187514467)
            ·
              refine ⟨182911958044951465781271701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 121941305363300977187514467 182911958044951465781271701)
              ·
                refine ⟨8573998033357099958497111, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 182911958044951465781271701 8573998033357099958497111)
                ·
                  refine ⟨12860997050035649937745667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8573998033357099958497111 12860997050035649937745667)
                  ·
                    refine ⟨19291495575053474906618501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12860997050035649937745667 19291495575053474906618501)
                    ·
                      refine ⟨3617155420322526544990969, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19291495575053474906618501 3617155420322526544990969)
                      ·
                        rfl

theorem cell23_7044385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 1, 6, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 1, 6, 1, 1, 4].length) (baseStart_7044385 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7044385 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7044385 prefixEnd_7044385 := by exact prefixLift 7044385
  have htrace : WordTrace (prefixWord ++ tailWord_7044385) baseStart_7044385 baseEnd_7044385 := by
    simpa [prefixWord, tailWord_7044385, baseEnd_7044385] using wordTrace_append hprefix tailTrace_7044385
  have hstable : (prefixWord ++ tailWord_7044385).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7044385).length < 2 ^ (prefixWord ++ tailWord_7044385).sum := by decide
  have hdescent : baseEnd_7044385 < baseStart_7044385 := by decide
  rcases family_descends (prefixWord ++ tailWord_7044385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7044389 : List Nat := [1, 3, 1, 2, 4, 3, 1, 1, 2, 3, 2]
def baseStart_7044389 : Nat := 118140960795 + 7044389 * 2 ^ 59
def prefixEnd_7044389 : Nat := 4983230072969 + 3 ^ 40 * 7044389 * 2
def baseEnd_7044389 : Nat := 3617157474245144529340951

theorem tailTrace_7044389 : CollatzResearch.WordTrace tailWord_7044389 prefixEnd_7044389 3617157474245144529340951 := by
  unfold tailWord_7044389
  simp only [CollatzResearch.WordTrace]
  refine ⟨256929974476389213703752221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171286649650926142469168147 256929974476389213703752221)
  ·
    refine ⟨96348740428645955138907083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 256929974476389213703752221 96348740428645955138907083)
    ·
      refine ⟨144523110642968932708360625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96348740428645955138907083 144523110642968932708360625)
      ·
        refine ⟨108392332982226699531270469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 144523110642968932708360625 108392332982226699531270469)
        ·
          refine ⟨20323562434167506162113213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 108392332982226699531270469 20323562434167506162113213)
          ·
            refine ⟨7621335912812814810792455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20323562434167506162113213 7621335912812814810792455)
            ·
              refine ⟨11432003869219222216188683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7621335912812814810792455 11432003869219222216188683)
              ·
                refine ⟨17148005803828833324283025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11432003869219222216188683 17148005803828833324283025)
                ·
                  refine ⟨12861004352871624993212269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17148005803828833324283025 12861004352871624993212269)
                  ·
                    refine ⟨4822876632326859372454601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12861004352871624993212269 4822876632326859372454601)
                    ·
                      refine ⟨3617157474245144529340951, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4822876632326859372454601 3617157474245144529340951)
                      ·
                        rfl

theorem cell23_7044389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 3, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 3, 1, 1, 2, 3, 2].length) (baseStart_7044389 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7044389 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7044389 prefixEnd_7044389 := by exact prefixLift 7044389
  have htrace : WordTrace (prefixWord ++ tailWord_7044389) baseStart_7044389 baseEnd_7044389 := by
    simpa [prefixWord, tailWord_7044389, baseEnd_7044389] using wordTrace_append hprefix tailTrace_7044389
  have hstable : (prefixWord ++ tailWord_7044389).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7044389).length < 2 ^ (prefixWord ++ tailWord_7044389).sum := by decide
  have hdescent : baseEnd_7044389 < baseStart_7044389 := by decide
  rcases family_descends (prefixWord ++ tailWord_7044389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7044402 : List Nat := [3, 2, 1, 1, 4, 2, 1, 3, 1, 1, 4]
def baseStart_7044402 : Nat := 118140960795 + 7044402 * 2 ^ 59
def prefixEnd_7044402 : Nat := 4983230072969 + 3 ^ 40 * 7044402 * 2
def baseEnd_7044402 : Nat := 3617164149493652978478391

theorem tailTrace_7044402 : CollatzResearch.WordTrace tailWord_7044402 prefixEnd_7044402 3617164149493652978478391 := by
  unfold tailWord_7044402
  simp only [CollatzResearch.WordTrace]
  refine ⟨64232612156335529230993865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 171286965750228077949316973 64232612156335529230993865)
  ·
    refine ⟨48174459117251646923245399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64232612156335529230993865 48174459117251646923245399)
    ·
      refine ⟨72261688675877470384868099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48174459117251646923245399 72261688675877470384868099)
      ·
        refine ⟨108392533013816205577302149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72261688675877470384868099 108392533013816205577302149)
        ·
          refine ⟨20323599940090538545744153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 108392533013816205577302149 20323599940090538545744153)
          ·
            refine ⟨15242699955067903909308115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20323599940090538545744153 15242699955067903909308115)
            ·
              refine ⟨22864049932601855863962173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15242699955067903909308115 22864049932601855863962173)
              ·
                refine ⟨8574018724725695948985815, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22864049932601855863962173 8574018724725695948985815)
                ·
                  refine ⟨12861028087088543923478723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8574018724725695948985815 12861028087088543923478723)
                  ·
                    refine ⟨19291542130632815885218085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12861028087088543923478723 19291542130632815885218085)
                    ·
                      refine ⟨3617164149493652978478391, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19291542130632815885218085 3617164149493652978478391)
                      ·
                        rfl

theorem cell23_7044402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 2, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 2, 1, 3, 1, 1, 4].length) (baseStart_7044402 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7044402 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7044402 prefixEnd_7044402 := by exact prefixLift 7044402
  have htrace : WordTrace (prefixWord ++ tailWord_7044402) baseStart_7044402 baseEnd_7044402 := by
    simpa [prefixWord, tailWord_7044402, baseEnd_7044402] using wordTrace_append hprefix tailTrace_7044402
  have hstable : (prefixWord ++ tailWord_7044402).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7044402).length < 2 ^ (prefixWord ++ tailWord_7044402).sum := by decide
  have hdescent : baseEnd_7044402 < baseStart_7044402 := by decide
  rcases family_descends (prefixWord ++ tailWord_7044402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7044412 : List Nat := [2, 2, 2, 2, 1, 3, 3, 2, 2, 4]
def baseStart_7044412 : Nat := 118140960795 + 7044412 * 2 ^ 59
def prefixEnd_7044412 : Nat := 4983230072969 + 3 ^ 40 * 7044412 * 2
def baseEnd_7044412 : Nat := 1205723094766732646451115

theorem tailTrace_7044412 : CollatzResearch.WordTrace tailWord_7044412 prefixEnd_7044412 1205723094766732646451115 := by
  unfold tailWord_7044412
  simp only [CollatzResearch.WordTrace]
  refine ⟨128465406677652944315919745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 171287208903537259087892993 128465406677652944315919745)
  ·
    refine ⟨96349055008239708236939809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 128465406677652944315919745 96349055008239708236939809)
    ·
      refine ⟨72261791256179781177704857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 96349055008239708236939809 72261791256179781177704857)
      ·
        refine ⟨54196343442134835883278643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72261791256179781177704857 54196343442134835883278643)
        ·
          refine ⟨81294515163202253824917965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54196343442134835883278643 81294515163202253824917965)
          ·
            refine ⟨30485443186200845184344237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 81294515163202253824917965 30485443186200845184344237)
            ·
              refine ⟨11432041194825316944129089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30485443186200845184344237 11432041194825316944129089)
              ·
                refine ⟨8574030896118987708096817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11432041194825316944129089 8574030896118987708096817)
                ·
                  refine ⟨6430523172089240781072613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8574030896118987708096817 6430523172089240781072613)
                  ·
                    refine ⟨1205723094766732646451115, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6430523172089240781072613 1205723094766732646451115)
                    ·
                      rfl

theorem cell23_7044412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 3, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 3, 3, 2, 2, 4].length) (baseStart_7044412 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7044412 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7044412 prefixEnd_7044412 := by exact prefixLift 7044412
  have htrace : WordTrace (prefixWord ++ tailWord_7044412) baseStart_7044412 baseEnd_7044412 := by
    simpa [prefixWord, tailWord_7044412, baseEnd_7044412] using wordTrace_append hprefix tailTrace_7044412
  have hstable : (prefixWord ++ tailWord_7044412).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7044412).length < 2 ^ (prefixWord ++ tailWord_7044412).sum := by decide
  have hdescent : baseEnd_7044412 < baseStart_7044412 := by decide
  rcases family_descends (prefixWord ++ tailWord_7044412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7044452 : List Nat := [2, 3, 1, 1, 3, 2, 1, 2, 4, 1, 3]
def baseStart_7044452 : Nat := 118140960795 + 7044452 * 2 ^ 59
def prefixEnd_7044452 : Nat := 4983230072969 + 3 ^ 40 * 7044452 * 2
def baseEnd_7044452 : Nat := 3617189823526377782853161

theorem tailTrace_7044452 : CollatzResearch.WordTrace tailWord_7044452 prefixEnd_7044452 3617189823526377782853161 := by
  unfold tailWord_7044452
  simp only [CollatzResearch.WordTrace]
  refine ⟨128466136137580487731647805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 171288181516773983642197073 128466136137580487731647805)
  ·
    refine ⟨48174801051592682899367927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 128466136137580487731647805 48174801051592682899367927)
    ·
      refine ⟨72262201577389024349051891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48174801051592682899367927 72262201577389024349051891)
      ·
        refine ⟨108393302366083536523577837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72262201577389024349051891 108393302366083536523577837)
        ·
          refine ⟨40647488387281326196341689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 108393302366083536523577837 40647488387281326196341689)
          ·
            refine ⟨30485616290460994647256267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40647488387281326196341689 30485616290460994647256267)
            ·
              refine ⟨45728424435691491970884401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30485616290460994647256267 45728424435691491970884401)
              ·
                refine ⟨34296318326768618978163301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45728424435691491970884401 34296318326768618978163301)
                ·
                  refine ⟨6430559686269116058405619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 34296318326768618978163301 6430559686269116058405619)
                  ·
                    refine ⟨9645839529403674087608429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6430559686269116058405619 9645839529403674087608429)
                    ·
                      refine ⟨3617189823526377782853161, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9645839529403674087608429 3617189823526377782853161)
                      ·
                        rfl

theorem cell23_7044452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 2, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 2, 1, 2, 4, 1, 3].length) (baseStart_7044452 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7044452 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7044452 prefixEnd_7044452 := by exact prefixLift 7044452
  have htrace : WordTrace (prefixWord ++ tailWord_7044452) baseStart_7044452 baseEnd_7044452 := by
    simpa [prefixWord, tailWord_7044452, baseEnd_7044452] using wordTrace_append hprefix tailTrace_7044452
  have hstable : (prefixWord ++ tailWord_7044452).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7044452).length < 2 ^ (prefixWord ++ tailWord_7044452).sum := by decide
  have hdescent : baseEnd_7044452 < baseStart_7044452 := by decide
  rcases family_descends (prefixWord ++ tailWord_7044452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7044492 : List Nat := [2, 2, 1, 2, 1, 3, 2, 3, 1, 4, 2]
def baseStart_7044492 : Nat := 118140960795 + 7044492 * 2 ^ 59
def prefixEnd_7044492 : Nat := 4983230072969 + 3 ^ 40 * 7044492 * 2
def baseEnd_7044492 : Nat := 3617210362752557626352977

theorem tailTrace_7044492 : CollatzResearch.WordTrace tailWord_7044492 prefixEnd_7044492 3617210362752557626352977 := by
  unfold tailWord_7044492
  simp only [CollatzResearch.WordTrace]
  refine ⟨128466865597508031147375865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 171289154130010708196501153 128466865597508031147375865)
  ·
    refine ⟨96350149198131023360531899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 128466865597508031147375865 96350149198131023360531899)
    ·
      refine ⟨144525223797196535040797849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96350149198131023360531899 144525223797196535040797849)
      ·
        refine ⟨108393917847897401280598387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 144525223797196535040797849 108393917847897401280598387)
        ·
          refine ⟨162590876771846101920897581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 108393917847897401280598387 162590876771846101920897581)
          ·
            refine ⟨60971578789442288220336593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 162590876771846101920897581 60971578789442288220336593)
            ·
              refine ⟨45728684092081716165252445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 60971578789442288220336593 45728684092081716165252445)
              ·
                refine ⟨17148256534530643561969667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 45728684092081716165252445 17148256534530643561969667)
                ·
                  refine ⟨25722384801795965342954501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17148256534530643561969667 25722384801795965342954501)
                  ·
                    refine ⟨4822947150336743501803969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25722384801795965342954501 4822947150336743501803969)
                    ·
                      refine ⟨3617210362752557626352977, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4822947150336743501803969 3617210362752557626352977)
                      ·
                        rfl

theorem cell23_7044492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 2, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 2, 3, 1, 4, 2].length) (baseStart_7044492 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7044492 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7044492 prefixEnd_7044492 := by exact prefixLift 7044492
  have htrace : WordTrace (prefixWord ++ tailWord_7044492) baseStart_7044492 baseEnd_7044492 := by
    simpa [prefixWord, tailWord_7044492, baseEnd_7044492] using wordTrace_append hprefix tailTrace_7044492
  have hstable : (prefixWord ++ tailWord_7044492).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7044492).length < 2 ^ (prefixWord ++ tailWord_7044492).sum := by decide
  have hdescent : baseEnd_7044492 < baseStart_7044492 := by decide
  rcases family_descends (prefixWord ++ tailWord_7044492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7044509 : List Nat := [1, 4, 2, 1, 3, 2, 1, 2, 1, 4, 2]
def baseStart_7044509 : Nat := 118140960795 + 7044509 * 2 ^ 59
def prefixEnd_7044509 : Nat := 4983230072969 + 3 ^ 40 * 7044509 * 2
def baseEnd_7044509 : Nat := 3617219091923684059840399

theorem tailTrace_7044509 : CollatzResearch.WordTrace tailWord_7044509 prefixEnd_7044509 3617219091923684059840399 := by
  unfold tailWord_7044509
  simp only [CollatzResearch.WordTrace]
  refine ⟨256934351235954474198120581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171289567490636316132080387 256934351235954474198120581)
  ·
    refine ⟨48175190856741463912147609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 256934351235954474198120581 48175190856741463912147609)
    ·
      refine ⟨36131393142556097934110707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48175190856741463912147609 36131393142556097934110707)
      ·
        refine ⟨54197089713834146901166061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36131393142556097934110707 54197089713834146901166061)
        ·
          refine ⟨20323908642687805087937273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 54197089713834146901166061 20323908642687805087937273)
          ·
            refine ⟨15242931482015853815952955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20323908642687805087937273 15242931482015853815952955)
            ·
              refine ⟨22864397223023780723929433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15242931482015853815952955 22864397223023780723929433)
              ·
                refine ⟨17148297917267835542947075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22864397223023780723929433 17148297917267835542947075)
                ·
                  refine ⟨25722446875901753314420613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17148297917267835542947075 25722446875901753314420613)
                  ·
                    refine ⟨4822958789231578746453865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25722446875901753314420613 4822958789231578746453865)
                    ·
                      refine ⟨3617219091923684059840399, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4822958789231578746453865 3617219091923684059840399)
                      ·
                        rfl

theorem cell23_7044509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 2, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 2, 1, 2, 1, 4, 2].length) (baseStart_7044509 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7044509 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7044509 prefixEnd_7044509 := by exact prefixLift 7044509
  have htrace : WordTrace (prefixWord ++ tailWord_7044509) baseStart_7044509 baseEnd_7044509 := by
    simpa [prefixWord, tailWord_7044509, baseEnd_7044509] using wordTrace_append hprefix tailTrace_7044509
  have hstable : (prefixWord ++ tailWord_7044509).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7044509).length < 2 ^ (prefixWord ++ tailWord_7044509).sum := by decide
  have hdescent : baseEnd_7044509 < baseStart_7044509 := by decide
  rcases family_descends (prefixWord ++ tailWord_7044509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7044552 : List Nat := [2, 1, 3, 1, 3, 1, 1, 2, 2, 5, 2]
def baseStart_7044552 : Nat := 118140960795 + 7044552 * 2 ^ 59
def prefixEnd_7044552 : Nat := 4983230072969 + 3 ^ 40 * 7044552 * 2
def baseEnd_7044552 : Nat := 3617241171591827391602701

theorem tailTrace_7044552 : CollatzResearch.WordTrace tailWord_7044552 prefixEnd_7044552 3617241171591827391602701 := by
  unfold tailWord_7044552
  simp only [CollatzResearch.WordTrace]
  refine ⟨128467959787399346270967955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 171290613049865795027957273 128467959787399346270967955)
  ·
    refine ⟨192701939681099019406451933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128467959787399346270967955 192701939681099019406451933)
    ·
      refine ⟨72263227380412132277419475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 192701939681099019406451933 72263227380412132277419475)
      ·
        refine ⟨108394841070618198416129213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72263227380412132277419475 108394841070618198416129213)
        ·
          refine ⟨40648065401481824406048455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 108394841070618198416129213 40648065401481824406048455)
          ·
            refine ⟨60972098102222736609072683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40648065401481824406048455 60972098102222736609072683)
            ·
              refine ⟨91458147153334104913609025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60972098102222736609072683 91458147153334104913609025)
              ·
                refine ⟨68593610365000578685206769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 91458147153334104913609025 68593610365000578685206769)
                ·
                  refine ⟨51445207773750434013905077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 68593610365000578685206769 51445207773750434013905077)
                  ·
                    refine ⟨4822988228789103188803601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 51445207773750434013905077 4822988228789103188803601)
                    ·
                      refine ⟨3617241171591827391602701, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4822988228789103188803601 3617241171591827391602701)
                      ·
                        rfl

theorem cell23_7044552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 1, 2, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 1, 2, 2, 5, 2].length) (baseStart_7044552 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7044552 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7044552 prefixEnd_7044552 := by exact prefixLift 7044552
  have htrace : WordTrace (prefixWord ++ tailWord_7044552) baseStart_7044552 baseEnd_7044552 := by
    simpa [prefixWord, tailWord_7044552, baseEnd_7044552] using wordTrace_append hprefix tailTrace_7044552
  have hstable : (prefixWord ++ tailWord_7044552).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7044552).length < 2 ^ (prefixWord ++ tailWord_7044552).sum := by decide
  have hdescent : baseEnd_7044552 < baseStart_7044552 := by decide
  rcases family_descends (prefixWord ++ tailWord_7044552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7044566 : List Nat := [5, 2, 1, 1, 1, 3, 2, 3, 5]
def baseStart_7044566 : Nat := 118140960795 + 7044566 * 2 ^ 59
def prefixEnd_7044566 : Nat := 4983230072969 + 3 ^ 40 * 7044566 * 2
def baseEnd_7044566 : Nat := 401916484480110037425293

theorem tailTrace_7044566 : CollatzResearch.WordTrace tailWord_7044566 prefixEnd_7044566 401916484480110037425293 := by
  unfold tailWord_7044566
  simp only [CollatzResearch.WordTrace]
  refine ⟨16058526887296748308309097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 171290953464498648621963701 16058526887296748308309097)
  ·
    refine ⟨12043895165472561231231823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16058526887296748308309097 12043895165472561231231823)
    ·
      refine ⟨18065842748208841846847735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12043895165472561231231823 18065842748208841846847735)
      ·
        refine ⟨27098764122313262770271603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18065842748208841846847735 27098764122313262770271603)
        ·
          refine ⟨40648146183469894155407405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27098764122313262770271603 40648146183469894155407405)
          ·
            refine ⟨15243054818801210308277777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40648146183469894155407405 15243054818801210308277777)
            ·
              refine ⟨11432291114100907731208333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15243054818801210308277777 11432291114100907731208333)
              ·
                refine ⟨4287109167787840399203125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11432291114100907731208333 4287109167787840399203125)
                ·
                  refine ⟨401916484480110037425293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4287109167787840399203125 401916484480110037425293)
                  ·
                    rfl

theorem cell23_7044566_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 3, 2, 3, 5].length) (baseStart_7044566 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7044566 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7044566 prefixEnd_7044566 := by exact prefixLift 7044566
  have htrace : WordTrace (prefixWord ++ tailWord_7044566) baseStart_7044566 baseEnd_7044566 := by
    simpa [prefixWord, tailWord_7044566, baseEnd_7044566] using wordTrace_append hprefix tailTrace_7044566
  have hstable : (prefixWord ++ tailWord_7044566).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7044566).length < 2 ^ (prefixWord ++ tailWord_7044566).sum := by decide
  have hdescent : baseEnd_7044566 < baseStart_7044566 := by decide
  rcases family_descends (prefixWord ++ tailWord_7044566) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7044592 : List Nat := [2, 1, 1, 1, 3, 4, 1, 3, 3, 4]
def baseStart_7044592 : Nat := 118140960795 + 7044592 * 2 ^ 59
def prefixEnd_7044592 : Nat := 4983230072969 + 3 ^ 40 * 7044592 * 2
def baseEnd_7044592 : Nat := 1205753903606002411700839

theorem tailTrace_7044592 : CollatzResearch.WordTrace tailWord_7044592 prefixEnd_7044592 1205753903606002411700839 := by
  unfold tailWord_7044592
  simp only [CollatzResearch.WordTrace]
  refine ⟨128468689247326889686696015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 171291585663102519582261353 128468689247326889686696015)
  ·
    refine ⟨192703033870990334530044023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128468689247326889686696015 192703033870990334530044023)
    ·
      refine ⟨289054550806485501795066035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 192703033870990334530044023 289054550806485501795066035)
      ·
        refine ⟨433581826209728252692599053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 289054550806485501795066035 433581826209728252692599053)
        ·
          refine ⟨162593184828648094759724645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 433581826209728252692599053 162593184828648094759724645)
          ·
            refine ⟨30486222155371517767448371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 162593184828648094759724645 30486222155371517767448371)
            ·
              refine ⟨45729333233057276651172557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30486222155371517767448371 45729333233057276651172557)
              ·
                refine ⟨17148499962396478744189709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 45729333233057276651172557 17148499962396478744189709)
                ·
                  refine ⟨6430687485898679529071141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17148499962396478744189709 6430687485898679529071141)
                  ·
                    refine ⟨1205753903606002411700839, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6430687485898679529071141 1205753903606002411700839)
                    ·
                      rfl

theorem cell23_7044592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 4, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 4, 1, 3, 3, 4].length) (baseStart_7044592 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7044592 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7044592 prefixEnd_7044592 := by exact prefixLift 7044592
  have htrace : WordTrace (prefixWord ++ tailWord_7044592) baseStart_7044592 baseEnd_7044592 := by
    simpa [prefixWord, tailWord_7044592, baseEnd_7044592] using wordTrace_append hprefix tailTrace_7044592
  have hstable : (prefixWord ++ tailWord_7044592).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7044592).length < 2 ^ (prefixWord ++ tailWord_7044592).sum := by decide
  have hdescent : baseEnd_7044592 < baseStart_7044592 := by decide
  rcases family_descends (prefixWord ++ tailWord_7044592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7044643 : List Nat := [1, 1, 1, 4, 5, 1, 3, 2, 1, 4]
def baseStart_7044643 : Nat := 118140960795 + 7044643 * 2 ^ 59
def prefixEnd_7044643 : Nat := 4983230072969 + 3 ^ 40 * 7044643 * 2
def baseEnd_7044643 : Nat := 1205762632777128845188261

theorem tailTrace_7044643 : CollatzResearch.WordTrace tailWord_7044643 prefixEnd_7044643 1205762632777128845188261 := by
  unfold tailWord_7044643
  simp only [CollatzResearch.WordTrace]
  refine ⟨256939238617469015083498583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171292825744979343388999055 256939238617469015083498583)
  ·
    refine ⟨385408857926203522625247875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 256939238617469015083498583 385408857926203522625247875)
    ·
      refine ⟨578113286889305283937871813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 385408857926203522625247875 578113286889305283937871813)
      ·
        refine ⟨108396241291744740738350965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 578113286889305283937871813 108396241291744740738350965)
        ·
          refine ⟨10162147621101069444220403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 108396241291744740738350965 10162147621101069444220403)
          ·
            refine ⟨15243221431651604166330605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10162147621101069444220403 15243221431651604166330605)
            ·
              refine ⟨5716208036869351562373977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15243221431651604166330605 5716208036869351562373977)
              ·
                refine ⟨4287156027652013671780483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5716208036869351562373977 4287156027652013671780483)
                ·
                  refine ⟨6430734041478020507670725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4287156027652013671780483 6430734041478020507670725)
                  ·
                    refine ⟨1205762632777128845188261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6430734041478020507670725 1205762632777128845188261)
                    ·
                      rfl

theorem cell23_7044643_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 5, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 5, 1, 3, 2, 1, 4].length) (baseStart_7044643 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7044643 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7044643 prefixEnd_7044643 := by exact prefixLift 7044643
  have htrace : WordTrace (prefixWord ++ tailWord_7044643) baseStart_7044643 baseEnd_7044643 := by
    simpa [prefixWord, tailWord_7044643, baseEnd_7044643] using wordTrace_append hprefix tailTrace_7044643
  have hstable : (prefixWord ++ tailWord_7044643).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7044643).length < 2 ^ (prefixWord ++ tailWord_7044643).sum := by decide
  have hdescent : baseEnd_7044643 < baseStart_7044643 := by decide
  rcases family_descends (prefixWord ++ tailWord_7044643) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7044645 : List Nat := [1, 3, 1, 2, 2, 1, 1, 2, 2, 1, 7]
def baseStart_7044645 : Nat := 118140960795 + 7044645 * 2 ^ 59
def prefixEnd_7044645 : Nat := 4983230072969 + 3 ^ 40 * 7044645 * 2
def baseEnd_7044645 : Nat := 3617288925292695527739773

theorem tailTrace_7044645 : CollatzResearch.WordTrace tailWord_7044645 prefixEnd_7044645 3617288925292695527739773 := by
  unfold tailWord_7044645
  simp only [CollatzResearch.WordTrace]
  refine ⟨256939311563461769425071389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171292874375641179616714259 256939311563461769425071389)
  ·
    refine ⟨96352241836298163534401771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 256939311563461769425071389 96352241836298163534401771)
    ·
      refine ⟨144528362754447245301602657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96352241836298163534401771 144528362754447245301602657)
      ·
        refine ⟨108396272065835433976201993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 144528362754447245301602657 108396272065835433976201993)
        ·
          refine ⟨81297204049376575482151495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 108396272065835433976201993 81297204049376575482151495)
          ·
            refine ⟨121945806074064863223227243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81297204049376575482151495 121945806074064863223227243)
            ·
              refine ⟨182918709111097294834840865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 121945806074064863223227243 182918709111097294834840865)
              ·
                refine ⟨137189031833322971126130649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 182918709111097294834840865 137189031833322971126130649)
                ·
                  refine ⟨102891773874992228344597987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 137189031833322971126130649 102891773874992228344597987)
                  ·
                    refine ⟨154337660812488342516896981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 102891773874992228344597987 154337660812488342516896981)
                    ·
                      refine ⟨3617288925292695527739773, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 154337660812488342516896981 3617288925292695527739773)
                      ·
                        rfl

theorem cell23_7044645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 1, 2, 2, 1, 7].length) (baseStart_7044645 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7044645 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7044645 prefixEnd_7044645 := by exact prefixLift 7044645
  have htrace : WordTrace (prefixWord ++ tailWord_7044645) baseStart_7044645 baseEnd_7044645 := by
    simpa [prefixWord, tailWord_7044645, baseEnd_7044645] using wordTrace_append hprefix tailTrace_7044645
  have hstable : (prefixWord ++ tailWord_7044645).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7044645).length < 2 ^ (prefixWord ++ tailWord_7044645).sum := by decide
  have hdescent : baseEnd_7044645 < baseStart_7044645 := by decide
  rcases family_descends (prefixWord ++ tailWord_7044645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7044669 : List Nat := [1, 4, 1, 3, 3, 1, 1, 1, 3, 5]
def baseStart_7044669 : Nat := 118140960795 + 7044669 * 2 ^ 59
def prefixEnd_7044669 : Nat := 4983230072969 + 3 ^ 40 * 7044669 * 2
def baseEnd_7044669 : Nat := 1205767082942801144613221

theorem tailTrace_7044669 : CollatzResearch.WordTrace tailWord_7044669 prefixEnd_7044669 1205767082942801144613221 := by
  unfold tailWord_7044669
  simp only [CollatzResearch.WordTrace]
  refine ⟨256940186915374821523945061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171293457943583214349296707 256940186915374821523945061)
  ·
    refine ⟨48176285046632779035739699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 256940186915374821523945061 48176285046632779035739699)
    ·
      refine ⟨72264427569949168553609549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48176285046632779035739699 72264427569949168553609549)
      ·
        refine ⟨27099160338730938207603581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 72264427569949168553609549 27099160338730938207603581)
        ·
          refine ⟨10162185127024101827851343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27099160338730938207603581 10162185127024101827851343)
          ·
            refine ⟨15243277690536152741777015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10162185127024101827851343 15243277690536152741777015)
            ·
              refine ⟨22864916535804229112665523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15243277690536152741777015 22864916535804229112665523)
              ·
                refine ⟨34297374803706343668998285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22864916535804229112665523 34297374803706343668998285)
                ·
                  refine ⟨12861515551389878875874357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34297374803706343668998285 12861515551389878875874357)
                  ·
                    refine ⟨1205767082942801144613221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12861515551389878875874357 1205767082942801144613221)
                    ·
                      rfl

theorem cell23_7044669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 3, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 3, 1, 1, 1, 3, 5].length) (baseStart_7044669 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7044669 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7044669 prefixEnd_7044669 := by exact prefixLift 7044669
  have htrace : WordTrace (prefixWord ++ tailWord_7044669) baseStart_7044669 baseEnd_7044669 := by
    simpa [prefixWord, tailWord_7044669, baseEnd_7044669] using wordTrace_append hprefix tailTrace_7044669
  have hstable : (prefixWord ++ tailWord_7044669).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7044669).length < 2 ^ (prefixWord ++ tailWord_7044669).sum := by decide
  have hdescent : baseEnd_7044669 < baseStart_7044669 := by decide
  rcases family_descends (prefixWord ++ tailWord_7044669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7044675 : List Nat := [1, 1, 1, 3, 1, 2, 1, 1, 2, 5, 5]
def baseStart_7044675 : Nat := 118140960795 + 7044675 * 2 ^ 59
def prefixEnd_7044675 : Nat := 4983230072969 + 3 ^ 40 * 7044675 * 2
def baseEnd_7044675 : Nat := 3617304329712330410364635

theorem tailTrace_7044675 : CollatzResearch.WordTrace tailWord_7044675 prefixEnd_7044675 3617304329712330410364635 := by
  unfold tailWord_7044675
  simp only [CollatzResearch.WordTrace]
  refine ⟨256940405753353084548663479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171293603835568723032442319 256940405753353084548663479)
  ·
    refine ⟨385410608630029626822995219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 256940405753353084548663479 385410608630029626822995219)
    ·
      refine ⟨578115912945044440234492829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 385410608630029626822995219 578115912945044440234492829)
      ·
        refine ⟨216793467354391665087934811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 578115912945044440234492829 216793467354391665087934811)
        ·
          refine ⟨325190201031587497631902217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 216793467354391665087934811 325190201031587497631902217)
          ·
            refine ⟨243892650773690623223926663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 325190201031587497631902217 243892650773690623223926663)
            ·
              refine ⟨365838976160535934835889995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 243892650773690623223926663 365838976160535934835889995)
              ·
                refine ⟨548758464240803902253834993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 365838976160535934835889995 548758464240803902253834993)
                ·
                  refine ⟨411568848180602926690376245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 548758464240803902253834993 411568848180602926690376245)
                  ·
                    refine ⟨38584579516931524377222773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 411568848180602926690376245 38584579516931524377222773)
                    ·
                      refine ⟨3617304329712330410364635, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 38584579516931524377222773 3617304329712330410364635)
                      ·
                        rfl

theorem cell23_7044675_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 2, 5, 5].length) (baseStart_7044675 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7044675 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7044675 prefixEnd_7044675 := by exact prefixLift 7044675
  have htrace : WordTrace (prefixWord ++ tailWord_7044675) baseStart_7044675 baseEnd_7044675 := by
    simpa [prefixWord, tailWord_7044675, baseEnd_7044675] using wordTrace_append hprefix tailTrace_7044675
  have hstable : (prefixWord ++ tailWord_7044675).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7044675).length < 2 ^ (prefixWord ++ tailWord_7044675).sum := by decide
  have hdescent : baseEnd_7044675 < baseStart_7044675 := by decide
  rcases family_descends (prefixWord ++ tailWord_7044675) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7044682 : List Nat := [3, 1, 2, 1, 1, 3, 3, 2, 1, 6]
def baseStart_7044682 : Nat := 118140960795 + 7044682 * 2 ^ 59
def prefixEnd_7044682 : Nat := 4983230072969 + 3 ^ 40 * 7044682 * 2
def baseEnd_7044682 : Nat := 1205769308025637294325701

theorem tailTrace_7044682 : CollatzResearch.WordTrace tailWord_7044682 prefixEnd_7044682 1205769308025637294325701 := by
  unfold tailWord_7044682
  simp only [CollatzResearch.WordTrace]
  refine ⟨64235165266081931186042075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 171293774042885149829445533 64235165266081931186042075)
  ·
    refine ⟨96352747899122896779063113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64235165266081931186042075 96352747899122896779063113)
    ·
      refine ⟨72264560924342172584297335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 96352747899122896779063113 72264560924342172584297335)
      ·
        refine ⟨108396841386513258876446003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72264560924342172584297335 108396841386513258876446003)
        ·
          refine ⟨162595262079769888314669005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 108396841386513258876446003 162595262079769888314669005)
          ·
            refine ⟨60973223279913708118000877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 162595262079769888314669005 60973223279913708118000877)
            ·
              refine ⟨22864958729967640544250329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 60973223279913708118000877 22864958729967640544250329)
              ·
                refine ⟨17148719047475730408187747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22864958729967640544250329 17148719047475730408187747)
                ·
                  refine ⟨25723078571213595612281621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17148719047475730408187747 25723078571213595612281621)
                  ·
                    refine ⟨1205769308025637294325701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25723078571213595612281621 1205769308025637294325701)
                    ·
                      rfl

theorem cell23_7044682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 3, 2, 1, 6].length) (baseStart_7044682 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7044682 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7044682 prefixEnd_7044682 := by exact prefixLift 7044682
  have htrace : WordTrace (prefixWord ++ tailWord_7044682) baseStart_7044682 baseEnd_7044682 := by
    simpa [prefixWord, tailWord_7044682, baseEnd_7044682] using wordTrace_append hprefix tailTrace_7044682
  have hstable : (prefixWord ++ tailWord_7044682).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7044682).length < 2 ^ (prefixWord ++ tailWord_7044682).sum := by decide
  have hdescent : baseEnd_7044682 < baseStart_7044682 := by decide
  rcases family_descends (prefixWord ++ tailWord_7044682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7044694 : List Nat := [5, 2, 2, 2, 1, 2, 2, 2, 1, 4]
def baseStart_7044694 : Nat := 118140960795 + 7044694 * 2 ^ 59
def prefixEnd_7044694 : Nat := 4983230072969 + 3 ^ 40 * 7044694 * 2
def baseEnd_7044694 : Nat := 1205771361948255278675683

theorem tailTrace_7044694 : CollatzResearch.WordTrace tailWord_7044694 prefixEnd_7044694 1205771361948255278675683 := by
  unfold tailWord_7044694
  simp only [CollatzResearch.WordTrace]
  refine ⟨16058818671267765674600321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 171294065826856167195736757 16058818671267765674600321)
  ·
    refine ⟨12044114003450824255950241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16058818671267765674600321 12044114003450824255950241)
    ·
      refine ⟨9033085502588118191962681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12044114003450824255950241 9033085502588118191962681)
      ·
        refine ⟨6774814126941088643972011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9033085502588118191962681 6774814126941088643972011)
        ·
          refine ⟨10162221190411632965958017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6774814126941088643972011 10162221190411632965958017)
          ·
            refine ⟨7621665892808724724468513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10162221190411632965958017 7621665892808724724468513)
            ·
              refine ⟨5716249419606543543351385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7621665892808724724468513 5716249419606543543351385)
              ·
                refine ⟨4287187064704907657513539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5716249419606543543351385 4287187064704907657513539)
                ·
                  refine ⟨6430780597057361486270309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4287187064704907657513539 6430780597057361486270309)
                  ·
                    refine ⟨1205771361948255278675683, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6430780597057361486270309 1205771361948255278675683)
                    ·
                      rfl

theorem cell23_7044694_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 1, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 1, 2, 2, 2, 1, 4].length) (baseStart_7044694 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7044694 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7044694 prefixEnd_7044694 := by exact prefixLift 7044694
  have htrace : WordTrace (prefixWord ++ tailWord_7044694) baseStart_7044694 baseEnd_7044694 := by
    simpa [prefixWord, tailWord_7044694, baseEnd_7044694] using wordTrace_append hprefix tailTrace_7044694
  have hstable : (prefixWord ++ tailWord_7044694).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7044694).length < 2 ^ (prefixWord ++ tailWord_7044694).sum := by decide
  have hdescent : baseEnd_7044694 < baseStart_7044694 := by decide
  rcases family_descends (prefixWord ++ tailWord_7044694) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7044695 : List Nat := [1, 1, 3, 2, 2, 14]
def baseStart_7044695 : Nat := 118140960795 + 7044695 * 2 ^ 59
def prefixEnd_7044695 : Nat := 4983230072969 + 3 ^ 40 * 7044695 * 2
def baseEnd_7044695 : Nat := 14886068309981153630101

theorem tailTrace_7044695 : CollatzResearch.WordTrace tailWord_7044695 prefixEnd_7044695 14886068309981153630101 := by
  unfold tailWord_7044695
  simp only [CollatzResearch.WordTrace]
  refine ⟨256941135213280627964391539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171294090142187085309594359 256941135213280627964391539)
  ·
    refine ⟨385411702819920941946587309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 256941135213280627964391539 385411702819920941946587309)
    ·
      refine ⟨144529388557470353229970241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 385411702819920941946587309 144529388557470353229970241)
      ·
        refine ⟨108397041418102764922477681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 144529388557470353229970241 108397041418102764922477681)
        ·
          refine ⟨81297781063577073691858261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 108397041418102764922477681 81297781063577073691858261)
          ·
            refine ⟨14886068309981153630101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 14 81297781063577073691858261 14886068309981153630101)
            ·
              rfl

theorem cell23_7044695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 14].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 14].length) (baseStart_7044695 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7044695 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7044695 prefixEnd_7044695 := by exact prefixLift 7044695
  have htrace : WordTrace (prefixWord ++ tailWord_7044695) baseStart_7044695 baseEnd_7044695 := by
    simpa [prefixWord, tailWord_7044695, baseEnd_7044695] using wordTrace_append hprefix tailTrace_7044695
  have hstable : (prefixWord ++ tailWord_7044695).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7044695).length < 2 ^ (prefixWord ++ tailWord_7044695).sum := by decide
  have hdescent : baseEnd_7044695 < baseStart_7044695 := by decide
  rcases family_descends (prefixWord ++ tailWord_7044695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7044700 : List Nat := [2, 2, 4, 1, 2, 1, 4, 2, 1, 1, 3]
def baseStart_7044700 : Nat := 118140960795 + 7044700 * 2 ^ 59
def prefixEnd_7044700 : Nat := 4983230072969 + 3 ^ 40 * 7044700 * 2
def baseEnd_7044700 : Nat := 3617317166728692812552021

theorem tailTrace_7044700 : CollatzResearch.WordTrace tailWord_7044700 prefixEnd_7044700 3617317166728692812552021 := by
  unfold tailWord_7044700
  simp only [CollatzResearch.WordTrace]
  refine ⟨128470658789131256909161777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 171294211718841675878882369 128470658789131256909161777)
  ·
    refine ⟨96352994091848442681871333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 128470658789131256909161777 96352994091848442681871333)
    ·
      refine ⟨18066186392221583002850875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 96352994091848442681871333 18066186392221583002850875)
      ·
        refine ⟨27099279588332374504276313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18066186392221583002850875 27099279588332374504276313)
        ·
          refine ⟨20324459691249280878207235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27099279588332374504276313 20324459691249280878207235)
          ·
            refine ⟨30486689536873921317310853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20324459691249280878207235 30486689536873921317310853)
            ·
              refine ⟨5716254288163860246995785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 30486689536873921317310853 5716254288163860246995785)
              ·
                refine ⟨4287190716122895185246839, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5716254288163860246995785 4287190716122895185246839)
                ·
                  refine ⟨6430786074184342777870259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4287190716122895185246839 6430786074184342777870259)
                  ·
                    refine ⟨9646179111276514166805389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6430786074184342777870259 9646179111276514166805389)
                    ·
                      refine ⟨3617317166728692812552021, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9646179111276514166805389 3617317166728692812552021)
                      ·
                        rfl

theorem cell23_7044700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 1, 4, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 1, 4, 2, 1, 1, 3].length) (baseStart_7044700 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7044700 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7044700 prefixEnd_7044700 := by exact prefixLift 7044700
  have htrace : WordTrace (prefixWord ++ tailWord_7044700) baseStart_7044700 baseEnd_7044700 := by
    simpa [prefixWord, tailWord_7044700, baseEnd_7044700] using wordTrace_append hprefix tailTrace_7044700
  have hstable : (prefixWord ++ tailWord_7044700).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7044700).length < 2 ^ (prefixWord ++ tailWord_7044700).sum := by decide
  have hdescent : baseEnd_7044700 < baseStart_7044700 := by decide
  rcases family_descends (prefixWord ++ tailWord_7044700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7044709 : List Nat := [1, 3, 1, 3, 3, 1, 1, 2, 3, 2, 3]
def baseStart_7044709 : Nat := 118140960795 + 7044709 * 2 ^ 59
def prefixEnd_7044709 : Nat := 4983230072969 + 3 ^ 40 * 7044709 * 2
def baseEnd_7044709 : Nat := 3617321788054583277339479

theorem tailTrace_7044709 : CollatzResearch.WordTrace tailWord_7044709 prefixEnd_7044709 3617321788054583277339479 := by
  unfold tailWord_7044709
  simp only [CollatzResearch.WordTrace]
  refine ⟨256941645835229908355401181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171294430556819938903600787 256941645835229908355401181)
  ·
    refine ⟨96353117188211215633275443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 256941645835229908355401181 96353117188211215633275443)
    ·
      refine ⟨144529675782316823449913165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96353117188211215633275443 144529675782316823449913165)
      ·
        refine ⟨54198628418368808793717437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 144529675782316823449913165 54198628418368808793717437)
        ·
          refine ⟨20324485656888303297644039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 54198628418368808793717437 20324485656888303297644039)
          ·
            refine ⟨30486728485332454946466059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20324485656888303297644039 30486728485332454946466059)
            ·
              refine ⟨45730092727998682419699089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30486728485332454946466059 45730092727998682419699089)
              ·
                refine ⟨34297569545999011814774317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45730092727998682419699089 34297569545999011814774317)
                ·
                  refine ⟨12861588579749629430540369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34297569545999011814774317 12861588579749629430540369)
                  ·
                    refine ⟨9646191434812222072905277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12861588579749629430540369 9646191434812222072905277)
                    ·
                      refine ⟨3617321788054583277339479, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9646191434812222072905277 3617321788054583277339479)
                      ·
                        rfl

theorem cell23_7044709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 1, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 1, 1, 2, 3, 2, 3].length) (baseStart_7044709 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7044709 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7044709 prefixEnd_7044709 := by exact prefixLift 7044709
  have htrace : WordTrace (prefixWord ++ tailWord_7044709) baseStart_7044709 baseEnd_7044709 := by
    simpa [prefixWord, tailWord_7044709, baseEnd_7044709] using wordTrace_append hprefix tailTrace_7044709
  have hstable : (prefixWord ++ tailWord_7044709).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7044709).length < 2 ^ (prefixWord ++ tailWord_7044709).sum := by decide
  have hdescent : baseEnd_7044709 < baseStart_7044709 := by decide
  rcases family_descends (prefixWord ++ tailWord_7044709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7044726 : List Nat := [5, 1, 1, 2, 2, 1, 2, 1, 3, 2, 3]
def baseStart_7044726 : Nat := 118140960795 + 7044726 * 2 ^ 59
def prefixEnd_7044726 : Nat := 4983230072969 + 3 ^ 40 * 7044726 * 2
def baseEnd_7044726 : Nat := 3617330517225709710826901

theorem tailTrace_7044726 : CollatzResearch.WordTrace tailWord_7044726 prefixEnd_7044726 3617330517225709710826901 := by
  unfold tailWord_7044726
  simp only [CollatzResearch.WordTrace]
  refine ⟨16058891617260520016173127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 171294843917445546839180021 16058891617260520016173127)
  ·
    refine ⟨24088337425890780024259691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16058891617260520016173127 24088337425890780024259691)
    ·
      refine ⟨36132506138836170036389537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24088337425890780024259691 36132506138836170036389537)
      ·
        refine ⟨27099379604127127527292153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36132506138836170036389537 27099379604127127527292153)
        ·
          refine ⟨20324534703095345645469115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27099379604127127527292153 20324534703095345645469115)
          ·
            refine ⟨30486802054643018468203673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20324534703095345645469115 30486802054643018468203673)
            ·
              refine ⟨22865101540982263851152755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30486802054643018468203673 22865101540982263851152755)
              ·
                refine ⟨34297652311473395776729133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22865101540982263851152755 34297652311473395776729133)
                ·
                  refine ⟨12861619616802523416273425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34297652311473395776729133 12861619616802523416273425)
                  ·
                    refine ⟨9646214712601892562205069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12861619616802523416273425 9646214712601892562205069)
                    ·
                      refine ⟨3617330517225709710826901, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9646214712601892562205069 3617330517225709710826901)
                      ·
                        rfl

theorem cell23_7044726_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 1, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 1, 2, 1, 3, 2, 3].length) (baseStart_7044726 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7044726 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7044726 prefixEnd_7044726 := by exact prefixLift 7044726
  have htrace : WordTrace (prefixWord ++ tailWord_7044726) baseStart_7044726 baseEnd_7044726 := by
    simpa [prefixWord, tailWord_7044726, baseEnd_7044726] using wordTrace_append hprefix tailTrace_7044726
  have hstable : (prefixWord ++ tailWord_7044726).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7044726).length < 2 ^ (prefixWord ++ tailWord_7044726).sum := by decide
  have hdescent : baseEnd_7044726 < baseStart_7044726 := by decide
  rcases family_descends (prefixWord ++ tailWord_7044726) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7044739 : List Nat := [1, 1, 1, 3, 3, 1, 1, 4, 4, 1, 3]
def baseStart_7044739 : Nat := 118140960795 + 7044739 * 2 ^ 59
def prefixEnd_7044739 : Nat := 4983230072969 + 3 ^ 40 * 7044739 * 2
def baseEnd_7044739 : Nat := 3617337192474218159964341

theorem tailTrace_7044739 : CollatzResearch.WordTrace tailWord_7044739 prefixEnd_7044739 3617337192474218159964341 := by
  unfold tailWord_7044739
  simp only [CollatzResearch.WordTrace]
  refine ⟨256942740025121223478993271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171295160016747482319328847 256942740025121223478993271)
  ·
    refine ⟨385414110037681835218489907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 256942740025121223478993271 385414110037681835218489907)
    ·
      refine ⟨578121165056522752827734861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 385414110037681835218489907 578121165056522752827734861)
      ·
        refine ⟨216795436896196032310400573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 578121165056522752827734861 216795436896196032310400573)
        ·
          refine ⟨81298288836073512116400215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 216795436896196032310400573 81298288836073512116400215)
          ·
            refine ⟨121947433254110268174600323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81298288836073512116400215 121947433254110268174600323)
            ·
              refine ⟨182921149881165402261900485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 121947433254110268174600323 182921149881165402261900485)
              ·
                refine ⟨34297715602718512924106341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 182921149881165402261900485 34297715602718512924106341)
                ·
                  refine ⟨6430821675509721173269939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 34297715602718512924106341 6430821675509721173269939)
                  ·
                    refine ⟨9646232513264581759904909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6430821675509721173269939 9646232513264581759904909)
                    ·
                      refine ⟨3617337192474218159964341, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9646232513264581759904909 3617337192474218159964341)
                      ·
                        rfl

theorem cell23_7044739_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 1, 4, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 1, 4, 4, 1, 3].length) (baseStart_7044739 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7044739 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7044739 prefixEnd_7044739 := by exact prefixLift 7044739
  have htrace : WordTrace (prefixWord ++ tailWord_7044739) baseStart_7044739 baseEnd_7044739 := by
    simpa [prefixWord, tailWord_7044739, baseEnd_7044739] using wordTrace_append hprefix tailTrace_7044739
  have hstable : (prefixWord ++ tailWord_7044739).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7044739).length < 2 ^ (prefixWord ++ tailWord_7044739).sum := by decide
  have hdescent : baseEnd_7044739 < baseStart_7044739 := by decide
  rcases family_descends (prefixWord ++ tailWord_7044739) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7044740 : List Nat := [2, 3, 2, 1, 5, 1, 2, 1, 1, 1, 4]
def baseStart_7044740 : Nat := 118140960795 + 7044740 * 2 ^ 59
def prefixEnd_7044740 : Nat := 4983230072969 + 3 ^ 40 * 7044740 * 2
def baseEnd_7044740 : Nat := 3617337705954872656051837

theorem tailTrace_7044740 : CollatzResearch.WordTrace tailWord_7044740 prefixEnd_7044740 3617337705954872656051837 := by
  unfold tailWord_7044740
  simp only [CollatzResearch.WordTrace]
  refine ⟨128471388249058800324889837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 171295184332078400433186449 128471388249058800324889837)
  ·
    refine ⟨48176770593397050121833689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 128471388249058800324889837 48176770593397050121833689)
    ·
      refine ⟨36132577945047787591375267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48176770593397050121833689 36132577945047787591375267)
      ·
        refine ⟨54198866917571681387062901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36132577945047787591375267 54198866917571681387062901)
        ·
          refine ⟨5081143773522345130037147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 54198866917571681387062901 5081143773522345130037147)
          ·
            refine ⟨7621715660283517695055721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5081143773522345130037147 7621715660283517695055721)
            ·
              refine ⟨5716286745212638271291791, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7621715660283517695055721 5716286745212638271291791)
              ·
                refine ⟨8574430117818957406937687, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5716286745212638271291791 8574430117818957406937687)
                ·
                  refine ⟨12861645176728436110406531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8574430117818957406937687 12861645176728436110406531)
                  ·
                    refine ⟨19292467765092654165609797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12861645176728436110406531 19292467765092654165609797)
                    ·
                      refine ⟨3617337705954872656051837, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19292467765092654165609797 3617337705954872656051837)
                      ·
                        rfl

theorem cell23_7044740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 5, 1, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 5, 1, 2, 1, 1, 1, 4].length) (baseStart_7044740 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7044740 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7044740 prefixEnd_7044740 := by exact prefixLift 7044740
  have htrace : WordTrace (prefixWord ++ tailWord_7044740) baseStart_7044740 baseEnd_7044740 := by
    simpa [prefixWord, tailWord_7044740, baseEnd_7044740] using wordTrace_append hprefix tailTrace_7044740
  have hstable : (prefixWord ++ tailWord_7044740).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7044740).length < 2 ^ (prefixWord ++ tailWord_7044740).sum := by decide
  have hdescent : baseEnd_7044740 < baseStart_7044740 := by decide
  rcases family_descends (prefixWord ++ tailWord_7044740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7044743 : List Nat := [1, 1, 4, 2, 1, 5, 2, 1, 1, 2, 3]
def baseStart_7044743 : Nat := 118140960795 + 7044743 * 2 ^ 59
def prefixEnd_7044743 : Nat := 4983230072969 + 3 ^ 40 * 7044743 * 2
def baseEnd_7044743 : Nat := 3617339246396836144314323

theorem tailTrace_7044743 : CollatzResearch.WordTrace tailWord_7044743 prefixEnd_7044743 3617339246396836144314323 := by
  unfold tailWord_7044743
  simp only [CollatzResearch.WordTrace]
  refine ⟨256942885917106732162138883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171295257278071154774759255 256942885917106732162138883)
  ·
    refine ⟨385414328875660098243208325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 256942885917106732162138883 385414328875660098243208325)
    ·
      refine ⟨72265186664186268420601561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 385414328875660098243208325 72265186664186268420601561)
      ·
        refine ⟨54198889998139701315451171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72265186664186268420601561 54198889998139701315451171)
        ·
          refine ⟨81298334997209551973176757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54198889998139701315451171 81298334997209551973176757)
          ·
            refine ⟨7621718905988395497485321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 81298334997209551973176757 7621718905988395497485321)
            ·
              refine ⟨5716289179491296623113991, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7621718905988395497485321 5716289179491296623113991)
              ·
                refine ⟨8574433769236944934670987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5716289179491296623113991 8574433769236944934670987)
                ·
                  refine ⟨12861650653855417402006481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8574433769236944934670987 12861650653855417402006481)
                  ·
                    refine ⟨9646237990391563051504861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12861650653855417402006481 9646237990391563051504861)
                    ·
                      refine ⟨3617339246396836144314323, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9646237990391563051504861 3617339246396836144314323)
                      ·
                        rfl

theorem cell23_7044743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 5, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 5, 2, 1, 1, 2, 3].length) (baseStart_7044743 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7044743 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7044743 prefixEnd_7044743 := by exact prefixLift 7044743
  have htrace : WordTrace (prefixWord ++ tailWord_7044743) baseStart_7044743 baseEnd_7044743 := by
    simpa [prefixWord, tailWord_7044743, baseEnd_7044743] using wordTrace_append hprefix tailTrace_7044743
  have hstable : (prefixWord ++ tailWord_7044743).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7044743).length < 2 ^ (prefixWord ++ tailWord_7044743).sum := by decide
  have hdescent : baseEnd_7044743 < baseStart_7044743 := by decide
  rcases family_descends (prefixWord ++ tailWord_7044743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7044770 : List Nat := [3, 3, 1, 4, 2, 1, 1, 1, 1, 2, 4]
def baseStart_7044770 : Nat := 118140960795 + 7044770 * 2 ^ 59
def prefixEnd_7044770 : Nat := 4983230072969 + 3 ^ 40 * 7044770 * 2
def baseEnd_7044770 : Nat := 3617353110374507538676699

theorem tailTrace_7044770 : CollatzResearch.WordTrace tailWord_7044770 prefixEnd_7044770 3617353110374507538676699 := by
  unfold tailWord_7044770
  simp only [CollatzResearch.WordTrace]
  refine ⟨64235967672002228943342941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 171295913792005943848914509 64235967672002228943342941)
  ·
    refine ⟨24088487877000835853753603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 64235967672002228943342941 24088487877000835853753603)
    ·
      refine ⟨36132731815501253780630405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24088487877000835853753603 36132731815501253780630405)
      ·
        refine ⟨6774887215406485083868201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 36132731815501253780630405 6774887215406485083868201)
        ·
          refine ⟨5081165411554863812901151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6774887215406485083868201 5081165411554863812901151)
          ·
            refine ⟨7621748117332295719351727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5081165411554863812901151 7621748117332295719351727)
            ·
              refine ⟨11432622175998443579027591, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7621748117332295719351727 11432622175998443579027591)
              ·
                refine ⟨17148933263997665368541387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11432622175998443579027591 17148933263997665368541387)
                ·
                  refine ⟨25723399895996498052812081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17148933263997665368541387 25723399895996498052812081)
                  ·
                    refine ⟨19292549921997373539609061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25723399895996498052812081 19292549921997373539609061)
                    ·
                      refine ⟨3617353110374507538676699, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19292549921997373539609061 3617353110374507538676699)
                      ·
                        rfl

theorem cell23_7044770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 2, 1, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 2, 1, 1, 1, 1, 2, 4].length) (baseStart_7044770 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7044770 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7044770 prefixEnd_7044770 := by exact prefixLift 7044770
  have htrace : WordTrace (prefixWord ++ tailWord_7044770) baseStart_7044770 baseEnd_7044770 := by
    simpa [prefixWord, tailWord_7044770, baseEnd_7044770] using wordTrace_append hprefix tailTrace_7044770
  have hstable : (prefixWord ++ tailWord_7044770).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7044770).length < 2 ^ (prefixWord ++ tailWord_7044770).sum := by decide
  have hdescent : baseEnd_7044770 < baseStart_7044770 := by decide
  rcases family_descends (prefixWord ++ tailWord_7044770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7044792 : List Nat := [2, 1, 2, 1, 2, 1, 1, 4, 1, 4, 4]
def baseStart_7044792 : Nat := 118140960795 + 7044792 * 2 ^ 59
def prefixEnd_7044792 : Nat := 4983230072969 + 3 ^ 40 * 7044792 * 2
def baseEnd_7044792 : Nat := 3617364406948906452601597

theorem tailTrace_7044792 : CollatzResearch.WordTrace tailWord_7044792 prefixEnd_7044792 3617364406948906452601597 := by
  unfold tailWord_7044792
  simp only [CollatzResearch.WordTrace]
  refine ⟨128472336546964606765336315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 171296448729286142353781753 128472336546964606765336315)
  ·
    refine ⟨192708504820446910148004473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128472336546964606765336315 192708504820446910148004473)
    ·
      refine ⟨144531378615335182611003355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 192708504820446910148004473 144531378615335182611003355)
      ·
        refine ⟨216797067923002773916505033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 144531378615335182611003355 216797067923002773916505033)
        ·
          refine ⟨162597800942252080437378775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 216797067923002773916505033 162597800942252080437378775)
          ·
            refine ⟨243896701413378120656068163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 162597800942252080437378775 243896701413378120656068163)
            ·
              refine ⟨365845052120067180984102245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 243896701413378120656068163 365845052120067180984102245)
              ·
                refine ⟨68595947272512596434519171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 365845052120067180984102245 68595947272512596434519171)
                ·
                  refine ⟨102893920908768894651778757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 68595947272512596434519171 102893920908768894651778757)
                  ·
                    refine ⟨19292610170394167747208517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 102893920908768894651778757 19292610170394167747208517)
                    ·
                      refine ⟨3617364406948906452601597, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19292610170394167747208517 3617364406948906452601597)
                      ·
                        rfl

theorem cell23_7044792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 4, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 4, 1, 4, 4].length) (baseStart_7044792 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7044792 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7044792 prefixEnd_7044792 := by exact prefixLift 7044792
  have htrace : WordTrace (prefixWord ++ tailWord_7044792) baseStart_7044792 baseEnd_7044792 := by
    simpa [prefixWord, tailWord_7044792, baseEnd_7044792] using wordTrace_append hprefix tailTrace_7044792
  have hstable : (prefixWord ++ tailWord_7044792).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7044792).length < 2 ^ (prefixWord ++ tailWord_7044792).sum := by decide
  have hdescent : baseEnd_7044792 < baseStart_7044792 := by decide
  rcases family_descends (prefixWord ++ tailWord_7044792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7044832 : List Nat := [2, 1, 1, 3, 1, 2, 2, 1, 3, 7]
def baseStart_7044832 : Nat := 118140960795 + 7044832 * 2 ^ 59
def prefixEnd_7044832 : Nat := 4983230072969 + 3 ^ 40 * 7044832 * 2
def baseEnd_7044832 : Nat := 1205794982058362098700471

theorem tailTrace_7044832 : CollatzResearch.WordTrace tailWord_7044832 prefixEnd_7044832 1205794982058362098700471 := by
  unfold tailWord_7044832
  simp only [CollatzResearch.WordTrace]
  refine ⟨128473066006892150181064375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 171297421342522866908085833 128473066006892150181064375)
  ·
    refine ⟨192709599010338225271596563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128473066006892150181064375 192709599010338225271596563)
    ·
      refine ⟨289064398515507337907394845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 192709599010338225271596563 289064398515507337907394845)
      ·
        refine ⟨108399149443315251715273067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 289064398515507337907394845 108399149443315251715273067)
        ·
          refine ⟨162598724164972877572909601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 108399149443315251715273067 162598724164972877572909601)
          ·
            refine ⟨121949043123729658179682201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 162598724164972877572909601 121949043123729658179682201)
            ·
              refine ⟨91461782342797243634761651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 121949043123729658179682201 91461782342797243634761651)
              ·
                refine ⟨137192673514195865452142477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 91461782342797243634761651 137192673514195865452142477)
                ·
                  refine ⟨51447252567823449544553429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 137192673514195865452142477 51447252567823449544553429)
                  ·
                    refine ⟨1205794982058362098700471, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 51447252567823449544553429 1205794982058362098700471)
                    ·
                      rfl

theorem cell23_7044832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 2, 1, 3, 7].length) (baseStart_7044832 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7044832 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7044832 prefixEnd_7044832 := by exact prefixLift 7044832
  have htrace : WordTrace (prefixWord ++ tailWord_7044832) baseStart_7044832 baseEnd_7044832 := by
    simpa [prefixWord, tailWord_7044832, baseEnd_7044832] using wordTrace_append hprefix tailTrace_7044832
  have hstable : (prefixWord ++ tailWord_7044832).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7044832).length < 2 ^ (prefixWord ++ tailWord_7044832).sum := by decide
  have hdescent : baseEnd_7044832 < baseStart_7044832 := by decide
  rcases family_descends (prefixWord ++ tailWord_7044832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7044849 : List Nat := [1, 2, 2, 2, 2, 3, 1, 3, 2, 5]
def baseStart_7044849 : Nat := 118140960795 + 7044849 * 2 ^ 59
def prefixEnd_7044849 : Nat := 4983230072969 + 3 ^ 40 * 7044849 * 2
def baseEnd_7044849 : Nat := 1205797891782070909862945

theorem tailTrace_7044849 : CollatzResearch.WordTrace tailWord_7044849 prefixEnd_7044849 1205797891782070909862945 := by
  unfold tailWord_7044849
  simp only [CollatzResearch.WordTrace]
  refine ⟨256946752054722712265497601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171297834703148474843665067 256946752054722712265497601)
  ·
    refine ⟨192710064041042034199123201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 256946752054722712265497601 192710064041042034199123201)
    ·
      refine ⟨144532548030781525649342401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 192710064041042034199123201 144532548030781525649342401)
      ·
        refine ⟨108399411023086144237006801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 144532548030781525649342401 108399411023086144237006801)
        ·
          refine ⟨81299558267314608177755101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 108399411023086144237006801 81299558267314608177755101)
          ·
            refine ⟨30487334350242978066658163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 81299558267314608177755101 30487334350242978066658163)
            ·
              refine ⟨45731001525364467099987245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30487334350242978066658163 45731001525364467099987245)
              ·
                refine ⟨17149125572011675162495217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 45731001525364467099987245 17149125572011675162495217)
                ·
                  refine ⟨12861844179008756371871413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17149125572011675162495217 12861844179008756371871413)
                  ·
                    refine ⟨1205797891782070909862945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12861844179008756371871413 1205797891782070909862945)
                    ·
                      rfl

theorem cell23_7044849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 3, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 3, 1, 3, 2, 5].length) (baseStart_7044849 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7044849 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7044849 prefixEnd_7044849 := by exact prefixLift 7044849
  have htrace : WordTrace (prefixWord ++ tailWord_7044849) baseStart_7044849 baseEnd_7044849 := by
    simpa [prefixWord, tailWord_7044849, baseEnd_7044849] using wordTrace_append hprefix tailTrace_7044849
  have hstable : (prefixWord ++ tailWord_7044849).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7044849).length < 2 ^ (prefixWord ++ tailWord_7044849).sum := by decide
  have hdescent : baseEnd_7044849 < baseStart_7044849 := by decide
  rcases family_descends (prefixWord ++ tailWord_7044849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7044866 : List Nat := [3, 4, 1, 1, 1, 1, 1, 4, 2, 5]
def baseStart_7044866 : Nat := 118140960795 + 7044866 * 2 ^ 59
def prefixEnd_7044866 : Nat := 4983230072969 + 3 ^ 40 * 7044866 * 2
def baseEnd_7044866 : Nat := 1205800801505779721025419

theorem tailTrace_7044866 : CollatzResearch.WordTrace tailWord_7044866 prefixEnd_7044866 1205800801505779721025419 := by
  unfold tailWord_7044866
  simp only [CollatzResearch.WordTrace]
  refine ⟨64236843023915281042216613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 171298248063774082779244301 64236843023915281042216613)
  ·
    refine ⟨12044408066984115195415615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 64236843023915281042216613 12044408066984115195415615)
    ·
      refine ⟨18066612100476172793123423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12044408066984115195415615 18066612100476172793123423)
      ·
        refine ⟨27099918150714259189685135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18066612100476172793123423 27099918150714259189685135)
        ·
          refine ⟨40649877226071388784527703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27099918150714259189685135 40649877226071388784527703)
          ·
            refine ⟨60974815839107083176791555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40649877226071388784527703 60974815839107083176791555)
            ·
              refine ⟨91462223758660624765187333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60974815839107083176791555 91462223758660624765187333)
              ·
                refine ⟨17149166954748867143472625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 91462223758660624765187333 17149166954748867143472625)
                ·
                  refine ⟨12861875216061650357604469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17149166954748867143472625 12861875216061650357604469)
                  ·
                    refine ⟨1205800801505779721025419, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12861875216061650357604469 1205800801505779721025419)
                    ·
                      rfl

theorem cell23_7044866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 1, 4, 2, 5].length) (baseStart_7044866 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7044866 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7044866 prefixEnd_7044866 := by exact prefixLift 7044866
  have htrace : WordTrace (prefixWord ++ tailWord_7044866) baseStart_7044866 baseEnd_7044866 := by
    simpa [prefixWord, tailWord_7044866, baseEnd_7044866] using wordTrace_append hprefix tailTrace_7044866
  have hstable : (prefixWord ++ tailWord_7044866).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7044866).length < 2 ^ (prefixWord ++ tailWord_7044866).sum := by decide
  have hdescent : baseEnd_7044866 < baseStart_7044866 := by decide
  rcases family_descends (prefixWord ++ tailWord_7044866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7044877 : List Nat := [1, 7, 2, 1, 1, 1, 1, 1, 2, 2, 4]
def baseStart_7044877 : Nat := 118140960795 + 7044877 * 2 ^ 59
def prefixEnd_7044877 : Nat := 4983230072969 + 3 ^ 40 * 7044877 * 2
def baseEnd_7044877 : Nat := 3617408052804538620038707

theorem tailTrace_7044877 : CollatzResearch.WordTrace tailWord_7044877 prefixEnd_7044877 3617408052804538620038707 := by
  unfold tailWord_7044877
  simp only [CollatzResearch.WordTrace]
  refine ⟨256947773298621273047516885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171298515532414182031677923 256947773298621273047516885)
  ·
    refine ⟨6022213436686436087051177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 256947773298621273047516885 6022213436686436087051177)
    ·
      refine ⟨4516660077514827065288383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6022213436686436087051177 4516660077514827065288383)
      ·
        refine ⟨6774990116272240597932575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4516660077514827065288383 6774990116272240597932575)
        ·
          refine ⟨10162485174408360896898863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6774990116272240597932575 10162485174408360896898863)
          ·
            refine ⟨15243727761612541345348295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10162485174408360896898863 15243727761612541345348295)
            ·
              refine ⟨22865591642418812018022443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15243727761612541345348295 22865591642418812018022443)
              ·
                refine ⟨34298387463628218027033665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22865591642418812018022443 34298387463628218027033665)
                ·
                  refine ⟨25723790597721163520275249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34298387463628218027033665 25723790597721163520275249)
                  ·
                    refine ⟨19292842948290872640206437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25723790597721163520275249 19292842948290872640206437)
                    ·
                      refine ⟨3617408052804538620038707, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19292842948290872640206437 3617408052804538620038707)
                      ·
                        rfl

theorem cell23_7044877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 1, 1, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 1, 1, 1, 1, 2, 2, 4].length) (baseStart_7044877 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7044877 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7044877 prefixEnd_7044877 := by exact prefixLift 7044877
  have htrace : WordTrace (prefixWord ++ tailWord_7044877) baseStart_7044877 baseEnd_7044877 := by
    simpa [prefixWord, tailWord_7044877, baseEnd_7044877] using wordTrace_append hprefix tailTrace_7044877
  have hstable : (prefixWord ++ tailWord_7044877).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7044877).length < 2 ^ (prefixWord ++ tailWord_7044877).sum := by decide
  have hdescent : baseEnd_7044877 < baseStart_7044877 := by decide
  rcases family_descends (prefixWord ++ tailWord_7044877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7044896 : List Nat := [2, 1, 1, 5, 1, 1, 3, 2, 3, 4]
def baseStart_7044896 : Nat := 118140960795 + 7044896 * 2 ^ 59
def prefixEnd_7044896 : Nat := 4983230072969 + 3 ^ 40 * 7044896 * 2
def baseEnd_7044896 : Nat := 1205805936312324681900373

theorem tailTrace_7044896 : CollatzResearch.WordTrace tailWord_7044896 prefixEnd_7044896 1205805936312324681900373 := by
  unfold tailWord_7044896
  simp only [CollatzResearch.WordTrace]
  refine ⟨128474233142776219646229271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 171298977523701626194972361 128474233142776219646229271)
  ·
    refine ⟨192711349714164329469343907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128474233142776219646229271 192711349714164329469343907)
    ·
      refine ⟨289067024571246494204015861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 192711349714164329469343907 289067024571246494204015861)
      ·
        refine ⟨27100033553554358831626487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 289067024571246494204015861 27100033553554358831626487)
        ·
          refine ⟨40650050330331538247439731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27100033553554358831626487 40650050330331538247439731)
          ·
            refine ⟨60975075495497307371159597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40650050330331538247439731 60975075495497307371159597)
            ·
              refine ⟨22865653310811490264184849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 60975075495497307371159597 22865653310811490264184849)
              ·
                refine ⟨17149239983108617698138637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22865653310811490264184849 17149239983108617698138637)
                ·
                  refine ⟨6430964993665731636801989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17149239983108617698138637 6430964993665731636801989)
                  ·
                    refine ⟨1205805936312324681900373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6430964993665731636801989 1205805936312324681900373)
                    ·
                      rfl

theorem cell23_7044896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 3, 2, 3, 4].length) (baseStart_7044896 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7044896 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7044896 prefixEnd_7044896 := by exact prefixLift 7044896
  have htrace : WordTrace (prefixWord ++ tailWord_7044896) baseStart_7044896 baseEnd_7044896 := by
    simpa [prefixWord, tailWord_7044896, baseEnd_7044896] using wordTrace_append hprefix tailTrace_7044896
  have hstable : (prefixWord ++ tailWord_7044896).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7044896).length < 2 ^ (prefixWord ++ tailWord_7044896).sum := by decide
  have hdescent : baseEnd_7044896 < baseStart_7044896 := by decide
  rcases family_descends (prefixWord ++ tailWord_7044896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7044913 : List Nat := [1, 2, 2, 3, 2, 2, 1, 5, 1, 4]
def baseStart_7044913 : Nat := 118140960795 + 7044913 * 2 ^ 59
def prefixEnd_7044913 : Nat := 4983230072969 + 3 ^ 40 * 7044913 * 2
def baseEnd_7044913 : Nat := 1205808846036033493062847

theorem tailTrace_7044913 : CollatzResearch.WordTrace tailWord_7044913 prefixEnd_7044913 1205808846036033493062847 := by
  unfold tailWord_7044913
  simp only [CollatzResearch.WordTrace]
  refine ⟨256949086326490851195827393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171299390884327234130551595 256949086326490851195827393)
  ·
    refine ⟨192711814744868138396870545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 256949086326490851195827393 192711814744868138396870545)
    ·
      refine ⟨144533861058651103797652909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 192711814744868138396870545 144533861058651103797652909)
      ·
        refine ⟨54200197896994163924119841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 144533861058651103797652909 54200197896994163924119841)
        ·
          refine ⟨40650148422745622943089881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54200197896994163924119841 40650148422745622943089881)
          ·
            refine ⟨30487611317059217207317411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40650148422745622943089881 30487611317059217207317411)
            ·
              refine ⟨45731416975588825810976117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30487611317059217207317411 45731416975588825810976117)
              ·
                refine ⟨4287320341461452419779011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 45731416975588825810976117 4287320341461452419779011)
                ·
                  refine ⟨6430980512192178629668517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4287320341461452419779011 6430980512192178629668517)
                  ·
                    refine ⟨1205808846036033493062847, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6430980512192178629668517 1205808846036033493062847)
                    ·
                      rfl

theorem cell23_7044913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 2, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 2, 1, 5, 1, 4].length) (baseStart_7044913 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7044913 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7044913 prefixEnd_7044913 := by exact prefixLift 7044913
  have htrace : WordTrace (prefixWord ++ tailWord_7044913) baseStart_7044913 baseEnd_7044913 := by
    simpa [prefixWord, tailWord_7044913, baseEnd_7044913] using wordTrace_append hprefix tailTrace_7044913
  have hstable : (prefixWord ++ tailWord_7044913).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7044913).length < 2 ^ (prefixWord ++ tailWord_7044913).sum := by decide
  have hdescent : baseEnd_7044913 < baseStart_7044913 := by decide
  rcases family_descends (prefixWord ++ tailWord_7044913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7044916 : List Nat := [2, 5, 1, 1, 2, 1, 1, 1, 2, 1, 6]
def baseStart_7044916 : Nat := 118140960795 + 7044916 * 2 ^ 59
def prefixEnd_7044916 : Nat := 4983230072969 + 3 ^ 40 * 7044916 * 2
def baseEnd_7044916 : Nat := 3617428078550063967451027

theorem tailTrace_7044916 : CollatzResearch.WordTrace tailWord_7044916 prefixEnd_7044916 3617428078550063967451027 := by
  unfold tailWord_7044916
  simp only [CollatzResearch.WordTrace]
  refine ⟨128474597872739991354093301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 171299463830319988472124401 128474597872739991354093301)
  ·
    refine ⟨12044493550569374189446247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 128474597872739991354093301 12044493550569374189446247)
    ·
      refine ⟨18066740325854061284169371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12044493550569374189446247 18066740325854061284169371)
      ·
        refine ⟨27100110488781091926254057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18066740325854061284169371 27100110488781091926254057)
        ·
          refine ⟨20325082866585818944690543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27100110488781091926254057 20325082866585818944690543)
          ·
            refine ⟨30487624299878728417035815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20325082866585818944690543 30487624299878728417035815)
            ·
              refine ⟨45731436449818092625553723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30487624299878728417035815 45731436449818092625553723)
              ·
                refine ⟨68597154674727138938330585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45731436449818092625553723 68597154674727138938330585)
                ·
                  refine ⟨51447866006045354203747939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 68597154674727138938330585 51447866006045354203747939)
                  ·
                    refine ⟨77171799009068031305621909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 51447866006045354203747939 77171799009068031305621909)
                    ·
                      refine ⟨3617428078550063967451027, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 77171799009068031305621909 3617428078550063967451027)
                      ·
                        rfl

theorem cell23_7044916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 1, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 1, 1, 1, 2, 1, 6].length) (baseStart_7044916 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7044916 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7044916 prefixEnd_7044916 := by exact prefixLift 7044916
  have htrace : WordTrace (prefixWord ++ tailWord_7044916) baseStart_7044916 baseEnd_7044916 := by
    simpa [prefixWord, tailWord_7044916, baseEnd_7044916] using wordTrace_append hprefix tailTrace_7044916
  have hstable : (prefixWord ++ tailWord_7044916).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7044916).length < 2 ^ (prefixWord ++ tailWord_7044916).sum := by decide
  have hdescent : baseEnd_7044916 < baseStart_7044916 := by decide
  rcases family_descends (prefixWord ++ tailWord_7044916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7044926 : List Nat := [4, 2, 1, 2, 2, 2, 1, 1, 8]
def baseStart_7044926 : Nat := 118140960795 + 7044926 * 2 ^ 59
def prefixEnd_7044926 : Nat := 4983230072969 + 3 ^ 40 * 7044926 * 2
def baseEnd_7044926 : Nat := 401937023706289880925109

theorem tailTrace_7044926 : CollatzResearch.WordTrace tailWord_7044926 prefixEnd_7044926 401937023706289880925109 := by
  unfold tailWord_7044926
  simp only [CollatzResearch.WordTrace]
  refine ⟨32118695059430469302006329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 171299706983629169610700421 32118695059430469302006329)
  ·
    refine ⟨24089021294572851976504747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32118695059430469302006329 24089021294572851976504747)
    ·
      refine ⟨36133531941859277964757121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24089021294572851976504747 36133531941859277964757121)
      ·
        refine ⟨27100148956394458473567841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36133531941859277964757121 27100148956394458473567841)
        ·
          refine ⟨20325111717295843855175881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27100148956394458473567841 20325111717295843855175881)
          ·
            refine ⟨15243833787971882891381911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20325111717295843855175881 15243833787971882891381911)
            ·
              refine ⟨22865750681957824337072867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15243833787971882891381911 22865750681957824337072867)
              ·
                refine ⟨34298626022936736505609301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22865750681957824337072867 34298626022936736505609301)
                ·
                  refine ⟨401937023706289880925109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 34298626022936736505609301 401937023706289880925109)
                  ·
                    rfl

theorem cell23_7044926_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 2, 1, 1, 8].length) (baseStart_7044926 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7044926 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7044926 prefixEnd_7044926 := by exact prefixLift 7044926
  have htrace : WordTrace (prefixWord ++ tailWord_7044926) baseStart_7044926 baseEnd_7044926 := by
    simpa [prefixWord, tailWord_7044926, baseEnd_7044926] using wordTrace_append hprefix tailTrace_7044926
  have hstable : (prefixWord ++ tailWord_7044926).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7044926).length < 2 ^ (prefixWord ++ tailWord_7044926).sum := by decide
  have hdescent : baseEnd_7044926 < baseStart_7044926 := by decide
  rcases family_descends (prefixWord ++ tailWord_7044926) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7044969 : List Nat := [1, 2, 1, 1, 1, 3, 1, 6, 1, 6]
def baseStart_7044969 : Nat := 118140960795 + 7044969 * 2 ^ 59
def prefixEnd_7044969 : Nat := 4983230072969 + 3 ^ 40 * 7044969 * 2
def baseEnd_7044969 : Nat := 1205818431008250753362761

theorem tailTrace_7044969 : CollatzResearch.WordTrace tailWord_7044969 prefixEnd_7044969 1205818431008250753362761 := by
  unfold tailWord_7044969
  simp only [CollatzResearch.WordTrace]
  refine ⟨256951128814287972759865961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171300752542858648506577307 256951128814287972759865961)
  ·
    refine ⟨192713346610715979569899471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 256951128814287972759865961 192713346610715979569899471)
    ·
      refine ⟨289070019916073969354849207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 192713346610715979569899471 289070019916073969354849207)
      ·
        refine ⟨433605029874110954032273811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 289070019916073969354849207 433605029874110954032273811)
        ·
          refine ⟨650407544811166431048410717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 433605029874110954032273811 650407544811166431048410717)
          ·
            refine ⟨243902829304187411643154019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 650407544811166431048410717 243902829304187411643154019)
            ·
              refine ⟨365854243956281117464731029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 243902829304187411643154019 365854243956281117464731029)
              ·
                refine ⟨17149417685450677381159267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 365854243956281117464731029 17149417685450677381159267)
                ·
                  refine ⟨25724126528176016071738901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17149417685450677381159267 25724126528176016071738901)
                  ·
                    refine ⟨1205818431008250753362761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25724126528176016071738901 1205818431008250753362761)
                    ·
                      rfl

theorem cell23_7044969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 1, 6, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 1, 6, 1, 6].length) (baseStart_7044969 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7044969 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7044969 prefixEnd_7044969 := by exact prefixLift 7044969
  have htrace : WordTrace (prefixWord ++ tailWord_7044969) baseStart_7044969 baseEnd_7044969 := by
    simpa [prefixWord, tailWord_7044969, baseEnd_7044969] using wordTrace_append hprefix tailTrace_7044969
  have hstable : (prefixWord ++ tailWord_7044969).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7044969).length < 2 ^ (prefixWord ++ tailWord_7044969).sum := by decide
  have hdescent : baseEnd_7044969 < baseStart_7044969 := by decide
  rcases family_descends (prefixWord ++ tailWord_7044969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7044986 : List Nat := [3, 1, 1, 1, 1, 1, 6, 1, 4, 4]
def baseStart_7044986 : Nat := 118140960795 + 7044986 * 2 ^ 59
def prefixEnd_7044986 : Nat := 4983230072969 + 3 ^ 40 * 7044986 * 2
def baseEnd_7044986 : Nat := 1205821340731959564525235

theorem tailTrace_7044986 : CollatzResearch.WordTrace tailWord_7044986 prefixEnd_7044986 1205821340731959564525235 := by
  unfold tailWord_7044986
  simp only [CollatzResearch.WordTrace]
  refine ⟨64237937213806596165808703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 171301165903484256442156541 64237937213806596165808703)
  ·
    refine ⟨96356905820709894248713055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64237937213806596165808703 96356905820709894248713055)
    ·
      refine ⟨144535358731064841373069583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96356905820709894248713055 144535358731064841373069583)
      ·
        refine ⟨216803038096597262059604375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 144535358731064841373069583 216803038096597262059604375)
        ·
          refine ⟨325204557144895893089406563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 216803038096597262059604375 325204557144895893089406563)
          ·
            refine ⟨487806835717343839634109845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 325204557144895893089406563 487806835717343839634109845)
            ·
              refine ⟨22865945424250492482848899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 487806835717343839634109845 22865945424250492482848899)
              ·
                refine ⟨34298918136375738724273349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22865945424250492482848899 34298918136375738724273349)
                ·
                  refine ⟨6431047150570451010801253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 34298918136375738724273349 6431047150570451010801253)
                  ·
                    refine ⟨1205821340731959564525235, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6431047150570451010801253 1205821340731959564525235)
                    ·
                      rfl

theorem cell23_7044986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 6, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 6, 1, 4, 4].length) (baseStart_7044986 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7044986 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7044986 prefixEnd_7044986 := by exact prefixLift 7044986
  have htrace : WordTrace (prefixWord ++ tailWord_7044986) baseStart_7044986 baseEnd_7044986 := by
    simpa [prefixWord, tailWord_7044986, baseEnd_7044986] using wordTrace_append hprefix tailTrace_7044986
  have hstable : (prefixWord ++ tailWord_7044986).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7044986).length < 2 ^ (prefixWord ++ tailWord_7044986).sum := by decide
  have hdescent : baseEnd_7044986 < baseStart_7044986 := by decide
  rcases family_descends (prefixWord ++ tailWord_7044986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7044996 : List Nat := [2, 3, 2, 1, 1, 1, 4, 2, 1, 1, 5]
def baseStart_7044996 : Nat := 118140960795 + 7044996 * 2 ^ 59
def prefixEnd_7044996 : Nat := 4983230072969 + 3 ^ 40 * 7044996 * 2
def baseEnd_7044996 : Nat := 3617469157002423654450659

theorem tailTrace_7044996 : CollatzResearch.WordTrace tailWord_7044996 prefixEnd_7044996 3617469157002423654450659 := by
  unfold tailWord_7044996
  simp only [CollatzResearch.WordTrace]
  refine ⟨128476056792595078185549421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 171301409056793437580732561 128476056792595078185549421)
  ·
    refine ⟨48178521297223154319581033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 128476056792595078185549421 48178521297223154319581033)
    ·
      refine ⟨36133890972917365739685775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48178521297223154319581033 36133890972917365739685775)
      ·
        refine ⟨54200836459376048609528663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36133890972917365739685775 54200836459376048609528663)
        ·
          refine ⟨81301254689064072914292995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54200836459376048609528663 81301254689064072914292995)
          ·
            refine ⟨121951882033596109371439493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81301254689064072914292995 121951882033596109371439493)
            ·
              refine ⟨22865977881299270507144905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 121951882033596109371439493 22865977881299270507144905)
              ·
                refine ⟨17149483410974452880358679, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22865977881299270507144905 17149483410974452880358679)
                ·
                  refine ⟨25724225116461679320538019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17149483410974452880358679 25724225116461679320538019)
                  ·
                    refine ⟨38586337674692518980807029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 25724225116461679320538019 38586337674692518980807029)
                    ·
                      refine ⟨3617469157002423654450659, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 38586337674692518980807029 3617469157002423654450659)
                      ·
                        rfl

theorem cell23_7044996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 4, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 4, 2, 1, 1, 5].length) (baseStart_7044996 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7044996 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7044996 prefixEnd_7044996 := by exact prefixLift 7044996
  have htrace : WordTrace (prefixWord ++ tailWord_7044996) baseStart_7044996 baseEnd_7044996 := by
    simpa [prefixWord, tailWord_7044996, baseEnd_7044996] using wordTrace_append hprefix tailTrace_7044996
  have hstable : (prefixWord ++ tailWord_7044996).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7044996).length < 2 ^ (prefixWord ++ tailWord_7044996).sum := by decide
  have hdescent : baseEnd_7044996 < baseStart_7044996 := by decide
  rcases family_descends (prefixWord ++ tailWord_7044996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7045010 : List Nat := [3, 2, 3, 2, 1, 1, 3, 2, 1, 1, 4]
def baseStart_7045010 : Nat := 118140960795 + 7045010 * 2 ^ 59
def prefixEnd_7045010 : Nat := 4983230072969 + 3 ^ 40 * 7045010 * 2
def baseEnd_7045010 : Nat := 3617476345731586599675595

theorem tailTrace_7045010 : CollatzResearch.WordTrace tailWord_7045010 prefixEnd_7045010 3617476345731586599675595 := by
  unfold tailWord_7045010
  simp only [CollatzResearch.WordTrace]
  refine ⟨64238156051784859190527121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 171301749471426291174738989 64238156051784859190527121)
  ·
    refine ⟨48178617038838644392895341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64238156051784859190527121 48178617038838644392895341)
    ·
      refine ⟨18066981389564491647335753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 48178617038838644392895341 18066981389564491647335753)
      ·
        refine ⟨13550236042173368735501815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18066981389564491647335753 13550236042173368735501815)
        ·
          refine ⟨20325354063260053103252723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13550236042173368735501815 20325354063260053103252723)
          ·
            refine ⟨30488031094890079654879085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20325354063260053103252723 30488031094890079654879085)
            ·
              refine ⟨11433011660583779870579657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30488031094890079654879085 11433011660583779870579657)
              ·
                refine ⟨8574758745437834902934743, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11433011660583779870579657 8574758745437834902934743)
                ·
                  refine ⟨12862138118156752354402115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8574758745437834902934743 12862138118156752354402115)
                  ·
                    refine ⟨19293207177235128531603173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12862138118156752354402115 19293207177235128531603173)
                    ·
                      refine ⟨3617476345731586599675595, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19293207177235128531603173 3617476345731586599675595)
                      ·
                        rfl

theorem cell23_7045010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 1, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 1, 3, 2, 1, 1, 4].length) (baseStart_7045010 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7045010 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7045010 prefixEnd_7045010 := by exact prefixLift 7045010
  have htrace : WordTrace (prefixWord ++ tailWord_7045010) baseStart_7045010 baseEnd_7045010 := by
    simpa [prefixWord, tailWord_7045010, baseEnd_7045010] using wordTrace_append hprefix tailTrace_7045010
  have hstable : (prefixWord ++ tailWord_7045010).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7045010).length < 2 ^ (prefixWord ++ tailWord_7045010).sum := by decide
  have hdescent : baseEnd_7045010 < baseStart_7045010 := by decide
  rcases family_descends (prefixWord ++ tailWord_7045010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7045023 : List Nat := [1, 1, 2, 5, 3, 1, 1, 2, 1, 2, 4]
def baseStart_7045023 : Nat := 118140960795 + 7045023 * 2 ^ 59
def prefixEnd_7045023 : Nat := 4983230072969 + 3 ^ 40 * 7045023 * 2
def baseEnd_7045023 : Nat := 3617483020980095048813035

theorem tailTrace_7045023 : CollatzResearch.WordTrace tailWord_7045023 prefixEnd_7045023 3617483020980095048813035 := by
  unfold tailWord_7045023
  simp only [CollatzResearch.WordTrace]
  refine ⟨256953098356092339982331723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171302065570728226654887815 256953098356092339982331723)
  ·
    refine ⟨385429647534138509973497585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 256953098356092339982331723 385429647534138509973497585)
    ·
      refine ⟨289072235650603882480123189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 385429647534138509973497585 289072235650603882480123189)
      ·
        refine ⟨27100522092244113982511549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 289072235650603882480123189 27100522092244113982511549)
        ·
          refine ⟨10162695784591542743441831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27100522092244113982511549 10162695784591542743441831)
          ·
            refine ⟨15244043676887314115162747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10162695784591542743441831 15244043676887314115162747)
            ·
              refine ⟨22866065515330971172744121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15244043676887314115162747 22866065515330971172744121)
              ·
                refine ⟨17149549136498228379558091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22866065515330971172744121 17149549136498228379558091)
                ·
                  refine ⟨25724323704747342569337137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17149549136498228379558091 25724323704747342569337137)
                  ·
                    refine ⟨19293242778560506927002853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25724323704747342569337137 19293242778560506927002853)
                    ·
                      refine ⟨3617483020980095048813035, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19293242778560506927002853 3617483020980095048813035)
                      ·
                        rfl

theorem cell23_7045023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 3, 1, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 3, 1, 1, 2, 1, 2, 4].length) (baseStart_7045023 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7045023 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7045023 prefixEnd_7045023 := by exact prefixLift 7045023
  have htrace : WordTrace (prefixWord ++ tailWord_7045023) baseStart_7045023 baseEnd_7045023 := by
    simpa [prefixWord, tailWord_7045023, baseEnd_7045023] using wordTrace_append hprefix tailTrace_7045023
  have hstable : (prefixWord ++ tailWord_7045023).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7045023).length < 2 ^ (prefixWord ++ tailWord_7045023).sum := by decide
  have hdescent : baseEnd_7045023 < baseStart_7045023 := by decide
  rcases family_descends (prefixWord ++ tailWord_7045023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7045029 : List Nat := [1, 3, 1, 2, 1, 1, 1, 2, 4, 7]
def baseStart_7045029 : Nat := 118140960795 + 7045029 * 2 ^ 59
def prefixEnd_7045029 : Nat := 4983230072969 + 3 ^ 40 * 7045029 * 2
def baseEnd_7045029 : Nat := 1205828700621340675112669

theorem tailTrace_7045029 : CollatzResearch.WordTrace tailWord_7045029 prefixEnd_7045029 1205828700621340675112669 := by
  unfold tailWord_7045029
  simp only [CollatzResearch.WordTrace]
  refine ⟨256953317194070603007050141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171302211462713735338033427 256953317194070603007050141)
  ·
    refine ⟨96357493947776476127643803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 256953317194070603007050141 96357493947776476127643803)
    ·
      refine ⟨144536240921664714191465705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96357493947776476127643803 144536240921664714191465705)
      ·
        refine ⟨108402180691248535643599279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 144536240921664714191465705 108402180691248535643599279)
        ·
          refine ⟨162603271036872803465398919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 108402180691248535643599279 162603271036872803465398919)
          ·
            refine ⟨243904906555309205198098379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 162603271036872803465398919 243904906555309205198098379)
            ·
              refine ⟨365857359832963807797147569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 243904906555309205198098379 365857359832963807797147569)
              ·
                refine ⟨274393019874722855847860677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 365857359832963807797147569 274393019874722855847860677)
                ·
                  refine ⟨51448691226510535471473877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 274393019874722855847860677 51448691226510535471473877)
                  ·
                    refine ⟨1205828700621340675112669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 51448691226510535471473877 1205828700621340675112669)
                    ·
                      rfl

theorem cell23_7045029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 1, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 1, 2, 4, 7].length) (baseStart_7045029 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7045029 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7045029 prefixEnd_7045029 := by exact prefixLift 7045029
  have htrace : WordTrace (prefixWord ++ tailWord_7045029) baseStart_7045029 baseEnd_7045029 := by
    simpa [prefixWord, tailWord_7045029, baseEnd_7045029] using wordTrace_append hprefix tailTrace_7045029
  have hstable : (prefixWord ++ tailWord_7045029).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7045029).length < 2 ^ (prefixWord ++ tailWord_7045029).sum := by decide
  have hdescent : baseEnd_7045029 < baseStart_7045029 := by decide
  rcases family_descends (prefixWord ++ tailWord_7045029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7045070 : List Nat := [4, 1, 1, 1, 2, 2, 2, 4, 1, 3, 2]
def baseStart_7045070 : Nat := 118140960795 + 7045070 * 2 ^ 59
def prefixEnd_7045070 : Nat := 4983230072969 + 3 ^ 40 * 7045070 * 2
def baseEnd_7045070 : Nat := 3617507154570856364925319

theorem tailTrace_7045070 : CollatzResearch.WordTrace tailWord_7045070 prefixEnd_7045070 3617507154570856364925319 := by
  unfold tailWord_7045070
  simp only [CollatzResearch.WordTrace]
  refine ⟨32119351573365258376161583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 171303208391281378006195109 32119351573365258376161583)
  ·
    refine ⟨48179027360047887564242375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32119351573365258376161583 48179027360047887564242375)
    ·
      refine ⟨72268541040071831346363563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48179027360047887564242375 72268541040071831346363563)
      ·
        refine ⟨108402811560107747019545345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72268541040071831346363563 108402811560107747019545345)
        ·
          refine ⟨81302108670080810264659009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 108402811560107747019545345 81302108670080810264659009)
          ·
            refine ⟨60976581502560607698494257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 81302108670080810264659009 60976581502560607698494257)
            ·
              refine ⟨45732436126920455773870693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 60976581502560607698494257 45732436126920455773870693)
              ·
                refine ⟨8574831773797585457600755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 45732436126920455773870693 8574831773797585457600755)
                ·
                  refine ⟨12862247660696378186401133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8574831773797585457600755 12862247660696378186401133)
                  ·
                    refine ⟨4823342872761141819900425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12862247660696378186401133 4823342872761141819900425)
                    ·
                      refine ⟨3617507154570856364925319, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4823342872761141819900425 3617507154570856364925319)
                      ·
                        rfl

theorem cell23_7045070_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 2, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 2, 4, 1, 3, 2].length) (baseStart_7045070 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7045070 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7045070 prefixEnd_7045070 := by exact prefixLift 7045070
  have htrace : WordTrace (prefixWord ++ tailWord_7045070) baseStart_7045070 baseEnd_7045070 := by
    simpa [prefixWord, tailWord_7045070, baseEnd_7045070] using wordTrace_append hprefix tailTrace_7045070
  have hstable : (prefixWord ++ tailWord_7045070).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7045070).length < 2 ^ (prefixWord ++ tailWord_7045070).sum := by decide
  have hdescent : baseEnd_7045070 < baseStart_7045070 := by decide
  rcases family_descends (prefixWord ++ tailWord_7045070) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7045076 : List Nat := [2, 4, 1, 2, 1, 1, 1, 2, 1, 8]
def baseStart_7045076 : Nat := 118140960795 + 7045076 * 2 ^ 59
def prefixEnd_7045076 : Nat := 4983230072969 + 3 ^ 40 * 7045076 * 2
def baseEnd_7045076 : Nat := 1205836745151594447150097

theorem tailTrace_7045076 : CollatzResearch.WordTrace tailWord_7045076 prefixEnd_7045076 1205836745151594447150097 := by
  unfold tailWord_7045076
  simp only [CollatzResearch.WordTrace]
  refine ⟨128477515712450165017005541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 171303354283266886689340721 128477515712450165017005541)
  ·
    refine ⟨24089534196084405940688539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 128477515712450165017005541 24089534196084405940688539)
    ·
      refine ⟨36134301294126608911032809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24089534196084405940688539 36134301294126608911032809)
      ·
        refine ⟨27100725970594956683274607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36134301294126608911032809 27100725970594956683274607)
        ·
          refine ⟨40651088955892435024911911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27100725970594956683274607 40651088955892435024911911)
          ·
            refine ⟨60976633433838652537367867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40651088955892435024911911 60976633433838652537367867)
            ·
              refine ⟨91464950150757978806051801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60976633433838652537367867 91464950150757978806051801)
              ·
                refine ⟨68598712613068484104538851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 91464950150757978806051801 68598712613068484104538851)
                ·
                  refine ⟨102898068919602726156808277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 68598712613068484104538851 102898068919602726156808277)
                  ·
                    refine ⟨1205836745151594447150097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 102898068919602726156808277 1205836745151594447150097)
                    ·
                      rfl

theorem cell23_7045076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 1, 2, 1, 8].length) (baseStart_7045076 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7045076 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7045076 prefixEnd_7045076 := by exact prefixLift 7045076
  have htrace : WordTrace (prefixWord ++ tailWord_7045076) baseStart_7045076 baseEnd_7045076 := by
    simpa [prefixWord, tailWord_7045076, baseEnd_7045076] using wordTrace_append hprefix tailTrace_7045076
  have hstable : (prefixWord ++ tailWord_7045076).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7045076).length < 2 ^ (prefixWord ++ tailWord_7045076).sum := by decide
  have hdescent : baseEnd_7045076 < baseStart_7045076 := by decide
  rcases family_descends (prefixWord ++ tailWord_7045076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7045087 : List Nat := [1, 1, 2, 3, 4, 1, 4, 1, 1, 3, 2]
def baseStart_7045087 : Nat := 118140960795 + 7045087 * 2 ^ 59
def prefixEnd_7045087 : Nat := 4983230072969 + 3 ^ 40 * 7045087 * 2
def baseEnd_7045087 : Nat := 3617515883741982798412741

theorem tailTrace_7045087 : CollatzResearch.WordTrace tailWord_7045087 prefixEnd_7045087 3617515883741982798412741 := by
  unfold tailWord_7045087
  simp only [CollatzResearch.WordTrace]
  refine ⟨256955432627860478912661515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171303621751906985941774343 256955432627860478912661515)
  ·
    refine ⟨385433148941790718368992273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 256955432627860478912661515 385433148941790718368992273)
    ·
      refine ⟨289074861706343038776744205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 385433148941790718368992273 289074861706343038776744205)
      ·
        refine ⟨108403073139878639541279077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 289074861706343038776744205 108403073139878639541279077)
        ·
          refine ⟨20325576213727244913989827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 108403073139878639541279077 20325576213727244913989827)
          ·
            refine ⟨30488364320590867370984741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20325576213727244913989827 30488364320590867370984741)
            ·
              refine ⟨5716568310110787632059639, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 30488364320590867370984741 5716568310110787632059639)
              ·
                refine ⟨8574852465166181448089459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5716568310110787632059639 8574852465166181448089459)
                ·
                  refine ⟨12862278697749272172134189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8574852465166181448089459 12862278697749272172134189)
                  ·
                    refine ⟨4823354511655977064550321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12862278697749272172134189 4823354511655977064550321)
                    ·
                      refine ⟨3617515883741982798412741, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4823354511655977064550321 3617515883741982798412741)
                      ·
                        rfl

theorem cell23_7045087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 1, 4, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 1, 4, 1, 1, 3, 2].length) (baseStart_7045087 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7045087 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7045087 prefixEnd_7045087 := by exact prefixLift 7045087
  have htrace : WordTrace (prefixWord ++ tailWord_7045087) baseStart_7045087 baseEnd_7045087 := by
    simpa [prefixWord, tailWord_7045087, baseEnd_7045087] using wordTrace_append hprefix tailTrace_7045087
  have hstable : (prefixWord ++ tailWord_7045087).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7045087).length < 2 ^ (prefixWord ++ tailWord_7045087).sum := by decide
  have hdescent : baseEnd_7045087 < baseStart_7045087 := by decide
  rcases family_descends (prefixWord ++ tailWord_7045087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7045183 : List Nat := [1, 1, 2, 2, 3, 1, 2, 4, 3, 4]
def baseStart_7045183 : Nat := 118140960795 + 7045183 * 2 ^ 59
def prefixEnd_7045183 : Nat := 4983230072969 + 3 ^ 40 * 7045183 * 2
def baseEnd_7045183 : Nat := 1205855059294938140937433

theorem tailTrace_7045183 : CollatzResearch.WordTrace tailWord_7045183 prefixEnd_7045183 1205855059294938140937433 := by
  unfold tailWord_7045183
  simp only [CollatzResearch.WordTrace]
  refine ⟨256958934035512687308156203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171305956023675124872104135 256958934035512687308156203)
  ·
    refine ⟨385438401053269030962234305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 256958934035512687308156203 385438401053269030962234305)
    ·
      refine ⟨289078800789951773221675729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 385438401053269030962234305 289078800789951773221675729)
      ·
        refine ⟨216809100592463829916256797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 289078800789951773221675729 216809100592463829916256797)
        ·
          refine ⟨81303412722173936218596299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 216809100592463829916256797 81303412722173936218596299)
          ·
            refine ⟨121955119083260904327894449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81303412722173936218596299 121955119083260904327894449)
            ·
              refine ⟨91466339312445678245920837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 121955119083260904327894449 91466339312445678245920837)
              ·
                refine ⟨17149938621083564671110157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 91466339312445678245920837 17149938621083564671110157)
                ·
                  refine ⟨6431226982906336751666309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17149938621083564671110157 6431226982906336751666309)
                  ·
                    refine ⟨1205855059294938140937433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6431226982906336751666309 1205855059294938140937433)
                    ·
                      rfl

theorem cell23_7045183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 2, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 2, 4, 3, 4].length) (baseStart_7045183 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7045183 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7045183 prefixEnd_7045183 := by exact prefixLift 7045183
  have htrace : WordTrace (prefixWord ++ tailWord_7045183) baseStart_7045183 baseEnd_7045183 := by
    simpa [prefixWord, tailWord_7045183, baseEnd_7045183] using wordTrace_append hprefix tailTrace_7045183
  have hstable : (prefixWord ++ tailWord_7045183).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7045183).length < 2 ^ (prefixWord ++ tailWord_7045183).sum := by decide
  have hdescent : baseEnd_7045183 < baseStart_7045183 := by decide
  rcases family_descends (prefixWord ++ tailWord_7045183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7045196 : List Nat := [2, 2, 1, 3, 1, 1, 2, 1, 10]
def baseStart_7045196 : Nat := 118140960795 + 7045196 * 2 ^ 59
def prefixEnd_7045196 : Nat := 4983230072969 + 3 ^ 40 * 7045196 * 2
def baseEnd_7045196 : Nat := 401952428125924763549971

theorem tailTrace_7045196 : CollatzResearch.WordTrace tailWord_7045196 prefixEnd_7045196 401952428125924763549971 := by
  unfold tailWord_7045196
  simp only [CollatzResearch.WordTrace]
  refine ⟨128479704092232795264189721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 171306272122977060352252961 128479704092232795264189721)
  ·
    refine ⟨96359778069174596448142291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 128479704092232795264189721 96359778069174596448142291)
    ·
      refine ⟨144539667103761894672213437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96359778069174596448142291 144539667103761894672213437)
      ·
        refine ⟨54202375163910710502080039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 144539667103761894672213437 54202375163910710502080039)
        ·
          refine ⟨81303562745866065753120059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54202375163910710502080039 81303562745866065753120059)
          ·
            refine ⟨121955344118799098629680089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81303562745866065753120059 121955344118799098629680089)
            ·
              refine ⟨91466508089099323972260067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 121955344118799098629680089 91466508089099323972260067)
              ·
                refine ⟨137199762133648985958390101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 91466508089099323972260067 137199762133648985958390101)
                ·
                  refine ⟨401952428125924763549971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 137199762133648985958390101 401952428125924763549971)
                  ·
                    rfl

theorem cell23_7045196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 2, 1, 10].length) (baseStart_7045196 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7045196 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7045196 prefixEnd_7045196 := by exact prefixLift 7045196
  have htrace : WordTrace (prefixWord ++ tailWord_7045196) baseStart_7045196 baseEnd_7045196 := by
    simpa [prefixWord, tailWord_7045196, baseEnd_7045196] using wordTrace_append hprefix tailTrace_7045196
  have hstable : (prefixWord ++ tailWord_7045196).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7045196).length < 2 ^ (prefixWord ++ tailWord_7045196).sum := by decide
  have hdescent : baseEnd_7045196 < baseStart_7045196 := by decide
  rcases family_descends (prefixWord ++ tailWord_7045196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7045274 : List Nat := [3, 1, 1, 5, 2, 1, 2, 1, 3, 1, 3]
def baseStart_7045274 : Nat := 118140960795 + 7045274 * 2 ^ 59
def prefixEnd_7045274 : Nat := 4983230072969 + 3 ^ 40 * 7045274 * 2
def baseEnd_7045274 : Nat := 3617611904624373566774381

theorem tailTrace_7045274 : CollatzResearch.WordTrace tailWord_7045274 prefixEnd_7045274 3617611904624373566774381 := by
  unfold tailWord_7045274
  simp only [CollatzResearch.WordTrace]
  refine ⟨64240563269545752462429719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 171308168718788673233145917 64240563269545752462429719)
  ·
    refine ⟨96360844904318628693644579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64240563269545752462429719 96360844904318628693644579)
    ·
      refine ⟨144541267356477943040466869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96360844904318628693644579 144541267356477943040466869)
      ·
        refine ⟨13550743814669807160043769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 144541267356477943040466869 13550743814669807160043769)
        ·
          refine ⟨10163057861002355370032827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13550743814669807160043769 10163057861002355370032827)
          ·
            refine ⟨15244586791503533055049241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10163057861002355370032827 15244586791503533055049241)
            ·
              refine ⟨11433440093627649791286931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15244586791503533055049241 11433440093627649791286931)
              ·
                refine ⟨17150160140441474686930397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11433440093627649791286931 17150160140441474686930397)
                ·
                  refine ⟨6431310052665553007598899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17150160140441474686930397 6431310052665553007598899)
                  ·
                    refine ⟨9646965078998329511398349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6431310052665553007598899 9646965078998329511398349)
                    ·
                      refine ⟨3617611904624373566774381, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9646965078998329511398349 3617611904624373566774381)
                      ·
                        rfl

theorem cell23_7045274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 2, 1, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 2, 1, 2, 1, 3, 1, 3].length) (baseStart_7045274 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7045274 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7045274 prefixEnd_7045274 := by exact prefixLift 7045274
  have htrace : WordTrace (prefixWord ++ tailWord_7045274) baseStart_7045274 baseEnd_7045274 := by
    simpa [prefixWord, tailWord_7045274, baseEnd_7045274] using wordTrace_append hprefix tailTrace_7045274
  have hstable : (prefixWord ++ tailWord_7045274).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7045274).length < 2 ^ (prefixWord ++ tailWord_7045274).sum := by decide
  have hdescent : baseEnd_7045274 < baseStart_7045274 := by decide
  rcases family_descends (prefixWord ++ tailWord_7045274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7045303 : List Nat := [1, 1, 3, 1, 4, 3, 1, 9]
def baseStart_7045303 : Nat := 118140960795 + 7045303 * 2 ^ 59
def prefixEnd_7045303 : Nat := 4983230072969 + 3 ^ 40 * 7045303 * 2
def baseEnd_7045303 : Nat := 133986177613457553826361

theorem tailTrace_7045303 : CollatzResearch.WordTrace tailWord_7045303 prefixEnd_7045303 133986177613457553826361 := by
  unfold tailWord_7045303
  simp only [CollatzResearch.WordTrace]
  refine ⟨256963310795077947802524563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171308873863385298535016375 256963310795077947802524563)
  ·
    refine ⟨385444966192616921703786845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 256963310795077947802524563 385444966192616921703786845)
    ·
      refine ⟨144541862322231345638920067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 385444966192616921703786845 144541862322231345638920067)
      ·
        refine ⟨216812793483347018458380101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 144541862322231345638920067 216812793483347018458380101)
        ·
          refine ⟨40652398778127565960946269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 216812793483347018458380101 40652398778127565960946269)
          ·
            refine ⟨15244649541797837235354851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40652398778127565960946269 15244649541797837235354851)
            ·
              refine ⟨22866974312696755853032277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15244649541797837235354851 22866974312696755853032277)
              ·
                refine ⟨133986177613457553826361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 22866974312696755853032277 133986177613457553826361)
                ·
                  rfl

theorem cell23_7045303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 3, 1, 9].length) (baseStart_7045303 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7045303 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7045303 prefixEnd_7045303 := by exact prefixLift 7045303
  have htrace : WordTrace (prefixWord ++ tailWord_7045303) baseStart_7045303 baseEnd_7045303 := by
    simpa [prefixWord, tailWord_7045303, baseEnd_7045303] using wordTrace_append hprefix tailTrace_7045303
  have hstable : (prefixWord ++ tailWord_7045303).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7045303).length < 2 ^ (prefixWord ++ tailWord_7045303).sum := by decide
  have hdescent : baseEnd_7045303 < baseStart_7045303 := by decide
  rcases family_descends (prefixWord ++ tailWord_7045303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7045308 : List Nat := [2, 2, 2, 3, 4, 1, 1, 3, 1, 1, 3]
def baseStart_7045308 : Nat := 118140960795 + 7045308 * 2 ^ 59
def prefixEnd_7045308 : Nat := 4983230072969 + 3 ^ 40 * 7045308 * 2
def baseEnd_7045308 : Nat := 3617629362966626433749225

theorem tailTrace_7045308 : CollatzResearch.WordTrace tailWord_7045308 prefixEnd_7045308 3617629362966626433749225 := by
  unfold tailWord_7045308
  simp only [CollatzResearch.WordTrace]
  refine ⟨128481746580029916828228289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 171308995440039889104304385 128481746580029916828228289)
  ·
    refine ⟨96361309935022437621171217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 128481746580029916828228289 96361309935022437621171217)
    ·
      refine ⟨72270982451266828215878413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 96361309935022437621171217 72270982451266828215878413)
      ·
        refine ⟨27101618419225060580954405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 72270982451266828215878413 27101618419225060580954405)
        ·
          refine ⟨5081553453604698858928951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 27101618419225060580954405 5081553453604698858928951)
          ·
            refine ⟨7622330180407048288393427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5081553453604698858928951 7622330180407048288393427)
            ·
              refine ⟨11433495270610572432590141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7622330180407048288393427 11433495270610572432590141)
              ·
                refine ⟨4287560726478964662221303, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11433495270610572432590141 4287560726478964662221303)
                ·
                  refine ⟨6431341089718446993331955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4287560726478964662221303 6431341089718446993331955)
                  ·
                    refine ⟨9647011634577670489997933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6431341089718446993331955 9647011634577670489997933)
                    ·
                      refine ⟨3617629362966626433749225, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9647011634577670489997933 3617629362966626433749225)
                      ·
                        rfl

theorem cell23_7045308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 4, 1, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 4, 1, 1, 3, 1, 1, 3].length) (baseStart_7045308 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7045308 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7045308 prefixEnd_7045308 := by exact prefixLift 7045308
  have htrace : WordTrace (prefixWord ++ tailWord_7045308) baseStart_7045308 baseEnd_7045308 := by
    simpa [prefixWord, tailWord_7045308, baseEnd_7045308] using wordTrace_append hprefix tailTrace_7045308
  have hstable : (prefixWord ++ tailWord_7045308).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7045308).length < 2 ^ (prefixWord ++ tailWord_7045308).sum := by decide
  have hdescent : baseEnd_7045308 < baseStart_7045308 := by decide
  rcases family_descends (prefixWord ++ tailWord_7045308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7045341 : List Nat := [1, 4, 3, 2, 1, 3, 2, 1, 2, 4]
def baseStart_7045341 : Nat := 118140960795 + 7045341 * 2 ^ 59
def prefixEnd_7045341 : Nat := 4983230072969 + 3 ^ 40 * 7045341 * 2
def baseEnd_7045341 : Nat := 1205882102609408268212191

theorem tailTrace_7045341 : CollatzResearch.WordTrace tailWord_7045341 prefixEnd_7045341 1205882102609408268212191 := by
  unfold tailWord_7045341
  simp only [CollatzResearch.WordTrace]
  refine ⟨256964696768940280292407877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171309797845960186861605251 256964696768940280292407877)
  ·
    refine ⟨48180880644176302554826477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 256964696768940280292407877 48180880644176302554826477)
    ·
      refine ⟨18067830241566113458059929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 48180880644176302554826477 18067830241566113458059929)
      ·
        refine ⟨13550872681174585093544947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18067830241566113458059929 13550872681174585093544947)
        ·
          refine ⟨20326309021761877640317421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13550872681174585093544947 20326309021761877640317421)
          ·
            refine ⟨7622365883160704115119033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20326309021761877640317421 7622365883160704115119033)
            ·
              refine ⟨5716774412370528086339275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7622365883160704115119033 5716774412370528086339275)
              ·
                refine ⟨8575161618555792129508913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5716774412370528086339275 8575161618555792129508913)
                ·
                  refine ⟨6431371213916844097131685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8575161618555792129508913 6431371213916844097131685)
                  ·
                    refine ⟨1205882102609408268212191, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6431371213916844097131685 1205882102609408268212191)
                    ·
                      rfl

theorem cell23_7045341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 3, 2, 1, 2, 4].length) (baseStart_7045341 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7045341 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7045341 prefixEnd_7045341 := by exact prefixLift 7045341
  have htrace : WordTrace (prefixWord ++ tailWord_7045341) baseStart_7045341 baseEnd_7045341 := by
    simpa [prefixWord, tailWord_7045341, baseEnd_7045341] using wordTrace_append hprefix tailTrace_7045341
  have hstable : (prefixWord ++ tailWord_7045341).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7045341).length < 2 ^ (prefixWord ++ tailWord_7045341).sum := by decide
  have hdescent : baseEnd_7045341 < baseStart_7045341 := by decide
  rcases family_descends (prefixWord ++ tailWord_7045341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7045353 : List Nat := [1, 2, 1, 1, 1, 2, 2, 4, 2, 3, 4]
def baseStart_7045353 : Nat := 118140960795 + 7045353 * 2 ^ 59
def prefixEnd_7045353 : Nat := 4983230072969 + 3 ^ 40 * 7045353 * 2
def baseEnd_7045353 : Nat := 3617652469596078757686517

theorem tailTrace_7045353 : CollatzResearch.WordTrace tailWord_7045353 prefixEnd_7045353 3617652469596078757686517 := by
  unfold tailWord_7045353
  simp only [CollatzResearch.WordTrace]
  refine ⟨256965134444896806341844713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171310089629931204227896475 256965134444896806341844713)
  ·
    refine ⟨192723850833672604756383535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 256965134444896806341844713 192723850833672604756383535)
    ·
      refine ⟨289085776250508907134575303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 192723850833672604756383535 289085776250508907134575303)
      ·
        refine ⟨433628664375763360701862955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 289085776250508907134575303 433628664375763360701862955)
        ·
          refine ⟨650442996563645041052794433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 433628664375763360701862955 650442996563645041052794433)
          ·
            refine ⟨487832247422733780789595825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 650442996563645041052794433 487832247422733780789595825)
            ·
              refine ⟨365874185567050335592196869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 487832247422733780789595825 365874185567050335592196869)
              ·
                refine ⟨68601409793821937923536913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 365874185567050335592196869 68601409793821937923536913)
                ·
                  refine ⟨51451057345366453442652685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 68601409793821937923536913 51451057345366453442652685)
                  ·
                    refine ⟨19294146504512420040994757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 51451057345366453442652685 19294146504512420040994757)
                    ·
                      refine ⟨3617652469596078757686517, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19294146504512420040994757 3617652469596078757686517)
                      ·
                        rfl

theorem cell23_7045353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 2, 4, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 2, 4, 2, 3, 4].length) (baseStart_7045353 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7045353 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7045353 prefixEnd_7045353 := by exact prefixLift 7045353
  have htrace : WordTrace (prefixWord ++ tailWord_7045353) baseStart_7045353 baseEnd_7045353 := by
    simpa [prefixWord, tailWord_7045353, baseEnd_7045353] using wordTrace_append hprefix tailTrace_7045353
  have hstable : (prefixWord ++ tailWord_7045353).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7045353).length < 2 ^ (prefixWord ++ tailWord_7045353).sum := by decide
  have hdescent : baseEnd_7045353 < baseStart_7045353 := by decide
  rcases family_descends (prefixWord ++ tailWord_7045353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7045390 : List Nat := [4, 1, 1, 2, 1, 2, 1, 1, 1, 6, 3]
def baseStart_7045390 : Nat := 118140960795 + 7045390 * 2 ^ 59
def prefixEnd_7045390 : Nat := 4983230072969 + 3 ^ 40 * 7045390 * 2
def baseEnd_7045390 : Nat := 3617671468380295112923847

theorem tailTrace_7045390 : CollatzResearch.WordTrace tailWord_7045390 prefixEnd_7045390 3617671468380295112923847 := by
  unfold tailWord_7045390
  simp only [CollatzResearch.WordTrace]
  refine ⟨32120810493220345207617703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 171310989297175174440627749 32120810493220345207617703)
  ·
    refine ⟨48181215739830517811426555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32120810493220345207617703 48181215739830517811426555)
    ·
      refine ⟨72271823609745776717139833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48181215739830517811426555 72271823609745776717139833)
      ·
        refine ⟨54203867707309332537854875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72271823609745776717139833 54203867707309332537854875)
        ·
          refine ⟨81305801560963998806782313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54203867707309332537854875 81305801560963998806782313)
          ·
            refine ⟨60979351170722999105086735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 81305801560963998806782313 60979351170722999105086735)
            ·
              refine ⟨91469026756084498657630103, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60979351170722999105086735 91469026756084498657630103)
              ·
                refine ⟨137203540134126747986445155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 91469026756084498657630103 137203540134126747986445155)
                ·
                  refine ⟨205805310201190121979667733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 137203540134126747986445155 205805310201190121979667733)
                  ·
                    refine ⟨9647123915680786967796925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 205805310201190121979667733 9647123915680786967796925)
                    ·
                      refine ⟨3617671468380295112923847, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9647123915680786967796925 3617671468380295112923847)
                      ·
                        rfl

theorem cell23_7045390_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 1, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 1, 1, 1, 6, 3].length) (baseStart_7045390 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7045390 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7045390 prefixEnd_7045390 := by exact prefixLift 7045390
  have htrace : WordTrace (prefixWord ++ tailWord_7045390) baseStart_7045390 baseEnd_7045390 := by
    simpa [prefixWord, tailWord_7045390, baseEnd_7045390] using wordTrace_append hprefix tailTrace_7045390
  have hstable : (prefixWord ++ tailWord_7045390).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7045390).length < 2 ^ (prefixWord ++ tailWord_7045390).sum := by decide
  have hdescent : baseEnd_7045390 < baseStart_7045390 := by decide
  rcases family_descends (prefixWord ++ tailWord_7045390) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7045400 : List Nat := [2, 1, 2, 3, 1, 2, 3, 1, 2, 2, 4]
def baseStart_7045400 : Nat := 118140960795 + 7045400 * 2 ^ 59
def prefixEnd_7045400 : Nat := 4983230072969 + 3 ^ 40 * 7045400 * 2
def baseEnd_7045400 : Nat := 3617676603186840073798801

theorem tailTrace_7045400 : CollatzResearch.WordTrace tailWord_7045400 prefixEnd_7045400 3617676603186840073798801 := by
  unfold tailWord_7045400
  simp only [CollatzResearch.WordTrace]
  refine ⟨128483424337863266684402827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 171311232450484355579203769 128483424337863266684402827)
  ·
    refine ⟨192725136506794900026604241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128483424337863266684402827 192725136506794900026604241)
    ·
      refine ⟨144543852380096175019953181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 192725136506794900026604241 144543852380096175019953181)
      ·
        refine ⟨54203944642536065632482443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 144543852380096175019953181 54203944642536065632482443)
        ·
          refine ⟨81305916963804098448723665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54203944642536065632482443 81305916963804098448723665)
          ·
            refine ⟨60979437722853073836542749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 81305916963804098448723665 60979437722853073836542749)
            ·
              refine ⟨22867289146069902688703531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 60979437722853073836542749 22867289146069902688703531)
              ·
                refine ⟨34300933719104854033055297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22867289146069902688703531 34300933719104854033055297)
                ·
                  refine ⟨25725700289328640524791473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34300933719104854033055297 25725700289328640524791473)
                  ·
                    refine ⟨19294275216996480393593605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25725700289328640524791473 19294275216996480393593605)
                    ·
                      refine ⟨3617676603186840073798801, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19294275216996480393593605 3617676603186840073798801)
                      ·
                        rfl

theorem cell23_7045400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 3, 1, 2, 2, 4].length) (baseStart_7045400 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7045400 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7045400 prefixEnd_7045400 := by exact prefixLift 7045400
  have htrace : WordTrace (prefixWord ++ tailWord_7045400) baseStart_7045400 baseEnd_7045400 := by
    simpa [prefixWord, tailWord_7045400, baseEnd_7045400] using wordTrace_append hprefix tailTrace_7045400
  have hstable : (prefixWord ++ tailWord_7045400).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7045400).length < 2 ^ (prefixWord ++ tailWord_7045400).sum := by decide
  have hdescent : baseEnd_7045400 < baseStart_7045400 := by decide
  rcases family_descends (prefixWord ++ tailWord_7045400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7045410 : List Nat := [3, 3, 1, 1, 3, 1, 1, 1, 9]
def baseStart_7045410 : Nat := 118140960795 + 7045410 * 2 ^ 59
def prefixEnd_7045410 : Nat := 4983230072969 + 3 ^ 40 * 7045410 * 2
def baseEnd_7045410 : Nat := 401964637554820559408195

theorem tailTrace_7045410 : CollatzResearch.WordTrace tailWord_7045410 prefixEnd_7045410 401964637554820559408195 := by
  unfold tailWord_7045410
  simp only [CollatzResearch.WordTrace]
  refine ⟨64241803351422576269167421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 171311475603793536717779789 64241803351422576269167421)
  ·
    refine ⟨24090676256783466100937783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 64241803351422576269167421 24090676256783466100937783)
    ·
      refine ⟨36136014385175199151406675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24090676256783466100937783 36136014385175199151406675)
      ·
        refine ⟨54204021577762798727110013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36136014385175199151406675 54204021577762798727110013)
        ·
          refine ⟨20326508091661049522666255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 54204021577762798727110013 20326508091661049522666255)
          ·
            refine ⟨30489762137491574283999383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20326508091661049522666255 30489762137491574283999383)
            ·
              refine ⟨45734643206237361425999075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30489762137491574283999383 45734643206237361425999075)
              ·
                refine ⟨68601964809356042138998613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45734643206237361425999075 68601964809356042138998613)
                ·
                  refine ⟨401964637554820559408195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 68601964809356042138998613 401964637554820559408195)
                  ·
                    rfl

theorem cell23_7045410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 1, 1, 1, 9].length) (baseStart_7045410 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7045410 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7045410 prefixEnd_7045410 := by exact prefixLift 7045410
  have htrace : WordTrace (prefixWord ++ tailWord_7045410) baseStart_7045410 baseEnd_7045410 := by
    simpa [prefixWord, tailWord_7045410, baseEnd_7045410] using wordTrace_append hprefix tailTrace_7045410
  have hstable : (prefixWord ++ tailWord_7045410).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7045410).length < 2 ^ (prefixWord ++ tailWord_7045410).sum := by decide
  have hdescent : baseEnd_7045410 < baseStart_7045410 := by decide
  rcases family_descends (prefixWord ++ tailWord_7045410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7045427 : List Nat := [1, 1, 1, 2, 5, 1, 4, 3, 5]
def baseStart_7045427 : Nat := 118140960795 + 7045427 * 2 ^ 59
def prefixEnd_7045427 : Nat := 4983230072969 + 3 ^ 40 * 7045427 * 2
def baseEnd_7045427 : Nat := 401965607462723496462353

theorem tailTrace_7045427 : CollatzResearch.WordTrace tailWord_7045427 prefixEnd_7045427 401965607462723496462353 := by
  unfold tailWord_7045427
  simp only [CollatzResearch.WordTrace]
  refine ⟨256967833446628716980038535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171311888964419144653359023 256967833446628716980038535)
  ·
    refine ⟨385451750169943075470057803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 256967833446628716980038535 385451750169943075470057803)
    ·
      refine ⟨578177625254914613205086705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 385451750169943075470057803 578177625254914613205086705)
      ·
        refine ⟨433633218941185959903815029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 578177625254914613205086705 433633218941185959903815029)
        ·
          refine ⟨40653114275736183740982659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 433633218941185959903815029 40653114275736183740982659)
          ·
            refine ⟨60979671413604275611473989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40653114275736183740982659 60979671413604275611473989)
            ·
              refine ⟨11433688390050801677151373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 60979671413604275611473989 11433688390050801677151373)
              ·
                refine ⟨4287633146269050628931765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11433688390050801677151373 4287633146269050628931765)
                ·
                  refine ⟨401965607462723496462353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4287633146269050628931765 401965607462723496462353)
                  ·
                    rfl

theorem cell23_7045427_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 4, 3, 5].length) (baseStart_7045427 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7045427 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7045427 prefixEnd_7045427 := by exact prefixLift 7045427
  have htrace : WordTrace (prefixWord ++ tailWord_7045427) baseStart_7045427 baseEnd_7045427 := by
    simpa [prefixWord, tailWord_7045427, baseEnd_7045427] using wordTrace_append hprefix tailTrace_7045427
  have hstable : (prefixWord ++ tailWord_7045427).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7045427).length < 2 ^ (prefixWord ++ tailWord_7045427).sum := by decide
  have hdescent : baseEnd_7045427 < baseStart_7045427 := by decide
  rcases family_descends (prefixWord ++ tailWord_7045427) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7045438 : List Nat := [4, 2, 1, 2, 1, 4, 1, 2, 2, 2, 2]
def baseStart_7045438 : Nat := 118140960795 + 7045438 * 2 ^ 59
def prefixEnd_7045438 : Nat := 4983230072969 + 3 ^ 40 * 7045438 * 2
def baseEnd_7045438 : Nat := 3617696115451710925123627

theorem tailTrace_7045438 : CollatzResearch.WordTrace tailWord_7045438 prefixEnd_7045438 3617696115451710925123627 := by
  unfold tailWord_7045438
  simp only [CollatzResearch.WordTrace]
  refine ⟨32121029331198608232336121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 171312156433059243905792645 32121029331198608232336121)
  ·
    refine ⟨24090771998398956174252091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32121029331198608232336121 24090771998398956174252091)
    ·
      refine ⟨36136157997598434261378137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24090771998398956174252091 36136157997598434261378137)
      ·
        refine ⟨27102118498198825696033603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36136157997598434261378137 27102118498198825696033603)
        ·
          refine ⟨40653177747298238544050405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27102118498198825696033603 40653177747298238544050405)
          ·
            refine ⟨7622470827618419727009451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 40653177747298238544050405 7622470827618419727009451)
            ·
              refine ⟨11433706241427629590514177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7622470827618419727009451 11433706241427629590514177)
              ·
                refine ⟨8575279681070722192885633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11433706241427629590514177 8575279681070722192885633)
                ·
                  refine ⟨6431459760803041644664225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8575279681070722192885633 6431459760803041644664225)
                  ·
                    refine ⟨4823594820602281233498169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6431459760803041644664225 4823594820602281233498169)
                    ·
                      refine ⟨3617696115451710925123627, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4823594820602281233498169 3617696115451710925123627)
                      ·
                        rfl

theorem cell23_7045438_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 4, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 4, 1, 2, 2, 2, 2].length) (baseStart_7045438 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7045438 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7045438 prefixEnd_7045438 := by exact prefixLift 7045438
  have htrace : WordTrace (prefixWord ++ tailWord_7045438) baseStart_7045438 baseEnd_7045438 := by
    simpa [prefixWord, tailWord_7045438, baseEnd_7045438] using wordTrace_append hprefix tailTrace_7045438
  have hstable : (prefixWord ++ tailWord_7045438).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7045438).length < 2 ^ (prefixWord ++ tailWord_7045438).sum := by decide
  have hdescent : baseEnd_7045438 < baseStart_7045438 := by decide
  rcases family_descends (prefixWord ++ tailWord_7045438) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7045444 : List Nat := [2, 3, 4, 1, 2, 1, 2, 1, 7]
def baseStart_7045444 : Nat := 118140960795 + 7045444 * 2 ^ 59
def prefixEnd_7045444 : Nat := 4983230072969 + 3 ^ 40 * 7045444 * 2
def baseEnd_7045444 : Nat := 401966577370626433516511

theorem tailTrace_7045444 : CollatzResearch.WordTrace tailWord_7045444 prefixEnd_7045444 401966577370626433516511 := by
  unfold tailWord_7045444
  simp only [CollatzResearch.WordTrace]
  refine ⟨128484226743783564441703693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 171312302325044752588938257 128484226743783564441703693)
  ·
    refine ⟨48181585028918836665638885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 128484226743783564441703693 48181585028918836665638885)
    ·
      refine ⟨9034047192922281874807291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 48181585028918836665638885 9034047192922281874807291)
      ·
        refine ⟨13551070789383422812210937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9034047192922281874807291 13551070789383422812210937)
        ·
          refine ⟨10163303092037567109158203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13551070789383422812210937 10163303092037567109158203)
          ·
            refine ⟨15244954638056350663737305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10163303092037567109158203 15244954638056350663737305)
            ·
              refine ⟨11433715978542262997802979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15244954638056350663737305 11433715978542262997802979)
              ·
                refine ⟨17150573967813394496704469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11433715978542262997802979 17150573967813394496704469)
                ·
                  refine ⟨401966577370626433516511, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17150573967813394496704469 401966577370626433516511)
                  ·
                    rfl

theorem cell23_7045444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 2, 1, 2, 1, 7].length) (baseStart_7045444 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7045444 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7045444 prefixEnd_7045444 := by exact prefixLift 7045444
  have htrace : WordTrace (prefixWord ++ tailWord_7045444) baseStart_7045444 baseEnd_7045444 := by
    simpa [prefixWord, tailWord_7045444, baseEnd_7045444] using wordTrace_append hprefix tailTrace_7045444
  have hstable : (prefixWord ++ tailWord_7045444).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7045444).length < 2 ^ (prefixWord ++ tailWord_7045444).sum := by decide
  have hdescent : baseEnd_7045444 < baseStart_7045444 := by decide
  rcases family_descends (prefixWord ++ tailWord_7045444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7045554 : List Nat := [3, 2, 1, 1, 1, 1, 3, 4, 2, 3, 2]
def baseStart_7045554 : Nat := 118140960795 + 7045554 * 2 ^ 59
def prefixEnd_7045554 : Nat := 4983230072969 + 3 ^ 40 * 7045554 * 2
def baseEnd_7045554 : Nat := 3617755679207632471273093

theorem tailTrace_7045554 : CollatzResearch.WordTrace tailWord_7045554 prefixEnd_7045554 3617755679207632471273093 := by
  unfold tailWord_7045554
  simp only [CollatzResearch.WordTrace]
  refine ⟨64243116379292154417477929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 171314977011445745113274477 64243116379292154417477929)
  ·
    refine ⟨48182337284469115813108447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64243116379292154417477929 48182337284469115813108447)
    ·
      refine ⟨72273505926703673719662671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48182337284469115813108447 72273505926703673719662671)
      ·
        refine ⟨108410258890055510579494007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72273505926703673719662671 108410258890055510579494007)
        ·
          refine ⟨162615388335083265869241011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 108410258890055510579494007 162615388335083265869241011)
          ·
            refine ⟨243923082502624898803861517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 162615388335083265869241011 243923082502624898803861517)
            ·
              refine ⟨91471155938484337051448069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 243923082502624898803861517 91471155938484337051448069)
              ·
                refine ⟨17150841738465813197146513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 91471155938484337051448069 17150841738465813197146513)
                ·
                  refine ⟨12863131303849359897859885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17150841738465813197146513 12863131303849359897859885)
                  ·
                    refine ⟨4823674238943509961697457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12863131303849359897859885 4823674238943509961697457)
                    ·
                      refine ⟨3617755679207632471273093, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4823674238943509961697457 3617755679207632471273093)
                      ·
                        rfl

theorem cell23_7045554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 3, 4, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 3, 4, 2, 3, 2].length) (baseStart_7045554 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7045554 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7045554 prefixEnd_7045554 := by exact prefixLift 7045554
  have htrace : WordTrace (prefixWord ++ tailWord_7045554) baseStart_7045554 baseEnd_7045554 := by
    simpa [prefixWord, tailWord_7045554, baseEnd_7045554] using wordTrace_append hprefix tailTrace_7045554
  have hstable : (prefixWord ++ tailWord_7045554).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7045554).length < 2 ^ (prefixWord ++ tailWord_7045554).sum := by decide
  have hdescent : baseEnd_7045554 < baseStart_7045554 := by decide
  rcases family_descends (prefixWord ++ tailWord_7045554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7045560 : List Nat := [2, 1, 2, 1, 2, 2, 1, 1, 5, 6]
def baseStart_7045560 : Nat := 118140960795 + 7045560 * 2 ^ 59
def prefixEnd_7045560 : Nat := 4983230072969 + 3 ^ 40 * 7045560 * 2
def baseEnd_7045560 : Nat := 1205919586697186482599355

theorem tailTrace_7045560 : CollatzResearch.WordTrace tailWord_7045560 prefixEnd_7045560 1205919586697186482599355 := by
  unfold tailWord_7045560
  simp only [CollatzResearch.WordTrace]
  refine ⟨128486342177573440347315067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 171315122903431253796420089 128486342177573440347315067)
  ·
    refine ⟨192729513266360160520972601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128486342177573440347315067 192729513266360160520972601)
    ·
      refine ⟨144547134949770120390729451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 192729513266360160520972601 144547134949770120390729451)
      ·
        refine ⟨216820702424655180586094177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 144547134949770120390729451 216820702424655180586094177)
        ·
          refine ⟨162615526818491385439570633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 216820702424655180586094177 162615526818491385439570633)
          ·
            refine ⟨121961645113868539079677975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 162615526818491385439570633 121961645113868539079677975)
            ·
              refine ⟨182942467670802808619516963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 121961645113868539079677975 182942467670802808619516963)
              ·
                refine ⟨274413701506204212929275445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 182942467670802808619516963 274413701506204212929275445)
                ·
                  refine ⟨25726284516206644962119573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 274413701506204212929275445 25726284516206644962119573)
                  ·
                    refine ⟨1205919586697186482599355, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25726284516206644962119573 1205919586697186482599355)
                    ·
                      rfl

theorem cell23_7045560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 1, 1, 5, 6].length) (baseStart_7045560 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7045560 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7045560 prefixEnd_7045560 := by exact prefixLift 7045560
  have htrace : WordTrace (prefixWord ++ tailWord_7045560) baseStart_7045560 baseEnd_7045560 := by
    simpa [prefixWord, tailWord_7045560, baseEnd_7045560] using wordTrace_append hprefix tailTrace_7045560
  have hstable : (prefixWord ++ tailWord_7045560).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7045560).length < 2 ^ (prefixWord ++ tailWord_7045560).sum := by decide
  have hdescent : baseEnd_7045560 < baseStart_7045560 := by decide
  rcases family_descends (prefixWord ++ tailWord_7045560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7045567 : List Nat := [1, 1, 2, 2, 2, 1, 1, 1, 4, 6, 2]
def baseStart_7045567 : Nat := 118140960795 + 7045567 * 2 ^ 59
def prefixEnd_7045567 : Nat := 4983230072969 + 3 ^ 40 * 7045567 * 2
def baseEnd_7045567 : Nat := 3617762354456140920410533

theorem tailTrace_7045567 : CollatzResearch.WordTrace tailWord_7045567 prefixEnd_7045567 3617762354456140920410533 := by
  unfold tailWord_7045567
  simp only [CollatzResearch.WordTrace]
  refine ⟨256972939666121520890134955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171315293110747680593423303 256972939666121520890134955)
  ·
    refine ⟨385459409499182281335202433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 256972939666121520890134955 385459409499182281335202433)
    ·
      refine ⟨289094557124386711001401825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 385459409499182281335202433 289094557124386711001401825)
      ·
        refine ⟨216820917843290033251051369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 289094557124386711001401825 216820917843290033251051369)
        ·
          refine ⟨162615688382467524938288527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 216820917843290033251051369 162615688382467524938288527)
          ·
            refine ⟨243923532573701287407432791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 162615688382467524938288527 243923532573701287407432791)
            ·
              refine ⟨365885298860551931111149187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 243923532573701287407432791 365885298860551931111149187)
              ·
                refine ⟨548827948290827896666723781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 365885298860551931111149187 548827948290827896666723781)
                ·
                  refine ⟨102905240304530230625010709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 548827948290827896666723781 102905240304530230625010709)
                  ·
                    refine ⟨4823683139274854560547377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 102905240304530230625010709 4823683139274854560547377)
                    ·
                      refine ⟨3617762354456140920410533, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4823683139274854560547377 3617762354456140920410533)
                      ·
                        rfl

theorem cell23_7045567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 1, 1, 4, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 1, 1, 4, 6, 2].length) (baseStart_7045567 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7045567 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7045567 prefixEnd_7045567 := by exact prefixLift 7045567
  have htrace : WordTrace (prefixWord ++ tailWord_7045567) baseStart_7045567 baseEnd_7045567 := by
    simpa [prefixWord, tailWord_7045567, baseEnd_7045567] using wordTrace_append hprefix tailTrace_7045567
  have hstable : (prefixWord ++ tailWord_7045567).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7045567).length < 2 ^ (prefixWord ++ tailWord_7045567).sum := by decide
  have hdescent : baseEnd_7045567 < baseStart_7045567 := by decide
  rcases family_descends (prefixWord ++ tailWord_7045567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7045588 : List Nat := [2, 4, 1, 2, 2, 3, 1, 1, 2, 3, 2]
def baseStart_7045588 : Nat := 118140960795 + 7045588 * 2 ^ 59
def prefixEnd_7045588 : Nat := 4983230072969 + 3 ^ 40 * 7045588 * 2
def baseEnd_7045588 : Nat := 3617773137549885338247937

theorem tailTrace_7045588 : CollatzResearch.WordTrace tailWord_7045588 prefixEnd_7045588 3617773137549885338247937 := by
  unfold tailWord_7045588
  simp only [CollatzResearch.WordTrace]
  refine ⟨128486852799522720738324709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 171315803732696960984432945 128486852799522720738324709)
  ·
    refine ⟨24091284899910510138435883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 128486852799522720738324709 24091284899910510138435883)
    ·
      refine ⟨36136927349865765207653825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24091284899910510138435883 36136927349865765207653825)
      ·
        refine ⟨27102695512399323905740369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36136927349865765207653825 27102695512399323905740369)
        ·
          refine ⟨20327021634299492929305277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27102695512399323905740369 20327021634299492929305277)
          ·
            refine ⟨7622633112862309848489479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20327021634299492929305277 7622633112862309848489479)
            ·
              refine ⟨11433949669293464772734219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7622633112862309848489479 11433949669293464772734219)
              ·
                refine ⟨17150924503940197159101329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11433949669293464772734219 17150924503940197159101329)
                ·
                  refine ⟨12863193377955147869325997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17150924503940197159101329 12863193377955147869325997)
                  ·
                    refine ⟨4823697516733180450997249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12863193377955147869325997 4823697516733180450997249)
                    ·
                      refine ⟨3617773137549885338247937, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4823697516733180450997249 3617773137549885338247937)
                      ·
                        rfl

theorem cell23_7045588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 3, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 3, 1, 1, 2, 3, 2].length) (baseStart_7045588 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7045588 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7045588 prefixEnd_7045588 := by exact prefixLift 7045588
  have htrace : WordTrace (prefixWord ++ tailWord_7045588) baseStart_7045588 baseEnd_7045588 := by
    simpa [prefixWord, tailWord_7045588, baseEnd_7045588] using wordTrace_append hprefix tailTrace_7045588
  have hstable : (prefixWord ++ tailWord_7045588).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7045588).length < 2 ^ (prefixWord ++ tailWord_7045588).sum := by decide
  have hdescent : baseEnd_7045588 < baseStart_7045588 := by decide
  rcases family_descends (prefixWord ++ tailWord_7045588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7045621 : List Nat := [1, 3, 5, 1, 2, 1, 1, 2, 1, 1, 5]
def baseStart_7045621 : Nat := 118140960795 + 7045621 * 2 ^ 59
def prefixEnd_7045621 : Nat := 4983230072969 + 3 ^ 40 * 7045621 * 2
def baseEnd_7045621 : Nat := 3617790082411483709135285

theorem tailTrace_7045621 : CollatzResearch.WordTrace tailWord_7045621 prefixEnd_7045621 3617790082411483709135285 := by
  unfold tailWord_7045621
  simp only [CollatzResearch.WordTrace]
  refine ⟨256974909207925888112600717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171316606138617258741733811 256974909207925888112600717)
  ·
    refine ⟨96365590952972208042225269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 256974909207925888112600717 96365590952972208042225269)
    ·
      refine ⟨9034274151841144503958619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 96365590952972208042225269 9034274151841144503958619)
      ·
        refine ⟨13551411227761716755937929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9034274151841144503958619 13551411227761716755937929)
        ·
          refine ⟨10163558420821287566953447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13551411227761716755937929 10163558420821287566953447)
          ·
            refine ⟨15245337631231931350430171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10163558420821287566953447 15245337631231931350430171)
            ·
              refine ⟨22868006446847897025645257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15245337631231931350430171 22868006446847897025645257)
              ·
                refine ⟨17151004835135922769233943, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22868006446847897025645257 17151004835135922769233943)
                ·
                  refine ⟨25726507252703884153850915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17151004835135922769233943 25726507252703884153850915)
                  ·
                    refine ⟨38589760879055826230776373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 25726507252703884153850915 38589760879055826230776373)
                    ·
                      refine ⟨3617790082411483709135285, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 38589760879055826230776373 3617790082411483709135285)
                      ·
                        rfl

theorem cell23_7045621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 2, 1, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 2, 1, 1, 2, 1, 1, 5].length) (baseStart_7045621 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7045621 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7045621 prefixEnd_7045621 := by exact prefixLift 7045621
  have htrace : WordTrace (prefixWord ++ tailWord_7045621) baseStart_7045621 baseEnd_7045621 := by
    simpa [prefixWord, tailWord_7045621, baseEnd_7045621] using wordTrace_append hprefix tailTrace_7045621
  have hstable : (prefixWord ++ tailWord_7045621).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7045621).length < 2 ^ (prefixWord ++ tailWord_7045621).sum := by decide
  have hdescent : baseEnd_7045621 < baseStart_7045621 := by decide
  rcases family_descends (prefixWord ++ tailWord_7045621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7045652 : List Nat := [2, 4, 3, 1, 1, 1, 3, 3, 1, 2, 2]
def baseStart_7045652 : Nat := 118140960795 + 7045652 * 2 ^ 59
def prefixEnd_7045652 : Nat := 4983230072969 + 3 ^ 40 * 7045652 * 2
def baseEnd_7045652 : Nat := 3617806000311773087847643

theorem tailTrace_7045652 : CollatzResearch.WordTrace tailWord_7045652 prefixEnd_7045652 3617806000311773087847643 := by
  unfold tailWord_7045652
  simp only [CollatzResearch.WordTrace]
  refine ⟨128488019935406790203489605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 171317359913875720271319473 128488019935406790203489605)
  ·
    refine ⟨24091503737888773163154301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 128488019935406790203489605 24091503737888773163154301)
    ·
      refine ⟨9034313901708289936182863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24091503737888773163154301 9034313901708289936182863)
      ·
        refine ⟨13551470852562434904274295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9034313901708289936182863 13551470852562434904274295)
        ·
          refine ⟨20327206278843652356411443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13551470852562434904274295 20327206278843652356411443)
          ·
            refine ⟨30490809418265478534617165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20327206278843652356411443 30490809418265478534617165)
            ·
              refine ⟨11434053531849554450481437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30490809418265478534617165 11434053531849554450481437)
              ·
                refine ⟨4287770074443582918930539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11434053531849554450481437 4287770074443582918930539)
                ·
                  refine ⟨6431655111665374378395809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4287770074443582918930539 6431655111665374378395809)
                  ·
                    refine ⟨4823741333749030783796857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6431655111665374378395809 4823741333749030783796857)
                    ·
                      refine ⟨3617806000311773087847643, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4823741333749030783796857 3617806000311773087847643)
                      ·
                        rfl

theorem cell23_7045652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 1, 3, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 1, 3, 3, 1, 2, 2].length) (baseStart_7045652 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7045652 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7045652 prefixEnd_7045652 := by exact prefixLift 7045652
  have htrace : WordTrace (prefixWord ++ tailWord_7045652) baseStart_7045652 baseEnd_7045652 := by
    simpa [prefixWord, tailWord_7045652, baseEnd_7045652] using wordTrace_append hprefix tailTrace_7045652
  have hstable : (prefixWord ++ tailWord_7045652).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7045652).length < 2 ^ (prefixWord ++ tailWord_7045652).sum := by decide
  have hdescent : baseEnd_7045652 < baseStart_7045652 := by decide
  rcases family_descends (prefixWord ++ tailWord_7045652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7045687 : List Nat := [1, 1, 3, 1, 2, 3, 2, 1, 1, 4, 4]
def baseStart_7045687 : Nat := 118140960795 + 7045687 * 2 ^ 59
def prefixEnd_7045687 : Nat := 4983230072969 + 3 ^ 40 * 7045687 * 2
def baseEnd_7045687 : Nat := 3617823972134680450909981

theorem tailTrace_7045687 : CollatzResearch.WordTrace tailWord_7045687 prefixEnd_7045687 3617823972134680450909981 := by
  unfold tailWord_7045687
  simp only [CollatzResearch.WordTrace]
  refine ⟨256977316425686781384503315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171318210950457854256335543 256977316425686781384503315)
  ·
    refine ⟨385465974638530172076754973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 256977316425686781384503315 385465974638530172076754973)
    ·
      refine ⟨144549740489448814528783115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 385465974638530172076754973 144549740489448814528783115)
      ·
        refine ⟨216824610734173221793174673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 144549740489448814528783115 216824610734173221793174673)
        ·
          refine ⟨162618458050629916344881005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 216824610734173221793174673 162618458050629916344881005)
          ·
            refine ⟨60981921768986218629330377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 162618458050629916344881005 60981921768986218629330377)
            ·
              refine ⟨45736441326739663971997783, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 60981921768986218629330377 45736441326739663971997783)
              ·
                refine ⟨68604661990109495957996675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45736441326739663971997783 68604661990109495957996675)
                ·
                  refine ⟨102906992985164243936995013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 68604661990109495957996675 102906992985164243936995013)
                  ·
                    refine ⟨19295061184718295738186565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 102906992985164243936995013 19295061184718295738186565)
                    ·
                      refine ⟨3617823972134680450909981, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19295061184718295738186565 3617823972134680450909981)
                      ·
                        rfl

theorem cell23_7045687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 2, 1, 1, 4, 4].length) (baseStart_7045687 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7045687 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7045687 prefixEnd_7045687 := by exact prefixLift 7045687
  have htrace : WordTrace (prefixWord ++ tailWord_7045687) baseStart_7045687 baseEnd_7045687 := by
    simpa [prefixWord, tailWord_7045687, baseEnd_7045687] using wordTrace_append hprefix tailTrace_7045687
  have hstable : (prefixWord ++ tailWord_7045687).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7045687).length < 2 ^ (prefixWord ++ tailWord_7045687).sum := by decide
  have hdescent : baseEnd_7045687 < baseStart_7045687 := by decide
  rcases family_descends (prefixWord ++ tailWord_7045687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7045741 : List Nat := [1, 5, 1, 1, 3, 2, 1, 1, 2, 3, 3]
def baseStart_7045741 : Nat := 118140960795 + 7045741 * 2 ^ 59
def prefixEnd_7045741 : Nat := 4983230072969 + 3 ^ 40 * 7045741 * 2
def baseEnd_7045741 : Nat := 3617851700090023239634733

theorem tailTrace_7045741 : CollatzResearch.WordTrace tailWord_7045741 prefixEnd_7045741 3617851700090023239634733 := by
  unfold tailWord_7045741
  simp only [CollatzResearch.WordTrace]
  refine ⟨256979285967491148606969077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171319523978327432404646051 256979285967491148606969077)
  ·
    refine ⟨24091808059452295181903351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 256979285967491148606969077 24091808059452295181903351)
    ·
      refine ⟨36137712089178442772855027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24091808059452295181903351 36137712089178442772855027)
      ·
        refine ⟨54206568133767664159282541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36137712089178442772855027 54206568133767664159282541)
        ·
          refine ⟨20327463050162874059730953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 54206568133767664159282541 20327463050162874059730953)
          ·
            refine ⟨15245597287622155544798215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20327463050162874059730953 15245597287622155544798215)
            ·
              refine ⟨22868395931433233317197323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15245597287622155544798215 22868395931433233317197323)
              ·
                refine ⟨34302593897149849975795985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22868395931433233317197323 34302593897149849975795985)
                ·
                  refine ⟨25726945422862387481846989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34302593897149849975795985 25726945422862387481846989)
                  ·
                    refine ⟨9647604533573395305692621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25726945422862387481846989 9647604533573395305692621)
                    ·
                      refine ⟨3617851700090023239634733, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9647604533573395305692621 3617851700090023239634733)
                      ·
                        rfl

theorem cell23_7045741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 2, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 2, 1, 1, 2, 3, 3].length) (baseStart_7045741 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7045741 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7045741 prefixEnd_7045741 := by exact prefixLift 7045741
  have htrace : WordTrace (prefixWord ++ tailWord_7045741) baseStart_7045741 baseEnd_7045741 := by
    simpa [prefixWord, tailWord_7045741, baseEnd_7045741] using wordTrace_append hprefix tailTrace_7045741
  have hstable : (prefixWord ++ tailWord_7045741).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7045741).length < 2 ^ (prefixWord ++ tailWord_7045741).sum := by decide
  have hdescent : baseEnd_7045741 < baseStart_7045741 := by decide
  rcases family_descends (prefixWord ++ tailWord_7045741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7045842 : List Nat := [3, 2, 2, 2, 3, 1, 3, 2, 1, 4]
def baseStart_7045842 : Nat := 118140960795 + 7045842 * 2 ^ 59
def prefixEnd_7045842 : Nat := 4983230072969 + 3 ^ 40 * 7045842 * 2
def baseEnd_7045842 : Nat := 1205967853878709114823923

theorem tailTrace_7045842 : CollatzResearch.WordTrace tailWord_7045842 prefixEnd_7045842 1205967853878709114823923 := by
  unfold tailWord_7045842
  simp only [CollatzResearch.WordTrace]
  refine ⟨64245742435031310714098945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 171321979826750161904263853 64245742435031310714098945)
  ·
    refine ⟨48184306826273483035574209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64245742435031310714098945 48184306826273483035574209)
    ·
      refine ⟨36138230119705112276680657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48184306826273483035574209 36138230119705112276680657)
      ·
        refine ⟨27103672589778834207510493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36138230119705112276680657 27103672589778834207510493)
        ·
          refine ⟨10163877221167062827816435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27103672589778834207510493 10163877221167062827816435)
          ·
            refine ⟨15245815831750594241724653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10163877221167062827816435 15245815831750594241724653)
            ·
              refine ⟨5717180936906472840646745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15245815831750594241724653 5717180936906472840646745)
              ·
                refine ⟨4287885702679854630485059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5717180936906472840646745 4287885702679854630485059)
                ·
                  refine ⟨6431828554019781945727589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4287885702679854630485059 6431828554019781945727589)
                  ·
                    refine ⟨1205967853878709114823923, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6431828554019781945727589 1205967853878709114823923)
                    ·
                      rfl

theorem cell23_7045842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 3, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 3, 1, 3, 2, 1, 4].length) (baseStart_7045842 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7045842 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7045842 prefixEnd_7045842 := by exact prefixLift 7045842
  have htrace : WordTrace (prefixWord ++ tailWord_7045842) baseStart_7045842 baseEnd_7045842 := by
    simpa [prefixWord, tailWord_7045842, baseEnd_7045842] using wordTrace_append hprefix tailTrace_7045842
  have hstable : (prefixWord ++ tailWord_7045842).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7045842).length < 2 ^ (prefixWord ++ tailWord_7045842).sum := by decide
  have hdescent : baseEnd_7045842 < baseStart_7045842 := by decide
  rcases family_descends (prefixWord ++ tailWord_7045842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7045848 : List Nat := [2, 1, 2, 2, 3, 2, 3, 1, 3, 1, 3]
def baseStart_7045848 : Nat := 118140960795 + 7045848 * 2 ^ 59
def prefixEnd_7045848 : Nat := 4983230072969 + 3 ^ 40 * 7045848 * 2
def baseEnd_7045848 : Nat := 3617906642520054320996741

theorem tailTrace_7045848 : CollatzResearch.WordTrace tailWord_7045848 prefixEnd_7045848 3617906642520054320996741 := by
  unfold tailWord_7045848
  simp only [CollatzResearch.WordTrace]
  refine ⟨128491594289051752940557099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 171322125718735670587409465 128491594289051752940557099)
  ·
    refine ⟨192737391433577629410835649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128491594289051752940557099 192737391433577629410835649)
    ·
      refine ⟨144553043575183222058126737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 192737391433577629410835649 144553043575183222058126737)
      ·
        refine ⟨108414782681387416543595053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 144553043575183222058126737 108414782681387416543595053)
        ·
          refine ⟨40655543505520281203848145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 108414782681387416543595053 40655543505520281203848145)
          ·
            refine ⟨30491657629140210902886109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40655543505520281203848145 30491657629140210902886109)
            ·
              refine ⟨11434371610927579088582291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30491657629140210902886109 11434371610927579088582291)
              ·
                refine ⟨17151557416391368632873437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11434371610927579088582291 17151557416391368632873437)
                ·
                  refine ⟨6431834031146763237327539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17151557416391368632873437 6431834031146763237327539)
                  ·
                    refine ⟨9647751046720144855991309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6431834031146763237327539 9647751046720144855991309)
                    ·
                      refine ⟨3617906642520054320996741, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9647751046720144855991309 3617906642520054320996741)
                      ·
                        rfl

theorem cell23_7045848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 2, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 2, 3, 1, 3, 1, 3].length) (baseStart_7045848 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7045848 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7045848 prefixEnd_7045848 := by exact prefixLift 7045848
  have htrace : WordTrace (prefixWord ++ tailWord_7045848) baseStart_7045848 baseEnd_7045848 := by
    simpa [prefixWord, tailWord_7045848, baseEnd_7045848] using wordTrace_append hprefix tailTrace_7045848
  have hstable : (prefixWord ++ tailWord_7045848).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7045848).length < 2 ^ (prefixWord ++ tailWord_7045848).sum := by decide
  have hdescent : baseEnd_7045848 < baseStart_7045848 := by decide
  rcases family_descends (prefixWord ++ tailWord_7045848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7045871 : List Nat := [1, 1, 2, 1, 5, 3, 1, 1, 3, 1, 4]
def baseStart_7045871 : Nat := 118140960795 + 7045871 * 2 ^ 59
def prefixEnd_7045871 : Nat := 4983230072969 + 3 ^ 40 * 7045871 * 2
def baseEnd_7045871 : Nat := 3617918452575107731009135

theorem tailTrace_7045871 : CollatzResearch.WordTrace tailWord_7045871 prefixEnd_7045871 3617918452575107731009135 := by
  unfold tailWord_7045871
  simp only [CollatzResearch.WordTrace]
  refine ⟨256984027457020180809201467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171322684971346787206134311 256984027457020180809201467)
  ·
    refine ⟨385476041185530271213802201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 256984027457020180809201467 385476041185530271213802201)
    ·
      refine ⟨289107030889147703410351651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 385476041185530271213802201 289107030889147703410351651)
      ·
        refine ⟨433660546333721555115527477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 289107030889147703410351651 433660546333721555115527477)
        ·
          refine ⟨40655676218786395792080701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 433660546333721555115527477 40655676218786395792080701)
          ·
            refine ⟨15245878582044898422030263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40655676218786395792080701 15245878582044898422030263)
            ·
              refine ⟨22868817873067347633045395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15245878582044898422030263 22868817873067347633045395)
              ·
                refine ⟨34303226809601021449568093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22868817873067347633045395 34303226809601021449568093)
                ·
                  refine ⟨12863710053600383043588035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34303226809601021449568093 12863710053600383043588035)
                  ·
                    refine ⟨19295565080400574565382053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12863710053600383043588035 19295565080400574565382053)
                    ·
                      refine ⟨3617918452575107731009135, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19295565080400574565382053 3617918452575107731009135)
                      ·
                        rfl

theorem cell23_7045871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 3, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 3, 1, 1, 3, 1, 4].length) (baseStart_7045871 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7045871 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7045871 prefixEnd_7045871 := by exact prefixLift 7045871
  have htrace : WordTrace (prefixWord ++ tailWord_7045871) baseStart_7045871 baseEnd_7045871 := by
    simpa [prefixWord, tailWord_7045871, baseEnd_7045871] using wordTrace_append hprefix tailTrace_7045871
  have hstable : (prefixWord ++ tailWord_7045871).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7045871).length < 2 ^ (prefixWord ++ tailWord_7045871).sum := by decide
  have hdescent : baseEnd_7045871 < baseStart_7045871 := by decide
  rcases family_descends (prefixWord ++ tailWord_7045871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7045898 : List Nat := [3, 1, 2, 2, 1, 2, 4, 2, 2, 4]
def baseStart_7045898 : Nat := 118140960795 + 7045898 * 2 ^ 59
def prefixEnd_7045898 : Nat := 4983230072969 + 3 ^ 40 * 7045898 * 2
def baseEnd_7045898 : Nat := 1205977438850926375123837

theorem tailTrace_7045898 : CollatzResearch.WordTrace tailWord_7045898 prefixEnd_7045898 1205977438850926375123837 := by
  unfold tailWord_7045898
  simp only [CollatzResearch.WordTrace]
  refine ⟨64246253056980591105108587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 171323341485281576280289565 64246253056980591105108587)
  ·
    refine ⟨96369379585470886657662881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64246253056980591105108587 96369379585470886657662881)
    ·
      refine ⟨72277034689103164993247161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 96369379585470886657662881 72277034689103164993247161)
      ·
        refine ⟨54207776016827373744935371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72277034689103164993247161 54207776016827373744935371)
        ·
          refine ⟨81311664025241060617403057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54207776016827373744935371 81311664025241060617403057)
          ·
            refine ⟨60983748018930795463052293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 81311664025241060617403057 60983748018930795463052293)
            ·
              refine ⟨11434452753549524149322305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 60983748018930795463052293 11434452753549524149322305)
              ·
                refine ⟨8575839565162143111991729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11434452753549524149322305 8575839565162143111991729)
                ·
                  refine ⟨6431879673871607333993797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8575839565162143111991729 6431879673871607333993797)
                  ·
                    refine ⟨1205977438850926375123837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6431879673871607333993797 1205977438850926375123837)
                    ·
                      rfl

theorem cell23_7045898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 4, 2, 2, 4].length) (baseStart_7045898 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7045898 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7045898 prefixEnd_7045898 := by exact prefixLift 7045898
  have htrace : WordTrace (prefixWord ++ tailWord_7045898) baseStart_7045898 baseEnd_7045898 := by
    simpa [prefixWord, tailWord_7045898, baseEnd_7045898] using wordTrace_append hprefix tailTrace_7045898
  have hstable : (prefixWord ++ tailWord_7045898).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7045898).length < 2 ^ (prefixWord ++ tailWord_7045898).sum := by decide
  have hdescent : baseEnd_7045898 < baseStart_7045898 := by decide
  rcases family_descends (prefixWord ++ tailWord_7045898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7045938 : List Nat := [3, 2, 1, 1, 3, 1, 2, 2, 4, 1, 3]
def baseStart_7045938 : Nat := 118140960795 + 7045938 * 2 ^ 59
def prefixEnd_7045938 : Nat := 4983230072969 + 3 ^ 40 * 7045938 * 2
def baseEnd_7045938 : Nat := 3617952855778958968871327

theorem tailTrace_7045938 : CollatzResearch.WordTrace tailWord_7045938 prefixEnd_7045938 3617952855778958968871327 := by
  unfold tailWord_7045938
  simp only [CollatzResearch.WordTrace]
  refine ⟨64246617786944362812972617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 171324314098518300834593645 64246617786944362812972617)
  ·
    refine ⟨48184963340208272109729463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64246617786944362812972617 48184963340208272109729463)
    ·
      refine ⟨72277445010312408164594195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48184963340208272109729463 72277445010312408164594195)
      ·
        refine ⟨108416167515468612246891293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72277445010312408164594195 108416167515468612246891293)
        ·
          refine ⟨40656062818300729592584235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 108416167515468612246891293 40656062818300729592584235)
          ·
            refine ⟨60984094227451094388876353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40656062818300729592584235 60984094227451094388876353)
            ·
              refine ⟨45738070670588320791657265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 60984094227451094388876353 45738070670588320791657265)
              ·
                refine ⟨34303553002941240593742949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45738070670588320791657265 34303553002941240593742949)
                ·
                  refine ⟨6431916188051482611326803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 34303553002941240593742949 6431916188051482611326803)
                  ·
                    refine ⟨9647874282077223916990205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6431916188051482611326803 9647874282077223916990205)
                    ·
                      refine ⟨3617952855778958968871327, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9647874282077223916990205 3617952855778958968871327)
                      ·
                        rfl

theorem cell23_7045938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 2, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 2, 2, 4, 1, 3].length) (baseStart_7045938 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7045938 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7045938 prefixEnd_7045938 := by exact prefixLift 7045938
  have htrace : WordTrace (prefixWord ++ tailWord_7045938) baseStart_7045938 baseEnd_7045938 := by
    simpa [prefixWord, tailWord_7045938, baseEnd_7045938] using wordTrace_append hprefix tailTrace_7045938
  have hstable : (prefixWord ++ tailWord_7045938).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7045938).length < 2 ^ (prefixWord ++ tailWord_7045938).sum := by decide
  have hdescent : baseEnd_7045938 < baseStart_7045938 := by decide
  rcases family_descends (prefixWord ++ tailWord_7045938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7045942 : List Nat := [5, 1, 2, 2, 2, 1, 1, 3, 1, 2, 3]
def baseStart_7045942 : Nat := 118140960795 + 7045942 * 2 ^ 59
def prefixEnd_7045942 : Nat := 4983230072969 + 3 ^ 40 * 7045942 * 2
def baseEnd_7045942 : Nat := 3617954909701576953221309

theorem tailTrace_7045942 : CollatzResearch.WordTrace tailWord_7045942 prefixEnd_7045942 3617954909701576953221309 := by
  unfold tailWord_7045942
  simp only [CollatzResearch.WordTrace]
  refine ⟨16061663564985184995939755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 171324411359841973290024053 16061663564985184995939755)
  ·
    refine ⟨24092495347477777493909633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16061663564985184995939755 24092495347477777493909633)
    ·
      refine ⟨18069371510608333120432225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24092495347477777493909633 18069371510608333120432225)
      ·
        refine ⟨13552028632956249840324169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18069371510608333120432225 13552028632956249840324169)
        ·
          refine ⟨10164021474717187380243127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13552028632956249840324169 10164021474717187380243127)
          ·
            refine ⟨15246032212075781070364691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10164021474717187380243127 15246032212075781070364691)
            ·
              refine ⟨22869048318113671605547037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15246032212075781070364691 22869048318113671605547037)
              ·
                refine ⟨8575893119292626852080139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22869048318113671605547037 8575893119292626852080139)
                ·
                  refine ⟨12863839678938940278120209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8575893119292626852080139 12863839678938940278120209)
                  ·
                    refine ⟨9647879759204205208590157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12863839678938940278120209 9647879759204205208590157)
                    ·
                      refine ⟨3617954909701576953221309, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9647879759204205208590157 3617954909701576953221309)
                      ·
                        rfl

theorem cell23_7045942_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 2, 1, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 2, 1, 1, 3, 1, 2, 3].length) (baseStart_7045942 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7045942 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7045942 prefixEnd_7045942 := by exact prefixLift 7045942
  have htrace : WordTrace (prefixWord ++ tailWord_7045942) baseStart_7045942 baseEnd_7045942 := by
    simpa [prefixWord, tailWord_7045942, baseEnd_7045942] using wordTrace_append hprefix tailTrace_7045942
  have hstable : (prefixWord ++ tailWord_7045942).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7045942).length < 2 ^ (prefixWord ++ tailWord_7045942).sum := by decide
  have hdescent : baseEnd_7045942 < baseStart_7045942 := by decide
  rcases family_descends (prefixWord ++ tailWord_7045942) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7045972 : List Nat := [2, 4, 1, 1, 5, 1, 1, 1, 1, 3, 3]
def baseStart_7045972 : Nat := 118140960795 + 7045972 * 2 ^ 59
def prefixEnd_7045972 : Nat := 4983230072969 + 3 ^ 40 * 7045972 * 2
def baseEnd_7045972 : Nat := 3617970314121211835846171

theorem tailTrace_7045972 : CollatzResearch.WordTrace tailWord_7045972 prefixEnd_7045972 3617970314121211835846171 := by
  unfold tailWord_7045972
  simp only [CollatzResearch.WordTrace]
  refine ⟨128493855614827137529314085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 171325140819769516705752113 128493855614827137529314085)
  ·
    refine ⟨24092597927780088286746391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 128493855614827137529314085 24092597927780088286746391)
    ·
      refine ⟨36138896891670132430119587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24092597927780088286746391 36138896891670132430119587)
      ·
        refine ⟨54208345337505198645179381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36138896891670132430119587 54208345337505198645179381)
        ·
          refine ⟨5082032375391112372985567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 54208345337505198645179381 5082032375391112372985567)
          ·
            refine ⟨7623048563086668559478351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5082032375391112372985567 7623048563086668559478351)
            ·
              refine ⟨11434572844630002839217527, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7623048563086668559478351 11434572844630002839217527)
              ·
                refine ⟨17151859266945004258826291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11434572844630002839217527 17151859266945004258826291)
                ·
                  refine ⟨25727788900417506388239437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17151859266945004258826291 25727788900417506388239437)
                  ·
                    refine ⟨9647920837656564895589789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25727788900417506388239437 9647920837656564895589789)
                    ·
                      refine ⟨3617970314121211835846171, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9647920837656564895589789 3617970314121211835846171)
                      ·
                        rfl

theorem cell23_7045972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 5, 1, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 5, 1, 1, 1, 1, 3, 3].length) (baseStart_7045972 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7045972 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7045972 prefixEnd_7045972 := by exact prefixLift 7045972
  have htrace : WordTrace (prefixWord ++ tailWord_7045972) baseStart_7045972 baseEnd_7045972 := by
    simpa [prefixWord, tailWord_7045972, baseEnd_7045972] using wordTrace_append hprefix tailTrace_7045972
  have hstable : (prefixWord ++ tailWord_7045972).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7045972).length < 2 ^ (prefixWord ++ tailWord_7045972).sum := by decide
  have hdescent : baseEnd_7045972 < baseStart_7045972 := by decide
  rcases family_descends (prefixWord ++ tailWord_7045972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7046011 : List Nat := [1, 1, 1, 1, 1, 5, 2, 1, 4, 3, 3]
def baseStart_7046011 : Nat := 118140960795 + 7046011 * 2 ^ 59
def prefixEnd_7046011 : Nat := 4983230072969 + 3 ^ 40 * 7046011 * 2
def baseEnd_7046011 : Nat := 3617990339866737183258491

theorem tailTrace_7046011 : CollatzResearch.WordTrace tailWord_7046011 prefixEnd_7046011 3617990339866737183258491 := by
  unfold tailWord_7046011
  simp only [CollatzResearch.WordTrace]
  refine ⟨256989133676512984719297887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171326089117675323146198591 256989133676512984719297887)
  ·
    refine ⟨385483700514769477078946831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 256989133676512984719297887 385483700514769477078946831)
    ·
      refine ⟨578225550772154215618420247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 385483700514769477078946831 578225550772154215618420247)
      ·
        refine ⟨867338326158231323427630371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 578225550772154215618420247 867338326158231323427630371)
        ·
          refine ⟨1301007489237346985141445557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 867338326158231323427630371 1301007489237346985141445557)
          ·
            refine ⟨121969452116001279857010521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 1301007489237346985141445557 121969452116001279857010521)
            ·
              refine ⟨91477089087000959892757891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 121969452116001279857010521 91477089087000959892757891)
              ·
                refine ⟨137215633630501439839136837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 91477089087000959892757891 137215633630501439839136837)
                ·
                  refine ⟨25727931305719019969838157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 137215633630501439839136837 25727931305719019969838157)
                  ·
                    refine ⟨9647974239644632488689309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25727931305719019969838157 9647974239644632488689309)
                    ·
                      refine ⟨3617990339866737183258491, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9647974239644632488689309 3617990339866737183258491)
                      ·
                        rfl

theorem cell23_7046011_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 2, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 2, 1, 4, 3, 3].length) (baseStart_7046011 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7046011 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7046011 prefixEnd_7046011 := by exact prefixLift 7046011
  have htrace : WordTrace (prefixWord ++ tailWord_7046011) baseStart_7046011 baseEnd_7046011 := by
    simpa [prefixWord, tailWord_7046011, baseEnd_7046011] using wordTrace_append hprefix tailTrace_7046011
  have hstable : (prefixWord ++ tailWord_7046011).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7046011).length < 2 ^ (prefixWord ++ tailWord_7046011).sum := by decide
  have hdescent : baseEnd_7046011 < baseStart_7046011 := by decide
  rcases family_descends (prefixWord ++ tailWord_7046011) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7046051 : List Nat := [1, 1, 1, 4, 1, 2, 2, 3, 1, 3, 4]
def baseStart_7046051 : Nat := 118140960795 + 7046051 * 2 ^ 59
def prefixEnd_7046051 : Nat := 4983230072969 + 3 ^ 40 * 7046051 * 2
def baseEnd_7046051 : Nat := 3618010879092917026758307

theorem tailTrace_7046051 : CollatzResearch.WordTrace tailWord_7046051 prefixEnd_7046051 3618010879092917026758307 := by
  unfold tailWord_7046051
  simp only [CollatzResearch.WordTrace]
  refine ⟨256990592596368071550754007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171327061730912047700502671 256990592596368071550754007)
  ·
    refine ⟨385485888894552107326131011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 256990592596368071550754007 385485888894552107326131011)
    ·
      refine ⟨578228833341828160989196517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 385485888894552107326131011 578228833341828160989196517)
      ·
        refine ⟨108417906251592780185474347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 578228833341828160989196517 108417906251592780185474347)
        ·
          refine ⟨162626859377389170278211521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 108417906251592780185474347 162626859377389170278211521)
          ·
            refine ⟨121970144533041877708658641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 162626859377389170278211521 121970144533041877708658641)
            ·
              refine ⟨91477608399781408281493981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 121970144533041877708658641 91477608399781408281493981)
              ·
                refine ⟨34304103149918028105560243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 91477608399781408281493981 34304103149918028105560243)
                ·
                  refine ⟨51456154724877042158340365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34304103149918028105560243 51456154724877042158340365)
                  ·
                    refine ⟨19296058021828890809377637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 51456154724877042158340365 19296058021828890809377637)
                    ·
                      refine ⟨3618010879092917026758307, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19296058021828890809377637 3618010879092917026758307)
                      ·
                        rfl

theorem cell23_7046051_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 2, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 2, 3, 1, 3, 4].length) (baseStart_7046051 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7046051 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7046051 prefixEnd_7046051 := by exact prefixLift 7046051
  have htrace : WordTrace (prefixWord ++ tailWord_7046051) baseStart_7046051 baseEnd_7046051 := by
    simpa [prefixWord, tailWord_7046051, baseEnd_7046051] using wordTrace_append hprefix tailTrace_7046051
  have hstable : (prefixWord ++ tailWord_7046051).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7046051).length < 2 ^ (prefixWord ++ tailWord_7046051).sum := by decide
  have hdescent : baseEnd_7046051 < baseStart_7046051 := by decide
  rcases family_descends (prefixWord ++ tailWord_7046051) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7046102 : List Nat := [5, 2, 1, 1, 2, 1, 3, 1, 2, 1, 4]
def baseStart_7046102 : Nat := 118140960795 + 7046102 * 2 ^ 59
def prefixEnd_7046102 : Nat := 4983230072969 + 3 ^ 40 * 7046102 * 2
def baseEnd_7046102 : Nat := 3618037066606296327220573

theorem tailTrace_7046102 : CollatzResearch.WordTrace tailWord_7046102 prefixEnd_7046102 3618037066606296327220573 := by
  unfold tailWord_7046102
  simp only [CollatzResearch.WordTrace]
  refine ⟨16062028294948956703803785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 171328301812788871507240373 16062028294948956703803785)
  ·
    refine ⟨12046521221211717527852839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16062028294948956703803785 12046521221211717527852839)
    ·
      refine ⟨18069781831817576291779259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12046521221211717527852839 18069781831817576291779259)
      ·
        refine ⟨27104672747726364437668889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18069781831817576291779259 27104672747726364437668889)
        ·
          refine ⟨20328504560794773328251667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27104672747726364437668889 20328504560794773328251667)
          ·
            refine ⟨30492756841192159992377501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20328504560794773328251667 30492756841192159992377501)
            ·
              refine ⟨11434783815447059997141563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30492756841192159992377501 11434783815447059997141563)
              ·
                refine ⟨17152175723170589995712345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11434783815447059997141563 17152175723170589995712345)
                ·
                  refine ⟨12864131792377942496784259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17152175723170589995712345 12864131792377942496784259)
                  ·
                    refine ⟨19296197688566913745176389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12864131792377942496784259 19296197688566913745176389)
                    ·
                      refine ⟨3618037066606296327220573, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19296197688566913745176389 3618037066606296327220573)
                      ·
                        rfl

theorem cell23_7046102_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 1, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 1, 3, 1, 2, 1, 4].length) (baseStart_7046102 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7046102 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7046102 prefixEnd_7046102 := by exact prefixLift 7046102
  have htrace : WordTrace (prefixWord ++ tailWord_7046102) baseStart_7046102 baseEnd_7046102 := by
    simpa [prefixWord, tailWord_7046102, baseEnd_7046102] using wordTrace_append hprefix tailTrace_7046102
  have hstable : (prefixWord ++ tailWord_7046102).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7046102).length < 2 ^ (prefixWord ++ tailWord_7046102).sum := by decide
  have hdescent : baseEnd_7046102 < baseStart_7046102 := by decide
  rcases family_descends (prefixWord ++ tailWord_7046102) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7046105 : List Nat := [1, 2, 1, 2, 5, 1, 3, 1, 2, 2, 3]
def baseStart_7046105 : Nat := 118140960795 + 7046105 * 2 ^ 59
def prefixEnd_7046105 : Nat := 4983230072969 + 3 ^ 40 * 7046105 * 2
def baseEnd_7046105 : Nat := 3618038607048259815483059

theorem tailTrace_7046105 : CollatzResearch.WordTrace tailWord_7046105 prefixEnd_7046105 3618038607048259815483059 := by
  unfold tailWord_7046105
  simp only [CollatzResearch.WordTrace]
  refine ⟨256992562138172438773219769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171328374758781625848813179 256992562138172438773219769)
  ·
    refine ⟨192744421603629329079914827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 256992562138172438773219769 192744421603629329079914827)
    ·
      refine ⟨289116632405443993619872241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 192744421603629329079914827 289116632405443993619872241)
      ·
        refine ⟨216837474304082995214904181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 289116632405443993619872241 216837474304082995214904181)
        ·
          refine ⟨20328513216007780801397267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 216837474304082995214904181 20328513216007780801397267)
          ·
            refine ⟨30492769824011671202095901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20328513216007780801397267 30492769824011671202095901)
            ·
              refine ⟨11434788684004376700785963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30492769824011671202095901 11434788684004376700785963)
              ·
                refine ⟨17152183026006565051178945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11434788684004376700785963 17152183026006565051178945)
                ·
                  refine ⟨12864137269504923788384209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17152183026006565051178945 12864137269504923788384209)
                  ·
                    refine ⟨9648102952128692841288157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12864137269504923788384209 9648102952128692841288157)
                    ·
                      refine ⟨3618038607048259815483059, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9648102952128692841288157 3618038607048259815483059)
                      ·
                        rfl

theorem cell23_7046105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 1, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 1, 3, 1, 2, 2, 3].length) (baseStart_7046105 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7046105 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7046105 prefixEnd_7046105 := by exact prefixLift 7046105
  have htrace : WordTrace (prefixWord ++ tailWord_7046105) baseStart_7046105 baseEnd_7046105 := by
    simpa [prefixWord, tailWord_7046105, baseEnd_7046105] using wordTrace_append hprefix tailTrace_7046105
  have hstable : (prefixWord ++ tailWord_7046105).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7046105).length < 2 ^ (prefixWord ++ tailWord_7046105).sum := by decide
  have hdescent : baseEnd_7046105 < baseStart_7046105 := by decide
  rcases family_descends (prefixWord ++ tailWord_7046105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7046145 : List Nat := [1, 2, 4, 1, 2, 2, 1, 2, 1, 5, 2]
def baseStart_7046145 : Nat := 118140960795 + 7046145 * 2 ^ 59
def prefixEnd_7046145 : Nat := 4983230072969 + 3 ^ 40 * 7046145 * 2
def baseEnd_7046145 : Nat := 3618059146274439658982875

theorem tailTrace_7046145 : CollatzResearch.WordTrace tailWord_7046145 prefixEnd_7046145 3618059146274439658982875 := by
  unfold tailWord_7046145
  simp only [CollatzResearch.WordTrace]
  refine ⟨256994021058027525604675889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171329347372018350403117259 256994021058027525604675889)
  ·
    refine ⟨192745515793520644203506917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 256994021058027525604675889 192745515793520644203506917)
    ·
      refine ⟨36139784211285120788157547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 192745515793520644203506917 36139784211285120788157547)
      ·
        refine ⟨54209676316927681182236321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36139784211285120788157547 54209676316927681182236321)
        ·
          refine ⟨40657257237695760886677241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54209676316927681182236321 40657257237695760886677241)
          ·
            refine ⟨30492942928271820665007931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40657257237695760886677241 30492942928271820665007931)
            ·
              refine ⟨45739414392407730997511897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30492942928271820665007931 45739414392407730997511897)
              ·
                refine ⟨34304560794305798248133923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45739414392407730997511897 34304560794305798248133923)
                ·
                  refine ⟨51456841191458697372200885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34304560794305798248133923 51456841191458697372200885)
                  ·
                    refine ⟨4824078861699252878643833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 51456841191458697372200885 4824078861699252878643833)
                    ·
                      refine ⟨3618059146274439658982875, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4824078861699252878643833 3618059146274439658982875)
                      ·
                        rfl

theorem cell23_7046145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 2, 1, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 2, 1, 2, 1, 5, 2].length) (baseStart_7046145 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7046145 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7046145 prefixEnd_7046145 := by exact prefixLift 7046145
  have htrace : WordTrace (prefixWord ++ tailWord_7046145) baseStart_7046145 baseEnd_7046145 := by
    simpa [prefixWord, tailWord_7046145, baseEnd_7046145] using wordTrace_append hprefix tailTrace_7046145
  have hstable : (prefixWord ++ tailWord_7046145).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7046145).length < 2 ^ (prefixWord ++ tailWord_7046145).sum := by decide
  have hdescent : baseEnd_7046145 < baseStart_7046145 := by decide
  rcases family_descends (prefixWord ++ tailWord_7046145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7046155 : List Nat := [1, 1, 1, 1, 6, 3, 2, 2, 1, 5]
def baseStart_7046155 : Nat := 118140960795 + 7046155 * 2 ^ 59
def prefixEnd_7046155 : Nat := 4983230072969 + 3 ^ 40 * 7046155 * 2
def baseEnd_7046155 : Nat := 1206021427026994873285943

theorem tailTrace_7046155 : CollatzResearch.WordTrace tailWord_7046155 prefixEnd_7046155 1206021427026994873285943 := by
  unfold tailWord_7046155
  simp only [CollatzResearch.WordTrace]
  refine ⟨256994385787991297312539919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171329590525327531541693279 256994385787991297312539919)
  ·
    refine ⟨385491578681986945968809879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 256994385787991297312539919 385491578681986945968809879)
    ·
      refine ⟨578237368022980418953214819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 385491578681986945968809879 578237368022980418953214819)
      ·
        refine ⟨867356052034470628429822229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 578237368022980418953214819 867356052034470628429822229)
        ·
          refine ⟨40657314939115810707647917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 867356052034470628429822229 40657314939115810707647917)
          ·
            refine ⟨15246493102168429015367969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40657314939115810707647917 15246493102168429015367969)
            ·
              refine ⟨11434869826626321761525977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15246493102168429015367969 11434869826626321761525977)
              ·
                refine ⟨8576152369969741321144483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11434869826626321761525977 8576152369969741321144483)
                ·
                  refine ⟨12864228554954611981716725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8576152369969741321144483 12864228554954611981716725)
                  ·
                    refine ⟨1206021427026994873285943, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12864228554954611981716725 1206021427026994873285943)
                    ·
                      rfl

theorem cell23_7046155_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 3, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 3, 2, 2, 1, 5].length) (baseStart_7046155 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7046155 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7046155 prefixEnd_7046155 := by exact prefixLift 7046155
  have htrace : WordTrace (prefixWord ++ tailWord_7046155) baseStart_7046155 baseEnd_7046155 := by
    simpa [prefixWord, tailWord_7046155, baseEnd_7046155] using wordTrace_append hprefix tailTrace_7046155
  have hstable : (prefixWord ++ tailWord_7046155).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7046155).length < 2 ^ (prefixWord ++ tailWord_7046155).sum := by decide
  have hdescent : baseEnd_7046155 < baseStart_7046155 := by decide
  rcases family_descends (prefixWord ++ tailWord_7046155) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7046175 : List Nat := [1, 1, 2, 4, 1, 3, 2, 3, 1, 1, 4]
def baseStart_7046175 : Nat := 118140960795 + 7046175 * 2 ^ 59
def prefixEnd_7046175 : Nat := 4983230072969 + 3 ^ 40 * 7046175 * 2
def baseEnd_7046175 : Nat := 3618074550694074541607737

theorem tailTrace_7046175 : CollatzResearch.WordTrace tailWord_7046175 prefixEnd_7046175 3618074550694074541607737 := by
  unfold tailWord_7046175
  simp only [CollatzResearch.WordTrace]
  refine ⟨256995115247918840728267979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171330076831945893818845319 256995115247918840728267979)
  ·
    refine ⟨385492672871878261092401969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 256995115247918840728267979 385492672871878261092401969)
    ·
      refine ⟨289119504653908695819301477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 385492672871878261092401969 289119504653908695819301477)
      ·
        refine ⟨54209907122607880466119027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 289119504653908695819301477 54209907122607880466119027)
        ·
          refine ⟨81314860683911820699178541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54209907122607880466119027 81314860683911820699178541)
          ·
            refine ⟨30493072756466932762191953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 81314860683911820699178541 30493072756466932762191953)
            ·
              refine ⟨22869804567350199571643965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30493072756466932762191953 22869804567350199571643965)
              ·
                refine ⟨8576176712756324839366487, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22869804567350199571643965 8576176712756324839366487)
                ·
                  refine ⟨12864265069134487259049731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8576176712756324839366487 12864265069134487259049731)
                  ·
                    refine ⟨19296397603701730888574597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12864265069134487259049731 19296397603701730888574597)
                    ·
                      refine ⟨3618074550694074541607737, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19296397603701730888574597 3618074550694074541607737)
                      ·
                        rfl

theorem cell23_7046175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 3, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 3, 2, 3, 1, 1, 4].length) (baseStart_7046175 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7046175 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7046175 prefixEnd_7046175 := by exact prefixLift 7046175
  have htrace : WordTrace (prefixWord ++ tailWord_7046175) baseStart_7046175 baseEnd_7046175 := by
    simpa [prefixWord, tailWord_7046175, baseEnd_7046175] using wordTrace_append hprefix tailTrace_7046175
  have hstable : (prefixWord ++ tailWord_7046175).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7046175).length < 2 ^ (prefixWord ++ tailWord_7046175).sum := by decide
  have hdescent : baseEnd_7046175 < baseStart_7046175 := by decide
  rcases family_descends (prefixWord ++ tailWord_7046175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7046186 : List Nat := [3, 1, 4, 1, 4, 1, 1, 1, 3, 1, 3]
def baseStart_7046186 : Nat := 118140960795 + 7046186 * 2 ^ 59
def prefixEnd_7046186 : Nat := 4983230072969 + 3 ^ 40 * 7046186 * 2
def baseEnd_7046186 : Nat := 3618080198981273998570187

theorem tailTrace_7046186 : CollatzResearch.WordTrace tailWord_7046186 prefixEnd_7046186 3618080198981273998570187 := by
  unfold tailWord_7046186
  simp only [CollatzResearch.WordTrace]
  refine ⟨64248879112719747401729603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 171330344300585993071278941 64248879112719747401729603)
  ·
    refine ⟨96373318669079621102594405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64248879112719747401729603 96373318669079621102594405)
    ·
      refine ⟨18069997250452428956736451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 96373318669079621102594405 18069997250452428956736451)
      ·
        refine ⟨27104995875678643435104677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18069997250452428956736451 27104995875678643435104677)
        ·
          refine ⟨5082186726689745644082127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 27104995875678643435104677 5082186726689745644082127)
          ·
            refine ⟨7623280090034618466123191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5082186726689745644082127 7623280090034618466123191)
            ·
              refine ⟨11434920135051927699184787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7623280090034618466123191 11434920135051927699184787)
              ·
                refine ⟨17152380202577891548777181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11434920135051927699184787 17152380202577891548777181)
                ·
                  refine ⟨6432142575966709330791443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17152380202577891548777181 6432142575966709330791443)
                  ·
                    refine ⟨9648213863950063996187165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6432142575966709330791443 9648213863950063996187165)
                    ·
                      refine ⟨3618080198981273998570187, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9648213863950063996187165 3618080198981273998570187)
                      ·
                        rfl

theorem cell23_7046186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 4, 1, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 4, 1, 1, 1, 3, 1, 3].length) (baseStart_7046186 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7046186 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7046186 prefixEnd_7046186 := by exact prefixLift 7046186
  have htrace : WordTrace (prefixWord ++ tailWord_7046186) baseStart_7046186 baseEnd_7046186 := by
    simpa [prefixWord, tailWord_7046186, baseEnd_7046186] using wordTrace_append hprefix tailTrace_7046186
  have hstable : (prefixWord ++ tailWord_7046186).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7046186).length < 2 ^ (prefixWord ++ tailWord_7046186).sum := by decide
  have hdescent : baseEnd_7046186 < baseStart_7046186 := by decide
  rcases family_descends (prefixWord ++ tailWord_7046186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7046202 : List Nat := [3, 1, 1, 1, 3, 1, 6, 1, 2, 4]
def baseStart_7046202 : Nat := 118140960795 + 7046202 * 2 ^ 59
def prefixEnd_7046202 : Nat := 4983230072969 + 3 ^ 40 * 7046202 * 2
def baseEnd_7046202 : Nat := 1206029471557248645323371

theorem tailTrace_7046202 : CollatzResearch.WordTrace tailWord_7046202 prefixEnd_7046202 1206029471557248645323371 := by
  unfold tailWord_7046202
  simp only [CollatzResearch.WordTrace]
  refine ⟨64249025004705256084875215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 171330733345880682893000573 64249025004705256084875215)
  ·
    refine ⟨96373537507057884127312823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64249025004705256084875215 96373537507057884127312823)
    ·
      refine ⟨144560306260586826190969235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96373537507057884127312823 144560306260586826190969235)
      ·
        refine ⟨216840459390880239286453853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 144560306260586826190969235 216840459390880239286453853)
        ·
          refine ⟨81315172271580089732420195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 216840459390880239286453853 81315172271580089732420195)
          ·
            refine ⟨121972758407370134598630293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81315172271580089732420195 121972758407370134598630293)
            ·
              refine ⟨5717473050345475059310795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 121972758407370134598630293 5717473050345475059310795)
              ·
                refine ⟨8576209575518212588966193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5717473050345475059310795 8576209575518212588966193)
                ·
                  refine ⟨6432157181638659441724645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8576209575518212588966193 6432157181638659441724645)
                  ·
                    refine ⟨1206029471557248645323371, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6432157181638659441724645 1206029471557248645323371)
                    ·
                      rfl

theorem cell23_7046202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 6, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 6, 1, 2, 4].length) (baseStart_7046202 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7046202 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7046202 prefixEnd_7046202 := by exact prefixLift 7046202
  have htrace : WordTrace (prefixWord ++ tailWord_7046202) baseStart_7046202 baseEnd_7046202 := by
    simpa [prefixWord, tailWord_7046202, baseEnd_7046202] using wordTrace_append hprefix tailTrace_7046202
  have hstable : (prefixWord ++ tailWord_7046202).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7046202).length < 2 ^ (prefixWord ++ tailWord_7046202).sum := by decide
  have hdescent : baseEnd_7046202 < baseStart_7046202 := by decide
  rcases family_descends (prefixWord ++ tailWord_7046202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7046209 : List Nat := [1, 2, 5, 1, 3, 2, 1, 2, 1, 1, 4]
def baseStart_7046209 : Nat := 118140960795 + 7046209 * 2 ^ 59
def prefixEnd_7046209 : Nat := 4983230072969 + 3 ^ 40 * 7046209 * 2
def baseEnd_7046209 : Nat := 3618092009036327408582581

theorem tailTrace_7046209 : CollatzResearch.WordTrace tailWord_7046209 prefixEnd_7046209 3618092009036327408582581 := by
  unfold tailWord_7046209
  simp only [CollatzResearch.WordTrace]
  refine ⟨256996355329795664535005681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171330903553197109690003787 256996355329795664535005681)
  ·
    refine ⟨192747266497346748401254261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 256996355329795664535005681 192747266497346748401254261)
    ·
      refine ⟨18070056234126257662617587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 192747266497346748401254261 18070056234126257662617587)
      ·
        refine ⟨27105084351189386493926381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18070056234126257662617587 27105084351189386493926381)
        ·
          refine ⟨10164406631696019935222393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27105084351189386493926381 10164406631696019935222393)
          ·
            refine ⟨7623304973772014951416795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10164406631696019935222393 7623304973772014951416795)
            ·
              refine ⟨11434957460658022427125193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7623304973772014951416795 11434957460658022427125193)
              ·
                refine ⟨8576218095493516820343895, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11434957460658022427125193 8576218095493516820343895)
                ·
                  refine ⟨12864327143240275230515843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8576218095493516820343895 12864327143240275230515843)
                  ·
                    refine ⟨19296490714860412845773765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12864327143240275230515843 19296490714860412845773765)
                    ·
                      refine ⟨3618092009036327408582581, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19296490714860412845773765 3618092009036327408582581)
                      ·
                        rfl

theorem cell23_7046209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 3, 2, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 3, 2, 1, 2, 1, 1, 4].length) (baseStart_7046209 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7046209 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7046209 prefixEnd_7046209 := by exact prefixLift 7046209
  have htrace : WordTrace (prefixWord ++ tailWord_7046209) baseStart_7046209 baseEnd_7046209 := by
    simpa [prefixWord, tailWord_7046209, baseEnd_7046209] using wordTrace_append hprefix tailTrace_7046209
  have hstable : (prefixWord ++ tailWord_7046209).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7046209).length < 2 ^ (prefixWord ++ tailWord_7046209).sum := by decide
  have hdescent : baseEnd_7046209 < baseStart_7046209 := by decide
  rcases family_descends (prefixWord ++ tailWord_7046209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7046225 : List Nat := [1, 2, 2, 1, 3, 1, 2, 1, 6, 1, 3]
def baseStart_7046225 : Nat := 118140960795 + 7046225 * 2 ^ 59
def prefixEnd_7046225 : Nat := 4983230072969 + 3 ^ 40 * 7046225 * 2
def baseEnd_7046225 : Nat := 3618100224726799345982507

theorem tailTrace_7046225 : CollatzResearch.WordTrace tailWord_7046225 prefixEnd_7046225 3618100224726799345982507 := by
  unfold tailWord_7046225
  simp only [CollatzResearch.WordTrace]
  refine ⟨256996938897737699267588129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171331292598491799511725419 256996938897737699267588129)
  ·
    refine ⟨192747704173303274450691097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 256996938897737699267588129 192747704173303274450691097)
    ·
      refine ⟨144560778129977455838018323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 192747704173303274450691097 144560778129977455838018323)
      ·
        refine ⟨216841167194966183757027485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 144560778129977455838018323 216841167194966183757027485)
        ·
          refine ⟨81315437698112318908885307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 216841167194966183757027485 81315437698112318908885307)
          ·
            refine ⟨121973156547168478363327961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81315437698112318908885307 121973156547168478363327961)
            ·
              refine ⟨91479867410376358772495971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 121973156547168478363327961 91479867410376358772495971)
              ·
                refine ⟨137219801115564538158743957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 91479867410376358772495971 137219801115564538158743957)
                ·
                  refine ⟨6432178177292087726191123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 137219801115564538158743957 6432178177292087726191123)
                  ·
                    refine ⟨9648267265938131589286685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6432178177292087726191123 9648267265938131589286685)
                    ·
                      refine ⟨3618100224726799345982507, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9648267265938131589286685 3618100224726799345982507)
                      ·
                        rfl

theorem cell23_7046225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 2, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 2, 1, 6, 1, 3].length) (baseStart_7046225 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7046225 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7046225 prefixEnd_7046225 := by exact prefixLift 7046225
  have htrace : WordTrace (prefixWord ++ tailWord_7046225) baseStart_7046225 baseEnd_7046225 := by
    simpa [prefixWord, tailWord_7046225, baseEnd_7046225] using wordTrace_append hprefix tailTrace_7046225
  have hstable : (prefixWord ++ tailWord_7046225).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7046225).length < 2 ^ (prefixWord ++ tailWord_7046225).sum := by decide
  have hdescent : baseEnd_7046225 < baseStart_7046225 := by decide
  rcases family_descends (prefixWord ++ tailWord_7046225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7046282 : List Nat := [3, 1, 2, 3, 1, 1, 1, 4, 1, 4, 2]
def baseStart_7046282 : Nat := 118140960795 + 7046282 * 2 ^ 59
def prefixEnd_7046282 : Nat := 4983230072969 + 3 ^ 40 * 7046282 * 2
def baseEnd_7046282 : Nat := 3618129493124105622969745

theorem tailTrace_7046282 : CollatzResearch.WordTrace tailWord_7046282 prefixEnd_7046282 3618129493124105622969745 := by
  unfold tailWord_7046282
  simp only [CollatzResearch.WordTrace]
  refine ⟨64249754464632799500603275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 171332678572354132001608733 64249754464632799500603275)
  ·
    refine ⟨96374631696949199250904913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64249754464632799500603275 96374631696949199250904913)
    ·
      refine ⟨72280973772711899438178685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 96374631696949199250904913 72280973772711899438178685)
      ·
        refine ⟨27105365164766962289317007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 72280973772711899438178685 27105365164766962289317007)
        ·
          refine ⟨40658047747150443433975511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27105365164766962289317007 40658047747150443433975511)
          ·
            refine ⟨60987071620725665150963267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40658047747150443433975511 60987071620725665150963267)
            ·
              refine ⟨91480607431088497726444901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60987071620725665150963267 91480607431088497726444901)
              ·
                refine ⟨17152613893329093323708419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 91480607431088497726444901 17152613893329093323708419)
                ·
                  refine ⟨25728920839993639985562629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17152613893329093323708419 25728920839993639985562629)
                  ·
                    refine ⟨4824172657498807497292993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25728920839993639985562629 4824172657498807497292993)
                    ·
                      refine ⟨3618129493124105622969745, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4824172657498807497292993 3618129493124105622969745)
                      ·
                        rfl

theorem cell23_7046282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 1, 4, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 1, 4, 1, 4, 2].length) (baseStart_7046282 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7046282 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7046282 prefixEnd_7046282 := by exact prefixLift 7046282
  have htrace : WordTrace (prefixWord ++ tailWord_7046282) baseStart_7046282 baseEnd_7046282 := by
    simpa [prefixWord, tailWord_7046282, baseEnd_7046282] using wordTrace_append hprefix tailTrace_7046282
  have hstable : (prefixWord ++ tailWord_7046282).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7046282).length < 2 ^ (prefixWord ++ tailWord_7046282).sum := by decide
  have hdescent : baseEnd_7046282 < baseStart_7046282 := by decide
  rcases family_descends (prefixWord ++ tailWord_7046282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7046286 : List Nat := [4, 1, 1, 3, 2, 1, 4, 1, 1, 3, 2]
def baseStart_7046286 : Nat := 118140960795 + 7046286 * 2 ^ 59
def prefixEnd_7046286 : Nat := 4983230072969 + 3 ^ 40 * 7046286 * 2
def baseEnd_7046286 : Nat := 3618131547046723607319727

theorem tailTrace_7046286 : CollatzResearch.WordTrace tailWord_7046286 prefixEnd_7046286 3618131547046723607319727 := by
  unfold tailWord_7046286
  simp only [CollatzResearch.WordTrace]
  refine ⟨32124895468814588335694839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 171332775833677804457039141 32124895468814588335694839)
  ·
    refine ⟨48187343203221882503542259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32124895468814588335694839 48187343203221882503542259)
    ·
      refine ⟨72281014804832823755313389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48187343203221882503542259 72281014804832823755313389)
      ·
        refine ⟨27105380551812308908242521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 72281014804832823755313389 27105380551812308908242521)
        ·
          refine ⟨20329035413859231681181891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27105380551812308908242521 20329035413859231681181891)
          ·
            refine ⟨30493553120788847521772837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20329035413859231681181891 30493553120788847521772837)
            ·
              refine ⟨5717541210147908910332407, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 30493553120788847521772837 5717541210147908910332407)
              ·
                refine ⟨8576311815221863365498611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5717541210147908910332407 8576311815221863365498611)
                ·
                  refine ⟨12864467722832795048247917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8576311815221863365498611 12864467722832795048247917)
                  ·
                    refine ⟨4824175396062298143092969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12864467722832795048247917 4824175396062298143092969)
                    ·
                      refine ⟨3618131547046723607319727, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4824175396062298143092969 3618131547046723607319727)
                      ·
                        rfl

theorem cell23_7046286_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 1, 4, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 1, 4, 1, 1, 3, 2].length) (baseStart_7046286 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7046286 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7046286 prefixEnd_7046286 := by exact prefixLift 7046286
  have htrace : WordTrace (prefixWord ++ tailWord_7046286) baseStart_7046286 baseEnd_7046286 := by
    simpa [prefixWord, tailWord_7046286, baseEnd_7046286] using wordTrace_append hprefix tailTrace_7046286
  have hstable : (prefixWord ++ tailWord_7046286).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7046286).length < 2 ^ (prefixWord ++ tailWord_7046286).sum := by decide
  have hdescent : baseEnd_7046286 < baseStart_7046286 := by decide
  rcases family_descends (prefixWord ++ tailWord_7046286) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7046295 : List Nat := [1, 1, 3, 3, 3, 1, 1, 2, 2, 2, 4]
def baseStart_7046295 : Nat := 118140960795 + 7046295 * 2 ^ 59
def prefixEnd_7046295 : Nat := 4983230072969 + 3 ^ 40 * 7046295 * 2
def baseEnd_7046295 : Nat := 3618136168372614072107185

theorem tailTrace_7046295 : CollatzResearch.WordTrace tailWord_7046295 prefixEnd_7046295 3618136168372614072107185 := by
  unfold tailWord_7046295
  simp only [CollatzResearch.WordTrace]
  refine ⟨256999492007484101222636339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171332994671656067481757559 256999492007484101222636339)
  ·
    refine ⟨385499238011226151833954509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 256999492007484101222636339 385499238011226151833954509)
    ·
      refine ⟨144562214254209806937732941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 385499238011226151833954509 144562214254209806937732941)
      ·
        refine ⟨54210830345328677601649853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 144562214254209806937732941 54210830345328677601649853)
        ·
          refine ⟨20329061379498254100618695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 54210830345328677601649853 20329061379498254100618695)
          ·
            refine ⟨30493592069247381150928043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20329061379498254100618695 30493592069247381150928043)
            ·
              refine ⟨45740388103871071726392065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30493592069247381150928043 45740388103871071726392065)
              ·
                refine ⟨34305291077903303794794049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45740388103871071726392065 34305291077903303794794049)
                ·
                  refine ⟨25728968308427477846095537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34305291077903303794794049 25728968308427477846095537)
                  ·
                    refine ⟨19296726231320608384571653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25728968308427477846095537 19296726231320608384571653)
                    ·
                      refine ⟨3618136168372614072107185, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19296726231320608384571653 3618136168372614072107185)
                      ·
                        rfl

theorem cell23_7046295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 1, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 1, 1, 2, 2, 2, 4].length) (baseStart_7046295 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7046295 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7046295 prefixEnd_7046295 := by exact prefixLift 7046295
  have htrace : WordTrace (prefixWord ++ tailWord_7046295) baseStart_7046295 baseEnd_7046295 := by
    simpa [prefixWord, tailWord_7046295, baseEnd_7046295] using wordTrace_append hprefix tailTrace_7046295
  have hstable : (prefixWord ++ tailWord_7046295).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7046295).length < 2 ^ (prefixWord ++ tailWord_7046295).sum := by decide
  have hdescent : baseEnd_7046295 < baseStart_7046295 := by decide
  rcases family_descends (prefixWord ++ tailWord_7046295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7046305 : List Nat := [1, 2, 3, 3, 1, 1, 4, 1, 7]
def baseStart_7046305 : Nat := 118140960795 + 7046305 * 2 ^ 59
def prefixEnd_7046305 : Nat := 4983230072969 + 3 ^ 40 * 7046305 * 2
def baseEnd_7046305 : Nat := 402015700353239892553571

theorem tailTrace_7046305 : CollatzResearch.WordTrace tailWord_7046305 prefixEnd_7046305 402015700353239892553571 := by
  unfold tailWord_7046305
  simp only [CollatzResearch.WordTrace]
  refine ⟨256999856737447872930500369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171333237824965248620333579 256999856737447872930500369)
  ·
    refine ⟨192749892553085904697875277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 256999856737447872930500369 192749892553085904697875277)
    ·
      refine ⟨72281209707407214261703229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 192749892553085904697875277 72281209707407214261703229)
      ·
        refine ⟨27105453640277705348138711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 72281209707407214261703229 27105453640277705348138711)
        ·
          refine ⟨40658180460416558022208067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27105453640277705348138711 40658180460416558022208067)
          ·
            refine ⟨60987270690624837033312101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40658180460416558022208067 60987270690624837033312101)
            ·
              refine ⟨11435113254492156943746019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 60987270690624837033312101 11435113254492156943746019)
              ·
                refine ⟨17152669881738235415619029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11435113254492156943746019 17152669881738235415619029)
                ·
                  refine ⟨402015700353239892553571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17152669881738235415619029 402015700353239892553571)
                  ·
                    rfl

theorem cell23_7046305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 4, 1, 7].length) (baseStart_7046305 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7046305 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7046305 prefixEnd_7046305 := by exact prefixLift 7046305
  have htrace : WordTrace (prefixWord ++ tailWord_7046305) baseStart_7046305 baseEnd_7046305 := by
    simpa [prefixWord, tailWord_7046305, baseEnd_7046305] using wordTrace_append hprefix tailTrace_7046305
  have hstable : (prefixWord ++ tailWord_7046305).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7046305).length < 2 ^ (prefixWord ++ tailWord_7046305).sum := by decide
  have hdescent : baseEnd_7046305 < baseStart_7046305 := by decide
  rcases family_descends (prefixWord ++ tailWord_7046305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7046328 : List Nat := [2, 1, 2, 1, 2, 1, 2, 1, 3, 1, 7]
def baseStart_7046328 : Nat := 118140960795 + 7046328 * 2 ^ 59
def prefixEnd_7046328 : Nat := 4983230072969 + 3 ^ 40 * 7046328 * 2
def baseEnd_7046328 : Nat := 3618153113234212442994533

theorem tailTrace_7046328 : CollatzResearch.WordTrace tailWord_7046328 prefixEnd_7046328 3618153113234212442994533 := by
  unfold tailWord_7046328
  simp only [CollatzResearch.WordTrace]
  refine ⟨128500347808182273929293819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 171333797077576365239058425 128500347808182273929293819)
  ·
    refine ⟨192750521712273410893940729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128500347808182273929293819 192750521712273410893940729)
    ·
      refine ⟨144562891284205058170455547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 192750521712273410893940729 144562891284205058170455547)
      ·
        refine ⟨216844336926307587255683321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 144562891284205058170455547 216844336926307587255683321)
        ·
          refine ⟨162633252694730690441762491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 216844336926307587255683321 162633252694730690441762491)
          ·
            refine ⟨243949879042096035662643737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 162633252694730690441762491 243949879042096035662643737)
            ·
              refine ⟨182962409281572026746982803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 243949879042096035662643737 182962409281572026746982803)
              ·
                refine ⟨274443613922358040120474205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 182962409281572026746982803 274443613922358040120474205)
                ·
                  refine ⟨102916355220884265045177827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 274443613922358040120474205 102916355220884265045177827)
                  ·
                    refine ⟨154374532831326397567766741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 102916355220884265045177827 154374532831326397567766741)
                    ·
                      refine ⟨3618153113234212442994533, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 154374532831326397567766741 3618153113234212442994533)
                      ·
                        rfl

theorem cell23_7046328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 2, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 2, 1, 3, 1, 7].length) (baseStart_7046328 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7046328 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7046328 prefixEnd_7046328 := by exact prefixLift 7046328
  have htrace : WordTrace (prefixWord ++ tailWord_7046328) baseStart_7046328 baseEnd_7046328 := by
    simpa [prefixWord, tailWord_7046328, baseEnd_7046328] using wordTrace_append hprefix tailTrace_7046328
  have hstable : (prefixWord ++ tailWord_7046328).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7046328).length < 2 ^ (prefixWord ++ tailWord_7046328).sum := by decide
  have hdescent : baseEnd_7046328 < baseStart_7046328 := by decide
  rcases family_descends (prefixWord ++ tailWord_7046328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7046355 : List Nat := [1, 1, 1, 2, 1, 1, 1, 8, 2, 1, 4]
def baseStart_7046355 : Nat := 118140960795 + 7046355 * 2 ^ 59
def prefixEnd_7046355 : Nat := 4983230072969 + 3 ^ 40 * 7046355 * 2
def baseEnd_7046355 : Nat := 3618166977211883837356909

theorem tailTrace_7046355 : CollatzResearch.WordTrace tailWord_7046355 prefixEnd_7046355 3618166977211883837356909 := by
  unfold tailWord_7046355
  simp only [CollatzResearch.WordTrace]
  refine ⟨257001680387266731469820519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171334453591511154313213679 257001680387266731469820519)
  ·
    refine ⟨385502520580900097204730779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 257001680387266731469820519 385502520580900097204730779)
    ·
      refine ⟨578253780871350145807096169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 385502520580900097204730779 578253780871350145807096169)
      ·
        refine ⟨433690335653512609355322127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 578253780871350145807096169 433690335653512609355322127)
        ·
          refine ⟨650535503480268914032983191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 433690335653512609355322127 650535503480268914032983191)
          ·
            refine ⟨975803255220403371049474787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 650535503480268914032983191 975803255220403371049474787)
            ·
              refine ⟨1463704882830605056574212181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 975803255220403371049474787 1463704882830605056574212181)
              ·
                refine ⟨17152791595671153006729049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 1463704882830605056574212181 17152791595671153006729049)
                ·
                  refine ⟨12864593696753364755046787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17152791595671153006729049 12864593696753364755046787)
                  ·
                    refine ⟨19296890545130047132570181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12864593696753364755046787 19296890545130047132570181)
                    ·
                      refine ⟨3618166977211883837356909, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19296890545130047132570181 3618166977211883837356909)
                      ·
                        rfl

theorem cell23_7046355_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 8, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 8, 2, 1, 4].length) (baseStart_7046355 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7046355 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7046355 prefixEnd_7046355 := by exact prefixLift 7046355
  have htrace : WordTrace (prefixWord ++ tailWord_7046355) baseStart_7046355 baseEnd_7046355 := by
    simpa [prefixWord, tailWord_7046355, baseEnd_7046355] using wordTrace_append hprefix tailTrace_7046355
  have hstable : (prefixWord ++ tailWord_7046355).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7046355).length < 2 ^ (prefixWord ++ tailWord_7046355).sum := by decide
  have hdescent : baseEnd_7046355 < baseStart_7046355 := by decide
  rcases family_descends (prefixWord ++ tailWord_7046355) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7046356 : List Nat := [2, 4, 1, 4, 2, 1, 1, 1, 7]
def baseStart_7046356 : Nat := 118140960795 + 7046356 * 2 ^ 59
def prefixEnd_7046356 : Nat := 4983230072969 + 3 ^ 40 * 7046356 * 2
def baseEnd_7046356 : Nat := 402018610076948703716045

theorem tailTrace_7046356 : CollatzResearch.WordTrace tailWord_7046356 prefixEnd_7046356 402018610076948703716045 := by
  unfold tailWord_7046356
  simp only [CollatzResearch.WordTrace]
  refine ⟨128500858430131554320303461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 171334477906842072427071281 128500858430131554320303461)
  ·
    refine ⟨24093910955649666435056899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 128500858430131554320303461 24093910955649666435056899)
    ·
      refine ⟨36140866433474499652585349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24093910955649666435056899 36140866433474499652585349)
      ·
        refine ⟨6776412456276468684859753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 36140866433474499652585349 6776412456276468684859753)
        ·
          refine ⟨5082309342207351513644815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6776412456276468684859753 5082309342207351513644815)
          ·
            refine ⟨7623464013311027270467223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5082309342207351513644815 7623464013311027270467223)
            ·
              refine ⟨11435196019966540905700835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7623464013311027270467223 11435196019966540905700835)
              ·
                refine ⟨17152794029949811358551253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11435196019966540905700835 17152794029949811358551253)
                ·
                  refine ⟨402018610076948703716045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17152794029949811358551253 402018610076948703716045)
                  ·
                    rfl

theorem cell23_7046356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 2, 1, 1, 1, 7].length) (baseStart_7046356 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7046356 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7046356 prefixEnd_7046356 := by exact prefixLift 7046356
  have htrace : WordTrace (prefixWord ++ tailWord_7046356) baseStart_7046356 baseEnd_7046356 := by
    simpa [prefixWord, tailWord_7046356, baseEnd_7046356] using wordTrace_append hprefix tailTrace_7046356
  have hstable : (prefixWord ++ tailWord_7046356).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7046356).length < 2 ^ (prefixWord ++ tailWord_7046356).sum := by decide
  have hdescent : baseEnd_7046356 < baseStart_7046356 := by decide
  rcases family_descends (prefixWord ++ tailWord_7046356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7046372 : List Nat := [2, 3, 1, 1, 1, 2, 2, 3, 2, 4, 2]
def baseStart_7046372 : Nat := 118140960795 + 7046372 * 2 ^ 59
def prefixEnd_7046372 : Nat := 4983230072969 + 3 ^ 40 * 7046372 * 2
def baseEnd_7046372 : Nat := 3618175706383010270844331

theorem tailTrace_7046372 : CollatzResearch.WordTrace tailWord_7046372 prefixEnd_7046372 3618175706383010270844331 := by
  unfold tailWord_7046372
  simp only [CollatzResearch.WordTrace]
  refine ⟨128501150214102571686594685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 171334866952136762248792913 128501150214102571686594685)
  ·
    refine ⟨48187931330288464382473007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 128501150214102571686594685 48187931330288464382473007)
    ·
      refine ⟨72281896995432696573709511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48187931330288464382473007 72281896995432696573709511)
      ·
        refine ⟨108422845493149044860564267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72281896995432696573709511 108422845493149044860564267)
        ·
          refine ⟨162634268239723567290846401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 108422845493149044860564267 162634268239723567290846401)
          ·
            refine ⟨121975701179792675468134801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 162634268239723567290846401 121975701179792675468134801)
            ·
              refine ⟨91481775884844506601101101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 121975701179792675468134801 91481775884844506601101101)
              ·
                refine ⟨34305665956816689975412913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 91481775884844506601101101 34305665956816689975412913)
                ·
                  refine ⟨25729249467612517481559685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34305665956816689975412913 25729249467612517481559685)
                  ·
                    refine ⟨4824234275177347027792441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25729249467612517481559685 4824234275177347027792441)
                    ·
                      refine ⟨3618175706383010270844331, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4824234275177347027792441 3618175706383010270844331)
                      ·
                        rfl

theorem cell23_7046372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 2, 3, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 2, 3, 2, 4, 2].length) (baseStart_7046372 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7046372 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7046372 prefixEnd_7046372 := by exact prefixLift 7046372
  have htrace : WordTrace (prefixWord ++ tailWord_7046372) baseStart_7046372 baseEnd_7046372 := by
    simpa [prefixWord, tailWord_7046372, baseEnd_7046372] using wordTrace_append hprefix tailTrace_7046372
  have hstable : (prefixWord ++ tailWord_7046372).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7046372).length < 2 ^ (prefixWord ++ tailWord_7046372).sum := by decide
  have hdescent : baseEnd_7046372 < baseStart_7046372 := by decide
  rcases family_descends (prefixWord ++ tailWord_7046372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7046382 : List Nat := [4, 1, 2, 1, 1, 1, 2, 4, 3, 4]
def baseStart_7046382 : Nat := 118140960795 + 7046382 * 2 ^ 59
def prefixEnd_7046382 : Nat := 4983230072969 + 3 ^ 40 * 7046382 * 2
def baseEnd_7046382 : Nat := 1206060280396518410573095

theorem tailTrace_7046382 : CollatzResearch.WordTrace tailWord_7046382 prefixEnd_7046382 1206060280396518410573095 := by
  unfold tailWord_7046382
  simp only [CollatzResearch.WordTrace]
  refine ⟨32125333144771114385131675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 171335110105445943387368933 32125333144771114385131675)
  ·
    refine ⟨48187999717156671577697513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32125333144771114385131675 48187999717156671577697513)
    ·
      refine ⟨36140999787867503683273135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48187999717156671577697513 36140999787867503683273135)
      ·
        refine ⟨54211499681801255524909703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36140999787867503683273135 54211499681801255524909703)
        ·
          refine ⟨81317249522701883287364555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54211499681801255524909703 81317249522701883287364555)
          ·
            refine ⟨121975874284052824931046833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81317249522701883287364555 121975874284052824931046833)
            ·
              refine ⟨91481905713039618698285125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 121975874284052824931046833 91481905713039618698285125)
              ·
                refine ⟨17152857321194928505928461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 91481905713039618698285125 17152857321194928505928461)
                ·
                  refine ⟨6432321495448098189723173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17152857321194928505928461 6432321495448098189723173)
                  ·
                    refine ⟨1206060280396518410573095, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6432321495448098189723173 1206060280396518410573095)
                    ·
                      rfl

theorem cell23_7046382_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 2, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 2, 4, 3, 4].length) (baseStart_7046382 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7046382 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7046382 prefixEnd_7046382 := by exact prefixLift 7046382
  have htrace : WordTrace (prefixWord ++ tailWord_7046382) baseStart_7046382 baseEnd_7046382 := by
    simpa [prefixWord, tailWord_7046382, baseEnd_7046382] using wordTrace_append hprefix tailTrace_7046382
  have hstable : (prefixWord ++ tailWord_7046382).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7046382).length < 2 ^ (prefixWord ++ tailWord_7046382).sum := by decide
  have hdescent : baseEnd_7046382 < baseStart_7046382 := by decide
  rcases family_descends (prefixWord ++ tailWord_7046382) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7046412 : List Nat := [2, 2, 1, 2, 2, 4, 2, 2, 6]
def baseStart_7046412 : Nat := 118140960795 + 7046412 * 2 ^ 59
def prefixEnd_7046412 : Nat := 4983230072969 + 3 ^ 40 * 7046412 * 2
def baseEnd_7046412 : Nat := 402021805067687790482683

theorem tailTrace_7046412 : CollatzResearch.WordTrace tailWord_7046412 prefixEnd_7046412 402021805067687790482683 := by
  unfold tailWord_7046412
  simp only [CollatzResearch.WordTrace]
  refine ⟨128501879674030115102322745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 171335839565373486803096993 128501879674030115102322745)
  ·
    refine ⟨96376409755522586326742059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 128501879674030115102322745 96376409755522586326742059)
    ·
      refine ⟨144564614633283879490113089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96376409755522586326742059 144564614633283879490113089)
      ·
        refine ⟨108423460974962909617584817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 144564614633283879490113089 108423460974962909617584817)
        ·
          refine ⟨81317595731222182213188613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 108423460974962909617584817 81317595731222182213188613)
          ·
            refine ⟨15247049199604159164972865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 81317595731222182213188613 15247049199604159164972865)
            ·
              refine ⟨11435286899703119373729649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15247049199604159164972865 11435286899703119373729649)
              ·
                refine ⟨8576465174777339530297237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11435286899703119373729649 8576465174777339530297237)
                ·
                  refine ⟨402021805067687790482683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8576465174777339530297237 402021805067687790482683)
                  ·
                    rfl

theorem cell23_7046412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 4, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 4, 2, 2, 6].length) (baseStart_7046412 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7046412 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7046412 prefixEnd_7046412 := by exact prefixLift 7046412
  have htrace : WordTrace (prefixWord ++ tailWord_7046412) baseStart_7046412 baseEnd_7046412 := by
    simpa [prefixWord, tailWord_7046412, baseEnd_7046412] using wordTrace_append hprefix tailTrace_7046412
  have hstable : (prefixWord ++ tailWord_7046412).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7046412).length < 2 ^ (prefixWord ++ tailWord_7046412).sum := by decide
  have hdescent : baseEnd_7046412 < baseStart_7046412 := by decide
  rcases family_descends (prefixWord ++ tailWord_7046412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7046449 : List Nat := [1, 2, 2, 3, 3, 2, 1, 1, 1, 5, 2]
def baseStart_7046449 : Nat := 118140960795 + 7046449 * 2 ^ 59
def prefixEnd_7046449 : Nat := 4983230072969 + 3 ^ 40 * 7046449 * 2
def baseEnd_7046449 : Nat := 3618215244393406469581477

theorem tailTrace_7046449 : CollatzResearch.WordTrace tailWord_7046449 prefixEnd_7046449 3618215244393406469581477 := by
  unfold tailWord_7046449
  simp only [CollatzResearch.WordTrace]
  refine ⟨257005108848926185523742401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171336739232617457015828267 257005108848926185523742401)
  ·
    refine ⟨192753831636694639142806801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 257005108848926185523742401 192753831636694639142806801)
    ·
      refine ⟨144565373727520979357105101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 192753831636694639142806801 144565373727520979357105101)
      ·
        refine ⟨54212015147820367258914413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 144565373727520979357105101 54212015147820367258914413)
        ·
          refine ⟨20329505680432637722092905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 54212015147820367258914413 20329505680432637722092905)
          ·
            refine ⟨15247129260324478291569679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20329505680432637722092905 15247129260324478291569679)
            ·
              refine ⟨22870693890486717437354519, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15247129260324478291569679 22870693890486717437354519)
              ·
                refine ⟨34306040835730076156031779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22870693890486717437354519 34306040835730076156031779)
                ·
                  refine ⟨51459061253595114234047669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34306040835730076156031779 51459061253595114234047669)
                  ·
                    refine ⟨4824286992524541959441969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 51459061253595114234047669 4824286992524541959441969)
                    ·
                      refine ⟨3618215244393406469581477, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4824286992524541959441969 3618215244393406469581477)
                      ·
                        rfl

theorem cell23_7046449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 2, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 2, 1, 1, 1, 5, 2].length) (baseStart_7046449 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7046449 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7046449 prefixEnd_7046449 := by exact prefixLift 7046449
  have htrace : WordTrace (prefixWord ++ tailWord_7046449) baseStart_7046449 baseEnd_7046449 := by
    simpa [prefixWord, tailWord_7046449, baseEnd_7046449] using wordTrace_append hprefix tailTrace_7046449
  have hstable : (prefixWord ++ tailWord_7046449).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7046449).length < 2 ^ (prefixWord ++ tailWord_7046449).sum := by decide
  have hdescent : baseEnd_7046449 < baseStart_7046449 := by decide
  rcases family_descends (prefixWord ++ tailWord_7046449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7046496 : List Nat := [2, 1, 1, 3, 4, 1, 2, 2, 3, 2, 2]
def baseStart_7046496 : Nat := 118140960795 + 7046496 * 2 ^ 59
def prefixEnd_7046496 : Nat := 4983230072969 + 3 ^ 40 * 7046496 * 2
def baseEnd_7046496 : Nat := 3618239377984167785693761

theorem tailTrace_7046496 : CollatzResearch.WordTrace tailWord_7046496 prefixEnd_7046496 3618239377984167785693761 := by
  unfold tailWord_7046496
  simp only [CollatzResearch.WordTrace]
  refine ⟨128503411539877956275351671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 171337882053170608367135561 128503411539877956275351671)
  ·
    refine ⟨192755117309816934413027507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128503411539877956275351671 192755117309816934413027507)
    ·
      refine ⟨289132675964725401619541261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 192755117309816934413027507 289132675964725401619541261)
      ·
        refine ⟨108424753486772025607327973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 289132675964725401619541261 108424753486772025607327973)
        ·
          refine ⟨20329641278769754801373995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 108424753486772025607327973 20329641278769754801373995)
          ·
            refine ⟨30494461918154632202060993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20329641278769754801373995 30494461918154632202060993)
            ·
              refine ⟨22870846438615974151545745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30494461918154632202060993 22870846438615974151545745)
              ·
                refine ⟨17153134828961980613659309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22870846438615974151545745 17153134828961980613659309)
                ·
                  refine ⟨6432425560860742730122241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17153134828961980613659309 6432425560860742730122241)
                  ·
                    refine ⟨4824319170645557047591681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6432425560860742730122241 4824319170645557047591681)
                    ·
                      refine ⟨3618239377984167785693761, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4824319170645557047591681 3618239377984167785693761)
                      ·
                        rfl

theorem cell23_7046496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 1, 2, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 1, 2, 2, 3, 2, 2].length) (baseStart_7046496 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7046496 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7046496 prefixEnd_7046496 := by exact prefixLift 7046496
  have htrace : WordTrace (prefixWord ++ tailWord_7046496) baseStart_7046496 baseEnd_7046496 := by
    simpa [prefixWord, tailWord_7046496, baseEnd_7046496] using wordTrace_append hprefix tailTrace_7046496
  have hstable : (prefixWord ++ tailWord_7046496).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7046496).length < 2 ^ (prefixWord ++ tailWord_7046496).sum := by decide
  have hdescent : baseEnd_7046496 < baseStart_7046496 := by decide
  rcases family_descends (prefixWord ++ tailWord_7046496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7046499 : List Nat := [1, 1, 1, 5, 2, 2, 1, 4, 1, 2, 3]
def baseStart_7046499 : Nat := 118140960795 + 7046499 * 2 ^ 59
def prefixEnd_7046499 : Nat := 4983230072969 + 3 ^ 40 * 7046499 * 2
def baseEnd_7046499 : Nat := 3618240918426131273956247

theorem tailTrace_7046499 : CollatzResearch.WordTrace tailWord_7046499 prefixEnd_7046499 3618240918426131273956247 := by
  unfold tailWord_7046499
  simp only [CollatzResearch.WordTrace]
  refine ⟨257006932498745044063062551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171337954999163362708708367 257006932498745044063062551)
  ·
    refine ⟨385510398748117566094593827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 257006932498745044063062551 385510398748117566094593827)
    ·
      refine ⟨578265598122176349141890741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 385510398748117566094593827 578265598122176349141890741)
      ·
        refine ⟨54212399823954032732052257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 578265598122176349141890741 54212399823954032732052257)
        ·
          refine ⟨40659299867965524549039193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54212399823954032732052257 40659299867965524549039193)
          ·
            refine ⟨30494474900974143411779395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40659299867965524549039193 30494474900974143411779395)
            ·
              refine ⟨45741712351461215117669093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30494474900974143411779395 45741712351461215117669093)
              ·
                refine ⟨8576571065898977834562955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 45741712351461215117669093 8576571065898977834562955)
                ·
                  refine ⟨12864856598848466751844433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8576571065898977834562955 12864856598848466751844433)
                  ·
                    refine ⟨9648642449136350063883325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12864856598848466751844433 9648642449136350063883325)
                    ·
                      refine ⟨3618240918426131273956247, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9648642449136350063883325 3618240918426131273956247)
                      ·
                        rfl

theorem cell23_7046499_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 2, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 2, 1, 4, 1, 2, 3].length) (baseStart_7046499 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7046499 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7046499 prefixEnd_7046499 := by exact prefixLift 7046499
  have htrace : WordTrace (prefixWord ++ tailWord_7046499) baseStart_7046499 baseEnd_7046499 := by
    simpa [prefixWord, tailWord_7046499, baseEnd_7046499] using wordTrace_append hprefix tailTrace_7046499
  have hstable : (prefixWord ++ tailWord_7046499).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7046499).length < 2 ^ (prefixWord ++ tailWord_7046499).sum := by decide
  have hdescent : baseEnd_7046499 < baseStart_7046499 := by decide
  rcases family_descends (prefixWord ++ tailWord_7046499) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7046512 : List Nat := [2, 1, 1, 1, 4, 2, 2, 1, 3, 3, 3]
def baseStart_7046512 : Nat := 118140960795 + 7046512 * 2 ^ 59
def prefixEnd_7046512 : Nat := 4983230072969 + 3 ^ 40 * 7046512 * 2
def baseEnd_7046512 : Nat := 3618247593674639723093687

theorem tailTrace_7046512 : CollatzResearch.WordTrace tailWord_7046512 prefixEnd_7046512 3618247593674639723093687 := by
  unfold tailWord_7046512
  simp only [CollatzResearch.WordTrace]
  refine ⟨128503703323848973641642895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 171338271098465298188857193 128503703323848973641642895)
  ·
    refine ⟨192755554985773460462464343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128503703323848973641642895 192755554985773460462464343)
    ·
      refine ⟨289133332478660190693696515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 192755554985773460462464343 289133332478660190693696515)
      ·
        refine ⟨433699998717990286040544773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 289133332478660190693696515 433699998717990286040544773)
        ·
          refine ⟨81318749759623178632602145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 433699998717990286040544773 81318749759623178632602145)
          ·
            refine ⟨60989062319717383974451609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 81318749759623178632602145 60989062319717383974451609)
            ·
              refine ⟨45741796739788037980838707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 60989062319717383974451609 45741796739788037980838707)
              ·
                refine ⟨68612695109682056971258061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45741796739788037980838707 68612695109682056971258061)
                ·
                  refine ⟨25729760666130771364221773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 68612695109682056971258061 25729760666130771364221773)
                  ·
                    refine ⟨9648660249799039261583165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25729760666130771364221773 9648660249799039261583165)
                    ·
                      refine ⟨3618247593674639723093687, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9648660249799039261583165 3618247593674639723093687)
                      ·
                        rfl

theorem cell23_7046512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 2, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 2, 1, 3, 3, 3].length) (baseStart_7046512 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7046512 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7046512 prefixEnd_7046512 := by exact prefixLift 7046512
  have htrace : WordTrace (prefixWord ++ tailWord_7046512) baseStart_7046512 baseEnd_7046512 := by
    simpa [prefixWord, tailWord_7046512, baseEnd_7046512] using wordTrace_append hprefix tailTrace_7046512
  have hstable : (prefixWord ++ tailWord_7046512).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7046512).length < 2 ^ (prefixWord ++ tailWord_7046512).sum := by decide
  have hdescent : baseEnd_7046512 < baseStart_7046512 := by decide
  rcases family_descends (prefixWord ++ tailWord_7046512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7046513 : List Nat := [1, 2, 2, 2, 1, 2, 5, 3, 1, 2, 2]
def baseStart_7046513 : Nat := 118140960795 + 7046513 * 2 ^ 59
def prefixEnd_7046513 : Nat := 4983230072969 + 3 ^ 40 * 7046513 * 2
def baseEnd_7046513 : Nat := 3618248107155294219181183

theorem tailTrace_7046513 : CollatzResearch.WordTrace tailWord_7046513 prefixEnd_7046513 3618248107155294219181183 := by
  unfold tailWord_7046513
  simp only [CollatzResearch.WordTrace]
  refine ⟨257007443120694324454072193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171338295413796216302714795 257007443120694324454072193)
  ·
    refine ⟨192755582340520743340554145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 257007443120694324454072193 192755582340520743340554145)
    ·
      refine ⟨144566686755390557505415609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 192755582340520743340554145 144566686755390557505415609)
      ·
        refine ⟨108425015066542918129061707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 144566686755390557505415609 108425015066542918129061707)
        ·
          refine ⟨162637522599814377193592561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 108425015066542918129061707 162637522599814377193592561)
          ·
            refine ⟨121978141949860782895194421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 162637522599814377193592561 121978141949860782895194421)
            ·
              refine ⟨11435450807799448396424477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 121978141949860782895194421 11435450807799448396424477)
              ·
                refine ⟨4288294052924793148659179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11435450807799448396424477 4288294052924793148659179)
                ·
                  refine ⟨6432441079387189722988769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4288294052924793148659179 6432441079387189722988769)
                  ·
                    refine ⟨4824330809540392292241577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6432441079387189722988769 4824330809540392292241577)
                    ·
                      refine ⟨3618248107155294219181183, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4824330809540392292241577 3618248107155294219181183)
                      ·
                        rfl

theorem cell23_7046513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 5, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 5, 3, 1, 2, 2].length) (baseStart_7046513 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7046513 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7046513 prefixEnd_7046513 := by exact prefixLift 7046513
  have htrace : WordTrace (prefixWord ++ tailWord_7046513) baseStart_7046513 baseEnd_7046513 := by
    simpa [prefixWord, tailWord_7046513, baseEnd_7046513] using wordTrace_append hprefix tailTrace_7046513
  have hstable : (prefixWord ++ tailWord_7046513).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7046513).length < 2 ^ (prefixWord ++ tailWord_7046513).sum := by decide
  have hdescent : baseEnd_7046513 < baseStart_7046513 := by decide
  rcases family_descends (prefixWord ++ tailWord_7046513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7046530 : List Nat := [3, 4, 2, 1, 1, 1, 3, 1, 3, 2, 2]
def baseStart_7046530 : Nat := 118140960795 + 7046530 * 2 ^ 59
def prefixEnd_7046530 : Nat := 4983230072969 + 3 ^ 40 * 7046530 * 2
def baseEnd_7046530 : Nat := 3618256836326420652668605

theorem tailTrace_7046530 : CollatzResearch.WordTrace tailWord_7046530 prefixEnd_7046530 3618256836326420652668605 := by
  unfold tailWord_7046530
  simp only [CollatzResearch.WordTrace]
  refine ⟨64252015790408184089360261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 171338708774421824238294029 64252015790408184089360261)
  ·
    refine ⟨12047252960701534516755049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 64252015790408184089360261 12047252960701534516755049)
    ·
      refine ⟨9035439720526150887566287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12047252960701534516755049 9035439720526150887566287)
      ·
        refine ⟨13553159580789226331349431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9035439720526150887566287 13553159580789226331349431)
        ·
          refine ⟨20329739371183839497024147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13553159580789226331349431 20329739371183839497024147)
          ·
            refine ⟨30494609056775759245536221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20329739371183839497024147 30494609056775759245536221)
            ·
              refine ⟨11435478396290909717076083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30494609056775759245536221 11435478396290909717076083)
              ·
                refine ⟨17153217594436364575614125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11435478396290909717076083 17153217594436364575614125)
                ·
                  refine ⟨6432456597913636715855297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17153217594436364575614125 6432456597913636715855297)
                  ·
                    refine ⟨4824342448435227536891473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6432456597913636715855297 4824342448435227536891473)
                    ·
                      refine ⟨3618256836326420652668605, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4824342448435227536891473 3618256836326420652668605)
                      ·
                        rfl

theorem cell23_7046530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 1, 3, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 1, 3, 1, 3, 2, 2].length) (baseStart_7046530 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7046530 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7046530 prefixEnd_7046530 := by exact prefixLift 7046530
  have htrace : WordTrace (prefixWord ++ tailWord_7046530) baseStart_7046530 baseEnd_7046530 := by
    simpa [prefixWord, tailWord_7046530, baseEnd_7046530] using wordTrace_append hprefix tailTrace_7046530
  have hstable : (prefixWord ++ tailWord_7046530).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7046530).length < 2 ^ (prefixWord ++ tailWord_7046530).sum := by decide
  have hdescent : baseEnd_7046530 < baseStart_7046530 := by decide
  rcases family_descends (prefixWord ++ tailWord_7046530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7046539 : List Nat := [1, 1, 1, 1, 4, 3, 2, 2, 3, 3, 2]
def baseStart_7046539 : Nat := 118140960795 + 7046539 * 2 ^ 59
def prefixEnd_7046539 : Nat := 4983230072969 + 3 ^ 40 * 7046539 * 2
def baseEnd_7046539 : Nat := 3618261457652311117456063

theorem tailTrace_7046539 : CollatzResearch.WordTrace tailWord_7046539 prefixEnd_7046539 3618261457652311117456063 := by
  unfold tailWord_7046539
  simp only [CollatzResearch.WordTrace]
  refine ⟨257008391418600130894518671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171338927612400087263012447 257008391418600130894518671)
  ·
    refine ⟨385512587127900196341778007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 257008391418600130894518671 385512587127900196341778007)
    ·
      refine ⟨578268880691850294512667011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 385512587127900196341778007 578268880691850294512667011)
      ·
        refine ⟨867403321037775441769000517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 578268880691850294512667011 867403321037775441769000517)
        ·
          refine ⟨162638122694582895331687597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 867403321037775441769000517 162638122694582895331687597)
          ·
            refine ⟨60989296010468585749382849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 162638122694582895331687597 60989296010468585749382849)
            ·
              refine ⟨45741972007851439312037137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 60989296010468585749382849 45741972007851439312037137)
              ·
                refine ⟨34306479005888579484027853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45741972007851439312037137 34306479005888579484027853)
                ·
                  refine ⟨12864929627208217306510445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34306479005888579484027853 12864929627208217306510445)
                  ·
                    refine ⟨4824348610203081489941417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12864929627208217306510445 4824348610203081489941417)
                    ·
                      refine ⟨3618261457652311117456063, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4824348610203081489941417 3618261457652311117456063)
                      ·
                        rfl

theorem cell23_7046539_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 2, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 2, 2, 3, 3, 2].length) (baseStart_7046539 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7046539 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7046539 prefixEnd_7046539 := by exact prefixLift 7046539
  have htrace : WordTrace (prefixWord ++ tailWord_7046539) baseStart_7046539 baseEnd_7046539 := by
    simpa [prefixWord, tailWord_7046539, baseEnd_7046539] using wordTrace_append hprefix tailTrace_7046539
  have hstable : (prefixWord ++ tailWord_7046539).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7046539).length < 2 ^ (prefixWord ++ tailWord_7046539).sum := by decide
  have hdescent : baseEnd_7046539 < baseStart_7046539 := by decide
  rcases family_descends (prefixWord ++ tailWord_7046539) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7046572 : List Nat := [2, 2, 1, 1, 1, 1, 6, 1, 2, 1, 5]
def baseStart_7046572 : Nat := 118140960795 + 7046572 * 2 ^ 59
def prefixEnd_7046572 : Nat := 4983230072969 + 3 ^ 40 * 7046572 * 2
def baseEnd_7046572 : Nat := 3618278402513909488343411

theorem tailTrace_7046572 : CollatzResearch.WordTrace tailWord_7046572 prefixEnd_7046572 3618278402513909488343411 := by
  unfold tailWord_7046572
  simp only [CollatzResearch.WordTrace]
  refine ⟨128504797513740288765234985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 171339730018320385020313313 128504797513740288765234985)
  ·
    refine ⟨96378598135305216573926239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 128504797513740288765234985 96378598135305216573926239)
    ·
      refine ⟨144567897202957824860889359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96378598135305216573926239 144567897202957824860889359)
      ·
        refine ⟨216851845804436737291334039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 144567897202957824860889359 216851845804436737291334039)
        ·
          refine ⟨325277768706655105937001059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 216851845804436737291334039 325277768706655105937001059)
          ·
            refine ⟨487916653059982658905501589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 325277768706655105937001059 487916653059982658905501589)
            ·
              refine ⟨22871093112186687136195387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 487916653059982658905501589 22871093112186687136195387)
              ·
                refine ⟨34306639668280030704293081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22871093112186687136195387 34306639668280030704293081)
                ·
                  refine ⟨25729979751210023028219811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34306639668280030704293081 25729979751210023028219811)
                  ·
                    refine ⟨38594969626815034542329717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 25729979751210023028219811 38594969626815034542329717)
                    ·
                      refine ⟨3618278402513909488343411, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 38594969626815034542329717 3618278402513909488343411)
                      ·
                        rfl

theorem cell23_7046572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 1, 5].length) (baseStart_7046572 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7046572 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7046572 prefixEnd_7046572 := by exact prefixLift 7046572
  have htrace : WordTrace (prefixWord ++ tailWord_7046572) baseStart_7046572 baseEnd_7046572 := by
    simpa [prefixWord, tailWord_7046572, baseEnd_7046572] using wordTrace_append hprefix tailTrace_7046572
  have hstable : (prefixWord ++ tailWord_7046572).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7046572).length < 2 ^ (prefixWord ++ tailWord_7046572).sum := by decide
  have hdescent : baseEnd_7046572 < baseStart_7046572 := by decide
  rcases family_descends (prefixWord ++ tailWord_7046572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7046637 : List Nat := [1, 5, 1, 3, 2, 2, 1, 2, 2, 2, 2]
def baseStart_7046637 : Nat := 118140960795 + 7046637 * 2 ^ 59
def prefixEnd_7046637 : Nat := 4983230072969 + 3 ^ 40 * 7046637 * 2
def baseEnd_7046637 : Nat := 3618311778756451734030613

theorem tailTrace_7046637 : CollatzResearch.WordTrace tailWord_7046637 prefixEnd_7046637 3618311778756451734030613 := by
  unfold tailWord_7046637
  simp only [CollatzResearch.WordTrace]
  refine ⟨257011965772245093631586165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171341310514830062421057443 257011965772245093631586165)
  ·
    refine ⟨24094871791147977527961203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 257011965772245093631586165 24094871791147977527961203)
    ·
      refine ⟨36142307686721966291941805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24094871791147977527961203 36142307686721966291941805)
      ·
        refine ⟨13553365382520737359478177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36142307686721966291941805 13553365382520737359478177)
        ·
          refine ⟨10165024036890553019608633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13553365382520737359478177 10165024036890553019608633)
          ·
            refine ⟨7623768027667914764706475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10165024036890553019608633 7623768027667914764706475)
            ·
              refine ⟨11435652041501872147059713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7623768027667914764706475 11435652041501872147059713)
              ·
                refine ⟨8576739031126404110294785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11435652041501872147059713 8576739031126404110294785)
                ·
                  refine ⟨6432554273344803082721089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8576739031126404110294785 6432554273344803082721089)
                  ·
                    refine ⟨4824415705008602312040817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6432554273344803082721089 4824415705008602312040817)
                    ·
                      refine ⟨3618311778756451734030613, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4824415705008602312040817 3618311778756451734030613)
                      ·
                        rfl

theorem cell23_7046637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 2, 2, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 2, 2, 1, 2, 2, 2, 2].length) (baseStart_7046637 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7046637 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7046637 prefixEnd_7046637 := by exact prefixLift 7046637
  have htrace : WordTrace (prefixWord ++ tailWord_7046637) baseStart_7046637 baseEnd_7046637 := by
    simpa [prefixWord, tailWord_7046637, baseEnd_7046637] using wordTrace_append hprefix tailTrace_7046637
  have hstable : (prefixWord ++ tailWord_7046637).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7046637).length < 2 ^ (prefixWord ++ tailWord_7046637).sum := by decide
  have hdescent : baseEnd_7046637 < baseStart_7046637 := by decide
  rcases family_descends (prefixWord ++ tailWord_7046637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7046654 : List Nat := [4, 2, 2, 3, 1, 1, 3, 1, 2, 2, 2]
def baseStart_7046654 : Nat := 118140960795 + 7046654 * 2 ^ 59
def prefixEnd_7046654 : Nat := 4983230072969 + 3 ^ 40 * 7046654 * 2
def baseEnd_7046654 : Nat := 3618320507927578167518035

theorem tailTrace_7046654 : CollatzResearch.WordTrace tailWord_7046654 prefixEnd_7046654 3618320507927578167518035 := by
  unfold tailWord_7046654
  simp only [CollatzResearch.WordTrace]
  refine ⟨32126573226647938191869377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 171341723875455670356636677 32126573226647938191869377)
  ·
    refine ⟨24094929919985953643902033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32126573226647938191869377 24094929919985953643902033)
    ·
      refine ⟨18071197439989465232926525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24094929919985953643902033 18071197439989465232926525)
      ·
        refine ⟨6776699039996049462347447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18071197439989465232926525 6776699039996049462347447)
        ·
          refine ⟨10165048559994074193521171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6776699039996049462347447 10165048559994074193521171)
          ·
            refine ⟨15247572839991111290281757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10165048559994074193521171 15247572839991111290281757)
            ·
              refine ⟨5717839814996666733855659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15247572839991111290281757 5717839814996666733855659)
              ·
                refine ⟨8576759722495000100783489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5717839814996666733855659 8576759722495000100783489)
                ·
                  refine ⟨6432569791871250075587617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8576759722495000100783489 6432569791871250075587617)
                  ·
                    refine ⟨4824427343903437556690713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6432569791871250075587617 4824427343903437556690713)
                    ·
                      refine ⟨3618320507927578167518035, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4824427343903437556690713 3618320507927578167518035)
                      ·
                        rfl

theorem cell23_7046654_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 1, 1, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 1, 1, 3, 1, 2, 2, 2].length) (baseStart_7046654 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7046654 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7046654 prefixEnd_7046654 := by exact prefixLift 7046654
  have htrace : WordTrace (prefixWord ++ tailWord_7046654) baseStart_7046654 baseEnd_7046654 := by
    simpa [prefixWord, tailWord_7046654, baseEnd_7046654] using wordTrace_append hprefix tailTrace_7046654
  have hstable : (prefixWord ++ tailWord_7046654).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7046654).length < 2 ^ (prefixWord ++ tailWord_7046654).sum := by decide
  have hdescent : baseEnd_7046654 < baseStart_7046654 := by decide
  rcases family_descends (prefixWord ++ tailWord_7046654) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7046659 : List Nat := [1, 1, 1, 3, 2, 1, 2, 3, 1, 6, 2]
def baseStart_7046659 : Nat := 118140960795 + 7046659 * 2 ^ 59
def prefixEnd_7046659 : Nat := 4983230072969 + 3 ^ 40 * 7046659 * 2
def baseEnd_7046659 : Nat := 3618323075330850647955511

theorem tailTrace_7046659 : CollatzResearch.WordTrace tailWord_7046659 prefixEnd_7046659 3618323075330850647955511 := by
  unfold tailWord_7046659
  simp only [CollatzResearch.WordTrace]
  refine ⟨257012768178165391388887031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171341845452110260925924687 257012768178165391388887031)
  ·
    refine ⟨385519152267248087083330547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 257012768178165391388887031 385519152267248087083330547)
    ·
      refine ⟨578278728400872130624995821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 385519152267248087083330547 578278728400872130624995821)
      ·
        refine ⟨216854523150327048984373433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 578278728400872130624995821 216854523150327048984373433)
        ·
          refine ⟨162640892362745286738280075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 216854523150327048984373433 162640892362745286738280075)
          ·
            refine ⟨243961338544117930107420113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 162640892362745286738280075 243961338544117930107420113)
            ·
              refine ⟨182971003908088447580565085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 243961338544117930107420113 182971003908088447580565085)
              ·
                refine ⟨68614126465533167842711907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 182971003908088447580565085 68614126465533167842711907)
                ·
                  refine ⟨102921189698299751764067861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 68614126465533167842711907 102921189698299751764067861)
                  ·
                    refine ⟨4824430767107800863940681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 102921189698299751764067861 4824430767107800863940681)
                    ·
                      refine ⟨3618323075330850647955511, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4824430767107800863940681 3618323075330850647955511)
                      ·
                        rfl

theorem cell23_7046659_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 2, 3, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 2, 3, 1, 6, 2].length) (baseStart_7046659 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7046659 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7046659 prefixEnd_7046659 := by exact prefixLift 7046659
  have htrace : WordTrace (prefixWord ++ tailWord_7046659) baseStart_7046659 baseEnd_7046659 := by
    simpa [prefixWord, tailWord_7046659, baseEnd_7046659] using wordTrace_append hprefix tailTrace_7046659
  have hstable : (prefixWord ++ tailWord_7046659).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7046659).length < 2 ^ (prefixWord ++ tailWord_7046659).sum := by decide
  have hdescent : baseEnd_7046659 < baseStart_7046659 := by decide
  rcases family_descends (prefixWord ++ tailWord_7046659) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7046716 : List Nat := [2, 2, 2, 2, 4, 1, 1, 3, 6]
def baseStart_7046716 : Nat := 118140960795 + 7046716 * 2 ^ 59
def prefixEnd_7046716 : Nat := 4983230072969 + 3 ^ 40 * 7046716 * 2
def baseEnd_7046716 : Nat := 402039149303128547215861

theorem tailTrace_7046716 : CollatzResearch.WordTrace tailWord_7046716 prefixEnd_7046716 402039149303128547215861 := by
  unfold tailWord_7046716
  simp only [CollatzResearch.WordTrace]
  refine ⟨128507423569479445061856001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 171343231425972593415808001 128507423569479445061856001)
  ·
    refine ⟨96380567677109583796392001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 128507423569479445061856001 96380567677109583796392001)
    ·
      refine ⟨72285425757832187847294001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 96380567677109583796392001 72285425757832187847294001)
      ·
        refine ⟨54214069318374140885470501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72285425757832187847294001 54214069318374140885470501)
        ·
          refine ⟨10165137997195151416025719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 54214069318374140885470501 10165137997195151416025719)
          ·
            refine ⟨15247706995792727124038579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10165137997195151416025719 15247706995792727124038579)
            ·
              refine ⟨22871560493689090686057869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15247706995792727124038579 22871560493689090686057869)
              ·
                refine ⟨8576835185133409007271701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22871560493689090686057869 8576835185133409007271701)
                ·
                  refine ⟨402039149303128547215861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8576835185133409007271701 402039149303128547215861)
                  ·
                    rfl

theorem cell23_7046716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 4, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 4, 1, 1, 3, 6].length) (baseStart_7046716 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7046716 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7046716 prefixEnd_7046716 := by exact prefixLift 7046716
  have htrace : WordTrace (prefixWord ++ tailWord_7046716) baseStart_7046716 baseEnd_7046716 := by
    simpa [prefixWord, tailWord_7046716, baseEnd_7046716] using wordTrace_append hprefix tailTrace_7046716
  have hstable : (prefixWord ++ tailWord_7046716).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7046716).length < 2 ^ (prefixWord ++ tailWord_7046716).sum := by decide
  have hdescent : baseEnd_7046716 < baseStart_7046716 := by decide
  rcases family_descends (prefixWord ++ tailWord_7046716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7046769 : List Nat := [1, 2, 2, 2, 1, 1, 1, 6, 1, 1, 5]
def baseStart_7046769 : Nat := 118140960795 + 7046769 * 2 ^ 59
def prefixEnd_7046769 : Nat := 4983230072969 + 3 ^ 40 * 7046769 * 2
def baseEnd_7046769 : Nat := 3618379558202845217580005

theorem tailTrace_7046769 : CollatzResearch.WordTrace tailWord_7046769 prefixEnd_7046769 3618379558202845217580005 := by
  unfold tailWord_7046769
  simp only [CollatzResearch.WordTrace]
  refine ⟨257016780207766880175391361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171344520138511253450260907 257016780207766880175391361)
  ·
    refine ⟨192762585155825160131543521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 257016780207766880175391361 192762585155825160131543521)
    ·
      refine ⟨144571938866868870098657641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 192762585155825160131543521 144571938866868870098657641)
      ·
        refine ⟨108428954150151652573993231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 144571938866868870098657641 108428954150151652573993231)
        ·
          refine ⟨162643431225227478860989847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 108428954150151652573993231 162643431225227478860989847)
          ·
            refine ⟨243965146837841218291484771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 162643431225227478860989847 243965146837841218291484771)
            ·
              refine ⟨365947720256761827437227157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 243965146837841218291484771 365947720256761827437227157)
              ·
                refine ⟨17153799387035710661120023, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 365947720256761827437227157 17153799387035710661120023)
                ·
                  refine ⟨25730699080553565991680035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17153799387035710661120023 25730699080553565991680035)
                  ·
                    refine ⟨38596048620830348987520053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 25730699080553565991680035 38596048620830348987520053)
                    ·
                      refine ⟨3618379558202845217580005, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 38596048620830348987520053 3618379558202845217580005)
                      ·
                        rfl

theorem cell23_7046769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 1, 6, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 1, 6, 1, 1, 5].length) (baseStart_7046769 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7046769 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7046769 prefixEnd_7046769 := by exact prefixLift 7046769
  have htrace : WordTrace (prefixWord ++ tailWord_7046769) baseStart_7046769 baseEnd_7046769 := by
    simpa [prefixWord, tailWord_7046769, baseEnd_7046769] using wordTrace_append hprefix tailTrace_7046769
  have hstable : (prefixWord ++ tailWord_7046769).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7046769).length < 2 ^ (prefixWord ++ tailWord_7046769).sum := by decide
  have hdescent : baseEnd_7046769 < baseStart_7046769 := by decide
  rcases family_descends (prefixWord ++ tailWord_7046769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7046817 : List Nat := [1, 2, 3, 3, 2, 1, 2, 4, 1, 2, 2]
def baseStart_7046817 : Nat := 118140960795 + 7046817 * 2 ^ 59
def prefixEnd_7046817 : Nat := 4983230072969 + 3 ^ 40 * 7046817 * 2
def baseEnd_7046817 : Nat := 3618404205274261029779785

theorem tailTrace_7046817 : CollatzResearch.WordTrace tailWord_7046817 prefixEnd_7046817 3618404205274261029779785 := by
  unfold tailWord_7046817
  simp only [CollatzResearch.WordTrace]
  refine ⟨257018530911592984373138705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171345687274395322915425803 257018530911592984373138705)
  ·
    refine ⟨192763898183694738279854029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 257018530911592984373138705 192763898183694738279854029)
    ·
      refine ⟨72286461818885526854945261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 192763898183694738279854029 72286461818885526854945261)
      ·
        refine ⟨27107423182082072570604473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 72286461818885526854945261 27107423182082072570604473)
        ·
          refine ⟨20330567386561554427953355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27107423182082072570604473 20330567386561554427953355)
          ·
            refine ⟨30495851079842331641930033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20330567386561554427953355 30495851079842331641930033)
            ·
              refine ⟨22871888309881748731447525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30495851079842331641930033 22871888309881748731447525)
              ·
                refine ⟨4288479058102827887146411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22871888309881748731447525 4288479058102827887146411)
                ·
                  refine ⟨6432718587154241830719617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4288479058102827887146411 6432718587154241830719617)
                  ·
                    refine ⟨4824538940365681373039713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6432718587154241830719617 4824538940365681373039713)
                    ·
                      refine ⟨3618404205274261029779785, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4824538940365681373039713 3618404205274261029779785)
                      ·
                        rfl

theorem cell23_7046817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 1, 2, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 1, 2, 4, 1, 2, 2].length) (baseStart_7046817 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7046817 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7046817 prefixEnd_7046817 := by exact prefixLift 7046817
  have htrace : WordTrace (prefixWord ++ tailWord_7046817) baseStart_7046817 baseEnd_7046817 := by
    simpa [prefixWord, tailWord_7046817, baseEnd_7046817] using wordTrace_append hprefix tailTrace_7046817
  have hstable : (prefixWord ++ tailWord_7046817).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7046817).length < 2 ^ (prefixWord ++ tailWord_7046817).sum := by decide
  have hdescent : baseEnd_7046817 < baseStart_7046817 := by decide
  rcases family_descends (prefixWord ++ tailWord_7046817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7046846 : List Nat := [4, 2, 1, 1, 2, 2, 1, 1, 2, 2, 5]
def baseStart_7046846 : Nat := 118140960795 + 7046846 * 2 ^ 59
def prefixEnd_7046846 : Nat := 4983230072969 + 3 ^ 40 * 7046846 * 2
def baseEnd_7046846 : Nat := 3618419096213241416317151

theorem tailTrace_7046846 : CollatzResearch.WordTrace tailWord_7046846 prefixEnd_7046846 3618419096213241416317151 := by
  unfold tailWord_7046846
  simp only [CollatzResearch.WordTrace]
  refine ⟨32127448578560990290743049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 171346392418991948217296261 32127448578560990290743049)
  ·
    refine ⟨24095586433920742718057287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32127448578560990290743049 24095586433920742718057287)
    ·
      refine ⟨36143379650881114077085931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24095586433920742718057287 36143379650881114077085931)
      ·
        refine ⟨54215069476321671115628897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36143379650881114077085931 54215069476321671115628897)
        ·
          refine ⟨40661302107241253336721673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54215069476321671115628897 40661302107241253336721673)
          ·
            refine ⟨30495976580430940002541255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40661302107241253336721673 30495976580430940002541255)
            ·
              refine ⟨45743964870646410003811883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30495976580430940002541255 45743964870646410003811883)
              ·
                refine ⟨68615947305969615005717825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45743964870646410003811883 68615947305969615005717825)
                ·
                  refine ⟨51461960479477211254288369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 68615947305969615005717825 51461960479477211254288369)
                  ·
                    refine ⟨38596470359607908440716277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 51461960479477211254288369 38596470359607908440716277)
                    ·
                      refine ⟨3618419096213241416317151, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 38596470359607908440716277 3618419096213241416317151)
                      ·
                        rfl

theorem cell23_7046846_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 2, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 2, 1, 1, 2, 2, 5].length) (baseStart_7046846 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7046846 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7046846 prefixEnd_7046846 := by exact prefixLift 7046846
  have htrace : WordTrace (prefixWord ++ tailWord_7046846) baseStart_7046846 baseEnd_7046846 := by
    simpa [prefixWord, tailWord_7046846, baseEnd_7046846] using wordTrace_append hprefix tailTrace_7046846
  have hstable : (prefixWord ++ tailWord_7046846).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7046846).length < 2 ^ (prefixWord ++ tailWord_7046846).sum := by decide
  have hdescent : baseEnd_7046846 < baseStart_7046846 := by decide
  rcases family_descends (prefixWord ++ tailWord_7046846) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7046906 : List Nat := [3, 1, 1, 1, 1, 3, 1, 2, 4, 3, 3]
def baseStart_7046906 : Nat := 118140960795 + 7046906 * 2 ^ 59
def prefixEnd_7046906 : Nat := 4983230072969 + 3 ^ 40 * 7046906 * 2
def baseEnd_7046906 : Nat := 3618449905052511181566875

theorem tailTrace_7046906 : CollatzResearch.WordTrace tailWord_7046906 prefixEnd_7046906 3618449905052511181566875 := by
  unfold tailWord_7046906
  simp only [CollatzResearch.WordTrace]
  refine ⟨64255444252067638143282143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 171347851338847035048752381 64255444252067638143282143)
  ·
    refine ⟨96383166378101457214923215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64255444252067638143282143 96383166378101457214923215)
    ·
      refine ⟨144574749567152185822384823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96383166378101457214923215 144574749567152185822384823)
      ·
        refine ⟨216862124350728278733577235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 144574749567152185822384823 216862124350728278733577235)
        ·
          refine ⟨325293186526092418100365853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 216862124350728278733577235 325293186526092418100365853)
          ·
            refine ⟨121984944947284656787637195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 325293186526092418100365853 121984944947284656787637195)
            ·
              refine ⟨182977417420926985181455793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 121984944947284656787637195 182977417420926985181455793)
              ·
                refine ⟨137233063065695238886091845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 182977417420926985181455793 137233063065695238886091845)
                ·
                  refine ⟨25731199324817857291142221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 137233063065695238886091845 25731199324817857291142221)
                  ·
                    refine ⟨9649199746806696484178333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25731199324817857291142221 9649199746806696484178333)
                    ·
                      refine ⟨3618449905052511181566875, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9649199746806696484178333 3618449905052511181566875)
                      ·
                        rfl

theorem cell23_7046906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 1, 2, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 1, 2, 4, 3, 3].length) (baseStart_7046906 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7046906 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7046906 prefixEnd_7046906 := by exact prefixLift 7046906
  have htrace : WordTrace (prefixWord ++ tailWord_7046906) baseStart_7046906 baseEnd_7046906 := by
    simpa [prefixWord, tailWord_7046906, baseEnd_7046906] using wordTrace_append hprefix tailTrace_7046906
  have hstable : (prefixWord ++ tailWord_7046906).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7046906).length < 2 ^ (prefixWord ++ tailWord_7046906).sum := by decide
  have hdescent : baseEnd_7046906 < baseStart_7046906 := by decide
  rcases family_descends (prefixWord ++ tailWord_7046906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7046933 : List Nat := [1, 3, 2, 1, 2, 3, 1, 1, 2, 5, 2]
def baseStart_7046933 : Nat := 118140960795 + 7046933 * 2 ^ 59
def prefixEnd_7046933 : Nat := 4983230072969 + 3 ^ 40 * 7046933 * 2
def baseEnd_7046933 : Nat := 3618463769030182575929251

theorem tailTrace_7046933 : CollatzResearch.WordTrace tailWord_7046933 prefixEnd_7046933 3618463769030182575929251 := by
  unfold tailWord_7046933
  simp only [CollatzResearch.WordTrace]
  refine ⟨257022761779172736184361453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171348507852781824122907635 257022761779172736184361453)
  ·
    refine ⟨96383535667189776069135545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 257022761779172736184361453 96383535667189776069135545)
    ·
      refine ⟨72287651750392332051851659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 96383535667189776069135545 72287651750392332051851659)
      ·
        refine ⟨108431477625588498077777489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72287651750392332051851659 108431477625588498077777489)
        ·
          refine ⟨81323608219191373558333117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 108431477625588498077777489 81323608219191373558333117)
          ·
            refine ⟨30496353082196765084374919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 81323608219191373558333117 30496353082196765084374919)
            ·
              refine ⟨45744529623295147626562379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30496353082196765084374919 45744529623295147626562379)
              ·
                refine ⟨68616794434942721439843569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45744529623295147626562379 68616794434942721439843569)
                ·
                  refine ⟨51462595826207041079882677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 68616794434942721439843569 51462595826207041079882677)
                  ·
                    refine ⟨4824618358706910101239001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 51462595826207041079882677 4824618358706910101239001)
                    ·
                      refine ⟨3618463769030182575929251, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4824618358706910101239001 3618463769030182575929251)
                      ·
                        rfl

theorem cell23_7046933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 3, 1, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 3, 1, 1, 2, 5, 2].length) (baseStart_7046933 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7046933 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7046933 prefixEnd_7046933 := by exact prefixLift 7046933
  have htrace : WordTrace (prefixWord ++ tailWord_7046933) baseStart_7046933 baseEnd_7046933 := by
    simpa [prefixWord, tailWord_7046933, baseEnd_7046933] using wordTrace_append hprefix tailTrace_7046933
  have hstable : (prefixWord ++ tailWord_7046933).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7046933).length < 2 ^ (prefixWord ++ tailWord_7046933).sum := by decide
  have hdescent : baseEnd_7046933 < baseStart_7046933 := by decide
  rcases family_descends (prefixWord ++ tailWord_7046933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7046936 : List Nat := [2, 1, 2, 3, 1, 1, 4, 1, 1, 2, 5]
def baseStart_7046936 : Nat := 118140960795 + 7046936 * 2 ^ 59
def prefixEnd_7046936 : Nat := 4983230072969 + 3 ^ 40 * 7046936 * 2
def baseEnd_7046936 : Nat := 3618465309472146064191737

theorem tailTrace_7046936 : CollatzResearch.WordTrace tailWord_7046936 prefixEnd_7046936 3618465309472146064191737 := by
  unfold tailWord_7046936
  simp only [CollatzResearch.WordTrace]
  refine ⟨128511435599080933848360331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 171348580798774578464480441 128511435599080933848360331)
  ·
    refine ⟨192767153398621400772540497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128511435599080933848360331 192767153398621400772540497)
    ·
      refine ⟨144575365048966050579405373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 192767153398621400772540497 144575365048966050579405373)
      ·
        refine ⟨54215761893362268967277015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 144575365048966050579405373 54215761893362268967277015)
        ·
          refine ⟨81323642840043403450915523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54215761893362268967277015 81323642840043403450915523)
          ·
            refine ⟨121985464260065105176373285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81323642840043403450915523 121985464260065105176373285)
            ·
              refine ⟨22872274548762207220569991, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 121985464260065105176373285 22872274548762207220569991)
              ·
                refine ⟨34308411823143310830854987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22872274548762207220569991 34308411823143310830854987)
                ·
                  refine ⟨51462617734714966246282481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34308411823143310830854987 51462617734714966246282481)
                  ·
                    refine ⟨38596963301036224684711861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 51462617734714966246282481 38596963301036224684711861)
                    ·
                      refine ⟨3618465309472146064191737, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 38596963301036224684711861 3618465309472146064191737)
                      ·
                        rfl

theorem cell23_7046936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 4, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 4, 1, 1, 2, 5].length) (baseStart_7046936 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7046936 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7046936 prefixEnd_7046936 := by exact prefixLift 7046936
  have htrace : WordTrace (prefixWord ++ tailWord_7046936) baseStart_7046936 baseEnd_7046936 := by
    simpa [prefixWord, tailWord_7046936, baseEnd_7046936] using wordTrace_append hprefix tailTrace_7046936
  have hstable : (prefixWord ++ tailWord_7046936).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7046936).length < 2 ^ (prefixWord ++ tailWord_7046936).sum := by decide
  have hdescent : baseEnd_7046936 < baseStart_7046936 := by decide
  rcases family_descends (prefixWord ++ tailWord_7046936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7046963 : List Nat := [1, 1, 1, 2, 7, 1, 1, 1, 1, 3, 4]
def baseStart_7046963 : Nat := 118140960795 + 7046963 * 2 ^ 59
def prefixEnd_7046963 : Nat := 4983230072969 + 3 ^ 40 * 7046963 * 2
def baseEnd_7046963 : Nat := 3618479173449817458554113

theorem tailTrace_7046963 : CollatzResearch.WordTrace tailWord_7046963 prefixEnd_7046963 3618479173449817458554113 := by
  unfold tailWord_7046963
  simp only [CollatzResearch.WordTrace]
  refine ⟨257023855969064051307953543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171349237312709367538635695 257023855969064051307953543)
  ·
    refine ⟨385535783953596076961930315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 257023855969064051307953543 385535783953596076961930315)
    ·
      refine ⟨578303675930394115442895473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 385535783953596076961930315 578303675930394115442895473)
      ·
        refine ⟨433727756947795586582171605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 578303675930394115442895473 433727756947795586582171605)
        ·
          refine ⟨10165494303463959060519647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 433727756947795586582171605 10165494303463959060519647)
          ·
            refine ⟨15248241455195938590779471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10165494303463959060519647 15248241455195938590779471)
            ·
              refine ⟨22872362182793907886169207, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15248241455195938590779471 22872362182793907886169207)
              ·
                refine ⟨34308543274190861829253811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22872362182793907886169207 34308543274190861829253811)
                ·
                  refine ⟨51462814911286292743880717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34308543274190861829253811 51462814911286292743880717)
                  ·
                    refine ⟨19298555591732359778955269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 51462814911286292743880717 19298555591732359778955269)
                    ·
                      refine ⟨3618479173449817458554113, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19298555591732359778955269 3618479173449817458554113)
                      ·
                        rfl

theorem cell23_7046963_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 7, 1, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 7, 1, 1, 1, 1, 3, 4].length) (baseStart_7046963 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7046963 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7046963 prefixEnd_7046963 := by exact prefixLift 7046963
  have htrace : WordTrace (prefixWord ++ tailWord_7046963) baseStart_7046963 baseEnd_7046963 := by
    simpa [prefixWord, tailWord_7046963, baseEnd_7046963] using wordTrace_append hprefix tailTrace_7046963
  have hstable : (prefixWord ++ tailWord_7046963).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7046963).length < 2 ^ (prefixWord ++ tailWord_7046963).sum := by decide
  have hdescent : baseEnd_7046963 < baseStart_7046963 := by decide
  rcases family_descends (prefixWord ++ tailWord_7046963) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7046983 : List Nat := [1, 1, 4, 1, 2, 1, 2, 4, 2, 2, 3]
def baseStart_7046983 : Nat := 118140960795 + 7046983 * 2 ^ 59
def prefixEnd_7046983 : Nat := 4983230072969 + 3 ^ 40 * 7046983 * 2
def baseEnd_7046983 : Nat := 3618489443062907380304021

theorem tailTrace_7046983 : CollatzResearch.WordTrace tailWord_7046983 prefixEnd_7046983 3618489443062907380304021 := by
  unfold tailWord_7046983
  simp only [CollatzResearch.WordTrace]
  refine ⟨257024585428991594723681603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171349723619327729815787735 257024585428991594723681603)
  ·
    refine ⟨385536878143487392085522405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 257024585428991594723681603 385536878143487392085522405)
    ·
      refine ⟨72288164651903886016035451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 385536878143487392085522405 72288164651903886016035451)
      ·
        refine ⟨108432246977855829024053177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72288164651903886016035451 108432246977855829024053177)
        ·
          refine ⟨81324185233391871768039883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 108432246977855829024053177 81324185233391871768039883)
          ·
            refine ⟨121986277850087807652059825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81324185233391871768039883 121986277850087807652059825)
            ·
              refine ⟨91489708387565855739044869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 121986277850087807652059825 91489708387565855739044869)
              ·
                refine ⟨17154320322668597951070913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 91489708387565855739044869 17154320322668597951070913)
                ·
                  refine ⟨12865740242001448463303185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17154320322668597951070913 12865740242001448463303185)
                  ·
                    refine ⟨9649305181501086347477389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12865740242001448463303185 9649305181501086347477389)
                    ·
                      refine ⟨3618489443062907380304021, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9649305181501086347477389 3618489443062907380304021)
                      ·
                        rfl

theorem cell23_7046983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 2, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 2, 4, 2, 2, 3].length) (baseStart_7046983 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7046983 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7046983 prefixEnd_7046983 := by exact prefixLift 7046983
  have htrace : WordTrace (prefixWord ++ tailWord_7046983) baseStart_7046983 baseEnd_7046983 := by
    simpa [prefixWord, tailWord_7046983, baseEnd_7046983] using wordTrace_append hprefix tailTrace_7046983
  have hstable : (prefixWord ++ tailWord_7046983).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7046983).length < 2 ^ (prefixWord ++ tailWord_7046983).sum := by decide
  have hdescent : baseEnd_7046983 < baseStart_7046983 := by decide
  rcases family_descends (prefixWord ++ tailWord_7046983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7046986 : List Nat := [3, 1, 2, 1, 1, 1, 5, 1, 8]
def baseStart_7046986 : Nat := 118140960795 + 7046986 * 2 ^ 59
def prefixEnd_7046986 : Nat := 4983230072969 + 3 ^ 40 * 7046986 * 2
def baseEnd_7046986 : Nat := 402054553722763429840723

theorem tailTrace_7046986 : CollatzResearch.WordTrace tailWord_7046986 prefixEnd_7046986 402054553722763429840723 := by
  unfold tailWord_7046986
  simp only [CollatzResearch.WordTrace]
  refine ⟨64256173711995181559010203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 171349796565320484157360541 64256173711995181559010203)
  ·
    refine ⟨96384260567992772338515305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64256173711995181559010203 96384260567992772338515305)
    ·
      refine ⟨72288195425994579253886479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 96384260567992772338515305 72288195425994579253886479)
      ·
        refine ⟨108432293138991868880829719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72288195425994579253886479 108432293138991868880829719)
        ·
          refine ⟨162648439708487803321244579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 108432293138991868880829719 162648439708487803321244579)
          ·
            refine ⟨243972659562731704981866869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 162648439708487803321244579 243972659562731704981866869)
            ·
              refine ⟨22872436834006097342050019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 243972659562731704981866869 22872436834006097342050019)
              ·
                refine ⟨34308655251009146013075029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22872436834006097342050019 34308655251009146013075029)
                ·
                  refine ⟨402054553722763429840723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 34308655251009146013075029 402054553722763429840723)
                  ·
                    rfl

theorem cell23_7046986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 5, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 5, 1, 8].length) (baseStart_7046986 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7046986 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7046986 prefixEnd_7046986 := by exact prefixLift 7046986
  have htrace : WordTrace (prefixWord ++ tailWord_7046986) baseStart_7046986 baseEnd_7046986 := by
    simpa [prefixWord, tailWord_7046986, baseEnd_7046986] using wordTrace_append hprefix tailTrace_7046986
  have hstable : (prefixWord ++ tailWord_7046986).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7046986).length < 2 ^ (prefixWord ++ tailWord_7046986).sum := by decide
  have hdescent : baseEnd_7046986 < baseStart_7046986 := by decide
  rcases family_descends (prefixWord ++ tailWord_7046986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7047033 : List Nat := [1, 2, 1, 3, 2, 2, 1, 5, 1, 5]
def baseStart_7047033 : Nat := 118140960795 + 7047033 * 2 ^ 59
def prefixEnd_7047033 : Nat := 4983230072969 + 3 ^ 40 * 7047033 * 2
def baseEnd_7047033 : Nat := 1206171705698544061559597

theorem tailTrace_7047033 : CollatzResearch.WordTrace tailWord_7047033 prefixEnd_7047033 1206171705698544061559597 := by
  unfold tailWord_7047033
  simp only [CollatzResearch.WordTrace]
  refine ⟨257026409078810453263001753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171350939385873635508667835 257026409078810453263001753)
  ·
    refine ⟨192769806809107839947251315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 257026409078810453263001753 192769806809107839947251315)
    ·
      refine ⟨289154710213661759920876973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 192769806809107839947251315 289154710213661759920876973)
      ·
        refine ⟨108433016330123159970328865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 289154710213661759920876973 108433016330123159970328865)
        ·
          refine ⟨81324762247592369977746649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 108433016330123159970328865 81324762247592369977746649)
          ·
            refine ⟨60993571685694277483309987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 81324762247592369977746649 60993571685694277483309987)
            ·
              refine ⟨91490357528541416224964981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60993571685694277483309987 91490357528541416224964981)
              ·
                refine ⟨8577221018300757771090467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 91490357528541416224964981 8577221018300757771090467)
                ·
                  refine ⟨12865831527451136656635701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8577221018300757771090467 12865831527451136656635701)
                  ·
                    refine ⟨1206171705698544061559597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12865831527451136656635701 1206171705698544061559597)
                    ·
                      rfl

theorem cell23_7047033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 1, 5, 1, 5].length) (baseStart_7047033 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7047033 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7047033 prefixEnd_7047033 := by exact prefixLift 7047033
  have htrace : WordTrace (prefixWord ++ tailWord_7047033) baseStart_7047033 baseEnd_7047033 := by
    simpa [prefixWord, tailWord_7047033, baseEnd_7047033] using wordTrace_append hprefix tailTrace_7047033
  have hstable : (prefixWord ++ tailWord_7047033).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7047033).length < 2 ^ (prefixWord ++ tailWord_7047033).sum := by decide
  have hdescent : baseEnd_7047033 < baseStart_7047033 := by decide
  rcases family_descends (prefixWord ++ tailWord_7047033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7047040 : List Nat := [2, 1, 1, 2, 1, 2, 5, 2, 2, 3, 2]
def baseStart_7047040 : Nat := 118140960795 + 7047040 * 2 ^ 59
def prefixEnd_7047040 : Nat := 4983230072969 + 3 ^ 40 * 7047040 * 2
def baseEnd_7047040 : Nat := 3618518711460213657291259

theorem tailTrace_7047040 : CollatzResearch.WordTrace tailWord_7047040 prefixEnd_7047040 3618518711460213657291259 := by
  unfold tailWord_7047040
  simp only [CollatzResearch.WordTrace]
  refine ⟨128513332194892546729253287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 171351109593190062305671049 128513332194892546729253287)
  ·
    refine ⟨192769998292338820093879931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128513332194892546729253287 192769998292338820093879931)
    ·
      refine ⟨289154997438508230140819897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 192769998292338820093879931 289154997438508230140819897)
      ·
        refine ⟨216866248078881172605614923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 289154997438508230140819897 216866248078881172605614923)
        ·
          refine ⟨325299372118321758908422385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 216866248078881172605614923 325299372118321758908422385)
          ·
            refine ⟨243974529088741319181316789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 325299372118321758908422385 243974529088741319181316789)
            ·
              refine ⟨22872612102069498673248449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 243974529088741319181316789 22872612102069498673248449)
              ·
                refine ⟨17154459076552124004936337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22872612102069498673248449 17154459076552124004936337)
                ·
                  refine ⟨12865844307414093003702253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17154459076552124004936337 12865844307414093003702253)
                  ·
                    refine ⟨4824691615280284876388345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12865844307414093003702253 4824691615280284876388345)
                    ·
                      refine ⟨3618518711460213657291259, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4824691615280284876388345 3618518711460213657291259)
                      ·
                        rfl

theorem cell23_7047040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 5, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 5, 2, 2, 3, 2].length) (baseStart_7047040 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7047040 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7047040 prefixEnd_7047040 := by exact prefixLift 7047040
  have htrace : WordTrace (prefixWord ++ tailWord_7047040) baseStart_7047040 baseEnd_7047040 := by
    simpa [prefixWord, tailWord_7047040, baseEnd_7047040] using wordTrace_append hprefix tailTrace_7047040
  have hstable : (prefixWord ++ tailWord_7047040).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7047040).length < 2 ^ (prefixWord ++ tailWord_7047040).sum := by decide
  have hdescent : baseEnd_7047040 < baseStart_7047040 := by decide
  rcases family_descends (prefixWord ++ tailWord_7047040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7047041 : List Nat := [1, 2, 4, 4, 1, 1, 3, 2, 1, 4]
def baseStart_7047041 : Nat := 118140960795 + 7047041 * 2 ^ 59
def prefixEnd_7047041 : Nat := 4983230072969 + 3 ^ 40 * 7047041 * 2
def baseEnd_7047041 : Nat := 1206173074980289384459585

theorem tailTrace_7047041 : CollatzResearch.WordTrace tailWord_7047041 prefixEnd_7047041 1206173074980289384459585 := by
  unfold tailWord_7047041
  simp only [CollatzResearch.WordTrace]
  refine ⟨257026700862781470629292977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171351133908520980419528651 257026700862781470629292977)
  ·
    refine ⟨192770025647086102971969733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 257026700862781470629292977 192770025647086102971969733)
    ·
      refine ⟨36144379808828644307244325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 192770025647086102971969733 36144379808828644307244325)
      ·
        refine ⟨6777071214155370807608311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 36144379808828644307244325 6777071214155370807608311)
        ·
          refine ⟨10165606821233056211412467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6777071214155370807608311 10165606821233056211412467)
          ·
            refine ⟨15248410231849584317118701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10165606821233056211412467 15248410231849584317118701)
            ·
              refine ⟨5718153836943594118919513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15248410231849584317118701 5718153836943594118919513)
              ·
                refine ⟨4288615377707695589189635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5718153836943594118919513 4288615377707695589189635)
                ·
                  refine ⟨6432923066561543383784453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4288615377707695589189635 6432923066561543383784453)
                  ·
                    refine ⟨1206173074980289384459585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6432923066561543383784453 1206173074980289384459585)
                    ·
                      rfl

theorem cell23_7047041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 1, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 1, 1, 3, 2, 1, 4].length) (baseStart_7047041 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7047041 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7047041 prefixEnd_7047041 := by exact prefixLift 7047041
  have htrace : WordTrace (prefixWord ++ tailWord_7047041) baseStart_7047041 baseEnd_7047041 := by
    simpa [prefixWord, tailWord_7047041, baseEnd_7047041] using wordTrace_append hprefix tailTrace_7047041
  have hstable : (prefixWord ++ tailWord_7047041).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7047041).length < 2 ^ (prefixWord ++ tailWord_7047041).sum := by decide
  have hdescent : baseEnd_7047041 < baseStart_7047041 := by decide
  rcases family_descends (prefixWord ++ tailWord_7047041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7047054 : List Nat := [4, 1, 1, 5, 1, 2, 2, 1, 6]
def baseStart_7047054 : Nat := 118140960795 + 7047054 * 2 ^ 59
def prefixEnd_7047054 : Nat := 4983230072969 + 3 ^ 40 * 7047054 * 2
def baseEnd_7047054 : Nat := 402058433354375178057355

theorem tailTrace_7047054 : CollatzResearch.WordTrace tailWord_7047054 prefixEnd_7047054 402058433354375178057355 := by
  unfold tailWord_7047054
  simp only [CollatzResearch.WordTrace]
  refine ⟨32128396876466796731189527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 171351450007822915899677477 32128396876466796731189527)
  ·
    refine ⟨48192595314700195096784291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32128396876466796731189527 48192595314700195096784291)
    ·
      refine ⟨72288892972050292645176437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48192595314700195096784291 72288892972050292645176437)
      ·
        refine ⟨6777083716129714935485291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 72288892972050292645176437 6777083716129714935485291)
        ·
          refine ⟨10165625574194572403227937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6777083716129714935485291 10165625574194572403227937)
          ·
            refine ⟨7624219180645929302420953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10165625574194572403227937 7624219180645929302420953)
            ·
              refine ⟨5718164385484446976815715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7624219180645929302420953 5718164385484446976815715)
              ·
                refine ⟨8577246578226670465223573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5718164385484446976815715 8577246578226670465223573)
                ·
                  refine ⟨402058433354375178057355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8577246578226670465223573 402058433354375178057355)
                  ·
                    rfl

theorem cell23_7047054_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 1, 2, 2, 1, 6].length) (baseStart_7047054 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7047054 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7047054 prefixEnd_7047054 := by exact prefixLift 7047054
  have htrace : WordTrace (prefixWord ++ tailWord_7047054) baseStart_7047054 baseEnd_7047054 := by
    simpa [prefixWord, tailWord_7047054, baseEnd_7047054] using wordTrace_append hprefix tailTrace_7047054
  have hstable : (prefixWord ++ tailWord_7047054).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7047054).length < 2 ^ (prefixWord ++ tailWord_7047054).sum := by decide
  have hdescent : baseEnd_7047054 < baseStart_7047054 := by decide
  rcases family_descends (prefixWord ++ tailWord_7047054) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7047074 : List Nat := [3, 3, 1, 2, 3, 1, 2, 1, 2, 3, 2]
def baseStart_7047074 : Nat := 118140960795 + 7047074 * 2 ^ 59
def prefixEnd_7047074 : Nat := 4983230072969 + 3 ^ 40 * 7047074 * 2
def baseEnd_7047074 : Nat := 3618536169802466524266103

theorem tailTrace_7047074 : CollatzResearch.WordTrace tailWord_7047074 prefixEnd_7047074 3618536169802466524266103 := by
  unfold tailWord_7047074
  simp only [CollatzResearch.WordTrace]
  refine ⟨64256976117915479316311069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 171351936314441278176829517 64256976117915479316311069)
  ·
    refine ⟨24096366044218304743616651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 64256976117915479316311069 24096366044218304743616651)
    ·
      refine ⟨36144549066327457115424977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24096366044218304743616651 36144549066327457115424977)
      ·
        refine ⟨27108411799745592836568733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36144549066327457115424977 27108411799745592836568733)
        ·
          refine ⟨10165654424904597313713275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27108411799745592836568733 10165654424904597313713275)
          ·
            refine ⟨15248481637356895970569913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10165654424904597313713275 15248481637356895970569913)
            ·
              refine ⟨11436361228017671977927435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15248481637356895970569913 11436361228017671977927435)
              ·
                refine ⟨17154541842026507966891153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11436361228017671977927435 17154541842026507966891153)
                ·
                  refine ⟨12865906381519880975168365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17154541842026507966891153 12865906381519880975168365)
                  ·
                    refine ⟨4824714893069955365688137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12865906381519880975168365 4824714893069955365688137)
                    ·
                      refine ⟨3618536169802466524266103, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4824714893069955365688137 3618536169802466524266103)
                      ·
                        rfl

theorem cell23_7047074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 3, 1, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 3, 1, 2, 1, 2, 3, 2].length) (baseStart_7047074 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7047074 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7047074 prefixEnd_7047074 := by exact prefixLift 7047074
  have htrace : WordTrace (prefixWord ++ tailWord_7047074) baseStart_7047074 baseEnd_7047074 := by
    simpa [prefixWord, tailWord_7047074, baseEnd_7047074] using wordTrace_append hprefix tailTrace_7047074
  have hstable : (prefixWord ++ tailWord_7047074).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7047074).length < 2 ^ (prefixWord ++ tailWord_7047074).sum := by decide
  have hdescent : baseEnd_7047074 < baseStart_7047074 := by decide
  rcases family_descends (prefixWord ++ tailWord_7047074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7047090 : List Nat := [3, 2, 1, 1, 1, 1, 1, 7, 1, 2, 3]
def baseStart_7047090 : Nat := 118140960795 + 7047090 * 2 ^ 59
def prefixEnd_7047090 : Nat := 4983230072969 + 3 ^ 40 * 7047090 * 2
def baseEnd_7047090 : Nat := 3618544385492938461666029

theorem tailTrace_7047090 : CollatzResearch.WordTrace tailWord_7047090 prefixEnd_7047090 3618544385492938461666029 := by
  unfold tailWord_7047090
  simp only [CollatzResearch.WordTrace]
  refine ⟨64257122009900987999456681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 171352325359735967998551149 64257122009900987999456681)
  ·
    refine ⟨48192841507425740999592511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64257122009900987999456681 48192841507425740999592511)
    ·
      refine ⟨72289262261138611499388767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48192841507425740999592511 72289262261138611499388767)
      ·
        refine ⟨108433893391707917249083151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72289262261138611499388767 108433893391707917249083151)
        ·
          refine ⟨162650840087561875873624727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 108433893391707917249083151 162650840087561875873624727)
          ·
            refine ⟨243976260131342813810437091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 162650840087561875873624727 243976260131342813810437091)
            ·
              refine ⟨365964390197014220715655637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 243976260131342813810437091 365964390197014220715655637)
              ·
                refine ⟨8577290395242520798023179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 365964390197014220715655637 8577290395242520798023179)
                ·
                  refine ⟨12865935592863781197034769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8577290395242520798023179 12865935592863781197034769)
                  ·
                    refine ⟨9649451694647835897776077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12865935592863781197034769 9649451694647835897776077)
                    ·
                      refine ⟨3618544385492938461666029, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9649451694647835897776077 3618544385492938461666029)
                      ·
                        rfl

theorem cell23_7047090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 1, 7, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 1, 7, 1, 2, 3].length) (baseStart_7047090 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7047090 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7047090 prefixEnd_7047090 := by exact prefixLift 7047090
  have htrace : WordTrace (prefixWord ++ tailWord_7047090) baseStart_7047090 baseEnd_7047090 := by
    simpa [prefixWord, tailWord_7047090, baseEnd_7047090] using wordTrace_append hprefix tailTrace_7047090
  have hstable : (prefixWord ++ tailWord_7047090).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7047090).length < 2 ^ (prefixWord ++ tailWord_7047090).sum := by decide
  have hdescent : baseEnd_7047090 < baseStart_7047090 := by decide
  rcases family_descends (prefixWord ++ tailWord_7047090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7047103 : List Nat := [1, 1, 2, 2, 2, 1, 3, 2, 3, 3, 3]
def baseStart_7047103 : Nat := 118140960795 + 7047103 * 2 ^ 59
def prefixEnd_7047103 : Nat := 4983230072969 + 3 ^ 40 * 7047103 * 2
def baseEnd_7047103 : Nat := 3618551060741446910803469

theorem tailTrace_7047103 : CollatzResearch.WordTrace tailWord_7047103 prefixEnd_7047103 3618551060741446910803469 := by
  unfold tailWord_7047103
  simp only [CollatzResearch.WordTrace]
  refine ⟨257028962188556855218049963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171352641459037903478699975 257028962188556855218049963)
  ·
    refine ⟨385543443282835282827074945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 257028962188556855218049963 385543443282835282827074945)
    ·
      refine ⟨289157582462126462120306209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 385543443282835282827074945 289157582462126462120306209)
      ·
        refine ⟨216868186846594846590229657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 289157582462126462120306209 216868186846594846590229657)
        ·
          refine ⟨162651140134946134942672243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 216868186846594846590229657 162651140134946134942672243)
          ·
            refine ⟨243976710202419202414008365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 162651140134946134942672243 243976710202419202414008365)
            ·
              refine ⟨91491266325907200905253137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 243976710202419202414008365 91491266325907200905253137)
              ·
                refine ⟨68618449744430400678939853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 91491266325907200905253137 68618449744430400678939853)
                ·
                  refine ⟨25731918654161400254602445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 68618449744430400678939853 25731918654161400254602445)
                  ·
                    refine ⟨9649469495310525095475917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25731918654161400254602445 9649469495310525095475917)
                    ·
                      refine ⟨3618551060741446910803469, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9649469495310525095475917 3618551060741446910803469)
                      ·
                        rfl

theorem cell23_7047103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 3, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 3, 2, 3, 3, 3].length) (baseStart_7047103 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7047103 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7047103 prefixEnd_7047103 := by exact prefixLift 7047103
  have htrace : WordTrace (prefixWord ++ tailWord_7047103) baseStart_7047103 baseEnd_7047103 := by
    simpa [prefixWord, tailWord_7047103, baseEnd_7047103] using wordTrace_append hprefix tailTrace_7047103
  have hstable : (prefixWord ++ tailWord_7047103).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7047103).length < 2 ^ (prefixWord ++ tailWord_7047103).sum := by decide
  have hdescent : baseEnd_7047103 < baseStart_7047103 := by decide
  rcases family_descends (prefixWord ++ tailWord_7047103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7047104 : List Nat := [2, 1, 1, 2, 3, 2, 3, 4, 1, 2, 2]
def baseStart_7047104 : Nat := 118140960795 + 7047104 * 2 ^ 59
def prefixEnd_7047104 : Nat := 4983230072969 + 3 ^ 40 * 7047104 * 2
def baseEnd_7047104 : Nat := 3618551574222101406890965

theorem tailTrace_7047104 : CollatzResearch.WordTrace tailWord_7047104 prefixEnd_7047104 3618551574222101406890965 := by
  unfold tailWord_7047104
  simp only [CollatzResearch.WordTrace]
  refine ⟨128514499330776616194418183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 171352665774368821592557577 128514499330776616194418183)
  ·
    refine ⟨192771748996164924291627275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128514499330776616194418183 192771748996164924291627275)
    ·
      refine ⟨289157623494247386437440913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 192771748996164924291627275 289157623494247386437440913)
      ·
        refine ⟨216868217620685539828080685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 289157623494247386437440913 216868217620685539828080685)
        ·
          refine ⟨81325581607757077435530257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 216868217620685539828080685 81325581607757077435530257)
          ·
            refine ⟨60994186205817808076647693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 81325581607757077435530257 60994186205817808076647693)
            ·
              refine ⟨22872819827181678028742885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 60994186205817808076647693 22872819827181678028742885)
              ·
                refine ⟨4288653717596564630389291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22872819827181678028742885 4288653717596564630389291)
                ·
                  refine ⟨6432980576394846945583937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4288653717596564630389291 6432980576394846945583937)
                  ·
                    refine ⟨4824735432296135209187953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6432980576394846945583937 4824735432296135209187953)
                    ·
                      refine ⟨3618551574222101406890965, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4824735432296135209187953 3618551574222101406890965)
                      ·
                        rfl

theorem cell23_7047104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 3, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 3, 4, 1, 2, 2].length) (baseStart_7047104 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7047104 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7047104 prefixEnd_7047104 := by exact prefixLift 7047104
  have htrace : WordTrace (prefixWord ++ tailWord_7047104) baseStart_7047104 baseEnd_7047104 := by
    simpa [prefixWord, tailWord_7047104, baseEnd_7047104] using wordTrace_append hprefix tailTrace_7047104
  have hstable : (prefixWord ++ tailWord_7047104).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7047104).length < 2 ^ (prefixWord ++ tailWord_7047104).sum := by decide
  have hdescent : baseEnd_7047104 < baseStart_7047104 := by decide
  rcases family_descends (prefixWord ++ tailWord_7047104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7047138 : List Nat := [3, 3, 3, 1, 3, 1, 2, 1, 1, 1, 4]
def baseStart_7047138 : Nat := 118140960795 + 7047138 * 2 ^ 59
def prefixEnd_7047138 : Nat := 4983230072969 + 3 ^ 40 * 7047138 * 2
def baseEnd_7047138 : Nat := 3618569032564354273865809

theorem tailTrace_7047138 : CollatzResearch.WordTrace tailWord_7047138 prefixEnd_7047138 3618569032564354273865809 := by
  unfold tailWord_7047138
  simp only [CollatzResearch.WordTrace]
  refine ⟨64257559685857514048893517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 171353492495620037463716045 64257559685857514048893517)
  ·
    refine ⟨24096584882196567768335069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 64257559685857514048893517 24096584882196567768335069)
    ·
      refine ⟨9036219330823712913125651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24096584882196567768335069 9036219330823712913125651)
      ·
        refine ⟨13554328996235569369688477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9036219330823712913125651 13554328996235569369688477)
        ·
          refine ⟨5082873373588338513633179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13554328996235569369688477 5082873373588338513633179)
          ·
            refine ⟨7624310060382507770449769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5082873373588338513633179 7624310060382507770449769)
            ·
              refine ⟨5718232545286880827837327, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7624310060382507770449769 5718232545286880827837327)
              ·
                refine ⟨8577348817930321241755991, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5718232545286880827837327 8577348817930321241755991)
                ·
                  refine ⟨12866023226895481862633987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8577348817930321241755991 12866023226895481862633987)
                  ·
                    refine ⟨19299034840343222793950981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12866023226895481862633987 19299034840343222793950981)
                    ·
                      refine ⟨3618569032564354273865809, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19299034840343222793950981 3618569032564354273865809)
                      ·
                        rfl

theorem cell23_7047138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 3, 1, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 3, 1, 2, 1, 1, 1, 4].length) (baseStart_7047138 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7047138 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7047138 prefixEnd_7047138 := by exact prefixLift 7047138
  have htrace : WordTrace (prefixWord ++ tailWord_7047138) baseStart_7047138 baseEnd_7047138 := by
    simpa [prefixWord, tailWord_7047138, baseEnd_7047138] using wordTrace_append hprefix tailTrace_7047138
  have hstable : (prefixWord ++ tailWord_7047138).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7047138).length < 2 ^ (prefixWord ++ tailWord_7047138).sum := by decide
  have hdescent : baseEnd_7047138 < baseStart_7047138 := by decide
  rcases family_descends (prefixWord ++ tailWord_7047138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7047160 : List Nat := [2, 1, 2, 1, 1, 3, 2, 2, 3, 4, 2]
def baseStart_7047160 : Nat := 118140960795 + 7047160 * 2 ^ 59
def prefixEnd_7047160 : Nat := 4983230072969 + 3 ^ 40 * 7047160 * 2
def baseEnd_7047160 : Nat := 3618580329138753187790707

theorem tailTrace_7047160 : CollatzResearch.WordTrace tailWord_7047160 prefixEnd_7047160 3618580329138753187790707 := by
  unfold tailWord_7047160
  simp only [CollatzResearch.WordTrace]
  refine ⟨128515520574675176976437467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 171354027432900235968583289 128515520574675176976437467)
  ·
    refine ⟨192773280862012765464656201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128515520574675176976437467 192773280862012765464656201)
    ·
      refine ⟨144579960646509574098492151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 192773280862012765464656201 144579960646509574098492151)
      ·
        refine ⟨216869940969764361147738227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 144579960646509574098492151 216869940969764361147738227)
        ·
          refine ⟨325304911454646541721607341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 216869940969764361147738227 325304911454646541721607341)
          ·
            refine ⟨121989341795492453145602753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 325304911454646541721607341 121989341795492453145602753)
            ·
              refine ⟨91492006346619339859202065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 121989341795492453145602753 91492006346619339859202065)
              ·
                refine ⟨68619004759964504894401549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 91492006346619339859202065 68619004759964504894401549)
                ·
                  refine ⟨25732126784986689335400581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 68619004759964504894401549 25732126784986689335400581)
                  ·
                    refine ⟨4824773772185004250387609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25732126784986689335400581 4824773772185004250387609)
                    ·
                      refine ⟨3618580329138753187790707, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4824773772185004250387609 3618580329138753187790707)
                      ·
                        rfl

theorem cell23_7047160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 2, 2, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 2, 2, 3, 4, 2].length) (baseStart_7047160 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7047160 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7047160 prefixEnd_7047160 := by exact prefixLift 7047160
  have htrace : WordTrace (prefixWord ++ tailWord_7047160) baseStart_7047160 baseEnd_7047160 := by
    simpa [prefixWord, tailWord_7047160, baseEnd_7047160] using wordTrace_append hprefix tailTrace_7047160
  have hstable : (prefixWord ++ tailWord_7047160).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7047160).length < 2 ^ (prefixWord ++ tailWord_7047160).sum := by decide
  have hdescent : baseEnd_7047160 < baseStart_7047160 := by decide
  rcases family_descends (prefixWord ++ tailWord_7047160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7047163 : List Nat := [1, 1, 1, 1, 1, 3, 4, 1, 1, 6, 3]
def baseStart_7047163 : Nat := 118140960795 + 7047163 * 2 ^ 59
def prefixEnd_7047163 : Nat := 4983230072969 + 3 ^ 40 * 7047163 * 2
def baseEnd_7047163 : Nat := 3618581869580716676053193

theorem tailTrace_7047163 : CollatzResearch.WordTrace tailWord_7047163 prefixEnd_7047163 3618581869580716676053193 := by
  unfold tailWord_7047163
  simp only [CollatzResearch.WordTrace]
  refine ⟨257031150568339485465234143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171354100378892990310156095 257031150568339485465234143)
  ·
    refine ⟨385546725852509228197851215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 257031150568339485465234143 385546725852509228197851215)
    ·
      refine ⟨578320088778763842296776823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 385546725852509228197851215 578320088778763842296776823)
      ·
        refine ⟨867480133168145763445165235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 578320088778763842296776823 867480133168145763445165235)
        ·
          refine ⟨1301220199752218645167747853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 867480133168145763445165235 1301220199752218645167747853)
          ·
            refine ⟨487957574907081991937905445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1301220199752218645167747853 487957574907081991937905445)
            ·
              refine ⟨91492045295077873488357271, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 487957574907081991937905445 91492045295077873488357271)
              ·
                refine ⟨137238067942616810232535907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 91492045295077873488357271 137238067942616810232535907)
                ·
                  refine ⟨205857101913925215348803861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 137238067942616810232535907 205857101913925215348803861)
                  ·
                    refine ⟨9649551652215244469475181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 205857101913925215348803861 9649551652215244469475181)
                    ·
                      refine ⟨3618581869580716676053193, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9649551652215244469475181 3618581869580716676053193)
                      ·
                        rfl

theorem cell23_7047163_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 4, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 4, 1, 1, 6, 3].length) (baseStart_7047163 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7047163 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7047163 prefixEnd_7047163 := by exact prefixLift 7047163
  have htrace : WordTrace (prefixWord ++ tailWord_7047163) baseStart_7047163 baseEnd_7047163 := by
    simpa [prefixWord, tailWord_7047163, baseEnd_7047163] using wordTrace_append hprefix tailTrace_7047163
  have hstable : (prefixWord ++ tailWord_7047163).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7047163).length < 2 ^ (prefixWord ++ tailWord_7047163).sum := by decide
  have hdescent : baseEnd_7047163 < baseStart_7047163 := by decide
  rcases family_descends (prefixWord ++ tailWord_7047163) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7047223 : List Nat := [1, 1, 3, 1, 2, 2, 3, 1, 1, 1, 7]
def baseStart_7047223 : Nat := 118140960795 + 7047223 * 2 ^ 59
def prefixEnd_7047223 : Nat := 4983230072969 + 3 ^ 40 * 7047223 * 2
def baseEnd_7047223 : Nat := 3618612678419986441302917

theorem tailTrace_7047223 : CollatzResearch.WordTrace tailWord_7047223 prefixEnd_7047223 3618612678419986441302917 := by
  unfold tailWord_7047223
  simp only [CollatzResearch.WordTrace]
  refine ⟨257033338948122115712418323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171355559298748077141612215 257033338948122115712418323)
  ·
    refine ⟨385550008422183173568627485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 257033338948122115712418323 385550008422183173568627485)
    ·
      refine ⟨144581253158318690088235307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 385550008422183173568627485 144581253158318690088235307)
      ·
        refine ⟨216871879737478035132352961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 144581253158318690088235307 216871879737478035132352961)
        ·
          refine ⟨162653909803108526349264721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 216871879737478035132352961 162653909803108526349264721)
          ·
            refine ⟨121990432352331394761948541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 162653909803108526349264721 121990432352331394761948541)
            ·
              refine ⟨45746412132124273035730703, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 121990432352331394761948541 45746412132124273035730703)
              ·
                refine ⟨68619618198186409553596055, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45746412132124273035730703 68619618198186409553596055)
                ·
                  refine ⟨102929427297279614330394083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 68619618198186409553596055 102929427297279614330394083)
                  ·
                    refine ⟨154394140945919421495591125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 102929427297279614330394083 154394140945919421495591125)
                    ·
                      refine ⟨3618612678419986441302917, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 154394140945919421495591125 3618612678419986441302917)
                      ·
                        rfl

theorem cell23_7047223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 3, 1, 1, 1, 7].length) (baseStart_7047223 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7047223 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7047223 prefixEnd_7047223 := by exact prefixLift 7047223
  have htrace : WordTrace (prefixWord ++ tailWord_7047223) baseStart_7047223 baseEnd_7047223 := by
    simpa [prefixWord, tailWord_7047223, baseEnd_7047223] using wordTrace_append hprefix tailTrace_7047223
  have hstable : (prefixWord ++ tailWord_7047223).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7047223).length < 2 ^ (prefixWord ++ tailWord_7047223).sum := by decide
  have hdescent : baseEnd_7047223 < baseStart_7047223 := by decide
  rcases family_descends (prefixWord ++ tailWord_7047223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7047277 : List Nat := [1, 5, 1, 1, 2, 1, 2, 3, 3, 4]
def baseStart_7047277 : Nat := 118140960795 + 7047277 * 2 ^ 59
def prefixEnd_7047277 : Nat := 4983230072969 + 3 ^ 40 * 7047277 * 2
def baseEnd_7047277 : Nat := 1206213468791776410009223

theorem tailTrace_7047277 : CollatzResearch.WordTrace tailWord_7047277 prefixEnd_7047277 1206213468791776410009223 := by
  unfold tailWord_7047277
  simp only [CollatzResearch.WordTrace]
  refine ⟨257035308489926482934884085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171356872326617655289922723 257035308489926482934884085)
  ·
    refine ⟨24097060170930607775145383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 257035308489926482934884085 24097060170930607775145383)
    ·
      refine ⟨36145590256395911662718075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24097060170930607775145383 36145590256395911662718075)
      ·
        refine ⟨54218385384593867494077113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36145590256395911662718075 54218385384593867494077113)
        ·
          refine ⟨40663789038445400620557835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54218385384593867494077113 40663789038445400620557835)
          ·
            refine ⟨60995683557668100930836753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40663789038445400620557835 60995683557668100930836753)
            ·
              refine ⟨45746762668251075698127565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 60995683557668100930836753 45746762668251075698127565)
              ·
                refine ⟨17155036000594153386797837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 45746762668251075698127565 17155036000594153386797837)
                ·
                  refine ⟨6433138500222807520049189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17155036000594153386797837 6433138500222807520049189)
                  ·
                    refine ⟨1206213468791776410009223, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6433138500222807520049189 1206213468791776410009223)
                    ·
                      rfl

theorem cell23_7047277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 2, 3, 3, 4].length) (baseStart_7047277 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7047277 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7047277 prefixEnd_7047277 := by exact prefixLift 7047277
  have htrace : WordTrace (prefixWord ++ tailWord_7047277) baseStart_7047277 baseEnd_7047277 := by
    simpa [prefixWord, tailWord_7047277, baseEnd_7047277] using wordTrace_append hprefix tailTrace_7047277
  have hstable : (prefixWord ++ tailWord_7047277).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7047277).length < 2 ^ (prefixWord ++ tailWord_7047277).sum := by decide
  have hdescent : baseEnd_7047277 < baseStart_7047277 := by decide
  rcases family_descends (prefixWord ++ tailWord_7047277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7047304 : List Nat := [2, 1, 3, 4, 1, 1, 3, 1, 2, 2, 3]
def baseStart_7047304 : Nat := 118140960795 + 7047304 * 2 ^ 59
def prefixEnd_7047304 : Nat := 4983230072969 + 3 ^ 40 * 7047304 * 2
def baseEnd_7047304 : Nat := 3618654270353000624390045

theorem tailTrace_7047304 : CollatzResearch.WordTrace tailWord_7047304 prefixEnd_7047304 3618654270353000624390045 := by
  unfold tailWord_7047304
  simp only [CollatzResearch.WordTrace]
  refine ⟨128518146630414333273058483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 171357528840552444364077977 128518146630414333273058483)
  ·
    refine ⟨192777219945621499909587725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128518146630414333273058483 192777219945621499909587725)
    ·
      refine ⟨72291457479608062466095397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 192777219945621499909587725 72291457479608062466095397)
      ·
        refine ⟨13554648277426511712392887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 72291457479608062466095397 13554648277426511712392887)
        ·
          refine ⟨20331972416139767568589331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13554648277426511712392887 20331972416139767568589331)
          ·
            refine ⟨30497958624209651352883997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20331972416139767568589331 30497958624209651352883997)
            ·
              refine ⟨11436734484078619257331499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30497958624209651352883997 11436734484078619257331499)
              ·
                refine ⟨17155101726117928885997249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11436734484078619257331499 17155101726117928885997249)
                ·
                  refine ⟨12866326294588446664497937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17155101726117928885997249 12866326294588446664497937)
                  ·
                    refine ⟨9649744720941334998373453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12866326294588446664497937 9649744720941334998373453)
                    ·
                      refine ⟨3618654270353000624390045, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9649744720941334998373453 3618654270353000624390045)
                      ·
                        rfl

theorem cell23_7047304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 1, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 1, 3, 1, 2, 2, 3].length) (baseStart_7047304 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7047304 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7047304 prefixEnd_7047304 := by exact prefixLift 7047304
  have htrace : WordTrace (prefixWord ++ tailWord_7047304) baseStart_7047304 baseEnd_7047304 := by
    simpa [prefixWord, tailWord_7047304, baseEnd_7047304] using wordTrace_append hprefix tailTrace_7047304
  have hstable : (prefixWord ++ tailWord_7047304).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7047304).length < 2 ^ (prefixWord ++ tailWord_7047304).sum := by decide
  have hdescent : baseEnd_7047304 < baseStart_7047304 := by decide
  rcases family_descends (prefixWord ++ tailWord_7047304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7047317 : List Nat := [1, 3, 2, 1, 1, 1, 3, 2, 5, 1, 3]
def baseStart_7047317 : Nat := 118140960795 + 7047317 * 2 ^ 59
def prefixEnd_7047317 : Nat := 4983230072969 + 3 ^ 40 * 7047317 * 2
def baseEnd_7047317 : Nat := 3618660945601509073527485

theorem tailTrace_7047317 : CollatzResearch.WordTrace tailWord_7047317 prefixEnd_7047317 3618660945601509073527485 := by
  unfold tailWord_7047317
  simp only [CollatzResearch.WordTrace]
  refine ⟨257036767409781569766340205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171357844939854379844226803 257036767409781569766340205)
  ·
    refine ⟨96388787778668088662377577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 257036767409781569766340205 96388787778668088662377577)
    ·
      refine ⟨72291590834001066496783183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 96388787778668088662377577 72291590834001066496783183)
      ·
        refine ⟨108437386251001599745174775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72291590834001066496783183 108437386251001599745174775)
        ·
          refine ⟨162656079376502399617762163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 108437386251001599745174775 162656079376502399617762163)
          ·
            refine ⟨243984119064753599426643245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 162656079376502399617762163 243984119064753599426643245)
            ·
              refine ⟨91494044649282599784991217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 243984119064753599426643245 91494044649282599784991217)
              ·
                refine ⟨68620533486961949838743413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 91494044649282599784991217 68620533486961949838743413)
                ·
                  refine ⟨6433175014402682797382195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 68620533486961949838743413 6433175014402682797382195)
                  ·
                    refine ⟨9649762521604024196073293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6433175014402682797382195 9649762521604024196073293)
                    ·
                      refine ⟨3618660945601509073527485, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9649762521604024196073293 3618660945601509073527485)
                      ·
                        rfl

theorem cell23_7047317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 3, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 3, 2, 5, 1, 3].length) (baseStart_7047317 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7047317 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7047317 prefixEnd_7047317 := by exact prefixLift 7047317
  have htrace : WordTrace (prefixWord ++ tailWord_7047317) baseStart_7047317 baseEnd_7047317 := by
    simpa [prefixWord, tailWord_7047317, baseEnd_7047317] using wordTrace_append hprefix tailTrace_7047317
  have hstable : (prefixWord ++ tailWord_7047317).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7047317).length < 2 ^ (prefixWord ++ tailWord_7047317).sum := by decide
  have hdescent : baseEnd_7047317 < baseStart_7047317 := by decide
  rcases family_descends (prefixWord ++ tailWord_7047317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7047357 : List Nat := [1, 4, 1, 2, 1, 1, 1, 1, 1, 8, 2]
def baseStart_7047357 : Nat := 118140960795 + 7047357 * 2 ^ 59
def prefixEnd_7047357 : Nat := 4983230072969 + 3 ^ 40 * 7047357 * 2
def baseEnd_7047357 : Nat := 3618681484827688917027301

theorem tailTrace_7047357 : CollatzResearch.WordTrace tailWord_7047357 prefixEnd_7047357 3618681484827688917027301 := by
  unfold tailWord_7047357
  simp only [CollatzResearch.WordTrace]
  refine ⟨257038226329636656597796325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171358817553091104398530883 257038226329636656597796325)
  ·
    refine ⟨48194667436806873112086811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 257038226329636656597796325 48194667436806873112086811)
    ·
      refine ⟨72292001155210309668130217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48194667436806873112086811 72292001155210309668130217)
      ·
        refine ⟨54219000866407732251097663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72292001155210309668130217 54219000866407732251097663)
        ·
          refine ⟨81328501299611598376646495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54219000866407732251097663 81328501299611598376646495)
          ·
            refine ⟨121992751949417397564969743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81328501299611598376646495 121992751949417397564969743)
            ·
              refine ⟨182989127924126096347454615, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 121992751949417397564969743 182989127924126096347454615)
              ·
                refine ⟨274483691886189144521181923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 182989127924126096347454615 274483691886189144521181923)
                ·
                  refine ⟨411725537829283716781772885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 274483691886189144521181923 411725537829283716781772885)
                  ·
                    refine ⟨4824908646436918556036401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 411725537829283716781772885 4824908646436918556036401)
                    ·
                      refine ⟨3618681484827688917027301, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4824908646436918556036401 3618681484827688917027301)
                      ·
                        rfl

theorem cell23_7047357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 1, 1, 1, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 1, 1, 1, 8, 2].length) (baseStart_7047357 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7047357 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7047357 prefixEnd_7047357 := by exact prefixLift 7047357
  have htrace : WordTrace (prefixWord ++ tailWord_7047357) baseStart_7047357 baseEnd_7047357 := by
    simpa [prefixWord, tailWord_7047357, baseEnd_7047357] using wordTrace_append hprefix tailTrace_7047357
  have hstable : (prefixWord ++ tailWord_7047357).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7047357).length < 2 ^ (prefixWord ++ tailWord_7047357).sum := by decide
  have hdescent : baseEnd_7047357 < baseStart_7047357 := by decide
  rcases family_descends (prefixWord ++ tailWord_7047357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7047374 : List Nat := [4, 1, 1, 1, 4, 1, 2, 3, 1, 1, 4]
def baseStart_7047374 : Nat := 118140960795 + 7047374 * 2 ^ 59
def prefixEnd_7047374 : Nat := 4983230072969 + 3 ^ 40 * 7047374 * 2
def baseEnd_7047374 : Nat := 3618690213998815350514723

theorem tailTrace_7047374 : CollatzResearch.WordTrace tailWord_7047374 prefixEnd_7047374 3618690213998815350514723 := by
  unfold tailWord_7047374
  simp only [CollatzResearch.WordTrace]
  refine ⟨32129855796321883562645647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 171359230913716712334110117 32129855796321883562645647)
  ·
    refine ⟨48194783694482825343968471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32129855796321883562645647 48194783694482825343968471)
    ·
      refine ⟨72292175541724238015952707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48194783694482825343968471 72292175541724238015952707)
      ·
        refine ⟨108438263312586357023929061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72292175541724238015952707 108438263312586357023929061)
        ·
          refine ⟨20332174371109941941986699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 108438263312586357023929061 20332174371109941941986699)
          ·
            refine ⟨30498261556664912912980049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20332174371109941941986699 30498261556664912912980049)
            ·
              refine ⟨22873696167498684684735037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30498261556664912912980049 22873696167498684684735037)
              ·
                refine ⟨8577636062812006756775639, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22873696167498684684735037 8577636062812006756775639)
                ·
                  refine ⟨12866454094218010135163459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8577636062812006756775639 12866454094218010135163459)
                  ·
                    refine ⟨19299681141327015202745189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12866454094218010135163459 19299681141327015202745189)
                    ·
                      refine ⟨3618690213998815350514723, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19299681141327015202745189 3618690213998815350514723)
                      ·
                        rfl

theorem cell23_7047374_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 1, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 1, 2, 3, 1, 1, 4].length) (baseStart_7047374 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7047374 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7047374 prefixEnd_7047374 := by exact prefixLift 7047374
  have htrace : WordTrace (prefixWord ++ tailWord_7047374) baseStart_7047374 baseEnd_7047374 := by
    simpa [prefixWord, tailWord_7047374, baseEnd_7047374] using wordTrace_append hprefix tailTrace_7047374
  have hstable : (prefixWord ++ tailWord_7047374).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7047374).length < 2 ^ (prefixWord ++ tailWord_7047374).sum := by decide
  have hdescent : baseEnd_7047374 < baseStart_7047374 := by decide
  rcases family_descends (prefixWord ++ tailWord_7047374) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7047397 : List Nat := [1, 3, 1, 4, 2, 2, 2, 8]
def baseStart_7047397 : Nat := 118140960795 + 7047397 * 2 ^ 59
def prefixEnd_7047397 : Nat := 4983230072969 + 3 ^ 40 * 7047397 * 2
def baseEnd_7047397 : Nat := 134026000890884028167671

theorem tailTrace_7047397 : CollatzResearch.WordTrace tailWord_7047397 prefixEnd_7047397 134026000890884028167671 := by
  unfold tailWord_7047397
  simp only [CollatzResearch.WordTrace]
  refine ⟨257039685249491743429252445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171359790166327828952834963 257039685249491743429252445)
  ·
    refine ⟨96389881968559403785969667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 257039685249491743429252445 96389881968559403785969667)
    ·
      refine ⟨144584822952839105678954501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96389881968559403785969667 144584822952839105678954501)
      ·
        refine ⟨27109654303657332314803969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 144584822952839105678954501 27109654303657332314803969)
        ·
          refine ⟨20332240727742999236102977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27109654303657332314803969 20332240727742999236102977)
          ·
            refine ⟨15249180545807249427077233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20332240727742999236102977 15249180545807249427077233)
            ·
              refine ⟨11436885409355437070307925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15249180545807249427077233 11436885409355437070307925)
              ·
                refine ⟨134026000890884028167671, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 11436885409355437070307925 134026000890884028167671)
                ·
                  rfl

theorem cell23_7047397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 2, 2, 8].length) (baseStart_7047397 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7047397 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7047397 prefixEnd_7047397 := by exact prefixLift 7047397
  have htrace : WordTrace (prefixWord ++ tailWord_7047397) baseStart_7047397 baseEnd_7047397 := by
    simpa [prefixWord, tailWord_7047397, baseEnd_7047397] using wordTrace_append hprefix tailTrace_7047397
  have hstable : (prefixWord ++ tailWord_7047397).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7047397).length < 2 ^ (prefixWord ++ tailWord_7047397).sum := by decide
  have hdescent : baseEnd_7047397 < baseStart_7047397 := by decide
  rcases family_descends (prefixWord ++ tailWord_7047397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7047428 : List Nat := [2, 3, 2, 2, 3, 1, 3, 1, 1, 2, 3]
def baseStart_7047428 : Nat := 118140960795 + 7047428 * 2 ^ 59
def prefixEnd_7047428 : Nat := 4983230072969 + 3 ^ 40 * 7047428 * 2
def baseEnd_7047428 : Nat := 3618717941954158139239475

theorem tailTrace_7047428 : CollatzResearch.WordTrace tailWord_7047428 prefixEnd_7047428 3618717941954158139239475 := by
  unfold tailWord_7047428
  simp only [CollatzResearch.WordTrace]
  refine ⟨128520407956189717861815469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 171360543941586290482420625 128520407956189717861815469)
  ·
    refine ⟨48195152983571144198180801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 128520407956189717861815469 48195152983571144198180801)
    ·
      refine ⟨36146364737678358148635601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48195152983571144198180801 36146364737678358148635601)
      ·
        refine ⟨27109773553258768611476701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36146364737678358148635601 27109773553258768611476701)
        ·
          refine ⟨10166165082472038229303763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27109773553258768611476701 10166165082472038229303763)
          ·
            refine ⟨15249247623708057343955645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10166165082472038229303763 15249247623708057343955645)
            ·
              refine ⟨5718467858890521503983367, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15249247623708057343955645 5718467858890521503983367)
              ·
                refine ⟨8577701788335782255975051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5718467858890521503983367 8577701788335782255975051)
                ·
                  refine ⟨12866552682503673383962577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8577701788335782255975051 12866552682503673383962577)
                  ·
                    refine ⟨9649914511877755037971933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12866552682503673383962577 9649914511877755037971933)
                    ·
                      refine ⟨3618717941954158139239475, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9649914511877755037971933 3618717941954158139239475)
                      ·
                        rfl

theorem cell23_7047428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 3, 1, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 3, 1, 3, 1, 1, 2, 3].length) (baseStart_7047428 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7047428 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7047428 prefixEnd_7047428 := by exact prefixLift 7047428
  have htrace : WordTrace (prefixWord ++ tailWord_7047428) baseStart_7047428 baseEnd_7047428 := by
    simpa [prefixWord, tailWord_7047428, baseEnd_7047428] using wordTrace_append hprefix tailTrace_7047428
  have hstable : (prefixWord ++ tailWord_7047428).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7047428).length < 2 ^ (prefixWord ++ tailWord_7047428).sum := by decide
  have hdescent : baseEnd_7047428 < baseStart_7047428 := by decide
  rcases family_descends (prefixWord ++ tailWord_7047428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7047441 : List Nat := [1, 2, 2, 1, 1, 6, 2, 2, 2, 1, 3]
def baseStart_7047441 : Nat := 118140960795 + 7047441 * 2 ^ 59
def prefixEnd_7047441 : Nat := 4983230072969 + 3 ^ 40 * 7047441 * 2
def baseEnd_7047441 : Nat := 3618724617202666588376915

theorem tailTrace_7047441 : CollatzResearch.WordTrace tailWord_7047441 prefixEnd_7047441 3618724617202666588376915 := by
  unfold tailWord_7047441
  simp only [CollatzResearch.WordTrace]
  refine ⟨257041290061332338943854177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171360860040888225962569451 257041290061332338943854177)
  ·
    refine ⟨192780967545999254207890633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 257041290061332338943854177 192780967545999254207890633)
    ·
      refine ⟨144585725659499440655917975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 192780967545999254207890633 144585725659499440655917975)
      ·
        refine ⟨216878588489249160983876963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 144585725659499440655917975 216878588489249160983876963)
        ·
          refine ⟨325317882733873741475815445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 216878588489249160983876963 325317882733873741475815445)
          ·
            refine ⟨15249275753150331631678849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 325317882733873741475815445 15249275753150331631678849)
            ·
              refine ⟨11436956814862748723759137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15249275753150331631678849 11436956814862748723759137)
              ·
                refine ⟨8577717611147061542819353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11436956814862748723759137 8577717611147061542819353)
                ·
                  refine ⟨6433288208360296157114515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8577717611147061542819353 6433288208360296157114515)
                  ·
                    refine ⟨9649932312540444235671773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6433288208360296157114515 9649932312540444235671773)
                    ·
                      refine ⟨3618724617202666588376915, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9649932312540444235671773 3618724617202666588376915)
                      ·
                        rfl

theorem cell23_7047441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 6, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 6, 2, 2, 2, 1, 3].length) (baseStart_7047441 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7047441 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7047441 prefixEnd_7047441 := by exact prefixLift 7047441
  have htrace : WordTrace (prefixWord ++ tailWord_7047441) baseStart_7047441 baseEnd_7047441 := by
    simpa [prefixWord, tailWord_7047441, baseEnd_7047441] using wordTrace_append hprefix tailTrace_7047441
  have hstable : (prefixWord ++ tailWord_7047441).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7047441).length < 2 ^ (prefixWord ++ tailWord_7047441).sum := by decide
  have hdescent : baseEnd_7047441 < baseStart_7047441 := by decide
  rcases family_descends (prefixWord ++ tailWord_7047441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7047447 : List Nat := [1, 1, 3, 4, 1, 2, 1, 1, 2, 3, 4]
def baseStart_7047447 : Nat := 118140960795 + 7047447 * 2 ^ 59
def prefixEnd_7047447 : Nat := 4983230072969 + 3 ^ 40 * 7047447 * 2
def baseEnd_7047447 : Nat := 3618727698086593564901887

theorem tailTrace_7047447 : CollatzResearch.WordTrace tailWord_7047447 prefixEnd_7047447 3618727698086593564901887 := by
  unfold tailWord_7047447
  simp only [CollatzResearch.WordTrace]
  refine ⟨257041508899310601968572595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171361005932873734645715063 257041508899310601968572595)
  ·
    refine ⟨385562263348965902952858893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 257041508899310601968572595 385562263348965902952858893)
    ·
      refine ⟨144585848755862213607322085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 385562263348965902952858893 144585848755862213607322085)
      ·
        refine ⟨27109846641724165051372891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 144585848755862213607322085 27109846641724165051372891)
        ·
          refine ⟨40664769962586247577059337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27109846641724165051372891 40664769962586247577059337)
          ·
            refine ⟨30498577471939685682794503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40664769962586247577059337 30498577471939685682794503)
            ·
              refine ⟨45747866207909528524191755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30498577471939685682794503 45747866207909528524191755)
              ·
                refine ⟨68621799311864292786287633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45747866207909528524191755 68621799311864292786287633)
                ·
                  refine ⟨51466349483898219589715725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 68621799311864292786287633 51466349483898219589715725)
                  ·
                    refine ⟨19299881056461832346143397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 51466349483898219589715725 19299881056461832346143397)
                    ·
                      refine ⟨3618727698086593564901887, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19299881056461832346143397 3618727698086593564901887)
                      ·
                        rfl

theorem cell23_7047447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 2, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 2, 1, 1, 2, 3, 4].length) (baseStart_7047447 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7047447 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7047447 prefixEnd_7047447 := by exact prefixLift 7047447
  have htrace : WordTrace (prefixWord ++ tailWord_7047447) baseStart_7047447 baseEnd_7047447 := by
    simpa [prefixWord, tailWord_7047447, baseEnd_7047447] using wordTrace_append hprefix tailTrace_7047447
  have hstable : (prefixWord ++ tailWord_7047447).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7047447).length < 2 ^ (prefixWord ++ tailWord_7047447).sum := by decide
  have hdescent : baseEnd_7047447 < baseStart_7047447 := by decide
  rcases family_descends (prefixWord ++ tailWord_7047447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7047477 : List Nat := [1, 3, 3, 1, 2, 1, 1, 2, 1, 4, 4]
def baseStart_7047477 : Nat := 118140960795 + 7047477 * 2 ^ 59
def prefixEnd_7047477 : Nat := 4983230072969 + 3 ^ 40 * 7047477 * 2
def baseEnd_7047477 : Nat := 3618743102506228447526749

theorem tailTrace_7047477 : CollatzResearch.WordTrace tailWord_7047477 prefixEnd_7047477 3618743102506228447526749 := by
  unfold tailWord_7047477
  simp only [CollatzResearch.WordTrace]
  refine ⟨257042603089201917092164685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171361735392801278061443123 257042603089201917092164685)
  ·
    refine ⟨96390976158450718909561757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 257042603089201917092164685 96390976158450718909561757)
    ·
      refine ⟨36146616059419019591085659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 96390976158450718909561757 36146616059419019591085659)
      ·
        refine ⟨54219924089128529386628489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36146616059419019591085659 54219924089128529386628489)
        ·
          refine ⟨40664943066846397039971367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54219924089128529386628489 40664943066846397039971367)
          ·
            refine ⟨60997414600269595559957051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40664943066846397039971367 60997414600269595559957051)
            ·
              refine ⟨91496121900404393339935577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60997414600269595559957051 91496121900404393339935577)
              ·
                refine ⟨68622091425303295004951683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 91496121900404393339935577 68622091425303295004951683)
                ·
                  refine ⟨102933137137954942507427525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 68622091425303295004951683 102933137137954942507427525)
                  ·
                    refine ⟨19299963213366551720142661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 102933137137954942507427525 19299963213366551720142661)
                    ·
                      refine ⟨3618743102506228447526749, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19299963213366551720142661 3618743102506228447526749)
                      ·
                        rfl

theorem cell23_7047477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 1, 2, 1, 4, 4].length) (baseStart_7047477 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7047477 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7047477 prefixEnd_7047477 := by exact prefixLift 7047477
  have htrace : WordTrace (prefixWord ++ tailWord_7047477) baseStart_7047477 baseEnd_7047477 := by
    simpa [prefixWord, tailWord_7047477, baseEnd_7047477] using wordTrace_append hprefix tailTrace_7047477
  have hstable : (prefixWord ++ tailWord_7047477).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7047477).length < 2 ^ (prefixWord ++ tailWord_7047477).sum := by decide
  have hdescent : baseEnd_7047477 < baseStart_7047477 := by decide
  rcases family_descends (prefixWord ++ tailWord_7047477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7047481 : List Nat := [1, 2, 1, 6, 1, 1, 2, 2, 1, 4, 2]
def baseStart_7047481 : Nat := 118140960795 + 7047481 * 2 ^ 59
def prefixEnd_7047481 : Nat := 4983230072969 + 3 ^ 40 * 7047481 * 2
def baseEnd_7047481 : Nat := 3618745156428846431876731

theorem tailTrace_7047481 : CollatzResearch.WordTrace tailWord_7047481 prefixEnd_7047481 3618745156428846431876731 := by
  unfold tailWord_7047481
  simp only [CollatzResearch.WordTrace]
  refine ⟨257042748981187425775310297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171361832654124950516873531 257042748981187425775310297)
  ·
    refine ⟨192782061735890569331482723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 257042748981187425775310297 192782061735890569331482723)
    ·
      refine ⟨289173092603835853997224085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 192782061735890569331482723 289173092603835853997224085)
      ·
        refine ⟨13554988715804805656119879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 289173092603835853997224085 13554988715804805656119879)
        ·
          refine ⟨20332483073707208484179819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13554988715804805656119879 20332483073707208484179819)
          ·
            refine ⟨30498724610560812726269729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20332483073707208484179819 30498724610560812726269729)
            ·
              refine ⟨22874043457920609544702297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30498724610560812726269729 22874043457920609544702297)
              ·
                refine ⟨17155532593440457158526723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22874043457920609544702297 17155532593440457158526723)
                ·
                  refine ⟨25733298890160685737790085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17155532593440457158526723 25733298890160685737790085)
                  ·
                    refine ⟨4824993541905128575835641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25733298890160685737790085 4824993541905128575835641)
                    ·
                      refine ⟨3618745156428846431876731, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4824993541905128575835641 3618745156428846431876731)
                      ·
                        rfl

theorem cell23_7047481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 1, 2, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 1, 2, 2, 1, 4, 2].length) (baseStart_7047481 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7047481 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7047481 prefixEnd_7047481 := by exact prefixLift 7047481
  have htrace : WordTrace (prefixWord ++ tailWord_7047481) baseStart_7047481 baseEnd_7047481 := by
    simpa [prefixWord, tailWord_7047481, baseEnd_7047481] using wordTrace_append hprefix tailTrace_7047481
  have hstable : (prefixWord ++ tailWord_7047481).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7047481).length < 2 ^ (prefixWord ++ tailWord_7047481).sum := by decide
  have hdescent : baseEnd_7047481 < baseStart_7047481 := by decide
  rcases family_descends (prefixWord ++ tailWord_7047481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7047492 : List Nat := [2, 3, 4, 1, 3, 1, 1, 2, 2, 1, 3]
def baseStart_7047492 : Nat := 118140960795 + 7047492 * 2 ^ 59
def prefixEnd_7047492 : Nat := 4983230072969 + 3 ^ 40 * 7047492 * 2
def baseEnd_7047492 : Nat := 3618750804716045888839181

theorem tailTrace_7047492 : CollatzResearch.WordTrace tailWord_7047492 prefixEnd_7047492 3618750804716045888839181 := by
  unfold tailWord_7047492
  simp only [CollatzResearch.WordTrace]
  refine ⟨128521575092073787326980365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 171362100122765049769307153 128521575092073787326980365)
  ·
    refine ⟨48195590659527670247617637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 128521575092073787326980365 48195590659527670247617637)
    ·
      refine ⟨9036673248661438171428307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 48195590659527670247617637 9036673248661438171428307)
      ·
        refine ⟨13555009872992157257142461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9036673248661438171428307 13555009872992157257142461)
        ·
          refine ⟨5083128702372058971428423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13555009872992157257142461 5083128702372058971428423)
          ·
            refine ⟨7624693053558088457142635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5083128702372058971428423 7624693053558088457142635)
            ·
              refine ⟨11437039580337132685713953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7624693053558088457142635 11437039580337132685713953)
              ·
                refine ⟨8577779685252849514285465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11437039580337132685713953 8577779685252849514285465)
                ·
                  refine ⟨6433334763939637135714099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8577779685252849514285465 6433334763939637135714099)
                  ·
                    refine ⟨9650002145909455703571149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6433334763939637135714099 9650002145909455703571149)
                    ·
                      refine ⟨3618750804716045888839181, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9650002145909455703571149 3618750804716045888839181)
                      ·
                        rfl

theorem cell23_7047492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 3, 1, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 3, 1, 1, 2, 2, 1, 3].length) (baseStart_7047492 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7047492 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7047492 prefixEnd_7047492 := by exact prefixLift 7047492
  have htrace : WordTrace (prefixWord ++ tailWord_7047492) baseStart_7047492 baseEnd_7047492 := by
    simpa [prefixWord, tailWord_7047492, baseEnd_7047492] using wordTrace_append hprefix tailTrace_7047492
  have hstable : (prefixWord ++ tailWord_7047492).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7047492).length < 2 ^ (prefixWord ++ tailWord_7047492).sum := by decide
  have hdescent : baseEnd_7047492 < baseStart_7047492 := by decide
  rcases family_descends (prefixWord ++ tailWord_7047492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7047504 : List Nat := [2, 1, 1, 1, 1, 6, 2, 4, 5]
def baseStart_7047504 : Nat := 118140960795 + 7047504 * 2 ^ 59
def prefixEnd_7047504 : Nat := 4983230072969 + 3 ^ 40 * 7047504 * 2
def baseEnd_7047504 : Nat := 402084107387099982432125

theorem tailTrace_7047504 : CollatzResearch.WordTrace tailWord_7047504 prefixEnd_7047504 402084107387099982432125 := by
  unfold tailWord_7047504
  simp only [CollatzResearch.WordTrace]
  refine ⟨128521793930052050351698783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 171362391906736067135598377 128521793930052050351698783)
  ·
    refine ⟨192782690895078075527548175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128521793930052050351698783 192782690895078075527548175)
    ·
      refine ⟨289174036342617113291322263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 192782690895078075527548175 289174036342617113291322263)
      ·
        refine ⟨433761054513925669936983395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 289174036342617113291322263 433761054513925669936983395)
        ·
          refine ⟨650641581770888504905475093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 433761054513925669936983395 650641581770888504905475093)
          ·
            refine ⟨30498824145510398667444145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 650641581770888504905475093 30498824145510398667444145)
            ·
              refine ⟨22874118109132799000583109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30498824145510398667444145 22874118109132799000583109)
              ·
                refine ⟨4288897145462399812609333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22874118109132799000583109 4288897145462399812609333)
                ·
                  refine ⟨402084107387099982432125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4288897145462399812609333 402084107387099982432125)
                  ·
                    rfl

theorem cell23_7047504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 6, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 6, 2, 4, 5].length) (baseStart_7047504 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7047504 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7047504 prefixEnd_7047504 := by exact prefixLift 7047504
  have htrace : WordTrace (prefixWord ++ tailWord_7047504) baseStart_7047504 baseEnd_7047504 := by
    simpa [prefixWord, tailWord_7047504, baseEnd_7047504] using wordTrace_append hprefix tailTrace_7047504
  have hstable : (prefixWord ++ tailWord_7047504).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7047504).length < 2 ^ (prefixWord ++ tailWord_7047504).sum := by decide
  have hdescent : baseEnd_7047504 < baseStart_7047504 := by decide
  rcases family_descends (prefixWord ++ tailWord_7047504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7047591 : List Nat := [1, 1, 6, 1, 1, 2, 1, 3, 2, 2, 3]
def baseStart_7047591 : Nat := 118140960795 + 7047591 * 2 ^ 59
def prefixEnd_7047591 : Nat := 4983230072969 + 3 ^ 40 * 7047591 * 2
def baseEnd_7047591 : Nat := 3618801639300841001501225

theorem tailTrace_7047591 : CollatzResearch.WordTrace tailWord_7047591 prefixEnd_7047591 3618801639300841001501225 := by
  unfold tailWord_7047591
  simp only [CollatzResearch.WordTrace]
  refine ⟨257046761010788914561814627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171364507340525943041209751 257046761010788914561814627)
  ·
    refine ⟨385570141516183371842721941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 257046761010788914561814627 385570141516183371842721941)
    ·
      refine ⟨18073600383571095555127591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 385570141516183371842721941 18073600383571095555127591)
      ·
        refine ⟨27110400575356643332691387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18073600383571095555127591 27110400575356643332691387)
        ·
          refine ⟨40665600863034964999037081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27110400575356643332691387 40665600863034964999037081)
          ·
            refine ⟨30499200647276223749277811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40665600863034964999037081 30499200647276223749277811)
            ·
              refine ⟨45748800970914335623916717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30499200647276223749277811 45748800970914335623916717)
              ·
                refine ⟨17155800364092875858968769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 45748800970914335623916717 17155800364092875858968769)
                ·
                  refine ⟨12866850273069656894226577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17155800364092875858968769 12866850273069656894226577)
                  ·
                    refine ⟨9650137704802242670669933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12866850273069656894226577 9650137704802242670669933)
                    ·
                      refine ⟨3618801639300841001501225, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9650137704802242670669933 3618801639300841001501225)
                      ·
                        rfl

theorem cell23_7047591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 2, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 2, 1, 3, 2, 2, 3].length) (baseStart_7047591 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7047591 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7047591 prefixEnd_7047591 := by exact prefixLift 7047591
  have htrace : WordTrace (prefixWord ++ tailWord_7047591) baseStart_7047591 baseEnd_7047591 := by
    simpa [prefixWord, tailWord_7047591, baseEnd_7047591] using wordTrace_append hprefix tailTrace_7047591
  have hstable : (prefixWord ++ tailWord_7047591).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7047591).length < 2 ^ (prefixWord ++ tailWord_7047591).sum := by decide
  have hdescent : baseEnd_7047591 < baseStart_7047591 := by decide
  rcases family_descends (prefixWord ++ tailWord_7047591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7047624 : List Nat := [2, 1, 3, 1, 3, 2, 1, 2, 3, 5]
def baseStart_7047624 : Nat := 118140960795 + 7047624 * 2 ^ 59
def prefixEnd_7047624 : Nat := 4983230072969 + 3 ^ 40 * 7047624 * 2
def baseEnd_7047624 : Nat := 1206272861387479790796191

theorem tailTrace_7047624 : CollatzResearch.WordTrace tailWord_7047624 prefixEnd_7047624 1206272861387479790796191 := by
  unfold tailWord_7047624
  simp only [CollatzResearch.WordTrace]
  refine ⟨128523982309834680598882963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 171365309746446240798510617 128523982309834680598882963)
  ·
    refine ⟨192785973464752020898324445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128523982309834680598882963 192785973464752020898324445)
    ·
      refine ⟨72294740049282007836871667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 192785973464752020898324445 72294740049282007836871667)
      ·
        refine ⟨108442110073923011755307501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72294740049282007836871667 108442110073923011755307501)
        ·
          refine ⟨40665791277721129408240313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 108442110073923011755307501 40665791277721129408240313)
          ·
            refine ⟨30499343458290847056180235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40665791277721129408240313 30499343458290847056180235)
            ·
              refine ⟨45749015187436270584270353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30499343458290847056180235 45749015187436270584270353)
              ·
                refine ⟨34311761390577202938202765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45749015187436270584270353 34311761390577202938202765)
                ·
                  refine ⟨12866910521466451101826037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34311761390577202938202765 12866910521466451101826037)
                  ·
                    refine ⟨1206272861387479790796191, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12866910521466451101826037 1206272861387479790796191)
                    ·
                      rfl

theorem cell23_7047624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 2, 1, 2, 3, 5].length) (baseStart_7047624 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7047624 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7047624 prefixEnd_7047624 := by exact prefixLift 7047624
  have htrace : WordTrace (prefixWord ++ tailWord_7047624) baseStart_7047624 baseEnd_7047624 := by
    simpa [prefixWord, tailWord_7047624, baseEnd_7047624] using wordTrace_append hprefix tailTrace_7047624
  have hstable : (prefixWord ++ tailWord_7047624).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7047624).length < 2 ^ (prefixWord ++ tailWord_7047624).sum := by decide
  have hdescent : baseEnd_7047624 < baseStart_7047624 := by decide
  rcases family_descends (prefixWord ++ tailWord_7047624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7047655 : List Nat := [1, 1, 5, 2, 1, 1, 4, 3, 1, 1, 3]
def baseStart_7047655 : Nat := 118140960795 + 7047655 * 2 ^ 59
def prefixEnd_7047655 : Nat := 4983230072969 + 3 ^ 40 * 7047655 * 2
def baseEnd_7047655 : Nat := 3618834502062728751100931

theorem tailTrace_7047655 : CollatzResearch.WordTrace tailWord_7047655 prefixEnd_7047655 3618834502062728751100931 := by
  unfold tailWord_7047655
  simp only [CollatzResearch.WordTrace]
  refine ⟨257049095282557053492144419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171366063521704702328096279 257049095282557053492144419)
  ·
    refine ⟨385573642923835580238216629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 257049095282557053492144419 385573642923835580238216629)
    ·
      refine ⟨36147529024109585647332809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 385573642923835580238216629 36147529024109585647332809)
      ·
        refine ⟨27110646768082189235499607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36147529024109585647332809 27110646768082189235499607)
        ·
          refine ⟨40665970152123283853249411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27110646768082189235499607 40665970152123283853249411)
          ·
            refine ⟨60998955228184925779874117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40665970152123283853249411 60998955228184925779874117)
            ·
              refine ⟨11437304105284673583726397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 60998955228184925779874117 11437304105284673583726397)
              ·
                refine ⟨4288989039481752593897399, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11437304105284673583726397 4288989039481752593897399)
                ·
                  refine ⟨6433483559222628890846099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4288989039481752593897399 6433483559222628890846099)
                  ·
                    refine ⟨9650225338833943336269149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6433483559222628890846099 9650225338833943336269149)
                    ·
                      refine ⟨3618834502062728751100931, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9650225338833943336269149 3618834502062728751100931)
                      ·
                        rfl

theorem cell23_7047655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 4, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 4, 3, 1, 1, 3].length) (baseStart_7047655 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7047655 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7047655 prefixEnd_7047655 := by exact prefixLift 7047655
  have htrace : WordTrace (prefixWord ++ tailWord_7047655) baseStart_7047655 baseEnd_7047655 := by
    simpa [prefixWord, tailWord_7047655, baseEnd_7047655] using wordTrace_append hprefix tailTrace_7047655
  have hstable : (prefixWord ++ tailWord_7047655).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7047655).length < 2 ^ (prefixWord ++ tailWord_7047655).sum := by decide
  have hdescent : baseEnd_7047655 < baseStart_7047655 := by decide
  rcases family_descends (prefixWord ++ tailWord_7047655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7047658 : List Nat := [3, 1, 3, 1, 3, 1, 4, 1, 1, 5]
def baseStart_7047658 : Nat := 118140960795 + 7047658 * 2 ^ 59
def prefixEnd_7047658 : Nat := 4983230072969 + 3 ^ 40 * 7047658 * 2
def baseEnd_7047658 : Nat := 1206278680834897413121139

theorem tailTrace_7047658 : CollatzResearch.WordTrace tailWord_7047658 prefixEnd_7047658 1206278680834897413121139 := by
  unfold tailWord_7047658
  simp only [CollatzResearch.WordTrace]
  refine ⟨64262301175386546251125907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 171366136467697456669669085 64262301175386546251125907)
  ·
    refine ⟨96393451763079819376688861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64262301175386546251125907 96393451763079819376688861)
    ·
      refine ⟨36147544411154932266258323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 96393451763079819376688861 36147544411154932266258323)
      ·
        refine ⟨54221316616732398399387485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36147544411154932266258323 54221316616732398399387485)
        ·
          refine ⟨20332993731274649399770307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 54221316616732398399387485 20332993731274649399770307)
          ·
            refine ⟨30499490596911974099655461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20332993731274649399770307 30499490596911974099655461)
            ·
              refine ⟨5718654486920995143685399, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 30499490596911974099655461 5718654486920995143685399)
              ·
                refine ⟨8577981730381492715528099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5718654486920995143685399 8577981730381492715528099)
                ·
                  refine ⟨12866972595572239073292149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8577981730381492715528099 12866972595572239073292149)
                  ·
                    refine ⟨1206278680834897413121139, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12866972595572239073292149 1206278680834897413121139)
                    ·
                      rfl

theorem cell23_7047658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 1, 4, 1, 1, 5].length) (baseStart_7047658 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7047658 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7047658 prefixEnd_7047658 := by exact prefixLift 7047658
  have htrace : WordTrace (prefixWord ++ tailWord_7047658) baseStart_7047658 baseEnd_7047658 := by
    simpa [prefixWord, tailWord_7047658, baseEnd_7047658] using wordTrace_append hprefix tailTrace_7047658
  have hstable : (prefixWord ++ tailWord_7047658).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7047658).length < 2 ^ (prefixWord ++ tailWord_7047658).sum := by decide
  have hdescent : baseEnd_7047658 < baseStart_7047658 := by decide
  rcases family_descends (prefixWord ++ tailWord_7047658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7047664 : List Nat := [2, 1, 1, 1, 3, 3, 2, 3, 1, 1, 5]
def baseStart_7047664 : Nat := 118140960795 + 7047664 * 2 ^ 59
def prefixEnd_7047664 : Nat := 4983230072969 + 3 ^ 40 * 7047664 * 2
def baseEnd_7047664 : Nat := 3618839123388619215888389

theorem tailTrace_7047664 : CollatzResearch.WordTrace tailWord_7047664 prefixEnd_7047664 3618839123388619215888389 := by
  unfold tailWord_7047664
  simp only [CollatzResearch.WordTrace]
  refine ⟨128524711769762224014611023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 171366282359682965352814697 128524711769762224014611023)
  ·
    refine ⟨192787067654643336021916535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128524711769762224014611023 192787067654643336021916535)
    ·
      refine ⟨289180601481965004032874803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 192787067654643336021916535 289180601481965004032874803)
      ·
        refine ⟨433770902222947506049312205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 289180601481965004032874803 433770902222947506049312205)
        ·
          refine ⟨162664088333605314768492077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 433770902222947506049312205 162664088333605314768492077)
          ·
            refine ⟨60999033125101993038184529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 162664088333605314768492077 60999033125101993038184529)
            ·
              refine ⟨45749274843826494778638397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 60999033125101993038184529 45749274843826494778638397)
              ·
                refine ⟨17155978066434935541989399, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 45749274843826494778638397 17155978066434935541989399)
                ·
                  refine ⟨25733967099652403312984099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17155978066434935541989399 25733967099652403312984099)
                  ·
                    refine ⟨38600950649478604969476149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 25733967099652403312984099 38600950649478604969476149)
                    ·
                      refine ⟨3618839123388619215888389, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 38600950649478604969476149 3618839123388619215888389)
                      ·
                        rfl

theorem cell23_7047664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 2, 3, 1, 1, 5].length) (baseStart_7047664 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7047664 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7047664 prefixEnd_7047664 := by exact prefixLift 7047664
  have htrace : WordTrace (prefixWord ++ tailWord_7047664) baseStart_7047664 baseEnd_7047664 := by
    simpa [prefixWord, tailWord_7047664, baseEnd_7047664] using wordTrace_append hprefix tailTrace_7047664
  have hstable : (prefixWord ++ tailWord_7047664).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7047664).length < 2 ^ (prefixWord ++ tailWord_7047664).sum := by decide
  have hdescent : baseEnd_7047664 < baseStart_7047664 := by decide
  rcases family_descends (prefixWord ++ tailWord_7047664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7047667 : List Nat := [1, 1, 1, 2, 2, 2, 14]
def baseStart_7047667 : Nat := 118140960795 + 7047667 * 2 ^ 59
def prefixEnd_7047667 : Nat := 4983230072969 + 3 ^ 40 * 7047667 * 2
def baseEnd_7047667 : Nat := 44677045232476329680875

theorem tailTrace_7047667 : CollatzResearch.WordTrace tailWord_7047667 prefixEnd_7047667 44677045232476329680875 := by
  unfold tailWord_7047667
  simp only [CollatzResearch.WordTrace]
  refine ⟨257049532958513579541581255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171366355305675719694387503 257049532958513579541581255)
  ·
    refine ⟨385574299437770369312371883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 257049532958513579541581255 385574299437770369312371883)
    ·
      refine ⟨578361449156655553968557825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 385574299437770369312371883 578361449156655553968557825)
      ·
        refine ⟨433771086867491665476418369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 578361449156655553968557825 433771086867491665476418369)
        ·
          refine ⟨325328315150618749107313777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 433771086867491665476418369 325328315150618749107313777)
          ·
            refine ⟨243996236362964061830485333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 325328315150618749107313777 243996236362964061830485333)
            ·
              refine ⟨44677045232476329680875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 14 243996236362964061830485333 44677045232476329680875)
              ·
                rfl

theorem cell23_7047667_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 14].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 14].length) (baseStart_7047667 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7047667 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7047667 prefixEnd_7047667 := by exact prefixLift 7047667
  have htrace : WordTrace (prefixWord ++ tailWord_7047667) baseStart_7047667 baseEnd_7047667 := by
    simpa [prefixWord, tailWord_7047667, baseEnd_7047667] using wordTrace_append hprefix tailTrace_7047667
  have hstable : (prefixWord ++ tailWord_7047667).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7047667).length < 2 ^ (prefixWord ++ tailWord_7047667).sum := by decide
  have hdescent : baseEnd_7047667 < baseStart_7047667 := by decide
  rcases family_descends (prefixWord ++ tailWord_7047667) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7047681 : List Nat := [1, 2, 4, 1, 3, 2, 1, 2, 1, 1, 5]
def baseStart_7047681 : Nat := 118140960795 + 7047681 * 2 ^ 59
def prefixEnd_7047681 : Nat := 4983230072969 + 3 ^ 40 * 7047681 * 2
def baseEnd_7047681 : Nat := 3618847852559745649375811

theorem tailTrace_7047681 : CollatzResearch.WordTrace tailWord_7047681 prefixEnd_7047681 3618847852559745649375811 := by
  unfold tailWord_7047681
  simp only [CollatzResearch.WordTrace]
  refine ⟨257050043580462859932590897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171366695720308573288393931 257050043580462859932590897)
  ·
    refine ⟨192787532685347144949443173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 257050043580462859932590897 192787532685347144949443173)
    ·
      refine ⟨36147662378502589678020595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 192787532685347144949443173 36147662378502589678020595)
      ·
        refine ⟨54221493567753884517030893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36147662378502589678020595 54221493567753884517030893)
        ·
          refine ⟨20333060087907706693886585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 54221493567753884517030893 20333060087907706693886585)
          ·
            refine ⟨15249795065930780020414939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20333060087907706693886585 15249795065930780020414939)
            ·
              refine ⟨22874692598896170030622409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15249795065930780020414939 22874692598896170030622409)
              ·
                refine ⟨17156019449172127522966807, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22874692598896170030622409 17156019449172127522966807)
                ·
                  refine ⟨25734029173758191284450211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17156019449172127522966807 25734029173758191284450211)
                  ·
                    refine ⟨38601043760637286926675317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 25734029173758191284450211 38601043760637286926675317)
                    ·
                      refine ⟨3618847852559745649375811, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 38601043760637286926675317 3618847852559745649375811)
                      ·
                        rfl

theorem cell23_7047681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 2, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 2, 1, 2, 1, 1, 5].length) (baseStart_7047681 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7047681 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7047681 prefixEnd_7047681 := by exact prefixLift 7047681
  have htrace : WordTrace (prefixWord ++ tailWord_7047681) baseStart_7047681 baseEnd_7047681 := by
    simpa [prefixWord, tailWord_7047681, baseEnd_7047681] using wordTrace_append hprefix tailTrace_7047681
  have hstable : (prefixWord ++ tailWord_7047681).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7047681).length < 2 ^ (prefixWord ++ tailWord_7047681).sum := by decide
  have hdescent : baseEnd_7047681 < baseStart_7047681 := by decide
  rcases family_descends (prefixWord ++ tailWord_7047681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7047691 : List Nat := [1, 1, 1, 1, 7, 1, 3, 1, 1, 2, 4]
def baseStart_7047691 : Nat := 118140960795 + 7047691 * 2 ^ 59
def prefixEnd_7047691 : Nat := 4983230072969 + 3 ^ 40 * 7047691 * 2
def baseEnd_7047691 : Nat := 3618852987366290610250765

theorem tailTrace_7047691 : CollatzResearch.WordTrace tailWord_7047691 prefixEnd_7047691 3618852987366290610250765 := by
  unfold tailWord_7047691
  simp only [CollatzResearch.WordTrace]
  refine ⟨257050408310426631640454927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171366938873617754426969951 257050408310426631640454927)
  ·
    refine ⟨385575612465639947460682391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 257050408310426631640454927 385575612465639947460682391)
    ·
      refine ⟨578363418698459921191023587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 385575612465639947460682391 578363418698459921191023587)
      ·
        refine ⟨867545128047689881786535381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 578363418698459921191023587 867545128047689881786535381)
        ·
          refine ⟨20333088938617731604371923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 867545128047689881786535381 20333088938617731604371923)
          ·
            refine ⟨30499633407926597406557885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20333088938617731604371923 30499633407926597406557885)
            ·
              refine ⟨11437362527972474027459207, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30499633407926597406557885 11437362527972474027459207)
              ·
                refine ⟨17156043791958711041188811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11437362527972474027459207 17156043791958711041188811)
                ·
                  refine ⟨25734065687938066561783217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17156043791958711041188811 25734065687938066561783217)
                  ·
                    refine ⟨19300549265953549921337413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25734065687938066561783217 19300549265953549921337413)
                    ·
                      refine ⟨3618852987366290610250765, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19300549265953549921337413 3618852987366290610250765)
                      ·
                        rfl

theorem cell23_7047691_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 1, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 1, 3, 1, 1, 2, 4].length) (baseStart_7047691 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7047691 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7047691 prefixEnd_7047691 := by exact prefixLift 7047691
  have htrace : WordTrace (prefixWord ++ tailWord_7047691) baseStart_7047691 baseEnd_7047691 := by
    simpa [prefixWord, tailWord_7047691, baseEnd_7047691] using wordTrace_append hprefix tailTrace_7047691
  have hstable : (prefixWord ++ tailWord_7047691).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7047691).length < 2 ^ (prefixWord ++ tailWord_7047691).sum := by decide
  have hdescent : baseEnd_7047691 < baseStart_7047691 := by decide
  rcases family_descends (prefixWord ++ tailWord_7047691) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7047714 : List Nat := [3, 3, 1, 1, 1, 1, 1, 2, 1, 9]
def baseStart_7047714 : Nat := 118140960795 + 7047714 * 2 ^ 59
def prefixEnd_7047714 : Nat := 4983230072969 + 3 ^ 40 * 7047714 * 2
def baseEnd_7047714 : Nat := 1206288265807114673421053

theorem tailTrace_7047714 : CollatzResearch.WordTrace tailWord_7047714 prefixEnd_7047714 1206288265807114673421053 := by
  unfold tailWord_7047714
  simp only [CollatzResearch.WordTrace]
  refine ⟨64262811797335826642135549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 171367498126228871045694797 64262811797335826642135549)
  ·
    refine ⟨24098554424000934990800831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 64262811797335826642135549 24098554424000934990800831)
    ·
      refine ⟨36147831636001402486201247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24098554424000934990800831 36147831636001402486201247)
      ·
        refine ⟨54221747454002103729301871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36147831636001402486201247 54221747454002103729301871)
        ·
          refine ⟨81332621181003155593952807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54221747454002103729301871 81332621181003155593952807)
          ·
            refine ⟨121998931771504733390929211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81332621181003155593952807 121998931771504733390929211)
            ·
              refine ⟨182998397657257100086393817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 121998931771504733390929211 182998397657257100086393817)
              ·
                refine ⟨137248798242942825064795363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 182998397657257100086393817 137248798242942825064795363)
                ·
                  refine ⟨205873197364414237597193045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 137248798242942825064795363 205873197364414237597193045)
                  ·
                    refine ⟨1206288265807114673421053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 205873197364414237597193045 1206288265807114673421053)
                    ·
                      rfl

theorem cell23_7047714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 1, 2, 1, 9].length) (baseStart_7047714 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7047714 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7047714 prefixEnd_7047714 := by exact prefixLift 7047714
  have htrace : WordTrace (prefixWord ++ tailWord_7047714) baseStart_7047714 baseEnd_7047714 := by
    simpa [prefixWord, tailWord_7047714, baseEnd_7047714] using wordTrace_append hprefix tailTrace_7047714
  have hstable : (prefixWord ++ tailWord_7047714).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7047714).length < 2 ^ (prefixWord ++ tailWord_7047714).sum := by decide
  have hdescent : baseEnd_7047714 < baseStart_7047714 := by decide
  rcases family_descends (prefixWord ++ tailWord_7047714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7047744 : List Nat := [2, 1, 1, 2, 2, 2, 2, 3, 2, 6]
def baseStart_7047744 : Nat := 118140960795 + 7047744 * 2 ^ 59
def prefixEnd_7047744 : Nat := 4983230072969 + 3 ^ 40 * 7047744 * 2
def baseEnd_7047744 : Nat := 1206293400613659634296007

theorem tailTrace_7047744 : CollatzResearch.WordTrace tailWord_7047744 prefixEnd_7047744 1206293400613659634296007 := by
  unfold tailWord_7047744
  simp only [CollatzResearch.WordTrace]
  refine ⟨128526170689617310846067143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 171368227586156414461422857 128526170689617310846067143)
  ·
    refine ⟨192789256034425966269100715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128526170689617310846067143 192789256034425966269100715)
    ·
      refine ⟨289183884051638949403651073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 192789256034425966269100715 289183884051638949403651073)
      ·
        refine ⟨216887913038729212052738305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 289183884051638949403651073 216887913038729212052738305)
        ·
          refine ⟨162665934779046909039553729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 216887913038729212052738305 162665934779046909039553729)
          ·
            refine ⟨121999451084285181779665297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 162665934779046909039553729 121999451084285181779665297)
            ·
              refine ⟨91499588313213886334748973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 121999451084285181779665297 91499588313213886334748973)
              ·
                refine ⟨34312345617455207375530865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 91499588313213886334748973 34312345617455207375530865)
                ·
                  refine ⟨25734259213091405531648149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34312345617455207375530865 25734259213091405531648149)
                  ·
                    refine ⟨1206293400613659634296007, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25734259213091405531648149 1206293400613659634296007)
                    ·
                      rfl

theorem cell23_7047744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 2, 3, 2, 6].length) (baseStart_7047744 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7047744 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7047744 prefixEnd_7047744 := by exact prefixLift 7047744
  have htrace : WordTrace (prefixWord ++ tailWord_7047744) baseStart_7047744 baseEnd_7047744 := by
    simpa [prefixWord, tailWord_7047744, baseEnd_7047744] using wordTrace_append hprefix tailTrace_7047744
  have hstable : (prefixWord ++ tailWord_7047744).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7047744).length < 2 ^ (prefixWord ++ tailWord_7047744).sum := by decide
  have hdescent : baseEnd_7047744 < baseStart_7047744 := by decide
  rcases family_descends (prefixWord ++ tailWord_7047744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7047745 : List Nat := [1, 2, 5, 1, 1, 3, 1, 3, 2, 1, 3]
def baseStart_7047745 : Nat := 118140960795 + 7047745 * 2 ^ 59
def prefixEnd_7047745 : Nat := 4983230072969 + 3 ^ 40 * 7047745 * 2
def baseEnd_7047745 : Nat := 3618880715321633398975517

theorem tailTrace_7047745 : CollatzResearch.WordTrace tailWord_7047745 prefixEnd_7047745 3618880715321633398975517 := by
  unfold tailWord_7047745
  simp only [CollatzResearch.WordTrace]
  refine ⟨257052377852230998862920689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171368251901487332575280459 257052377852230998862920689)
  ·
    refine ⟨192789283389173249147190517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 257052377852230998862920689 192789283389173249147190517)
    ·
      refine ⟨18073995317734992107549111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 192789283389173249147190517 18073995317734992107549111)
      ·
        refine ⟨27110992976602488161323667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18073995317734992107549111 27110992976602488161323667)
        ·
          refine ⟨40666489464903732241985501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27110992976602488161323667 40666489464903732241985501)
          ·
            refine ⟨15249933549338899590744563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40666489464903732241985501 15249933549338899590744563)
            ·
              refine ⟨22874900324008349386116845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15249933549338899590744563 22874900324008349386116845)
              ·
                refine ⟨8578087621503131019793817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22874900324008349386116845 8578087621503131019793817)
                ·
                  refine ⟨6433565716127348264845363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8578087621503131019793817 6433565716127348264845363)
                  ·
                    refine ⟨9650348574191022397268045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6433565716127348264845363 9650348574191022397268045)
                    ·
                      refine ⟨3618880715321633398975517, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9650348574191022397268045 3618880715321633398975517)
                      ·
                        rfl

theorem cell23_7047745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 3, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 3, 1, 3, 2, 1, 3].length) (baseStart_7047745 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7047745 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7047745 prefixEnd_7047745 := by exact prefixLift 7047745
  have htrace : WordTrace (prefixWord ++ tailWord_7047745) baseStart_7047745 baseEnd_7047745 := by
    simpa [prefixWord, tailWord_7047745, baseEnd_7047745] using wordTrace_append hprefix tailTrace_7047745
  have hstable : (prefixWord ++ tailWord_7047745).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7047745).length < 2 ^ (prefixWord ++ tailWord_7047745).sum := by decide
  have hdescent : baseEnd_7047745 < baseStart_7047745 := by decide
  rcases family_descends (prefixWord ++ tailWord_7047745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7047768 : List Nat := [2, 1, 2, 2, 1, 2, 2, 1, 6, 2, 2]
def baseStart_7047768 : Nat := 118140960795 + 7047768 * 2 ^ 59
def prefixEnd_7047768 : Nat := 4983230072969 + 3 ^ 40 * 7047768 * 2
def baseEnd_7047768 : Nat := 3618892525376686808987911

theorem tailTrace_7047768 : CollatzResearch.WordTrace tailWord_7047768 prefixEnd_7047768 3618892525376686808987911 := by
  unfold tailWord_7047768
  simp only [CollatzResearch.WordTrace]
  refine ⟨128526608365573836895503979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 171368811154098449194005305 128526608365573836895503979)
  ·
    refine ⟨192789912548360755343255969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128526608365573836895503979 192789912548360755343255969)
    ·
      refine ⟨144592434411270566507441977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 192789912548360755343255969 144592434411270566507441977)
      ·
        refine ⟨108444325808452924880581483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 144592434411270566507441977 108444325808452924880581483)
        ·
          refine ⟨162666488712679387320872225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 108444325808452924880581483 162666488712679387320872225)
          ·
            refine ⟨121999866534509540490654169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 162666488712679387320872225 121999866534509540490654169)
            ·
              refine ⟨91499899900882155367990627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 121999866534509540490654169 91499899900882155367990627)
              ·
                refine ⟨137249849851323233051985941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 91499899900882155367990627 137249849851323233051985941)
                ·
                  refine ⟨6433586711780776549311841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 137249849851323233051985941 6433586711780776549311841)
                  ·
                    refine ⟨4825190033835582411983881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6433586711780776549311841 4825190033835582411983881)
                    ·
                      refine ⟨3618892525376686808987911, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4825190033835582411983881 3618892525376686808987911)
                      ·
                        rfl

theorem cell23_7047768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 2, 1, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 2, 1, 6, 2, 2].length) (baseStart_7047768 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7047768 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7047768 prefixEnd_7047768 := by exact prefixLift 7047768
  have htrace : WordTrace (prefixWord ++ tailWord_7047768) baseStart_7047768 baseEnd_7047768 := by
    simpa [prefixWord, tailWord_7047768, baseEnd_7047768] using wordTrace_append hprefix tailTrace_7047768
  have hstable : (prefixWord ++ tailWord_7047768).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7047768).length < 2 ^ (prefixWord ++ tailWord_7047768).sum := by decide
  have hdescent : baseEnd_7047768 < baseStart_7047768 := by decide
  rcases family_descends (prefixWord ++ tailWord_7047768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7047801 : List Nat := [1, 2, 1, 3, 3, 2, 1, 1, 1, 5, 3]
def baseStart_7047801 : Nat := 118140960795 + 7047801 * 2 ^ 59
def prefixEnd_7047801 : Nat := 4983230072969 + 3 ^ 40 * 7047801 * 2
def baseEnd_7047801 : Nat := 3618909470238285179875259

theorem tailTrace_7047801 : CollatzResearch.WordTrace tailWord_7047801 prefixEnd_7047801 3618909470238285179875259 := by
  unfold tailWord_7047801
  simp only [CollatzResearch.WordTrace]
  refine ⟨257054420340028120426959257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171369613560018746951306171 257054420340028120426959257)
  ·
    refine ⟨192790815255021090320219443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 257054420340028120426959257 192790815255021090320219443)
    ·
      refine ⟨289186222882531635480329165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 192790815255021090320219443 289186222882531635480329165)
      ·
        refine ⟨108444833580949363305123437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 289186222882531635480329165 108444833580949363305123437)
        ·
          refine ⟨40666812592856011239421289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 108444833580949363305123437 40666812592856011239421289)
          ·
            refine ⟨30500109444642008429565967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40666812592856011239421289 30500109444642008429565967)
            ·
              refine ⟨45750164166963012644348951, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30500109444642008429565967 45750164166963012644348951)
              ·
                refine ⟨68625246250444518966523427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45750164166963012644348951 68625246250444518966523427)
                ·
                  refine ⟨102937869375666778449785141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 68625246250444518966523427 102937869375666778449785141)
                  ·
                    refine ⟨9650425253968760479667357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 102937869375666778449785141 9650425253968760479667357)
                    ·
                      refine ⟨3618909470238285179875259, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9650425253968760479667357 3618909470238285179875259)
                      ·
                        rfl

theorem cell23_7047801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 2, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 2, 1, 1, 1, 5, 3].length) (baseStart_7047801 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7047801 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7047801 prefixEnd_7047801 := by exact prefixLift 7047801
  have htrace : WordTrace (prefixWord ++ tailWord_7047801) baseStart_7047801 baseEnd_7047801 := by
    simpa [prefixWord, tailWord_7047801, baseEnd_7047801] using wordTrace_append hprefix tailTrace_7047801
  have hstable : (prefixWord ++ tailWord_7047801).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7047801).length < 2 ^ (prefixWord ++ tailWord_7047801).sum := by decide
  have hdescent : baseEnd_7047801 < baseStart_7047801 := by decide
  rcases family_descends (prefixWord ++ tailWord_7047801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7047838 : List Nat := [4, 3, 1, 1, 1, 1, 2, 1, 4, 5]
def baseStart_7047838 : Nat := 118140960795 + 7047838 * 2 ^ 59
def prefixEnd_7047838 : Nat := 4983230072969 + 3 ^ 40 * 7047838 * 2
def baseEnd_7047838 : Nat := 1206309489674167178370863

theorem tailTrace_7047838 : CollatzResearch.WordTrace tailWord_7047838 prefixEnd_7047838 1206309489674167178370863 := by
  unfold tailWord_7047838
  simp only [CollatzResearch.WordTrace]
  refine ⟨32131971230111759468257021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 171370513227262717164037445 32131971230111759468257021)
  ·
    refine ⟨12049489211291909800596383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32131971230111759468257021 12049489211291909800596383)
    ·
      refine ⟨18074233816937864700894575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12049489211291909800596383 18074233816937864700894575)
      ·
        refine ⟨27111350725406797051341863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18074233816937864700894575 27111350725406797051341863)
        ·
          refine ⟨40667026088110195577012795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27111350725406797051341863 40667026088110195577012795)
          ·
            refine ⟨61000539132165293365519193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40667026088110195577012795 61000539132165293365519193)
            ·
              refine ⟨45750404349123970024139395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 61000539132165293365519193 45750404349123970024139395)
              ·
                refine ⟨68625606523685955036209093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45750404349123970024139395 68625606523685955036209093)
                ·
                  refine ⟨12867301223191116569289205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 68625606523685955036209093 12867301223191116569289205)
                  ·
                    refine ⟨1206309489674167178370863, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12867301223191116569289205 1206309489674167178370863)
                    ·
                      rfl

theorem cell23_7047838_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 2, 1, 4, 5].length) (baseStart_7047838 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7047838 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7047838 prefixEnd_7047838 := by exact prefixLift 7047838
  have htrace : WordTrace (prefixWord ++ tailWord_7047838) baseStart_7047838 baseEnd_7047838 := by
    simpa [prefixWord, tailWord_7047838, baseEnd_7047838] using wordTrace_append hprefix tailTrace_7047838
  have hstable : (prefixWord ++ tailWord_7047838).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7047838).length < 2 ^ (prefixWord ++ tailWord_7047838).sum := by decide
  have hdescent : baseEnd_7047838 < baseStart_7047838 := by decide
  rcases family_descends (prefixWord ++ tailWord_7047838) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7047868 : List Nat := [2, 2, 2, 3, 1, 1, 1, 4, 3, 4]
def baseStart_7047868 : Nat := 118140960795 + 7047868 * 2 ^ 59
def prefixEnd_7047868 : Nat := 4983230072969 + 3 ^ 40 * 7047868 * 2
def baseEnd_7047868 : Nat := 1206314624480712139245817

theorem tailTrace_7047868 : CollatzResearch.WordTrace tailWord_7047868 prefixEnd_7047868 1206314624480712139245817 := by
  unfold tailWord_7047868
  simp only [CollatzResearch.WordTrace]
  refine ⟨128528432015392695434824129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 171371242687190260579765505 128528432015392695434824129)
  ·
    refine ⟨96396324011544521576118097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 128528432015392695434824129 96396324011544521576118097)
    ·
      refine ⟨72297243008658391182088573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 96396324011544521576118097 72297243008658391182088573)
      ·
        refine ⟨27111466128246896693283215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 72297243008658391182088573 27111466128246896693283215)
        ·
          refine ⟨40667199192370345039924823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27111466128246896693283215 40667199192370345039924823)
          ·
            refine ⟨61000798788555517559887235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40667199192370345039924823 61000798788555517559887235)
            ·
              refine ⟨91501198182833276339830853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61000798788555517559887235 91501198182833276339830853)
              ·
                refine ⟨17156474659281239313718285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 91501198182833276339830853 17156474659281239313718285)
                ·
                  refine ⟨6433677997230464742644357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17156474659281239313718285 6433677997230464742644357)
                  ·
                    refine ⟨1206314624480712139245817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6433677997230464742644357 1206314624480712139245817)
                    ·
                      rfl

theorem cell23_7047868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 1, 4, 3, 4].length) (baseStart_7047868 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7047868 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7047868 prefixEnd_7047868 := by exact prefixLift 7047868
  have htrace : WordTrace (prefixWord ++ tailWord_7047868) baseStart_7047868 baseEnd_7047868 := by
    simpa [prefixWord, tailWord_7047868, baseEnd_7047868] using wordTrace_append hprefix tailTrace_7047868
  have hstable : (prefixWord ++ tailWord_7047868).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7047868).length < 2 ^ (prefixWord ++ tailWord_7047868).sum := by decide
  have hdescent : baseEnd_7047868 < baseStart_7047868 := by decide
  rcases family_descends (prefixWord ++ tailWord_7047868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7047959 : List Nat := [1, 1, 3, 4, 3, 1, 1, 4, 1, 1, 3]
def baseStart_7047959 : Nat := 118140960795 + 7047959 * 2 ^ 59
def prefixEnd_7047959 : Nat := 4983230072969 + 3 ^ 40 * 7047959 * 2
def baseEnd_7047959 : Nat := 3618990600181695561699533

theorem tailTrace_7047959 : CollatzResearch.WordTrace tailWord_7047959 prefixEnd_7047959 3618990600181695561699533 := by
  unfold tailWord_7047959
  simp only [CollatzResearch.WordTrace]
  refine ⟨257060183073455713411210931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171373455382303808940807287 257060183073455713411210931)
  ·
    refine ⟨385590274610183570116816397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 257060183073455713411210931 385590274610183570116816397)
    ·
      refine ⟨144596352978818838793806149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 385590274610183570116816397 144596352978818838793806149)
      ·
        refine ⟨27111816183528532273838653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 144596352978818838793806149 27111816183528532273838653)
        ·
          refine ⟨10166931068823199602689495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27111816183528532273838653 10166931068823199602689495)
          ·
            refine ⟨15250396603234799404034243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10166931068823199602689495 15250396603234799404034243)
            ·
              refine ⟨22875594904852199106051365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15250396603234799404034243 22875594904852199106051365)
              ·
                refine ⟨4289174044659787332384631, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22875594904852199106051365 4289174044659787332384631)
                ·
                  refine ⟨6433761066989680998576947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4289174044659787332384631 6433761066989680998576947)
                  ·
                    refine ⟨9650641600484521497865421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6433761066989680998576947 9650641600484521497865421)
                    ·
                      refine ⟨3618990600181695561699533, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9650641600484521497865421 3618990600181695561699533)
                      ·
                        rfl

theorem cell23_7047959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 3, 1, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 3, 1, 1, 4, 1, 1, 3].length) (baseStart_7047959 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7047959 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7047959 prefixEnd_7047959 := by exact prefixLift 7047959
  have htrace : WordTrace (prefixWord ++ tailWord_7047959) baseStart_7047959 baseEnd_7047959 := by
    simpa [prefixWord, tailWord_7047959, baseEnd_7047959] using wordTrace_append hprefix tailTrace_7047959
  have hstable : (prefixWord ++ tailWord_7047959).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7047959).length < 2 ^ (prefixWord ++ tailWord_7047959).sum := by decide
  have hdescent : baseEnd_7047959 < baseStart_7047959 := by decide
  rcases family_descends (prefixWord ++ tailWord_7047959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7047961 : List Nat := [1, 2, 1, 2, 1, 1, 1, 6, 1, 1, 6]
def baseStart_7047961 : Nat := 118140960795 + 7047961 * 2 ^ 59
def prefixEnd_7047961 : Nat := 4983230072969 + 3 ^ 40 * 7047961 * 2
def baseEnd_7047961 : Nat := 3618991627143004553874523

theorem tailTrace_7047961 : CollatzResearch.WordTrace tailWord_7047961 prefixEnd_7047961 3618991627143004553874523 := by
  unfold tailWord_7047961
  simp only [CollatzResearch.WordTrace]
  refine ⟨257060256019448467752783737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171373504012965645168522491 257060256019448467752783737)
  ·
    refine ⟨192795192014586350814587803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 257060256019448467752783737 192795192014586350814587803)
    ·
      refine ⟨289192788021879526221881705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 192795192014586350814587803 289192788021879526221881705)
      ·
        refine ⟨216894591016409644666411279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 289192788021879526221881705 216894591016409644666411279)
        ·
          refine ⟨325341886524614466999616919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 216894591016409644666411279 325341886524614466999616919)
          ·
            refine ⟨488012829786921700499425379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 325341886524614466999616919 488012829786921700499425379)
            ·
              refine ⟨732019244680382550749138069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 488012829786921700499425379 732019244680382550749138069)
              ·
                refine ⟨34313402094392932066365847, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 732019244680382550749138069 34313402094392932066365847)
                ·
                  refine ⟨51470103141589398099548771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34313402094392932066365847 51470103141589398099548771)
                  ·
                    refine ⟨77205154712384097149323157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 51470103141589398099548771 77205154712384097149323157)
                    ·
                      refine ⟨3618991627143004553874523, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 77205154712384097149323157 3618991627143004553874523)
                      ·
                        rfl

theorem cell23_7047961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 6, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 6, 1, 1, 6].length) (baseStart_7047961 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7047961 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7047961 prefixEnd_7047961 := by exact prefixLift 7047961
  have htrace : WordTrace (prefixWord ++ tailWord_7047961) baseStart_7047961 baseEnd_7047961 := by
    simpa [prefixWord, tailWord_7047961, baseEnd_7047961] using wordTrace_append hprefix tailTrace_7047961
  have hstable : (prefixWord ++ tailWord_7047961).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7047961).length < 2 ^ (prefixWord ++ tailWord_7047961).sum := by decide
  have hdescent : baseEnd_7047961 < baseStart_7047961 := by decide
  rcases family_descends (prefixWord ++ tailWord_7047961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7047985 : List Nat := [1, 2, 2, 3, 2, 1, 2, 4, 1, 2, 3]
def baseStart_7047985 : Nat := 118140960795 + 7047985 * 2 ^ 59
def prefixEnd_7047985 : Nat := 4983230072969 + 3 ^ 40 * 7047985 * 2
def baseEnd_7047985 : Nat := 3619003950678712459974413

theorem tailTrace_7047985 : CollatzResearch.WordTrace tailWord_7047985 prefixEnd_7047985 3619003950678712459974413 := by
  unfold tailWord_7047985
  simp only [CollatzResearch.WordTrace]
  refine ⟨257061131371361519851657409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171374087580907679901104939 257061131371361519851657409)
  ·
    refine ⟨192795848528521139888743057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 257061131371361519851657409 192795848528521139888743057)
    ·
      refine ⟨144596886396390854916557293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 192795848528521139888743057 144596886396390854916557293)
      ·
        refine ⟨54223832398646570593708985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 144596886396390854916557293 54223832398646570593708985)
        ·
          refine ⟨40667874298984927945281739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54223832398646570593708985 40667874298984927945281739)
          ·
            refine ⟨61001811448477391917922609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40667874298984927945281739 61001811448477391917922609)
            ·
              refine ⟨45751358586358043938441957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 61001811448477391917922609 45751358586358043938441957)
              ·
                refine ⟨8578379734942133238457867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 45751358586358043938441957 8578379734942133238457867)
                ·
                  refine ⟨12867569602413199857686801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8578379734942133238457867 12867569602413199857686801)
                  ·
                    refine ⟨9650677201809899893265101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12867569602413199857686801 9650677201809899893265101)
                    ·
                      refine ⟨3619003950678712459974413, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9650677201809899893265101 3619003950678712459974413)
                      ·
                        rfl

theorem cell23_7047985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 2, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 2, 4, 1, 2, 3].length) (baseStart_7047985 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7047985 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7047985 prefixEnd_7047985 := by exact prefixLift 7047985
  have htrace : WordTrace (prefixWord ++ tailWord_7047985) baseStart_7047985 baseEnd_7047985 := by
    simpa [prefixWord, tailWord_7047985, baseEnd_7047985] using wordTrace_append hprefix tailTrace_7047985
  have hstable : (prefixWord ++ tailWord_7047985).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7047985).length < 2 ^ (prefixWord ++ tailWord_7047985).sum := by decide
  have hdescent : baseEnd_7047985 < baseStart_7047985 := by decide
  rcases family_descends (prefixWord ++ tailWord_7047985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7047999 : List Nat := [1, 1, 2, 2, 5, 1, 1, 5, 1, 2, 2]
def baseStart_7047999 : Nat := 118140960795 + 7047999 * 2 ^ 59
def prefixEnd_7047999 : Nat := 4983230072969 + 3 ^ 40 * 7047999 * 2
def baseEnd_7047999 : Nat := 3619011139407875405199349

theorem tailTrace_7047999 : CollatzResearch.WordTrace tailWord_7047999 prefixEnd_7047999 3619011139407875405199349 := by
  unfold tailWord_7047999
  simp only [CollatzResearch.WordTrace]
  refine ⟨257061641993310800242667051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171374427995540533495111367 257061641993310800242667051)
  ·
    refine ⟨385592462989966200364000577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 257061641993310800242667051 385592462989966200364000577)
    ·
      refine ⟨289194347242474650273000433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 385592462989966200364000577 289194347242474650273000433)
      ·
        refine ⟨216895760431855987704750325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 289194347242474650273000433 216895760431855987704750325)
        ·
          refine ⟨20333977540486498847320343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 216895760431855987704750325 20333977540486498847320343)
          ·
            refine ⟨30500966310729748270980515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20333977540486498847320343 30500966310729748270980515)
            ·
              refine ⟨45751449466094622406470773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30500966310729748270980515 45751449466094622406470773)
              ·
                refine ⟨4289198387446370850606635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 45751449466094622406470773 4289198387446370850606635)
                ·
                  refine ⟨6433797581169556275909953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4289198387446370850606635 6433797581169556275909953)
                  ·
                    refine ⟨4825348185877167206932465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6433797581169556275909953 4825348185877167206932465)
                    ·
                      refine ⟨3619011139407875405199349, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4825348185877167206932465 3619011139407875405199349)
                      ·
                        rfl

theorem cell23_7047999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 1, 1, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 1, 1, 5, 1, 2, 2].length) (baseStart_7047999 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7047999 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7047999 prefixEnd_7047999 := by exact prefixLift 7047999
  have htrace : WordTrace (prefixWord ++ tailWord_7047999) baseStart_7047999 baseEnd_7047999 := by
    simpa [prefixWord, tailWord_7047999, baseEnd_7047999] using wordTrace_append hprefix tailTrace_7047999
  have hstable : (prefixWord ++ tailWord_7047999).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7047999).length < 2 ^ (prefixWord ++ tailWord_7047999).sum := by decide
  have hdescent : baseEnd_7047999 < baseStart_7047999 := by decide
  rcases family_descends (prefixWord ++ tailWord_7047999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7048055 : List Nat := [1, 1, 3, 1, 1, 2, 1, 6, 1, 4, 2]
def baseStart_7048055 : Nat := 118140960795 + 7048055 * 2 ^ 59
def prefixEnd_7048055 : Nat := 4983230072969 + 3 ^ 40 * 7048055 * 2
def baseEnd_7048055 : Nat := 3619039894324527186099091

theorem tailTrace_7048055 : CollatzResearch.WordTrace tailWord_7048055 prefixEnd_7048055 3619039894324527186099091 := by
  unfold tailWord_7048055
  simp only [CollatzResearch.WordTrace]
  refine ⟨257063684481107921806705619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171375789654071947871137079 257063684481107921806705619)
  ·
    refine ⟨385595526721661882710058429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 257063684481107921806705619 385595526721661882710058429)
    ·
      refine ⟨144598322520623206016271911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 385595526721661882710058429 144598322520623206016271911)
      ·
        refine ⟨216897483780934809024407867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 144598322520623206016271911 216897483780934809024407867)
        ·
          refine ⟨325346225671402213536611801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 216897483780934809024407867 325346225671402213536611801)
          ·
            refine ⟨244009669253551660152458851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 325346225671402213536611801 244009669253551660152458851)
            ·
              refine ⟨366014503880327490228688277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 244009669253551660152458851 366014503880327490228688277)
              ·
                refine ⟨17156929869390351104469763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 366014503880327490228688277 17156929869390351104469763)
                ·
                  refine ⟨25735394804085526656704645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17156929869390351104469763 25735394804085526656704645)
                  ·
                    refine ⟨4825386525766036248132121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25735394804085526656704645 4825386525766036248132121)
                    ·
                      refine ⟨3619039894324527186099091, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4825386525766036248132121 3619039894324527186099091)
                      ·
                        rfl

theorem cell23_7048055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 1, 6, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 1, 6, 1, 4, 2].length) (baseStart_7048055 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7048055 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7048055 prefixEnd_7048055 := by exact prefixLift 7048055
  have htrace : WordTrace (prefixWord ++ tailWord_7048055) baseStart_7048055 baseEnd_7048055 := by
    simpa [prefixWord, tailWord_7048055, baseEnd_7048055] using wordTrace_append hprefix tailTrace_7048055
  have hstable : (prefixWord ++ tailWord_7048055).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7048055).length < 2 ^ (prefixWord ++ tailWord_7048055).sum := by decide
  have hdescent : baseEnd_7048055 < baseStart_7048055 := by decide
  rcases family_descends (prefixWord ++ tailWord_7048055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7048058 : List Nat := [3, 1, 1, 1, 1, 1, 3, 2, 1, 6, 3]
def baseStart_7048058 : Nat := 118140960795 + 7048058 * 2 ^ 59
def prefixEnd_7048058 : Nat := 4983230072969 + 3 ^ 40 * 7048058 * 2
def baseEnd_7048058 : Nat := 3619041434766490674361577

theorem tailTrace_7048058 : CollatzResearch.WordTrace tailWord_7048058 prefixEnd_7048058 3619041434766490674361577 := by
  unfold tailWord_7048058
  simp only [CollatzResearch.WordTrace]
  refine ⟨64265948475024263329766207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 171375862600064702212709885 64265948475024263329766207)
  ·
    refine ⟨96398922712536394994649311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64265948475024263329766207 96398922712536394994649311)
    ·
      refine ⟨144598384068804592491973967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96398922712536394994649311 144598384068804592491973967)
      ·
        refine ⟨216897576103206888737960951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 144598384068804592491973967 216897576103206888737960951)
        ·
          refine ⟨325346364154810333106941427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 216897576103206888737960951 325346364154810333106941427)
          ·
            refine ⟨488019546232215499660412141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 325346364154810333106941427 488019546232215499660412141)
            ·
              refine ⟨183007329837080812372654553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 488019546232215499660412141 183007329837080812372654553)
              ·
                refine ⟨137255497377810609279490915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 183007329837080812372654553 137255497377810609279490915)
                ·
                  refine ⟨205883246066715913919236373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 137255497377810609279490915 205883246066715913919236373)
                  ·
                    refine ⟨9650777159377308464964205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 205883246066715913919236373 9650777159377308464964205)
                    ·
                      refine ⟨3619041434766490674361577, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9650777159377308464964205 3619041434766490674361577)
                      ·
                        rfl

theorem cell23_7048058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 3, 2, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 3, 2, 1, 6, 3].length) (baseStart_7048058 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7048058 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7048058 prefixEnd_7048058 := by exact prefixLift 7048058
  have htrace : WordTrace (prefixWord ++ tailWord_7048058) baseStart_7048058 baseEnd_7048058 := by
    simpa [prefixWord, tailWord_7048058, baseEnd_7048058] using wordTrace_append hprefix tailTrace_7048058
  have hstable : (prefixWord ++ tailWord_7048058).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7048058).length < 2 ^ (prefixWord ++ tailWord_7048058).sum := by decide
  have hdescent : baseEnd_7048058 < baseStart_7048058 := by decide
  rcases family_descends (prefixWord ++ tailWord_7048058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7048108 : List Nat := [2, 2, 1, 1, 1, 1, 2, 2, 6, 5]
def baseStart_7048108 : Nat := 118140960795 + 7048108 * 2 ^ 59
def prefixEnd_7048108 : Nat := 4983230072969 + 3 ^ 40 * 7048108 * 2
def baseEnd_7048108 : Nat := 1206355702933071826245449

theorem tailTrace_7048108 : CollatzResearch.WordTrace tailWord_7048108 prefixEnd_7048108 1206355702933071826245449 := by
  unfold tailWord_7048108
  simp only [CollatzResearch.WordTrace]
  refine ⟨128532808774957955929192489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 171377078366610607905589985 128532808774957955929192489)
  ·
    refine ⟨96399606581218466946894367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 128532808774957955929192489 96399606581218466946894367)
    ·
      refine ⟨144599409871827700420341551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96399606581218466946894367 144599409871827700420341551)
      ·
        refine ⟨216899114807741550630512327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 144599409871827700420341551 216899114807741550630512327)
        ·
          refine ⟨325348672211612325945768491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 216899114807741550630512327 325348672211612325945768491)
          ·
            refine ⟨488023008317418488918652737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 325348672211612325945768491 488023008317418488918652737)
            ·
              refine ⟨366017256238063866688989553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 488023008317418488918652737 366017256238063866688989553)
              ·
                refine ⟨274512942178547900016742165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 366017256238063866688989553 274512942178547900016742165)
                ·
                  refine ⟨12867794164619432813284789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 274512942178547900016742165 12867794164619432813284789)
                  ·
                    refine ⟨1206355702933071826245449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12867794164619432813284789 1206355702933071826245449)
                    ·
                      rfl

theorem cell23_7048108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 6, 5].length) (baseStart_7048108 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7048108 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7048108 prefixEnd_7048108 := by exact prefixLift 7048108
  have htrace : WordTrace (prefixWord ++ tailWord_7048108) baseStart_7048108 baseEnd_7048108 := by
    simpa [prefixWord, tailWord_7048108, baseEnd_7048108] using wordTrace_append hprefix tailTrace_7048108
  have hstable : (prefixWord ++ tailWord_7048108).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7048108).length < 2 ^ (prefixWord ++ tailWord_7048108).sum := by decide
  have hdescent : baseEnd_7048108 < baseStart_7048108 := by decide
  rcases family_descends (prefixWord ++ tailWord_7048108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7048138 : List Nat := [3, 1, 2, 1, 2, 1, 1, 2, 2, 8]
def baseStart_7048138 : Nat := 118140960795 + 7048138 * 2 ^ 59
def prefixEnd_7048138 : Nat := 4983230072969 + 3 ^ 40 * 7048138 * 2
def baseEnd_7048138 : Nat := 1206360837739616787120403

theorem tailTrace_7048138 : CollatzResearch.WordTrace tailWord_7048138 prefixEnd_7048138 1206360837739616787120403 := by
  unfold tailWord_7048138
  simp only [CollatzResearch.WordTrace]
  refine ⟨64266677934951806745494267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 171377807826538151321318045 64266677934951806745494267)
  ·
    refine ⟨96400016902427710118241401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64266677934951806745494267 96400016902427710118241401)
    ·
      refine ⟨72300012676820782588681051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 96400016902427710118241401 72300012676820782588681051)
      ·
        refine ⟨108450019015231173883021577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72300012676820782588681051 108450019015231173883021577)
        ·
          refine ⟨81337514261423380412266183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 108450019015231173883021577 81337514261423380412266183)
          ·
            refine ⟨122006271392135070618399275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81337514261423380412266183 122006271392135070618399275)
            ·
              refine ⟨183009407088202605927598913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 122006271392135070618399275 183009407088202605927598913)
              ·
                refine ⟨137257055316151954445699185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 183009407088202605927598913 137257055316151954445699185)
                ·
                  refine ⟨102942791487113965834274389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 137257055316151954445699185 102942791487113965834274389)
                  ·
                    refine ⟨1206360837739616787120403, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 102942791487113965834274389 1206360837739616787120403)
                    ·
                      rfl

theorem cell23_7048138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 1, 2, 2, 8].length) (baseStart_7048138 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7048138 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7048138 prefixEnd_7048138 := by exact prefixLift 7048138
  have htrace : WordTrace (prefixWord ++ tailWord_7048138) baseStart_7048138 baseEnd_7048138 := by
    simpa [prefixWord, tailWord_7048138, baseEnd_7048138] using wordTrace_append hprefix tailTrace_7048138
  have hstable : (prefixWord ++ tailWord_7048138).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7048138).length < 2 ^ (prefixWord ++ tailWord_7048138).sum := by decide
  have hdescent : baseEnd_7048138 < baseStart_7048138 := by decide
  rcases family_descends (prefixWord ++ tailWord_7048138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7048159 : List Nat := [1, 1, 2, 3, 6, 1, 1, 1, 2, 5]
def baseStart_7048159 : Nat := 118140960795 + 7048159 * 2 ^ 59
def prefixEnd_7048159 : Nat := 4983230072969 + 3 ^ 40 * 7048159 * 2
def baseEnd_7048159 : Nat := 1206364432104198259732871

theorem tailTrace_7048159 : CollatzResearch.WordTrace tailWord_7048159 prefixEnd_7048159 1206364432104198259732871 := by
  unfold tailWord_7048159
  simp only [CollatzResearch.WordTrace]
  refine ⟨257067477672731147568491531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171378318448487431712327687 257067477672731147568491531)
  ·
    refine ⟨385601216509096721352737297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 257067477672731147568491531 385601216509096721352737297)
    ·
      refine ⟨289200912381822541014552973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 385601216509096721352737297 289200912381822541014552973)
      ·
        refine ⟨108450342143183452880457365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 289200912381822541014552973 108450342143183452880457365)
        ·
          refine ⟨5083609787961724353771439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 108450342143183452880457365 5083609787961724353771439)
          ·
            refine ⟨7625414681942586530657159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5083609787961724353771439 7625414681942586530657159)
            ·
              refine ⟨11438122022913879795985739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7625414681942586530657159 11438122022913879795985739)
              ·
                refine ⟨17157183034370819693978609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11438122022913879795985739 17157183034370819693978609)
                ·
                  refine ⟨12867887275778114770483957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17157183034370819693978609 12867887275778114770483957)
                  ·
                    refine ⟨1206364432104198259732871, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12867887275778114770483957 1206364432104198259732871)
                    ·
                      rfl

theorem cell23_7048159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 6, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 6, 1, 1, 1, 2, 5].length) (baseStart_7048159 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7048159 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7048159 prefixEnd_7048159 := by exact prefixLift 7048159
  have htrace : WordTrace (prefixWord ++ tailWord_7048159) baseStart_7048159 baseEnd_7048159 := by
    simpa [prefixWord, tailWord_7048159, baseEnd_7048159] using wordTrace_append hprefix tailTrace_7048159
  have hstable : (prefixWord ++ tailWord_7048159).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7048159).length < 2 ^ (prefixWord ++ tailWord_7048159).sum := by decide
  have hdescent : baseEnd_7048159 < baseStart_7048159 := by decide
  rcases family_descends (prefixWord ++ tailWord_7048159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7048246 : List Nat := [5, 1, 2, 1, 1, 2, 3, 1, 3, 1, 3]
def baseStart_7048246 : Nat := 118140960795 + 7048246 * 2 ^ 59
def prefixEnd_7048246 : Nat := 4983230072969 + 3 ^ 40 * 7048246 * 2
def baseEnd_7048246 : Nat := 3619137969129535938810713

theorem tailTrace_7048246 : CollatzResearch.WordTrace tailWord_7048246 prefixEnd_7048246 3619137969129535938810713 := by
  unfold tailWord_7048246
  simp only [CollatzResearch.WordTrace]
  refine ⟨16066915676463497589181787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 171380433882277307617939061 16066915676463497589181787)
  ·
    refine ⟨24100373514695246383772681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16066915676463497589181787 24100373514695246383772681)
    ·
      refine ⟨18075280136021434787829511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24100373514695246383772681 18075280136021434787829511)
      ·
        refine ⟨27112920204032152181744267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18075280136021434787829511 27112920204032152181744267)
        ·
          refine ⟨40669380306048228272616401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27112920204032152181744267 40669380306048228272616401)
          ·
            refine ⟨30502035229536171204462301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40669380306048228272616401 30502035229536171204462301)
            ·
              refine ⟨11438263211076064201673363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30502035229536171204462301 11438263211076064201673363)
              ·
                refine ⟨17157394816614096302510045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11438263211076064201673363 17157394816614096302510045)
                ·
                  refine ⟨6434023056230286113441267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17157394816614096302510045 6434023056230286113441267)
                  ·
                    refine ⟨9651034584345429170161901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6434023056230286113441267 9651034584345429170161901)
                    ·
                      refine ⟨3619137969129535938810713, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9651034584345429170161901 3619137969129535938810713)
                      ·
                        rfl

theorem cell23_7048246_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 2, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 2, 3, 1, 3, 1, 3].length) (baseStart_7048246 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7048246 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7048246 prefixEnd_7048246 := by exact prefixLift 7048246
  have htrace : WordTrace (prefixWord ++ tailWord_7048246) baseStart_7048246 baseEnd_7048246 := by
    simpa [prefixWord, tailWord_7048246, baseEnd_7048246] using wordTrace_append hprefix tailTrace_7048246
  have hstable : (prefixWord ++ tailWord_7048246).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7048246).length < 2 ^ (prefixWord ++ tailWord_7048246).sum := by decide
  have hdescent : baseEnd_7048246 < baseStart_7048246 := by decide
  rcases family_descends (prefixWord ++ tailWord_7048246) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7048255 : List Nat := [1, 1, 2, 2, 3, 1, 1, 1, 2, 6, 3]
def baseStart_7048255 : Nat := 118140960795 + 7048255 * 2 ^ 59
def prefixEnd_7048255 : Nat := 4983230072969 + 3 ^ 40 * 7048255 * 2
def baseEnd_7048255 : Nat := 3619142590455426403598171

theorem tailTrace_7048255 : CollatzResearch.WordTrace tailWord_7048255 prefixEnd_7048255 3619142590455426403598171 := by
  unfold tailWord_7048255
  simp only [CollatzResearch.WordTrace]
  refine ⟨257070979080383355963986219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171380652720255570642657479 257070979080383355963986219)
  ·
    refine ⟨385606468620575033945979329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 257070979080383355963986219 385606468620575033945979329)
    ·
      refine ⟨289204851465431275459484497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 385606468620575033945979329 289204851465431275459484497)
      ·
        refine ⟨216903638599073456594613373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 289204851465431275459484497 216903638599073456594613373)
        ·
          refine ⟨81338864474652546222980015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 216903638599073456594613373 81338864474652546222980015)
          ·
            refine ⟨122008296711978819334470023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81338864474652546222980015 122008296711978819334470023)
            ·
              refine ⟨183012445067968229001705035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 122008296711978819334470023 183012445067968229001705035)
              ·
                refine ⟨274518667601952343502557553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 183012445067968229001705035 274518667601952343502557553)
                ·
                  refine ⟨205889000701464257626918165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 274518667601952343502557553 205889000701464257626918165)
                  ·
                    refine ⟨9651046907881137076261789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 205889000701464257626918165 9651046907881137076261789)
                    ·
                      refine ⟨3619142590455426403598171, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9651046907881137076261789 3619142590455426403598171)
                      ·
                        rfl

theorem cell23_7048255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 1, 1, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 1, 1, 2, 6, 3].length) (baseStart_7048255 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7048255 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7048255 prefixEnd_7048255 := by exact prefixLift 7048255
  have htrace : WordTrace (prefixWord ++ tailWord_7048255) baseStart_7048255 baseEnd_7048255 := by
    simpa [prefixWord, tailWord_7048255, baseEnd_7048255] using wordTrace_append hprefix tailTrace_7048255
  have hstable : (prefixWord ++ tailWord_7048255).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7048255).length < 2 ^ (prefixWord ++ tailWord_7048255).sum := by decide
  have hdescent : baseEnd_7048255 < baseStart_7048255 := by decide
  rcases family_descends (prefixWord ++ tailWord_7048255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7048269 : List Nat := [1, 6, 1, 1, 1, 3, 1, 1, 3, 1, 4]
def baseStart_7048269 : Nat := 118140960795 + 7048269 * 2 ^ 59
def prefixEnd_7048269 : Nat := 4983230072969 + 3 ^ 40 * 7048269 * 2
def baseEnd_7048269 : Nat := 3619149779184589348823107

theorem tailTrace_7048269 : CollatzResearch.WordTrace tailWord_7048269 prefixEnd_7048269 3619149779184589348823107 := by
  unfold tailWord_7048269
  simp only [CollatzResearch.WordTrace]
  refine ⟨257071489702332636354995861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171380993134888424236663907 257071489702332636354995861)
  ·
    refine ⟨12050226079796842329140431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 257071489702332636354995861 12050226079796842329140431)
    ·
      refine ⟨18075339119695263493710647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12050226079796842329140431 18075339119695263493710647)
      ·
        refine ⟨27113008679542895240565971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18075339119695263493710647 27113008679542895240565971)
        ·
          refine ⟨40669513019314342860848957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27113008679542895240565971 40669513019314342860848957)
          ·
            refine ⟨15251067382242878572818359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40669513019314342860848957 15251067382242878572818359)
            ·
              refine ⟨22876601073364317859227539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15251067382242878572818359 22876601073364317859227539)
              ·
                refine ⟨34314901610046476788841309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22876601073364317859227539 34314901610046476788841309)
                ·
                  refine ⟨12868088103767428795815491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34314901610046476788841309 12868088103767428795815491)
                  ·
                    refine ⟨19302132155651143193723237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12868088103767428795815491 19302132155651143193723237)
                    ·
                      refine ⟨3619149779184589348823107, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19302132155651143193723237 3619149779184589348823107)
                      ·
                        rfl

theorem cell23_7048269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 3, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 3, 1, 1, 3, 1, 4].length) (baseStart_7048269 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7048269 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7048269 prefixEnd_7048269 := by exact prefixLift 7048269
  have htrace : WordTrace (prefixWord ++ tailWord_7048269) baseStart_7048269 baseEnd_7048269 := by
    simpa [prefixWord, tailWord_7048269, baseEnd_7048269] using wordTrace_append hprefix tailTrace_7048269
  have hstable : (prefixWord ++ tailWord_7048269).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7048269).length < 2 ^ (prefixWord ++ tailWord_7048269).sum := by decide
  have hdescent : baseEnd_7048269 < baseStart_7048269 := by decide
  rcases family_descends (prefixWord ++ tailWord_7048269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7048329 : List Nat := [1, 2, 1, 1, 4, 3, 2, 1, 3, 3, 2]
def baseStart_7048329 : Nat := 118140960795 + 7048329 * 2 ^ 59
def prefixEnd_7048329 : Nat := 4983230072969 + 3 ^ 40 * 7048329 * 2
def baseEnd_7048329 : Nat := 3619180588023859114072831

theorem tailTrace_7048329 : CollatzResearch.WordTrace tailWord_7048329 prefixEnd_7048329 3619180588023859114072831 := by
  unfold tailWord_7048329
  simp only [CollatzResearch.WordTrace]
  refine ⟨257073678082115266602180041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171382452054743511068120027 257073678082115266602180041)
  ·
    refine ⟨192805258561586449951635031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 257073678082115266602180041 192805258561586449951635031)
    ·
      refine ⟨289207887842379674927452547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 192805258561586449951635031 289207887842379674927452547)
      ·
        refine ⟨433811831763569512391178821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 289207887842379674927452547 433811831763569512391178821)
        ·
          refine ⟨81339718455669283573346029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 433811831763569512391178821 81339718455669283573346029)
          ·
            refine ⟨30502394420875981340004761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 81339718455669283573346029 30502394420875981340004761)
            ·
              refine ⟨22876795815656986005003571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30502394420875981340004761 22876795815656986005003571)
              ·
                refine ⟨34315193723485479007505357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22876795815656986005003571 34315193723485479007505357)
                ·
                  refine ⟨12868197646307054627814509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34315193723485479007505357 12868197646307054627814509)
                  ·
                    refine ⟨4825574117365145485430441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12868197646307054627814509 4825574117365145485430441)
                    ·
                      refine ⟨3619180588023859114072831, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4825574117365145485430441 3619180588023859114072831)
                      ·
                        rfl

theorem cell23_7048329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 3, 2, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 3, 2, 1, 3, 3, 2].length) (baseStart_7048329 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7048329 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7048329 prefixEnd_7048329 := by exact prefixLift 7048329
  have htrace : WordTrace (prefixWord ++ tailWord_7048329) baseStart_7048329 baseEnd_7048329 := by
    simpa [prefixWord, tailWord_7048329, baseEnd_7048329] using wordTrace_append hprefix tailTrace_7048329
  have hstable : (prefixWord ++ tailWord_7048329).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7048329).length < 2 ^ (prefixWord ++ tailWord_7048329).sum := by decide
  have hdescent : baseEnd_7048329 < baseStart_7048329 := by decide
  rcases family_descends (prefixWord ++ tailWord_7048329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7048392 : List Nat := [2, 1, 3, 1, 2, 1, 2, 2, 1, 5, 3]
def baseStart_7048392 : Nat := 118140960795 + 7048392 * 2 ^ 59
def prefixEnd_7048392 : Nat := 4983230072969 + 3 ^ 40 * 7048392 * 2
def baseEnd_7048392 : Nat := 3619212937305092367585041

theorem tailTrace_7048392 : CollatzResearch.WordTrace tailWord_7048392 prefixEnd_7048392 3619212937305092367585041 := by
  unfold tailWord_7048392
  simp only [CollatzResearch.WordTrace]
  refine ⟨128537987940443514180861715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 171383983920591352241148953 128537987940443514180861715)
  ·
    refine ⟨192806981910665271271292573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128537987940443514180861715 192806981910665271271292573)
    ·
      refine ⟨72302618216499476726734715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 192806981910665271271292573 72302618216499476726734715)
      ·
        refine ⟨108453927324749215090102073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72302618216499476726734715 108453927324749215090102073)
        ·
          refine ⟨81340445493561911317576555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 108453927324749215090102073 81340445493561911317576555)
          ·
            refine ⟨122010668240342866976364833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81340445493561911317576555 122010668240342866976364833)
            ·
              refine ⟨91508001180257150232273625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 122010668240342866976364833 91508001180257150232273625)
              ·
                refine ⟨68631000885192862674205219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 91508001180257150232273625 68631000885192862674205219)
                ·
                  refine ⟨102946501327789294011307829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 68631000885192862674205219 102946501327789294011307829)
                  ·
                    refine ⟨9651234499480246313560109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 102946501327789294011307829 9651234499480246313560109)
                    ·
                      refine ⟨3619212937305092367585041, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9651234499480246313560109 3619212937305092367585041)
                      ·
                        rfl

theorem cell23_7048392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 2, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 2, 2, 1, 5, 3].length) (baseStart_7048392 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7048392 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7048392 prefixEnd_7048392 := by exact prefixLift 7048392
  have htrace : WordTrace (prefixWord ++ tailWord_7048392) baseStart_7048392 baseEnd_7048392 := by
    simpa [prefixWord, tailWord_7048392, baseEnd_7048392] using wordTrace_append hprefix tailTrace_7048392
  have hstable : (prefixWord ++ tailWord_7048392).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7048392).length < 2 ^ (prefixWord ++ tailWord_7048392).sum := by decide
  have hdescent : baseEnd_7048392 < baseStart_7048392 := by decide
  rcases family_descends (prefixWord ++ tailWord_7048392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7048416 : List Nat := [2, 1, 1, 3, 1, 5, 3, 2, 5]
def baseStart_7048416 : Nat := 118140960795 + 7048416 * 2 ^ 59
def prefixEnd_7048416 : Nat := 4983230072969 + 3 ^ 40 * 7048416 * 2
def baseEnd_7048416 : Nat := 402136140093422252631659

theorem tailTrace_7048416 : CollatzResearch.WordTrace tailWord_7048416 prefixEnd_7048416 402136140093422252631659 := by
  unfold tailWord_7048416
  simp only [CollatzResearch.WordTrace]
  refine ⟨128538425616400040230298551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 171384567488533386973731401 128538425616400040230298551)
  ·
    refine ⟨192807638424600060345447827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128538425616400040230298551 192807638424600060345447827)
    ·
      refine ⟨289211457636900090518171741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 192807638424600060345447827 289211457636900090518171741)
      ·
        refine ⟨108454296613837533944314403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 289211457636900090518171741 108454296613837533944314403)
        ·
          refine ⟨162681444920756300916471605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 108454296613837533944314403 162681444920756300916471605)
          ·
            refine ⟨15251385461320903210919213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 162681444920756300916471605 15251385461320903210919213)
            ·
              refine ⟨5719269547995338704094705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15251385461320903210919213 5719269547995338704094705)
              ·
                refine ⟨4289452160996504028071029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5719269547995338704094705 4289452160996504028071029)
                ·
                  refine ⟨402136140093422252631659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4289452160996504028071029 402136140093422252631659)
                  ·
                    rfl

theorem cell23_7048416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 5, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 5, 3, 2, 5].length) (baseStart_7048416 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7048416 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7048416 prefixEnd_7048416 := by exact prefixLift 7048416
  have htrace : WordTrace (prefixWord ++ tailWord_7048416) baseStart_7048416 baseEnd_7048416 := by
    simpa [prefixWord, tailWord_7048416, baseEnd_7048416] using wordTrace_append hprefix tailTrace_7048416
  have hstable : (prefixWord ++ tailWord_7048416).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7048416).length < 2 ^ (prefixWord ++ tailWord_7048416).sum := by decide
  have hdescent : baseEnd_7048416 < baseStart_7048416 := by decide
  rcases family_descends (prefixWord ++ tailWord_7048416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7048446 : List Nat := [4, 2, 2, 1, 1, 3, 2, 1, 2, 5]
def baseStart_7048446 : Nat := 118140960795 + 7048446 * 2 ^ 59
def prefixEnd_7048446 : Nat := 4983230072969 + 3 ^ 40 * 7048446 * 2
def baseEnd_7048446 : Nat := 1206413555086811718769931

theorem tailTrace_7048446 : CollatzResearch.WordTrace tailWord_7048446 prefixEnd_7048446 1206413555086811718769931 := by
  unfold tailWord_7048446
  simp only [CollatzResearch.WordTrace]
  refine ⟨32134743177836424448023649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 171385296948460930389459461 32134743177836424448023649)
  ·
    refine ⟨24101057383377318336017737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32134743177836424448023649 24101057383377318336017737)
    ·
      refine ⟨18075793037532988752013303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24101057383377318336017737 18075793037532988752013303)
      ·
        refine ⟨27113689556299483128019955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18075793037532988752013303 27113689556299483128019955)
        ·
          refine ⟨40670534334449224692029933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27113689556299483128019955 40670534334449224692029933)
          ·
            refine ⟨15251450375418459259511225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40670534334449224692029933 15251450375418459259511225)
            ·
              refine ⟨11438587781563844444633419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15251450375418459259511225 11438587781563844444633419)
              ·
                refine ⟨17157881672345766666950129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11438587781563844444633419 17157881672345766666950129)
                ·
                  refine ⟨12868411254259325000212597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17157881672345766666950129 12868411254259325000212597)
                  ·
                    refine ⟨1206413555086811718769931, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12868411254259325000212597 1206413555086811718769931)
                    ·
                      rfl

theorem cell23_7048446_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 3, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 3, 2, 1, 2, 5].length) (baseStart_7048446 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7048446 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7048446 prefixEnd_7048446 := by exact prefixLift 7048446
  have htrace : WordTrace (prefixWord ++ tailWord_7048446) baseStart_7048446 baseEnd_7048446 := by
    simpa [prefixWord, tailWord_7048446, baseEnd_7048446] using wordTrace_append hprefix tailTrace_7048446
  have hstable : (prefixWord ++ tailWord_7048446).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7048446).length < 2 ^ (prefixWord ++ tailWord_7048446).sum := by decide
  have hdescent : baseEnd_7048446 < baseStart_7048446 := by decide
  rcases family_descends (prefixWord ++ tailWord_7048446) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7048449 : List Nat := [1, 2, 4, 1, 1, 3, 1, 3, 2, 1, 4]
def baseStart_7048449 : Nat := 118140960795 + 7048449 * 2 ^ 59
def prefixEnd_7048449 : Nat := 4983230072969 + 3 ^ 40 * 7048449 * 2
def baseEnd_7048449 : Nat := 3619242205702398644572279

theorem tailTrace_7048449 : CollatzResearch.WordTrace tailWord_7048449 prefixEnd_7048449 3619242205702398644572279 := by
  unfold tailWord_7048449
  simp only [CollatzResearch.WordTrace]
  refine ⟨257078054841680527096548401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171385369894453684731032267 257078054841680527096548401)
  ·
    refine ⟨192808541131260395322411301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 257078054841680527096548401 192808541131260395322411301)
    ·
      refine ⟨36151601462111324122952119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 192808541131260395322411301 36151601462111324122952119)
      ·
        refine ⟨54227402193166986184428179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36151601462111324122952119 54227402193166986184428179)
        ·
          refine ⟨81341103289750479276642269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54227402193166986184428179 81341103289750479276642269)
          ·
            refine ⟨30502913733656429728740851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 81341103289750479276642269 30502913733656429728740851)
            ·
              refine ⟨45754370600484644593111277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30502913733656429728740851 45754370600484644593111277)
              ·
                refine ⟨17157888975181741722416729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 45754370600484644593111277 17157888975181741722416729)
                ·
                  refine ⟨12868416731386306291812547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17157888975181741722416729 12868416731386306291812547)
                  ·
                    refine ⟨19302625097079459437718821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12868416731386306291812547 19302625097079459437718821)
                    ·
                      refine ⟨3619242205702398644572279, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19302625097079459437718821 3619242205702398644572279)
                      ·
                        rfl

theorem cell23_7048449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 3, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 3, 1, 3, 2, 1, 4].length) (baseStart_7048449 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7048449 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7048449 prefixEnd_7048449 := by exact prefixLift 7048449
  have htrace : WordTrace (prefixWord ++ tailWord_7048449) baseStart_7048449 baseEnd_7048449 := by
    simpa [prefixWord, tailWord_7048449, baseEnd_7048449] using wordTrace_append hprefix tailTrace_7048449
  have hstable : (prefixWord ++ tailWord_7048449).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7048449).length < 2 ^ (prefixWord ++ tailWord_7048449).sum := by decide
  have hdescent : baseEnd_7048449 < baseStart_7048449 := by decide
  rcases family_descends (prefixWord ++ tailWord_7048449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7048493 : List Nat := [1, 5, 3, 1, 1, 2, 1, 2, 3, 4]
def baseStart_7048493 : Nat := 118140960795 + 7048493 * 2 ^ 59
def prefixEnd_7048493 : Nat := 4983230072969 + 3 ^ 40 * 7048493 * 2
def baseEnd_7048493 : Nat := 1206421599617065490807359

theorem tailTrace_7048493 : CollatzResearch.WordTrace tailWord_7048493 prefixEnd_7048493 1206421599617065490807359 := by
  unfold tailWord_7048493
  simp only [CollatzResearch.WordTrace]
  refine ⟨257079659653521122611150133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171386439769014081740766755 257079659653521122611150133)
  ·
    refine ⟨24101218092517605244795325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 257079659653521122611150133 24101218092517605244795325)
    ·
      refine ⟨9037956784694101966798247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24101218092517605244795325 9037956784694101966798247)
      ·
        refine ⟨13556935177041152950197371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9037956784694101966798247 13556935177041152950197371)
        ·
          refine ⟨20335402765561729425296057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13556935177041152950197371 20335402765561729425296057)
          ·
            refine ⟨15251552074171297068972043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20335402765561729425296057 15251552074171297068972043)
            ·
              refine ⟨22877328111256945603458065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15251552074171297068972043 22877328111256945603458065)
              ·
                refine ⟨17157996083442709202593549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22877328111256945603458065 17157996083442709202593549)
                ·
                  refine ⟨6434248531291015950972581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17157996083442709202593549 6434248531291015950972581)
                  ·
                    refine ⟨1206421599617065490807359, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6434248531291015950972581 1206421599617065490807359)
                    ·
                      rfl

theorem cell23_7048493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 2, 1, 2, 3, 4].length) (baseStart_7048493 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7048493 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7048493 prefixEnd_7048493 := by exact prefixLift 7048493
  have htrace : WordTrace (prefixWord ++ tailWord_7048493) baseStart_7048493 baseEnd_7048493 := by
    simpa [prefixWord, tailWord_7048493, baseEnd_7048493] using wordTrace_append hprefix tailTrace_7048493
  have hstable : (prefixWord ++ tailWord_7048493).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7048493).length < 2 ^ (prefixWord ++ tailWord_7048493).sum := by decide
  have hdescent : baseEnd_7048493 < baseStart_7048493 := by decide
  rcases family_descends (prefixWord ++ tailWord_7048493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7048526 : List Nat := [4, 1, 1, 1, 1, 1, 4, 1, 4, 3, 2]
def baseStart_7048526 : Nat := 118140960795 + 7048526 * 2 ^ 59
def prefixEnd_7048526 : Nat := 4983230072969 + 3 ^ 40 * 7048526 * 2
def baseEnd_7048526 : Nat := 3619281743712794843309425

theorem tailTrace_7048526 : CollatzResearch.WordTrace tailWord_7048526 prefixEnd_7048526 3619281743712794843309425 := by
  unfold tailWord_7048526
  simp only [CollatzResearch.WordTrace]
  refine ⟨32135107907800196155887679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 171387242174934379498067621 32135107907800196155887679)
  ·
    refine ⟨48202661861700294233831519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32135107907800196155887679 48202661861700294233831519)
    ·
      refine ⟨72303992792550441350747279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48202661861700294233831519 72303992792550441350747279)
      ·
        refine ⟨108455989188825662026120919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72303992792550441350747279 108455989188825662026120919)
        ·
          refine ⟨162683983783238493039181379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 108455989188825662026120919 162683983783238493039181379)
          ·
            refine ⟨244025975674857739558772069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 162683983783238493039181379 244025975674857739558772069)
            ·
              refine ⟨45754870439035826167269763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 244025975674857739558772069 45754870439035826167269763)
              ·
                refine ⟨68632305658553739250904645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45754870439035826167269763 68632305658553739250904645)
                ·
                  refine ⟨12868557310978826109544621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 68632305658553739250904645 12868557310978826109544621)
                  ·
                    refine ⟨4825708991617059791079233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12868557310978826109544621 4825708991617059791079233)
                    ·
                      refine ⟨3619281743712794843309425, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4825708991617059791079233 3619281743712794843309425)
                      ·
                        rfl

theorem cell23_7048526_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 4, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 4, 1, 4, 3, 2].length) (baseStart_7048526 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7048526 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7048526 prefixEnd_7048526 := by exact prefixLift 7048526
  have htrace : WordTrace (prefixWord ++ tailWord_7048526) baseStart_7048526 baseEnd_7048526 := by
    simpa [prefixWord, tailWord_7048526, baseEnd_7048526] using wordTrace_append hprefix tailTrace_7048526
  have hstable : (prefixWord ++ tailWord_7048526).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7048526).length < 2 ^ (prefixWord ++ tailWord_7048526).sum := by decide
  have hdescent : baseEnd_7048526 < baseStart_7048526 := by decide
  rcases family_descends (prefixWord ++ tailWord_7048526) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7048533 : List Nat := [1, 3, 2, 2, 3, 2, 2, 1, 3, 1, 3]
def baseStart_7048533 : Nat := 118140960795 + 7048533 * 2 ^ 59
def prefixEnd_7048533 : Nat := 4983230072969 + 3 ^ 40 * 7048533 * 2
def baseEnd_7048533 : Nat := 3619285338077376315921893

theorem tailTrace_7048533 : CollatzResearch.WordTrace tailWord_7048533 prefixEnd_7048533 3619285338077376315921893 := by
  unfold tailWord_7048533
  simp only [CollatzResearch.WordTrace]
  refine ⟨257081118573376209442606253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171387412382250806295070835 257081118573376209442606253)
  ·
    refine ⟨96405419465016078540977345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 257081118573376209442606253 96405419465016078540977345)
    ·
      refine ⟨72304064598762058905733009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 96405419465016078540977345 72304064598762058905733009)
      ·
        refine ⟨54228048449071544179299757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72304064598762058905733009 54228048449071544179299757)
        ·
          refine ⟨20335518168401829067237409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 54228048449071544179299757 20335518168401829067237409)
          ·
            refine ⟨15251638626301371800428057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20335518168401829067237409 15251638626301371800428057)
            ·
              refine ⟨11438728969726028850321043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15251638626301371800428057 11438728969726028850321043)
              ·
                refine ⟨17158093454589043275481565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11438728969726028850321043 17158093454589043275481565)
                ·
                  refine ⟨6434285045470891228305587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17158093454589043275481565 6434285045470891228305587)
                  ·
                    refine ⟨9651427568206336842458381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6434285045470891228305587 9651427568206336842458381)
                    ·
                      refine ⟨3619285338077376315921893, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9651427568206336842458381 3619285338077376315921893)
                      ·
                        rfl

theorem cell23_7048533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 2, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 2, 2, 1, 3, 1, 3].length) (baseStart_7048533 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7048533 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7048533 prefixEnd_7048533 := by exact prefixLift 7048533
  have htrace : WordTrace (prefixWord ++ tailWord_7048533) baseStart_7048533 baseEnd_7048533 := by
    simpa [prefixWord, tailWord_7048533, baseEnd_7048533] using wordTrace_append hprefix tailTrace_7048533
  have hstable : (prefixWord ++ tailWord_7048533).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7048533).length < 2 ^ (prefixWord ++ tailWord_7048533).sum := by decide
  have hdescent : baseEnd_7048533 < baseStart_7048533 := by decide
  rcases family_descends (prefixWord ++ tailWord_7048533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7048556 : List Nat := [2, 2, 1, 1, 5, 1, 1, 4, 1, 1, 4]
def baseStart_7048556 : Nat := 118140960795 + 7048556 * 2 ^ 59
def prefixEnd_7048556 : Nat := 4983230072969 + 3 ^ 40 * 7048556 * 2
def baseEnd_7048556 : Nat := 3619297148132429725934287

theorem tailTrace_7048556 : CollatzResearch.WordTrace tailWord_7048556 prefixEnd_7048556 3619297148132429725934287 := by
  unfold tailWord_7048556
  simp only [CollatzResearch.WordTrace]
  refine ⟨128540978726146442185346761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 171387971634861922913795681 128540978726146442185346761)
  ·
    refine ⟨96405734044609831639010071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 128540978726146442185346761 96405734044609831639010071)
    ·
      refine ⟨144608601066914747458515107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96405734044609831639010071 144608601066914747458515107)
      ·
        refine ⟨216912901600372121187772661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 144608601066914747458515107 216912901600372121187772661)
        ·
          refine ⟨20335584525034886361353687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 216912901600372121187772661 20335584525034886361353687)
          ·
            refine ⟨30503376787552329542030531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20335584525034886361353687 30503376787552329542030531)
            ·
              refine ⟨45755065181328494313045797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30503376787552329542030531 45755065181328494313045797)
              ·
                refine ⟨8579074721499092683696087, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 45755065181328494313045797 8579074721499092683696087)
                ·
                  refine ⟨12868612082248639025544131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8579074721499092683696087 12868612082248639025544131)
                  ·
                    refine ⟨19302918123372958538316197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12868612082248639025544131 19302918123372958538316197)
                    ·
                      refine ⟨3619297148132429725934287, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19302918123372958538316197 3619297148132429725934287)
                      ·
                        rfl

theorem cell23_7048556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 1, 1, 4].length) (baseStart_7048556 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7048556 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7048556 prefixEnd_7048556 := by exact prefixLift 7048556
  have htrace : WordTrace (prefixWord ++ tailWord_7048556) baseStart_7048556 baseEnd_7048556 := by
    simpa [prefixWord, tailWord_7048556, baseEnd_7048556] using wordTrace_append hprefix tailTrace_7048556
  have hstable : (prefixWord ++ tailWord_7048556).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7048556).length < 2 ^ (prefixWord ++ tailWord_7048556).sum := by decide
  have hdescent : baseEnd_7048556 < baseStart_7048556 := by decide
  rcases family_descends (prefixWord ++ tailWord_7048556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7048569 : List Nat := [1, 2, 1, 3, 2, 1, 2, 4, 1, 2, 4]
def baseStart_7048569 : Nat := 118140960795 + 7048569 * 2 ^ 59
def prefixEnd_7048569 : Nat := 4983230072969 + 3 ^ 40 * 7048569 * 2
def baseEnd_7048569 : Nat := 3619303823380938175071727

theorem tailTrace_7048569 : CollatzResearch.WordTrace tailWord_7048569 prefixEnd_7048569 3619303823380938175071727 := by
  unfold tailWord_7048569
  simp only [CollatzResearch.WordTrace]
  refine ⟨257082431601245787590916761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171388287734163858393944507 257082431601245787590916761)
  ·
    refine ⟨192811823700934340693187571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 257082431601245787590916761 192811823700934340693187571)
    ·
      refine ⟨289217735551401511039781357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 192811823700934340693187571 289217735551401511039781357)
      ·
        refine ⟨108456650831775566639918009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 289217735551401511039781357 108456650831775566639918009)
        ·
          refine ⟨81342488123831674979938507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 108456650831775566639918009 81342488123831674979938507)
          ·
            refine ⟨122013732185747512469907761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81342488123831674979938507 122013732185747512469907761)
            ·
              refine ⟨91510299139310634352430821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 122013732185747512469907761 91510299139310634352430821)
              ·
                refine ⟨17158181088620743941080779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 91510299139310634352430821 17158181088620743941080779)
                ·
                  refine ⟨25737271632931115911621169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17158181088620743941080779 25737271632931115911621169)
                  ·
                    refine ⟨19302953724698336933715877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25737271632931115911621169 19302953724698336933715877)
                    ·
                      refine ⟨3619303823380938175071727, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19302953724698336933715877 3619303823380938175071727)
                      ·
                        rfl

theorem cell23_7048569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 2, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 2, 4, 1, 2, 4].length) (baseStart_7048569 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7048569 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7048569 prefixEnd_7048569 := by exact prefixLift 7048569
  have htrace : WordTrace (prefixWord ++ tailWord_7048569) baseStart_7048569 baseEnd_7048569 := by
    simpa [prefixWord, tailWord_7048569, baseEnd_7048569] using wordTrace_append hprefix tailTrace_7048569
  have hstable : (prefixWord ++ tailWord_7048569).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7048569).length < 2 ^ (prefixWord ++ tailWord_7048569).sum := by decide
  have hdescent : baseEnd_7048569 < baseStart_7048569 := by decide
  rcases family_descends (prefixWord ++ tailWord_7048569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7048579 : List Nat := [1, 1, 1, 3, 5, 3, 9]
def baseStart_7048579 : Nat := 118140960795 + 7048579 * 2 ^ 59
def prefixEnd_7048579 : Nat := 4983230072969 + 3 ^ 40 * 7048579 * 2
def baseEnd_7048579 : Nat := 44682826644289915258601

theorem tailTrace_7048579 : CollatzResearch.WordTrace tailWord_7048579 prefixEnd_7048579 44682826644289915258601 := by
  unfold tailWord_7048579
  simp only [CollatzResearch.WordTrace]
  refine ⟨257082796331209559298780791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171388530887473039532520527 257082796331209559298780791)
  ·
    refine ⟨385624194496814338948171187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 257082796331209559298780791 385624194496814338948171187)
    ·
      refine ⟨578436291745221508422256781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 385624194496814338948171187 578436291745221508422256781)
      ·
        refine ⟨216913609404458065658346293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 578436291745221508422256781 216913609404458065658346293)
        ·
          refine ⟨20335650881667943655469965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 216913609404458065658346293 20335650881667943655469965)
          ·
            refine ⟨7625869080625478870801237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20335650881667943655469965 7625869080625478870801237)
            ·
              refine ⟨44682826644289915258601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 7625869080625478870801237 44682826644289915258601)
              ·
                rfl

theorem cell23_7048579_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 3, 9].length) (baseStart_7048579 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7048579 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7048579 prefixEnd_7048579 := by exact prefixLift 7048579
  have htrace : WordTrace (prefixWord ++ tailWord_7048579) baseStart_7048579 baseEnd_7048579 := by
    simpa [prefixWord, tailWord_7048579, baseEnd_7048579] using wordTrace_append hprefix tailTrace_7048579
  have hstable : (prefixWord ++ tailWord_7048579).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7048579).length < 2 ^ (prefixWord ++ tailWord_7048579).sum := by decide
  have hdescent : baseEnd_7048579 < baseStart_7048579 := by decide
  rcases family_descends (prefixWord ++ tailWord_7048579) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7048596 : List Nat := [2, 4, 2, 1, 2, 2, 2, 8]
def baseStart_7048596 : Nat := 118140960795 + 7048596 * 2 ^ 59
def prefixEnd_7048596 : Nat := 4983230072969 + 3 ^ 40 * 7048596 * 2
def baseEnd_7048596 : Nat := 134048803235504058127189

theorem tailTrace_7048596 : CollatzResearch.WordTrace tailWord_7048596 prefixEnd_7048596 134048803235504058127189 := by
  unfold tailWord_7048596
  simp only [CollatzResearch.WordTrace]
  refine ⟨128541708186073985601074821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 171388944248098647468099761 128541708186073985601074821)
  ·
    refine ⟨24101570284888872300201529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 128541708186073985601074821 24101570284888872300201529)
    ·
      refine ⟨18076177713666654225151147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24101570284888872300201529 18076177713666654225151147)
      ·
        refine ⟨27114266570499981337726721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18076177713666654225151147 27114266570499981337726721)
        ·
          refine ⟨20335699927874986003295041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27114266570499981337726721 20335699927874986003295041)
          ·
            refine ⟨15251774945906239502471281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20335699927874986003295041 15251774945906239502471281)
            ·
              refine ⟨11438831209429679626853461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15251774945906239502471281 11438831209429679626853461)
              ·
                refine ⟨134048803235504058127189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 11438831209429679626853461 134048803235504058127189)
                ·
                  rfl

theorem cell23_7048596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 2, 2, 8].length) (baseStart_7048596 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7048596 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7048596 prefixEnd_7048596 := by exact prefixLift 7048596
  have htrace : WordTrace (prefixWord ++ tailWord_7048596) baseStart_7048596 baseEnd_7048596 := by
    simpa [prefixWord, tailWord_7048596, baseEnd_7048596] using wordTrace_append hprefix tailTrace_7048596
  have hstable : (prefixWord ++ tailWord_7048596).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7048596).length < 2 ^ (prefixWord ++ tailWord_7048596).sum := by decide
  have hdescent : baseEnd_7048596 < baseStart_7048596 := by decide
  rcases family_descends (prefixWord ++ tailWord_7048596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7048610 : List Nat := [3, 3, 1, 2, 1, 4, 1, 2, 1, 2, 3]
def baseStart_7048610 : Nat := 118140960795 + 7048610 * 2 ^ 59
def prefixEnd_7048610 : Nat := 4983230072969 + 3 ^ 40 * 7048610 * 2
def baseEnd_7048610 : Nat := 3619324876087772514659039

theorem tailTrace_7048610 : CollatzResearch.WordTrace tailWord_7048610 prefixEnd_7048610 3619324876087772514659039 := by
  unfold tailWord_7048610
  simp only [CollatzResearch.WordTrace]
  refine ⟨64270981748524312898289821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 171389284662731501062106189 64270981748524312898289821)
  ·
    refine ⟨24101618155696617336858683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 64270981748524312898289821 24101618155696617336858683)
    ·
      refine ⟨36152427233544926005288025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24101618155696617336858683 36152427233544926005288025)
      ·
        refine ⟨27114320425158694503966019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36152427233544926005288025 27114320425158694503966019)
        ·
          refine ⟨40671480637738041755949029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27114320425158694503966019 40671480637738041755949029)
          ·
            refine ⟨7625902619575882829240443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 40671480637738041755949029 7625902619575882829240443)
            ·
              refine ⟨11438853929363824243860665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7625902619575882829240443 11438853929363824243860665)
              ·
                refine ⟨8579140447022868182895499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11438853929363824243860665 8579140447022868182895499)
                ·
                  refine ⟨12868710670534302274343249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8579140447022868182895499 12868710670534302274343249)
                  ·
                    refine ⟨9651533002900726705757437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12868710670534302274343249 9651533002900726705757437)
                    ·
                      refine ⟨3619324876087772514659039, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9651533002900726705757437 3619324876087772514659039)
                      ·
                        rfl

theorem cell23_7048610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 4, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 4, 1, 2, 1, 2, 3].length) (baseStart_7048610 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7048610 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7048610 prefixEnd_7048610 := by exact prefixLift 7048610
  have htrace : WordTrace (prefixWord ++ tailWord_7048610) baseStart_7048610 baseEnd_7048610 := by
    simpa [prefixWord, tailWord_7048610, baseEnd_7048610] using wordTrace_append hprefix tailTrace_7048610
  have hstable : (prefixWord ++ tailWord_7048610).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7048610).length < 2 ^ (prefixWord ++ tailWord_7048610).sum := by decide
  have hdescent : baseEnd_7048610 < baseStart_7048610 := by decide
  rcases family_descends (prefixWord ++ tailWord_7048610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7048693 : List Nat := [1, 3, 5, 1, 1, 1, 1, 2, 2, 2, 4]
def baseStart_7048693 : Nat := 118140960795 + 7048693 * 2 ^ 59
def prefixEnd_7048693 : Nat := 4983230072969 + 3 ^ 40 * 7048693 * 2
def baseEnd_7048693 : Nat := 3619367494982095689921157

theorem tailTrace_7048693 : CollatzResearch.WordTrace tailWord_7048693 prefixEnd_7048693 3619367494982095689921157 := by
  unfold tailWord_7048693
  simp only [CollatzResearch.WordTrace]
  refine ⟨257086954252796556768430733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171391302835197704512287155 257086954252796556768430733)
  ·
    refine ⟨96407607844798708788161525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 257086954252796556768430733 96407607844798708788161525)
    ·
      refine ⟨9038213235449878948890143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 96407607844798708788161525 9038213235449878948890143)
      ·
        refine ⟨13557319853174818423335215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9038213235449878948890143 13557319853174818423335215)
        ·
          refine ⟨20335979779762227635002823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13557319853174818423335215 20335979779762227635002823)
          ·
            refine ⟨30503969669643341452504235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20335979779762227635002823 30503969669643341452504235)
            ·
              refine ⟨45755954504465012178756353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30503969669643341452504235 45755954504465012178756353)
              ·
                refine ⟨34316965878348759134067265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45755954504465012178756353 34316965878348759134067265)
                ·
                  refine ⟨25737724408761569350550449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34316965878348759134067265 25737724408761569350550449)
                  ·
                    refine ⟨19303293306571177012912837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25737724408761569350550449 19303293306571177012912837)
                    ·
                      refine ⟨3619367494982095689921157, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19303293306571177012912837 3619367494982095689921157)
                      ·
                        rfl

theorem cell23_7048693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 1, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 1, 1, 2, 2, 2, 4].length) (baseStart_7048693 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7048693 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7048693 prefixEnd_7048693 := by exact prefixLift 7048693
  have htrace : WordTrace (prefixWord ++ tailWord_7048693) baseStart_7048693 baseEnd_7048693 := by
    simpa [prefixWord, tailWord_7048693, baseEnd_7048693] using wordTrace_append hprefix tailTrace_7048693
  have hstable : (prefixWord ++ tailWord_7048693).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7048693).length < 2 ^ (prefixWord ++ tailWord_7048693).sum := by decide
  have hdescent : baseEnd_7048693 < baseStart_7048693 := by decide
  rcases family_descends (prefixWord ++ tailWord_7048693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7048696 : List Nat := [2, 1, 2, 1, 1, 5, 1, 2, 2, 3, 3]
def baseStart_7048696 : Nat := 118140960795 + 7048696 * 2 ^ 59
def prefixEnd_7048696 : Nat := 4983230072969 + 3 ^ 40 * 7048696 * 2
def baseEnd_7048696 : Nat := 3619369035424059178183643

theorem tailTrace_7048696 : CollatzResearch.WordTrace tailWord_7048696 prefixEnd_7048696 3619369035424059178183643 := by
  unfold tailWord_7048696
  simp only [CollatzResearch.WordTrace]
  refine ⟨128543531835892844140394971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 171391375781190458853859961 128543531835892844140394971)
  ·
    refine ⟨192815297753839266210592457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128543531835892844140394971 192815297753839266210592457)
    ·
      refine ⟨144611473315379449657944343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 192815297753839266210592457 144611473315379449657944343)
      ·
        refine ⟨216917209973069174486916515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 144611473315379449657944343 216917209973069174486916515)
        ·
          refine ⟨325375814959603761730374773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 216917209973069174486916515 325375814959603761730374773)
          ·
            refine ⟨30503982652462852662222635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 325375814959603761730374773 30503982652462852662222635)
            ·
              refine ⟨45755973978694278993333953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30503982652462852662222635 45755973978694278993333953)
              ·
                refine ⟨34316980484020709245000465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45755973978694278993333953 34316980484020709245000465)
                ·
                  refine ⟨25737735363015531933750349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34316980484020709245000465 25737735363015531933750349)
                  ·
                    refine ⟨9651650761130824475156381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25737735363015531933750349 9651650761130824475156381)
                    ·
                      refine ⟨3619369035424059178183643, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9651650761130824475156381 3619369035424059178183643)
                      ·
                        rfl

theorem cell23_7048696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 5, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 5, 1, 2, 2, 3, 3].length) (baseStart_7048696 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7048696 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7048696 prefixEnd_7048696 := by exact prefixLift 7048696
  have htrace : WordTrace (prefixWord ++ tailWord_7048696) baseStart_7048696 baseEnd_7048696 := by
    simpa [prefixWord, tailWord_7048696, baseEnd_7048696] using wordTrace_append hprefix tailTrace_7048696
  have hstable : (prefixWord ++ tailWord_7048696).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7048696).length < 2 ^ (prefixWord ++ tailWord_7048696).sum := by decide
  have hdescent : baseEnd_7048696 < baseStart_7048696 := by decide
  rcases family_descends (prefixWord ++ tailWord_7048696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7048709 : List Nat := [1, 3, 1, 1, 2, 2, 1, 3, 1, 1, 7]
def baseStart_7048709 : Nat := 118140960795 + 7048709 * 2 ^ 59
def prefixEnd_7048709 : Nat := 4983230072969 + 3 ^ 40 * 7048709 * 2
def baseEnd_7048709 : Nat := 3619375710672567627321083

theorem tailTrace_7048709 : CollatzResearch.WordTrace tailWord_7048709 prefixEnd_7048709 3619375710672567627321083 := by
  unfold tailWord_7048709
  simp only [CollatzResearch.WordTrace]
  refine ⟨257087537820738591501013181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171391691880492394334008787 257087537820738591501013181)
  ·
    refine ⟨96407826682776971812879943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 257087537820738591501013181 96407826682776971812879943)
    ·
      refine ⟨144611740024165457719319915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96407826682776971812879943 144611740024165457719319915)
      ·
        refine ⟨216917610036248186578979873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 144611740024165457719319915 216917610036248186578979873)
        ·
          refine ⟨162688207527186139934234905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 216917610036248186578979873 162688207527186139934234905)
          ·
            refine ⟨122016155645389604950676179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 162688207527186139934234905 122016155645389604950676179)
            ·
              refine ⟨183024233468084407426014269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 122016155645389604950676179 183024233468084407426014269)
              ·
                refine ⟨68634087550531652784755351, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 183024233468084407426014269 68634087550531652784755351)
                ·
                  refine ⟨102951131325797479177133027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 68634087550531652784755351 102951131325797479177133027)
                  ·
                    refine ⟨154426696988696218765699541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 102951131325797479177133027 154426696988696218765699541)
                    ·
                      refine ⟨3619375710672567627321083, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 154426696988696218765699541 3619375710672567627321083)
                      ·
                        rfl

theorem cell23_7048709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 1, 3, 1, 1, 7].length) (baseStart_7048709 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7048709 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7048709 prefixEnd_7048709 := by exact prefixLift 7048709
  have htrace : WordTrace (prefixWord ++ tailWord_7048709) baseStart_7048709 baseEnd_7048709 := by
    simpa [prefixWord, tailWord_7048709, baseEnd_7048709] using wordTrace_append hprefix tailTrace_7048709
  have hstable : (prefixWord ++ tailWord_7048709).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7048709).length < 2 ^ (prefixWord ++ tailWord_7048709).sum := by decide
  have hdescent : baseEnd_7048709 < baseStart_7048709 := by decide
  rcases family_descends (prefixWord ++ tailWord_7048709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7048843 : List Nat := [1, 1, 1, 1, 4, 1, 4, 4, 1, 1, 4]
def baseStart_7048843 : Nat := 118140960795 + 7048843 * 2 ^ 59
def prefixEnd_7048843 : Nat := 4983230072969 + 3 ^ 40 * 7048843 * 2
def baseEnd_7048843 : Nat := 3619444517080270103045467

theorem tailTrace_7048843 : CollatzResearch.WordTrace tailWord_7048843 prefixEnd_7048843 3619444517080270103045467 := by
  unfold tailWord_7048843
  simp only [CollatzResearch.WordTrace]
  refine ⟨257092425202253132386391183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171394950134835421590927455 257092425202253132386391183)
  ·
    refine ⟨385638637803379698579586775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 257092425202253132386391183 385638637803379698579586775)
    ·
      refine ⟨578457956705069547869380163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 385638637803379698579586775 578457956705069547869380163)
      ·
        refine ⟨867686935057604321804070245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 578457956705069547869380163 867686935057604321804070245)
        ·
          refine ⟨162691300323300810338263171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 867686935057604321804070245 162691300323300810338263171)
          ·
            refine ⟨244036950484951215507394757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 162691300323300810338263171 244036950484951215507394757)
            ·
              refine ⟨45756928215928352907636517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 244036950484951215507394757 45756928215928352907636517)
              ·
                refine ⟨8579424040486566170181847, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 45756928215928352907636517 8579424040486566170181847)
                ·
                  refine ⟨12869136060729849255272771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8579424040486566170181847 12869136060729849255272771)
                  ·
                    refine ⟨19303704091094773882909157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12869136060729849255272771 19303704091094773882909157)
                    ·
                      refine ⟨3619444517080270103045467, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19303704091094773882909157 3619444517080270103045467)
                      ·
                        rfl

theorem cell23_7048843_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 4, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 4, 4, 1, 1, 4].length) (baseStart_7048843 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7048843 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7048843 prefixEnd_7048843 := by exact prefixLift 7048843
  have htrace : WordTrace (prefixWord ++ tailWord_7048843) baseStart_7048843 baseEnd_7048843 := by
    simpa [prefixWord, tailWord_7048843, baseEnd_7048843] using wordTrace_append hprefix tailTrace_7048843
  have hstable : (prefixWord ++ tailWord_7048843).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7048843).length < 2 ^ (prefixWord ++ tailWord_7048843).sum := by decide
  have hdescent : baseEnd_7048843 < baseStart_7048843 := by decide
  rcases family_descends (prefixWord ++ tailWord_7048843) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7048887 : List Nat := [1, 1, 3, 1, 5, 2, 3, 1, 2, 4]
def baseStart_7048887 : Nat := 118140960795 + 7048887 * 2 ^ 59
def prefixEnd_7048887 : Nat := 4983230072969 + 3 ^ 40 * 7048887 * 2
def baseEnd_7048887 : Nat := 1206489036743022643631755

theorem tailTrace_7048887 : CollatzResearch.WordTrace tailWord_7048887 prefixEnd_7048887 1206489036743022643631755 := by
  unfold tailWord_7048887
  simp only [CollatzResearch.WordTrace]
  refine ⟨257094030014093727900992915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171396020009395818600661943 257094030014093727900992915)
  ·
    refine ⟨385641045021140591851489373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 257094030014093727900992915 385641045021140591851489373)
    ·
      refine ⟨144615391882927721944308515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 385641045021140591851489373 144615391882927721944308515)
      ·
        refine ⟨216923087824391582916462773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 144615391882927721944308515 216923087824391582916462773)
        ·
          refine ⟨20336539483536710898418385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 216923087824391582916462773 20336539483536710898418385)
          ·
            refine ⟨15252404612652533173813789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20336539483536710898418385 15252404612652533173813789)
            ·
              refine ⟨5719651729744699940180171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15252404612652533173813789 5719651729744699940180171)
              ·
                refine ⟨8579477594617049910270257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5719651729744699940180171 8579477594617049910270257)
                ·
                  refine ⟨6434608195962787432702693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8579477594617049910270257 6434608195962787432702693)
                  ·
                    refine ⟨1206489036743022643631755, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6434608195962787432702693 1206489036743022643631755)
                    ·
                      rfl

theorem cell23_7048887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 2, 3, 1, 2, 4].length) (baseStart_7048887 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7048887 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7048887 prefixEnd_7048887 := by exact prefixLift 7048887
  have htrace : WordTrace (prefixWord ++ tailWord_7048887) baseStart_7048887 baseEnd_7048887 := by
    simpa [prefixWord, tailWord_7048887, baseEnd_7048887] using wordTrace_append hprefix tailTrace_7048887
  have hstable : (prefixWord ++ tailWord_7048887).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7048887).length < 2 ^ (prefixWord ++ tailWord_7048887).sum := by decide
  have hdescent : baseEnd_7048887 < baseStart_7048887 := by decide
  rcases family_descends (prefixWord ++ tailWord_7048887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7048890 : List Nat := [3, 1, 1, 1, 2, 6, 1, 1, 1, 2, 4]
def baseStart_7048890 : Nat := 118140960795 + 7048890 * 2 ^ 59
def prefixEnd_7048890 : Nat := 4983230072969 + 3 ^ 40 * 7048890 * 2
def baseEnd_7048890 : Nat := 3619468650671031419157751

theorem tailTrace_7048890 : CollatzResearch.WordTrace tailWord_7048890 prefixEnd_7048890 3619468650671031419157751 := by
  unfold tailWord_7048890
  simp only [CollatzResearch.WordTrace]
  refine ⟨64273534858270714853338031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 171396092955388572942234749 64273534858270714853338031)
  ·
    refine ⟨96410302287406072280007047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64273534858270714853338031 96410302287406072280007047)
    ·
      refine ⟨144615453431109108420010571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96410302287406072280007047 144615453431109108420010571)
      ·
        refine ⟨216923180146663662630015857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 144615453431109108420010571 216923180146663662630015857)
        ·
          refine ⟨162692385109997746972511893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 216923180146663662630015857 162692385109997746972511893)
          ·
            refine ⟨7626205552031144389336495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 162692385109997746972511893 7626205552031144389336495)
            ·
              refine ⟨11439308328046716584004743, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7626205552031144389336495 11439308328046716584004743)
              ·
                refine ⟨17158962492070074876007115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11439308328046716584004743 17158962492070074876007115)
                ·
                  refine ⟨25738443738105112314010673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17158962492070074876007115 25738443738105112314010673)
                  ·
                    refine ⟨19303832803578834235508005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25738443738105112314010673 19303832803578834235508005)
                    ·
                      refine ⟨3619468650671031419157751, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19303832803578834235508005 3619468650671031419157751)
                      ·
                        rfl

theorem cell23_7048890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 6, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 6, 1, 1, 1, 2, 4].length) (baseStart_7048890 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7048890 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7048890 prefixEnd_7048890 := by exact prefixLift 7048890
  have htrace : WordTrace (prefixWord ++ tailWord_7048890) baseStart_7048890 baseEnd_7048890 := by
    simpa [prefixWord, tailWord_7048890, baseEnd_7048890] using wordTrace_append hprefix tailTrace_7048890
  have hstable : (prefixWord ++ tailWord_7048890).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7048890).length < 2 ^ (prefixWord ++ tailWord_7048890).sum := by decide
  have hdescent : baseEnd_7048890 < baseStart_7048890 := by decide
  rcases family_descends (prefixWord ++ tailWord_7048890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7048910 : List Nat := [4, 1, 1, 1, 3, 1, 1, 1, 6, 1, 3]
def baseStart_7048910 : Nat := 118140960795 + 7048910 * 2 ^ 59
def prefixEnd_7048910 : Nat := 4983230072969 + 3 ^ 40 * 7048910 * 2
def baseEnd_7048910 : Nat := 3619478920284121340907659

theorem tailTrace_7048910 : CollatzResearch.WordTrace tailWord_7048910 prefixEnd_7048910 3619478920284121340907659 := by
  unfold tailWord_7048910
  simp only [CollatzResearch.WordTrace]
  refine ⟨32136858611626300353635023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 171396579262006935219386789 32136858611626300353635023)
  ·
    refine ⟨48205287917439450530452535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32136858611626300353635023 48205287917439450530452535)
    ·
      refine ⟨72307931876159175795678803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48205287917439450530452535 72307931876159175795678803)
      ·
        refine ⟨108461897814238763693518205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72307931876159175795678803 108461897814238763693518205)
        ·
          refine ⟨40673211680339536385069327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 108461897814238763693518205 40673211680339536385069327)
          ·
            refine ⟨61009817520509304577603991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40673211680339536385069327 61009817520509304577603991)
            ·
              refine ⟨91514726280763956866405987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61009817520509304577603991 91514726280763956866405987)
              ·
                refine ⟨137272089421145935299608981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 91514726280763956866405987 137272089421145935299608981)
                ·
                  refine ⟨6434629191616215717169171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 137272089421145935299608981 6434629191616215717169171)
                  ·
                    refine ⟨9651943787424323575753757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6434629191616215717169171 9651943787424323575753757)
                    ·
                      refine ⟨3619478920284121340907659, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9651943787424323575753757 3619478920284121340907659)
                      ·
                        rfl

theorem cell23_7048910_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 1, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 1, 1, 6, 1, 3].length) (baseStart_7048910 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7048910 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7048910 prefixEnd_7048910 := by exact prefixLift 7048910
  have htrace : WordTrace (prefixWord ++ tailWord_7048910) baseStart_7048910 baseEnd_7048910 := by
    simpa [prefixWord, tailWord_7048910, baseEnd_7048910] using wordTrace_append hprefix tailTrace_7048910
  have hstable : (prefixWord ++ tailWord_7048910).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7048910).length < 2 ^ (prefixWord ++ tailWord_7048910).sum := by decide
  have hdescent : baseEnd_7048910 < baseStart_7048910 := by decide
  rcases family_descends (prefixWord ++ tailWord_7048910) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7048933 : List Nat := [1, 3, 1, 4, 1, 1, 2, 1, 2, 3, 4]
def baseStart_7048933 : Nat := 118140960795 + 7048933 * 2 ^ 59
def prefixEnd_7048933 : Nat := 4983230072969 + 3 ^ 40 * 7048933 * 2
def baseEnd_7048933 : Nat := 3619490730339174750920053

theorem tailTrace_7048933 : CollatzResearch.WordTrace tailWord_7048933 prefixEnd_7048933 3619490730339174750920053 := by
  unfold tailWord_7048933
  simp only [CollatzResearch.WordTrace]
  refine ⟨257095707771927077757167453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171397138514618051838111635 257095707771927077757167453)
  ·
    refine ⟨96410890414472654158937795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 257095707771927077757167453 96410890414472654158937795)
    ·
      refine ⟨144616335621708981238406693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96410890414472654158937795 144616335621708981238406693)
      ·
        refine ⟨27115562929070433982201255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 144616335621708981238406693 27115562929070433982201255)
        ·
          refine ⟨40673344393605650973301883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27115562929070433982201255 40673344393605650973301883)
          ·
            refine ⟨61010016590408476459952825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40673344393605650973301883 61010016590408476459952825)
            ·
              refine ⟨45757512442806357344964619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 61010016590408476459952825 45757512442806357344964619)
              ·
                refine ⟨68636268664209536017446929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45757512442806357344964619 68636268664209536017446929)
                ·
                  refine ⟨51477201498157152013085197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 68636268664209536017446929 51477201498157152013085197)
                  ·
                    refine ⟨19303950561808932004906949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 51477201498157152013085197 19303950561808932004906949)
                    ·
                      refine ⟨3619490730339174750920053, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19303950561808932004906949 3619490730339174750920053)
                      ·
                        rfl

theorem cell23_7048933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 2, 1, 2, 3, 4].length) (baseStart_7048933 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7048933 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7048933 prefixEnd_7048933 := by exact prefixLift 7048933
  have htrace : WordTrace (prefixWord ++ tailWord_7048933) baseStart_7048933 baseEnd_7048933 := by
    simpa [prefixWord, tailWord_7048933, baseEnd_7048933] using wordTrace_append hprefix tailTrace_7048933
  have hstable : (prefixWord ++ tailWord_7048933).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7048933).length < 2 ^ (prefixWord ++ tailWord_7048933).sum := by decide
  have hdescent : baseEnd_7048933 < baseStart_7048933 := by decide
  rcases family_descends (prefixWord ++ tailWord_7048933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7049000 : List Nat := [2, 1, 5, 1, 1, 2, 1, 1, 1, 5, 3]
def baseStart_7049000 : Nat := 118140960795 + 7049000 * 2 ^ 59
def prefixEnd_7049000 : Nat := 4983230072969 + 3 ^ 40 * 7049000 * 2
def baseEnd_7049000 : Nat := 3619525133543025988782245

theorem tailTrace_7049000 : CollatzResearch.WordTrace tailWord_7049000 prefixEnd_7049000 3619525133543025988782245 := by
  unfold tailWord_7049000
  simp only [CollatzResearch.WordTrace]
  refine ⟨128549075731342174099928227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 171398767641789565466570969 128549075731342174099928227)
  ·
    refine ⟨192823613597013261149892341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128549075731342174099928227 192823613597013261149892341)
    ·
      refine ⟨18077213774719993232802407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 192823613597013261149892341 18077213774719993232802407)
      ·
        refine ⟨27115820662079989849203611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18077213774719993232802407 27115820662079989849203611)
        ·
          refine ⟨40673730993119984773805417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27115820662079989849203611 40673730993119984773805417)
          ·
            refine ⟨30505298244839988580354063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40673730993119984773805417 30505298244839988580354063)
            ·
              refine ⟨45757947367259982870531095, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30505298244839988580354063 45757947367259982870531095)
              ·
                refine ⟨68636921050889974305796643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45757947367259982870531095 68636921050889974305796643)
                ·
                  refine ⟨102955381576334961458694965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 68636921050889974305796643 102955381576334961458694965)
                  ·
                    refine ⟨9652067022781402636752653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 102955381576334961458694965 9652067022781402636752653)
                    ·
                      refine ⟨3619525133543025988782245, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9652067022781402636752653 3619525133543025988782245)
                      ·
                        rfl

theorem cell23_7049000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 2, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 2, 1, 1, 1, 5, 3].length) (baseStart_7049000 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7049000 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7049000 prefixEnd_7049000 := by exact prefixLift 7049000
  have htrace : WordTrace (prefixWord ++ tailWord_7049000) baseStart_7049000 baseEnd_7049000 := by
    simpa [prefixWord, tailWord_7049000, baseEnd_7049000] using wordTrace_append hprefix tailTrace_7049000
  have hstable : (prefixWord ++ tailWord_7049000).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7049000).length < 2 ^ (prefixWord ++ tailWord_7049000).sum := by decide
  have hdescent : baseEnd_7049000 < baseStart_7049000 := by decide
  rcases family_descends (prefixWord ++ tailWord_7049000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7049020 : List Nat := [2, 2, 2, 2, 1, 1, 5, 1, 2, 5]
def baseStart_7049020 : Nat := 118140960795 + 7049020 * 2 ^ 59
def prefixEnd_7049020 : Nat := 4983230072969 + 3 ^ 40 * 7049020 * 2
def baseEnd_7049020 : Nat := 1206511801052038636844051

theorem tailTrace_7049020 : CollatzResearch.WordTrace tailWord_7049020 prefixEnd_7049020 1206511801052038636844051 := by
  unfold tailWord_7049020
  simp only [CollatzResearch.WordTrace]
  refine ⟨128549440461305945807792257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 171399253948407927743723009 128549440461305945807792257)
  ·
    refine ⟨96412080345979459355844193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 128549440461305945807792257 96412080345979459355844193)
    ·
      refine ⟨72309060259484594516883145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 96412080345979459355844193 72309060259484594516883145)
      ·
        refine ⟨54231795194613445887662359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72309060259484594516883145 54231795194613445887662359)
        ·
          refine ⟨81347692791920168831493539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54231795194613445887662359 81347692791920168831493539)
          ·
            refine ⟨122021539187880253247240309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81347692791920168831493539 122021539187880253247240309)
            ·
              refine ⟨11439519298863773741928779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 122021539187880253247240309 11439519298863773741928779)
              ·
                refine ⟨17159278948295660612893169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11439519298863773741928779 17159278948295660612893169)
                ·
                  refine ⟨12869459211221745459669877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17159278948295660612893169 12869459211221745459669877)
                  ·
                    refine ⟨1206511801052038636844051, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12869459211221745459669877 1206511801052038636844051)
                    ·
                      rfl

theorem cell23_7049020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 5, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 5, 1, 2, 5].length) (baseStart_7049020 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7049020 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7049020 prefixEnd_7049020 := by exact prefixLift 7049020
  have htrace : WordTrace (prefixWord ++ tailWord_7049020) baseStart_7049020 baseEnd_7049020 := by
    simpa [prefixWord, tailWord_7049020, baseEnd_7049020] using wordTrace_append hprefix tailTrace_7049020
  have hstable : (prefixWord ++ tailWord_7049020).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7049020).length < 2 ^ (prefixWord ++ tailWord_7049020).sum := by decide
  have hdescent : baseEnd_7049020 < baseStart_7049020 := by decide
  rcases family_descends (prefixWord ++ tailWord_7049020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7049077 : List Nat := [1, 3, 4, 1, 1, 1, 2, 3, 2, 2, 3]
def baseStart_7049077 : Nat := 118140960795 + 7049077 * 2 ^ 59
def prefixEnd_7049077 : Nat := 4983230072969 + 3 ^ 40 * 7049077 * 2
def baseEnd_7049077 : Nat := 3619564671553422187519391

theorem tailTrace_7049077 : CollatzResearch.WordTrace tailWord_7049077 prefixEnd_7049077 3619564671553422187519391 := by
  unfold tailWord_7049077
  simp only [CollatzResearch.WordTrace]
  refine ⟨257100959883405390350409485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171400639922270260233606323 257100959883405390350409485)
  ·
    refine ⟨96412859956277021381403557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 257100959883405390350409485 96412859956277021381403557)
    ·
      refine ⟨18077411241801941509013167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 96412859956277021381403557 18077411241801941509013167)
      ·
        refine ⟨27116116862702912263519751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18077411241801941509013167 27116116862702912263519751)
        ·
          refine ⟨40674175294054368395279627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27116116862702912263519751 40674175294054368395279627)
          ·
            refine ⟨61011262941081552592919441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40674175294054368395279627 61011262941081552592919441)
            ·
              refine ⟨45758447205811164444689581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 61011262941081552592919441 45758447205811164444689581)
              ·
                refine ⟨17159417702179186666758593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 45758447205811164444689581 17159417702179186666758593)
                ·
                  refine ⟨12869563276634390000068945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17159417702179186666758593 12869563276634390000068945)
                  ·
                    refine ⟨9652172457475792500051709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12869563276634390000068945 9652172457475792500051709)
                    ·
                      refine ⟨3619564671553422187519391, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9652172457475792500051709 3619564671553422187519391)
                      ·
                        rfl

theorem cell23_7049077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 2, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 2, 3, 2, 2, 3].length) (baseStart_7049077 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7049077 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7049077 prefixEnd_7049077 := by exact prefixLift 7049077
  have htrace : WordTrace (prefixWord ++ tailWord_7049077) baseStart_7049077 baseEnd_7049077 := by
    simpa [prefixWord, tailWord_7049077, baseEnd_7049077] using wordTrace_append hprefix tailTrace_7049077
  have hstable : (prefixWord ++ tailWord_7049077).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7049077).length < 2 ^ (prefixWord ++ tailWord_7049077).sum := by decide
  have hdescent : baseEnd_7049077 < baseStart_7049077 := by decide
  rcases family_descends (prefixWord ++ tailWord_7049077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7049114 : List Nat := [3, 1, 1, 4, 2, 3, 2, 1, 6]
def baseStart_7049114 : Nat := 118140960795 + 7049114 * 2 ^ 59
def prefixEnd_7049114 : Nat := 4983230072969 + 3 ^ 40 * 7049114 * 2
def baseEnd_7049114 : Nat := 402175963370848726972969

theorem tailTrace_7049114 : CollatzResearch.WordTrace tailWord_7049114 prefixEnd_7049114 402175963370848726972969 := by
  unfold tailWord_7049114
  simp only [CollatzResearch.WordTrace]
  refine ⟨64275577346067836417376599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 171401539589514230446337597 64275577346067836417376599)
  ·
    refine ⟨96413366019101754626064899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64275577346067836417376599 96413366019101754626064899)
    ·
      refine ⟨144620049028652631939097349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96413366019101754626064899 144620049028652631939097349)
      ·
        refine ⟨27116259192872368488580753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 144620049028652631939097349 27116259192872368488580753)
        ·
          refine ⟨20337194394654276366435565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27116259192872368488580753 20337194394654276366435565)
          ·
            refine ⟨7626447897995353637413337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20337194394654276366435565 7626447897995353637413337)
            ·
              refine ⟨5719835923496515228060003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7626447897995353637413337 5719835923496515228060003)
              ·
                refine ⟨8579753885244772842090005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5719835923496515228060003 8579753885244772842090005)
                ·
                  refine ⟨402175963370848726972969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8579753885244772842090005 402175963370848726972969)
                  ·
                    rfl

theorem cell23_7049114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 3, 2, 1, 6].length) (baseStart_7049114 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7049114 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7049114 prefixEnd_7049114 := by exact prefixLift 7049114
  have htrace : WordTrace (prefixWord ++ tailWord_7049114) baseStart_7049114 baseEnd_7049114 := by
    simpa [prefixWord, tailWord_7049114, baseEnd_7049114] using wordTrace_append hprefix tailTrace_7049114
  have hstable : (prefixWord ++ tailWord_7049114).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7049114).length < 2 ^ (prefixWord ++ tailWord_7049114).sum := by decide
  have hdescent : baseEnd_7049114 < baseStart_7049114 := by decide
  rcases family_descends (prefixWord ++ tailWord_7049114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7049127 : List Nat := [1, 1, 6, 1, 2, 2, 1, 1, 3, 5]
def baseStart_7049127 : Nat := 118140960795 + 7049127 * 2 ^ 59
def prefixEnd_7049127 : Nat := 4983230072969 + 3 ^ 40 * 7049127 * 2
def baseEnd_7049127 : Nat := 1206530115195382330631387

theorem tailTrace_7049127 : CollatzResearch.WordTrace tailWord_7049127 prefixEnd_7049127 1206530115195382330631387 := by
  unfold tailWord_7049127
  simp only [CollatzResearch.WordTrace]
  refine ⟨257102783533224248889729635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171401855688816165926486423 257102783533224248889729635)
  ·
    refine ⟨385654175299836373334594453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 257102783533224248889729635 385654175299836373334594453)
    ·
      refine ⟨18077539467179830000059115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 385654175299836373334594453 18077539467179830000059115)
      ·
        refine ⟨27116309200769745000088673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18077539467179830000059115 27116309200769745000088673)
        ·
          refine ⟨20337231900577308750066505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27116309200769745000088673 20337231900577308750066505)
          ·
            refine ⟨15252923925432981562549879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20337231900577308750066505 15252923925432981562549879)
            ·
              refine ⟨22879385888149472343824819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15252923925432981562549879 22879385888149472343824819)
              ·
                refine ⟨34319078832224208515737229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22879385888149472343824819 34319078832224208515737229)
                ·
                  refine ⟨12869654562084078193401461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34319078832224208515737229 12869654562084078193401461)
                  ·
                    refine ⟨1206530115195382330631387, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12869654562084078193401461 1206530115195382330631387)
                    ·
                      rfl

theorem cell23_7049127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 2, 1, 1, 3, 5].length) (baseStart_7049127 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7049127 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7049127 prefixEnd_7049127 := by exact prefixLift 7049127
  have htrace : WordTrace (prefixWord ++ tailWord_7049127) baseStart_7049127 baseEnd_7049127 := by
    simpa [prefixWord, tailWord_7049127, baseEnd_7049127] using wordTrace_append hprefix tailTrace_7049127
  have hstable : (prefixWord ++ tailWord_7049127).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7049127).length < 2 ^ (prefixWord ++ tailWord_7049127).sum := by decide
  have hdescent : baseEnd_7049127 < baseStart_7049127 := by decide
  rcases family_descends (prefixWord ++ tailWord_7049127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7049153 : List Nat := [1, 2, 20]
def baseStart_7049153 : Nat := 118140960795 + 7049153 * 2 ^ 59
def prefixEnd_7049153 : Nat := 4983230072969 + 3 ^ 40 * 7049153 * 2
def baseEnd_7049153 : Nat := 551684757823984741681

theorem tailTrace_7049153 : CollatzResearch.WordTrace tailWord_7049153 prefixEnd_7049153 551684757823984741681 := by
  unfold tailWord_7049153
  simp only [CollatzResearch.WordTrace]
  refine ⟨257103731831130055330176113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171402487887420036886784075 257103731831130055330176113)
  ·
    refine ⟨192827798873347541497632085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 257103731831130055330176113 192827798873347541497632085)
    ·
      refine ⟨551684757823984741681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 20 192827798873347541497632085 551684757823984741681)
      ·
        rfl

theorem cell23_7049153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 20].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 20].length) (baseStart_7049153 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7049153 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7049153 prefixEnd_7049153 := by exact prefixLift 7049153
  have htrace : WordTrace (prefixWord ++ tailWord_7049153) baseStart_7049153 baseEnd_7049153 := by
    simpa [prefixWord, tailWord_7049153, baseEnd_7049153] using wordTrace_append hprefix tailTrace_7049153
  have hstable : (prefixWord ++ tailWord_7049153).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7049153).length < 2 ^ (prefixWord ++ tailWord_7049153).sum := by decide
  have hdescent : baseEnd_7049153 < baseStart_7049153 := by decide
  rcases family_descends (prefixWord ++ tailWord_7049153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7049187 : List Nat := [1, 1, 1, 6, 1, 3, 3, 7]
def baseStart_7049187 : Nat := 118140960795 + 7049187 * 2 ^ 59
def prefixEnd_7049187 : Nat := 4983230072969 + 3 ^ 40 * 7049187 * 2
def baseEnd_7049187 : Nat := 134060042756496916931255

theorem tailTrace_7049187 : CollatzResearch.WordTrace tailWord_7049187 prefixEnd_7049187 134060042756496916931255 := by
  unfold tailWord_7049187
  simp only [CollatzResearch.WordTrace]
  refine ⟨257104971913006879136913815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171403314608671252757942543 257104971913006879136913815)
  ·
    refine ⟨385657457869510318705370723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 257104971913006879136913815 385657457869510318705370723)
    ·
      refine ⟨578486186804265478058056085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 385657457869510318705370723 578486186804265478058056085)
      ·
        refine ⟨27116540006449944283971379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 578486186804265478058056085 27116540006449944283971379)
        ·
          refine ⟨40674810009674916425957069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27116540006449944283971379 40674810009674916425957069)
          ·
            refine ⟨15253053753628093659733901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40674810009674916425957069 15253053753628093659733901)
            ·
              refine ⟨5719895157610535122400213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15253053753628093659733901 5719895157610535122400213)
              ·
                refine ⟨134060042756496916931255, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5719895157610535122400213 134060042756496916931255)
                ·
                  rfl

theorem cell23_7049187_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 3, 3, 7].length) (baseStart_7049187 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7049187 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7049187 prefixEnd_7049187 := by exact prefixLift 7049187
  have htrace : WordTrace (prefixWord ++ tailWord_7049187) baseStart_7049187 baseEnd_7049187 := by
    simpa [prefixWord, tailWord_7049187, baseEnd_7049187] using wordTrace_append hprefix tailTrace_7049187
  have hstable : (prefixWord ++ tailWord_7049187).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7049187).length < 2 ^ (prefixWord ++ tailWord_7049187).sum := by decide
  have hdescent : baseEnd_7049187 < baseStart_7049187 := by decide
  rcases family_descends (prefixWord ++ tailWord_7049187) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7049198 : List Nat := [4, 1, 2, 1, 3, 1, 1, 5, 1, 2, 2]
def baseStart_7049198 : Nat := 118140960795 + 7049198 * 2 ^ 59
def prefixEnd_7049198 : Nat := 4983230072969 + 3 ^ 40 * 7049198 * 2
def baseEnd_7049198 : Nat := 3619626802712616214106335

theorem tailTrace_7049198 : CollatzResearch.WordTrace tailWord_7049198 prefixEnd_7049198 3619626802712616214106335 := by
  unfold tailWord_7049198
  simp only [CollatzResearch.WordTrace]
  refine ⟨32138171639495878501945531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 171403582077311352010376165 32138171639495878501945531)
  ·
    refine ⟨48207257459243817752918297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32138171639495878501945531 48207257459243817752918297)
    ·
      refine ⟨36155443094432863314688723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48207257459243817752918297 36155443094432863314688723)
      ·
        refine ⟨54233164641649294972033085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36155443094432863314688723 54233164641649294972033085)
        ·
          refine ⟨20337436740618485614512407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 54233164641649294972033085 20337436740618485614512407)
          ·
            refine ⟨30506155110927728421768611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20337436740618485614512407 30506155110927728421768611)
            ·
              refine ⟨45759232666391592632652917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30506155110927728421768611 45759232666391592632652917)
              ·
                refine ⟨4289928062474211809311211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 45759232666391592632652917 4289928062474211809311211)
                ·
                  refine ⟨6434892093711317713966817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4289928062474211809311211 6434892093711317713966817)
                  ·
                    refine ⟨4826169070283488285475113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6434892093711317713966817 4826169070283488285475113)
                    ·
                      refine ⟨3619626802712616214106335, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4826169070283488285475113 3619626802712616214106335)
                      ·
                        rfl

theorem cell23_7049198_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 1, 1, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 1, 1, 5, 1, 2, 2].length) (baseStart_7049198 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7049198 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7049198 prefixEnd_7049198 := by exact prefixLift 7049198
  have htrace : WordTrace (prefixWord ++ tailWord_7049198) baseStart_7049198 baseEnd_7049198 := by
    simpa [prefixWord, tailWord_7049198, baseEnd_7049198] using wordTrace_append hprefix tailTrace_7049198
  have hstable : (prefixWord ++ tailWord_7049198).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7049198).length < 2 ^ (prefixWord ++ tailWord_7049198).sum := by decide
  have hdescent : baseEnd_7049198 < baseStart_7049198 := by decide
  rcases family_descends (prefixWord ++ tailWord_7049198) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7049287 : List Nat := [1, 1, 4, 1, 3, 1, 2, 1, 1, 5, 3]
def baseStart_7049287 : Nat := 118140960795 + 7049287 * 2 ^ 59
def prefixEnd_7049287 : Nat := 4983230072969 + 3 ^ 40 * 7049287 * 2
def baseEnd_7049287 : Nat := 3619672502490866365893425

theorem tailTrace_7049287 : CollatzResearch.WordTrace tailWord_7049287 prefixEnd_7049287 3619672502490866365893425 := by
  unfold tailWord_7049287
  simp only [CollatzResearch.WordTrace]
  refine ⟨257108619212644596215554115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171405746141763064143702743 257108619212644596215554115)
  ·
    refine ⟨385662928818966894323331173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 257108619212644596215554115 385662928818966894323331173)
    ·
      refine ⟨72311799153556292685624595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 385662928818966894323331173 72311799153556292685624595)
      ·
        refine ⟨108467698730334439028436893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72311799153556292685624595 108467698730334439028436893)
        ·
          refine ⟨40675387023875414635663835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 108467698730334439028436893 40675387023875414635663835)
          ·
            refine ⟨61013080535813121953495753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40675387023875414635663835 61013080535813121953495753)
            ·
              refine ⟨45759810401859841465121815, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 61013080535813121953495753 45759810401859841465121815)
              ·
                refine ⟨68639715602789762197682723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45759810401859841465121815 68639715602789762197682723)
                ·
                  refine ⟨102959573404184643296524085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 68639715602789762197682723 102959573404184643296524085)
                  ·
                    refine ⟨9652460006642310309049133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 102959573404184643296524085 9652460006642310309049133)
                    ·
                      refine ⟨3619672502490866365893425, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9652460006642310309049133 3619672502490866365893425)
                      ·
                        rfl

theorem cell23_7049287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 2, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 2, 1, 1, 5, 3].length) (baseStart_7049287 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7049287 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7049287 prefixEnd_7049287 := by exact prefixLift 7049287
  have htrace : WordTrace (prefixWord ++ tailWord_7049287) baseStart_7049287 baseEnd_7049287 := by
    simpa [prefixWord, tailWord_7049287, baseEnd_7049287] using wordTrace_append hprefix tailTrace_7049287
  have hstable : (prefixWord ++ tailWord_7049287).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7049287).length < 2 ^ (prefixWord ++ tailWord_7049287).sum := by decide
  have hdescent : baseEnd_7049287 < baseStart_7049287 := by decide
  rcases family_descends (prefixWord ++ tailWord_7049287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7049317 : List Nat := [1, 3, 1, 3, 2, 2, 1, 2, 1, 2, 5]
def baseStart_7049317 : Nat := 118140960795 + 7049317 * 2 ^ 59
def prefixEnd_7049317 : Nat := 4983230072969 + 3 ^ 40 * 7049317 * 2
def baseEnd_7049317 : Nat := 3619687906910501248518287

theorem tailTrace_7049317 : CollatzResearch.WordTrace tailWord_7049317 prefixEnd_7049317 3619687906910501248518287 := by
  unfold tailWord_7049317
  simp only [CollatzResearch.WordTrace]
  refine ⟨257109713402535911339146205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171406475601690607559430803 257109713402535911339146205)
  ·
    refine ⟨96416142525950966752179827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 257109713402535911339146205 96416142525950966752179827)
    ·
      refine ⟨144624213788926450128269741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96416142525950966752179827 144624213788926450128269741)
      ·
        refine ⟨54234080170847418798101153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 144624213788926450128269741 54234080170847418798101153)
        ·
          refine ⟨40675560128135564098575865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54234080170847418798101153 40675560128135564098575865)
          ·
            refine ⟨30506670096101673073931899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40675560128135564098575865 30506670096101673073931899)
            ·
              refine ⟨45760005144152509610897849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30506670096101673073931899 45760005144152509610897849)
              ·
                refine ⟨34320003858114382208173387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45760005144152509610897849 34320003858114382208173387)
                ·
                  refine ⟨51480005787171573312260081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34320003858114382208173387 51480005787171573312260081)
                  ·
                    refine ⟨38610004340378679984195061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 51480005787171573312260081 38610004340378679984195061)
                    ·
                      refine ⟨3619687906910501248518287, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 38610004340378679984195061 3619687906910501248518287)
                      ·
                        rfl

theorem cell23_7049317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 2, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 2, 1, 2, 1, 2, 5].length) (baseStart_7049317 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7049317 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7049317 prefixEnd_7049317 := by exact prefixLift 7049317
  have htrace : WordTrace (prefixWord ++ tailWord_7049317) baseStart_7049317 baseEnd_7049317 := by
    simpa [prefixWord, tailWord_7049317, baseEnd_7049317] using wordTrace_append hprefix tailTrace_7049317
  have hstable : (prefixWord ++ tailWord_7049317).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7049317).length < 2 ^ (prefixWord ++ tailWord_7049317).sum := by decide
  have hdescent : baseEnd_7049317 < baseStart_7049317 := by decide
  rcases family_descends (prefixWord ++ tailWord_7049317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7049334 : List Nat := [5, 1, 1, 2, 1, 2, 2, 1, 1, 2, 5]
def baseStart_7049334 : Nat := 118140960795 + 7049334 * 2 ^ 59
def prefixEnd_7049334 : Nat := 4983230072969 + 3 ^ 40 * 7049334 * 2
def baseEnd_7049334 : Nat := 3619696636081627682005709

theorem tailTrace_7049334 : CollatzResearch.WordTrace tailWord_7049334 prefixEnd_7049334 3619696636081627682005709 := by
  unfold tailWord_7049334
  simp only [CollatzResearch.WordTrace]
  refine ⟨16069395840217145202657191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 171406888962316215495010037 16069395840217145202657191)
  ·
    refine ⟨24104093760325717803985787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16069395840217145202657191 24104093760325717803985787)
    ·
      refine ⟨36156140640488576705978681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24104093760325717803985787 36156140640488576705978681)
      ·
        refine ⟨27117105480366432529484011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36156140640488576705978681 27117105480366432529484011)
        ·
          refine ⟨40675658220549648794226017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27117105480366432529484011 40675658220549648794226017)
          ·
            refine ⟨30506743665412236595669513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40675658220549648794226017 30506743665412236595669513)
            ·
              refine ⟨22880057749059177446752135, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30506743665412236595669513 22880057749059177446752135)
              ·
                refine ⟨34320086623588766170128203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22880057749059177446752135 34320086623588766170128203)
                ·
                  refine ⟨51480129935383149255192305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34320086623588766170128203 51480129935383149255192305)
                  ·
                    refine ⟨38610097451537361941394229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 51480129935383149255192305 38610097451537361941394229)
                    ·
                      refine ⟨3619696636081627682005709, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 38610097451537361941394229 3619696636081627682005709)
                      ·
                        rfl

theorem cell23_7049334_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 2, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 2, 2, 1, 1, 2, 5].length) (baseStart_7049334 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7049334 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7049334 prefixEnd_7049334 := by exact prefixLift 7049334
  have htrace : WordTrace (prefixWord ++ tailWord_7049334) baseStart_7049334 baseEnd_7049334 := by
    simpa [prefixWord, tailWord_7049334, baseEnd_7049334] using wordTrace_append hprefix tailTrace_7049334
  have hstable : (prefixWord ++ tailWord_7049334).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7049334).length < 2 ^ (prefixWord ++ tailWord_7049334).sum := by decide
  have hdescent : baseEnd_7049334 < baseStart_7049334 := by decide
  rcases family_descends (prefixWord ++ tailWord_7049334) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7049354 : List Nat := [3, 1, 2, 3, 1, 2, 1, 1, 5, 4]
def baseStart_7049354 : Nat := 118140960795 + 7049354 * 2 ^ 59
def prefixEnd_7049354 : Nat := 4983230072969 + 3 ^ 40 * 7049354 * 2
def baseEnd_7049354 : Nat := 1206568968564905867918539

theorem tailTrace_7049354 : CollatzResearch.WordTrace tailWord_7049354 prefixEnd_7049354 1206568968564905867918539 := by
  unfold tailWord_7049354
  simp only [CollatzResearch.WordTrace]
  refine ⟨64277765725850466664560779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 171407375268934577772162077 64277765725850466664560779)
  ·
    refine ⟨96416648588775699996841169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64277765725850466664560779 96416648588775699996841169)
    ·
      refine ⟨72312486441581774997630877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 96416648588775699996841169 72312486441581774997630877)
      ·
        refine ⟨27117182415593165624111579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 72312486441581774997630877 27117182415593165624111579)
        ·
          refine ⟨40675773623389748436167369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27117182415593165624111579 40675773623389748436167369)
          ·
            refine ⟨30506830217542311327125527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40675773623389748436167369 30506830217542311327125527)
            ·
              refine ⟨45760245326313466990688291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30506830217542311327125527 45760245326313466990688291)
              ·
                refine ⟨68640367989470200486032437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45760245326313466990688291 68640367989470200486032437)
                ·
                  refine ⟨6435034499012831295565541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 68640367989470200486032437 6435034499012831295565541)
                  ·
                    refine ⟨1206568968564905867918539, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6435034499012831295565541 1206568968564905867918539)
                    ·
                      rfl

theorem cell23_7049354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 2, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 2, 1, 1, 5, 4].length) (baseStart_7049354 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7049354 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7049354 prefixEnd_7049354 := by exact prefixLift 7049354
  have htrace : WordTrace (prefixWord ++ tailWord_7049354) baseStart_7049354 baseEnd_7049354 := by
    simpa [prefixWord, tailWord_7049354, baseEnd_7049354] using wordTrace_append hprefix tailTrace_7049354
  have hstable : (prefixWord ++ tailWord_7049354).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7049354).length < 2 ^ (prefixWord ++ tailWord_7049354).sum := by decide
  have hdescent : baseEnd_7049354 < baseStart_7049354 := by decide
  rcases family_descends (prefixWord ++ tailWord_7049354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7049358 : List Nat := [4, 1, 1, 3, 4, 1, 1, 1, 2, 5]
def baseStart_7049358 : Nat := 118140960795 + 7049358 * 2 ^ 59
def prefixEnd_7049358 : Nat := 4983230072969 + 3 ^ 40 * 7049358 * 2
def baseEnd_7049358 : Nat := 1206569653205778529368533

theorem tailTrace_7049358 : CollatzResearch.WordTrace tailWord_7049358 prefixEnd_7049358 1206569653205778529368533 := by
  unfold tailWord_7049358
  simp only [CollatzResearch.WordTrace]
  refine ⟨32138901099423421917673591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 171407472530258250227592485 32138901099423421917673591)
  ·
    refine ⟨48208351649135132876510387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32138901099423421917673591 48208351649135132876510387)
    ·
      refine ⟨72312527473702699314765581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48208351649135132876510387 72312527473702699314765581)
      ·
        refine ⟨27117197802638512243037093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 72312527473702699314765581 27117197802638512243037093)
        ·
          refine ⟨5084474587994721045569455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 27117197802638512243037093 5084474587994721045569455)
          ·
            refine ⟨7626711881992081568354183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5084474587994721045569455 7626711881992081568354183)
            ·
              refine ⟨11440067822988122352531275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7626711881992081568354183 11440067822988122352531275)
              ·
                refine ⟨17160101734482183528796913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11440067822988122352531275 17160101734482183528796913)
                ·
                  refine ⟨12870076300861637646597685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17160101734482183528796913 12870076300861637646597685)
                  ·
                    refine ⟨1206569653205778529368533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12870076300861637646597685 1206569653205778529368533)
                    ·
                      rfl

theorem cell23_7049358_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 4, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 4, 1, 1, 1, 2, 5].length) (baseStart_7049358 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7049358 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7049358 prefixEnd_7049358 := by exact prefixLift 7049358
  have htrace : WordTrace (prefixWord ++ tailWord_7049358) baseStart_7049358 baseEnd_7049358 := by
    simpa [prefixWord, tailWord_7049358, baseEnd_7049358] using wordTrace_append hprefix tailTrace_7049358
  have hstable : (prefixWord ++ tailWord_7049358).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7049358).length < 2 ^ (prefixWord ++ tailWord_7049358).sum := by decide
  have hdescent : baseEnd_7049358 < baseStart_7049358 := by decide
  rcases family_descends (prefixWord ++ tailWord_7049358) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7049454 : List Nat := [4, 1, 2, 1, 1, 1, 1, 1, 2, 6, 3]
def baseStart_7049454 : Nat := 118140960795 + 7049454 * 2 ^ 59
def prefixEnd_7049454 : Nat := 4983230072969 + 3 ^ 40 * 7049454 * 2
def baseEnd_7049454 : Nat := 3619758253760167212505157

theorem tailTrace_7049454 : CollatzResearch.WordTrace tailWord_7049454 prefixEnd_7049454 3619758253760167212505157 := by
  unfold tailWord_7049454
  simp only [CollatzResearch.WordTrace]
  refine ⟨32139338775379947967110427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 171409806802026389157922277 32139338775379947967110427)
  ·
    refine ⟨48209008163069921950665641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32139338775379947967110427 48209008163069921950665641)
    ·
      refine ⟨36156756122302441462999231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48209008163069921950665641 36156756122302441462999231)
      ·
        refine ⟨54235134183453662194498847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36156756122302441462999231 54235134183453662194498847)
        ·
          refine ⟨81352701275180493291748271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54235134183453662194498847 81352701275180493291748271)
          ·
            refine ⟨122029051912770739937622407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81352701275180493291748271 122029051912770739937622407)
            ·
              refine ⟨183043577869156109906433611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 122029051912770739937622407 183043577869156109906433611)
              ·
                refine ⟨274565366803734164859650417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 183043577869156109906433611 274565366803734164859650417)
                ·
                  refine ⟨205924025102800623644737813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 274565366803734164859650417 205924025102800623644737813)
                  ·
                    refine ⟨9652688676693779233347085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 205924025102800623644737813 9652688676693779233347085)
                    ·
                      refine ⟨3619758253760167212505157, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9652688676693779233347085 3619758253760167212505157)
                      ·
                        rfl

theorem cell23_7049454_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 1, 1, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 1, 1, 2, 6, 3].length) (baseStart_7049454 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7049454 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7049454 prefixEnd_7049454 := by exact prefixLift 7049454
  have htrace : WordTrace (prefixWord ++ tailWord_7049454) baseStart_7049454 baseEnd_7049454 := by
    simpa [prefixWord, tailWord_7049454, baseEnd_7049454] using wordTrace_append hprefix tailTrace_7049454
  have hstable : (prefixWord ++ tailWord_7049454).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7049454).length < 2 ^ (prefixWord ++ tailWord_7049454).sum := by decide
  have hdescent : baseEnd_7049454 < baseStart_7049454 := by decide
  rcases family_descends (prefixWord ++ tailWord_7049454) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7049457 : List Nat := [1, 2, 2, 2, 2, 1, 3, 10]
def baseStart_7049457 : Nat := 118140960795 + 7049457 * 2 ^ 59
def prefixEnd_7049457 : Nat := 4983230072969 + 3 ^ 40 * 7049457 * 2
def baseEnd_7049457 : Nat := 134065177563041877806209

theorem tailTrace_7049457 : CollatzResearch.WordTrace tailWord_7049457 prefixEnd_7049457 134065177563041877806209 := by
  unfold tailWord_7049457
  simp only [CollatzResearch.WordTrace]
  refine ⟨257114819622028715249242625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171409879748019143499495083 257114819622028715249242625)
  ·
    refine ⟨192836114716521536436931969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 257114819622028715249242625 192836114716521536436931969)
    ·
      refine ⟨144627086037391152327698977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 192836114716521536436931969 144627086037391152327698977)
      ·
        refine ⟨108470314528043364245774233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 144627086037391152327698977 108470314528043364245774233)
        ·
          refine ⟨81352735896032523184330675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 108470314528043364245774233 81352735896032523184330675)
          ·
            refine ⟨122029103844048784776496013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81352735896032523184330675 122029103844048784776496013)
            ·
              refine ⟨45760913941518294291186005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 122029103844048784776496013 45760913941518294291186005)
              ·
                refine ⟨134065177563041877806209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 45760913941518294291186005 134065177563041877806209)
                ·
                  rfl

theorem cell23_7049457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 3, 10].length) (baseStart_7049457 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7049457 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7049457 prefixEnd_7049457 := by exact prefixLift 7049457
  have htrace : WordTrace (prefixWord ++ tailWord_7049457) baseStart_7049457 baseEnd_7049457 := by
    simpa [prefixWord, tailWord_7049457, baseEnd_7049457] using wordTrace_append hprefix tailTrace_7049457
  have hstable : (prefixWord ++ tailWord_7049457).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7049457).length < 2 ^ (prefixWord ++ tailWord_7049457).sum := by decide
  have hdescent : baseEnd_7049457 < baseStart_7049457 := by decide
  rcases family_descends (prefixWord ++ tailWord_7049457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7049468 : List Nat := [2, 2, 2, 1, 4, 3, 1, 2, 1, 1, 4]
def baseStart_7049468 : Nat := 118140960795 + 7049468 * 2 ^ 59
def prefixEnd_7049468 : Nat := 4983230072969 + 3 ^ 40 * 7049468 * 2
def baseEnd_7049468 : Nat := 3619765442489330157730093

theorem tailTrace_7049468 : CollatzResearch.WordTrace tailWord_7049468 prefixEnd_7049468 3619765442489330157730093 := by
  unfold tailWord_7049468
  simp only [CollatzResearch.WordTrace]
  refine ⟨128557610412494432063946529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 171410147216659242751928705 128557610412494432063946529)
  ·
    refine ⟨96418207809370824047959897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 128557610412494432063946529 96418207809370824047959897)
    ·
      refine ⟨72313655857028118035969923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 96418207809370824047959897 72313655857028118035969923)
      ·
        refine ⟨108470483785542177053954885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72313655857028118035969923 108470483785542177053954885)
        ·
          refine ⟨20338215709789158197616541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 108470483785542177053954885 20338215709789158197616541)
          ·
            refine ⟨7626830891170934324106203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20338215709789158197616541 7626830891170934324106203)
            ·
              refine ⟨11440246336756401486159305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7626830891170934324106203 11440246336756401486159305)
              ·
                refine ⟨8580184752567301114619479, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11440246336756401486159305 8580184752567301114619479)
                ·
                  refine ⟨12870277128850951671929219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8580184752567301114619479 12870277128850951671929219)
                  ·
                    refine ⟨19305415693276427507893829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12870277128850951671929219 19305415693276427507893829)
                    ·
                      refine ⟨3619765442489330157730093, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19305415693276427507893829 3619765442489330157730093)
                      ·
                        rfl

theorem cell23_7049468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 3, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 3, 1, 2, 1, 1, 4].length) (baseStart_7049468 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7049468 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7049468 prefixEnd_7049468 := by exact prefixLift 7049468
  have htrace : WordTrace (prefixWord ++ tailWord_7049468) baseStart_7049468 baseEnd_7049468 := by
    simpa [prefixWord, tailWord_7049468, baseEnd_7049468] using wordTrace_append hprefix tailTrace_7049468
  have hstable : (prefixWord ++ tailWord_7049468).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7049468).length < 2 ^ (prefixWord ++ tailWord_7049468).sum := by decide
  have hdescent : baseEnd_7049468 < baseStart_7049468 := by decide
  rcases family_descends (prefixWord ++ tailWord_7049468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7049487 : List Nat := [1, 1, 2, 1, 1, 1, 3, 2, 4, 7]
def baseStart_7049487 : Nat := 118140960795 + 7049487 * 2 ^ 59
def prefixEnd_7049487 : Nat := 4983230072969 + 3 ^ 40 * 7049487 * 2
def baseEnd_7049487 : Nat := 1206591732873921861130835

theorem tailTrace_7049487 : CollatzResearch.WordTrace tailWord_7049487 prefixEnd_7049487 1206591732873921861130835 := by
  unfold tailWord_7049487
  simp only [CollatzResearch.WordTrace]
  refine ⟨257115913811920030372834715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171410609207946686915223143 257115913811920030372834715)
  ·
    refine ⟨385673870717880045559252073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 257115913811920030372834715 385673870717880045559252073)
    ·
      refine ⟨289255403038410034169439055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 385673870717880045559252073 289255403038410034169439055)
      ·
        refine ⟨433883104557615051254158583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 289255403038410034169439055 433883104557615051254158583)
        ·
          refine ⟨650824656836422576881237875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 433883104557615051254158583 650824656836422576881237875)
          ·
            refine ⟨976236985254633865321856813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 650824656836422576881237875 976236985254633865321856813)
            ·
              refine ⟨366088869470487699495696305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 976236985254633865321856813 366088869470487699495696305)
              ·
                refine ⟨274566652102865774621772229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 366088869470487699495696305 274566652102865774621772229)
                ·
                  refine ⟨51481247269287332741582293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 274566652102865774621772229 51481247269287332741582293)
                  ·
                    refine ⟨1206591732873921861130835, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 51481247269287332741582293 1206591732873921861130835)
                    ·
                      rfl

theorem cell23_7049487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 3, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 3, 2, 4, 7].length) (baseStart_7049487 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7049487 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7049487 prefixEnd_7049487 := by exact prefixLift 7049487
  have htrace : WordTrace (prefixWord ++ tailWord_7049487) baseStart_7049487 baseEnd_7049487 := by
    simpa [prefixWord, tailWord_7049487, baseEnd_7049487] using wordTrace_append hprefix tailTrace_7049487
  have hstable : (prefixWord ++ tailWord_7049487).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7049487).length < 2 ^ (prefixWord ++ tailWord_7049487).sum := by decide
  have hdescent : baseEnd_7049487 < baseStart_7049487 := by decide
  rcases family_descends (prefixWord ++ tailWord_7049487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7049497 : List Nat := [1, 2, 1, 2, 1, 1, 1, 1, 1, 5, 7]
def baseStart_7049497 : Nat := 118140960795 + 7049497 * 2 ^ 59
def prefixEnd_7049497 : Nat := 4983230072969 + 3 ^ 40 * 7049497 * 2
def baseEnd_7049497 : Nat := 3619780333428310544267459

theorem tailTrace_7049497 : CollatzResearch.WordTrace tailWord_7049497 prefixEnd_7049497 3619780333428310544267459 := by
  unfold tailWord_7049497
  simp only [CollatzResearch.WordTrace]
  refine ⟨257116278541883802080698745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171410852361255868053799163 257116278541883802080698745)
  ·
    refine ⟨192837208906412851560524059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 257116278541883802080698745 192837208906412851560524059)
    ·
      refine ⟨289255813359619277340786089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 192837208906412851560524059 289255813359619277340786089)
      ·
        refine ⟨216941860019714458005589567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 289255813359619277340786089 216941860019714458005589567)
        ·
          refine ⟨325412790029571687008384351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 216941860019714458005589567 325412790029571687008384351)
          ·
            refine ⟨488119185044357530512576527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 325412790029571687008384351 488119185044357530512576527)
            ·
              refine ⟨732178777566536295768864791, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 488119185044357530512576527 732178777566536295768864791)
              ·
                refine ⟨1098268166349804443653297187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 732178777566536295768864791 1098268166349804443653297187)
                ·
                  refine ⟨1647402249524706665479945781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1098268166349804443653297187 1647402249524706665479945781)
                  ·
                    refine ⟨154443960892941249888744917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1647402249524706665479945781 154443960892941249888744917)
                    ·
                      refine ⟨3619780333428310544267459, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 154443960892941249888744917 3619780333428310544267459)
                      ·
                        rfl

theorem cell23_7049497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 1, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 1, 1, 5, 7].length) (baseStart_7049497 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7049497 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7049497 prefixEnd_7049497 := by exact prefixLift 7049497
  have htrace : WordTrace (prefixWord ++ tailWord_7049497) baseStart_7049497 baseEnd_7049497 := by
    simpa [prefixWord, tailWord_7049497, baseEnd_7049497] using wordTrace_append hprefix tailTrace_7049497
  have hstable : (prefixWord ++ tailWord_7049497).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7049497).length < 2 ^ (prefixWord ++ tailWord_7049497).sum := by decide
  have hdescent : baseEnd_7049497 < baseStart_7049497 := by decide
  rcases family_descends (prefixWord ++ tailWord_7049497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7049504 : List Nat := [2, 1, 1, 5, 2, 1, 1, 1, 2, 7]
def baseStart_7049504 : Nat := 118140960795 + 7049504 * 2 ^ 59
def prefixEnd_7049504 : Nat := 4983230072969 + 3 ^ 40 * 7049504 * 2
def baseEnd_7049504 : Nat := 1206594642597630672293309

theorem tailTrace_7049504 : CollatzResearch.WordTrace tailWord_7049504 prefixEnd_7049504 1206594642597630672293309 := by
  unfold tailWord_7049504
  simp only [CollatzResearch.WordTrace]
  refine ⟨128558266926429221138101783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 171411022568572294850802377 128558266926429221138101783)
  ·
    refine ⟨192837400389643831707152675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128558266926429221138101783 192837400389643831707152675)
    ·
      refine ⟨289256100584465747560729013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 192837400389643831707152675 289256100584465747560729013)
      ·
        refine ⟨27117759429793663833818345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 289256100584465747560729013 27117759429793663833818345)
        ·
          refine ⟨20338319572345247875363759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27117759429793663833818345 20338319572345247875363759)
          ·
            refine ⟨30507479358517871813045639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20338319572345247875363759 30507479358517871813045639)
            ·
              refine ⟨45761219037776807719568459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30507479358517871813045639 45761219037776807719568459)
              ·
                refine ⟨68641828556665211579352689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45761219037776807719568459 68641828556665211579352689)
                ·
                  refine ⟨51481371417498908684514517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 68641828556665211579352689 51481371417498908684514517)
                  ·
                    refine ⟨1206594642597630672293309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 51481371417498908684514517 1206594642597630672293309)
                    ·
                      rfl

theorem cell23_7049504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 1, 1, 1, 2, 7].length) (baseStart_7049504 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7049504 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7049504 prefixEnd_7049504 := by exact prefixLift 7049504
  have htrace : WordTrace (prefixWord ++ tailWord_7049504) baseStart_7049504 baseEnd_7049504 := by
    simpa [prefixWord, tailWord_7049504, baseEnd_7049504] using wordTrace_append hprefix tailTrace_7049504
  have hstable : (prefixWord ++ tailWord_7049504).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7049504).length < 2 ^ (prefixWord ++ tailWord_7049504).sum := by decide
  have hdescent : baseEnd_7049504 < baseStart_7049504 := by decide
  rcases family_descends (prefixWord ++ tailWord_7049504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7049544 : List Nat := [2, 1, 3, 1, 1, 2, 2, 3, 2, 1, 5]
def baseStart_7049544 : Nat := 118140960795 + 7049544 * 2 ^ 59
def prefixEnd_7049544 : Nat := 4983230072969 + 3 ^ 40 * 7049544 * 2
def baseEnd_7049544 : Nat := 3619804467019071860379743

theorem tailTrace_7049544 : CollatzResearch.WordTrace tailWord_7049544 prefixEnd_7049544 3619804467019071860379743 := by
  unfold tailWord_7049544
  simp only [CollatzResearch.WordTrace]
  refine ⟨128558996386356764553829843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 171411995181809019405106457 128558996386356764553829843)
  ·
    refine ⟨192838494579535146830744765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128558996386356764553829843 192838494579535146830744765)
    ·
      refine ⟨72314435467325680061529287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 192838494579535146830744765 72314435467325680061529287)
      ·
        refine ⟨108471653200988520092293931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72314435467325680061529287 108471653200988520092293931)
        ·
          refine ⟨162707479801482780138440897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 108471653200988520092293931 162707479801482780138440897)
          ·
            refine ⟨122030609851112085103830673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 162707479801482780138440897 122030609851112085103830673)
            ·
              refine ⟨91522957388334063827873005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 122030609851112085103830673 91522957388334063827873005)
              ·
                refine ⟨34321109020625273935452377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 91522957388334063827873005 34321109020625273935452377)
                ·
                  refine ⟨25740831765468955451589283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34321109020625273935452377 25740831765468955451589283)
                  ·
                    refine ⟨38611247648203433177383925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 25740831765468955451589283 38611247648203433177383925)
                    ·
                      refine ⟨3619804467019071860379743, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 38611247648203433177383925 3619804467019071860379743)
                      ·
                        rfl

theorem cell23_7049544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 2, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 2, 3, 2, 1, 5].length) (baseStart_7049544 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7049544 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7049544 prefixEnd_7049544 := by exact prefixLift 7049544
  have htrace : WordTrace (prefixWord ++ tailWord_7049544) baseStart_7049544 baseEnd_7049544 := by
    simpa [prefixWord, tailWord_7049544, baseEnd_7049544] using wordTrace_append hprefix tailTrace_7049544
  have hstable : (prefixWord ++ tailWord_7049544).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7049544).length < 2 ^ (prefixWord ++ tailWord_7049544).sum := by decide
  have hdescent : baseEnd_7049544 < baseStart_7049544 := by decide
  rcases family_descends (prefixWord ++ tailWord_7049544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7049566 : List Nat := [4, 4, 2, 1, 2, 1, 1, 1, 1, 2, 4]
def baseStart_7049566 : Nat := 118140960795 + 7049566 * 2 ^ 59
def prefixEnd_7049566 : Nat := 4983230072969 + 3 ^ 40 * 7049566 * 2
def baseEnd_7049566 : Nat := 3619815763593470774304643

theorem tailTrace_7049566 : CollatzResearch.WordTrace tailWord_7049566 prefixEnd_7049566 3619815763593470774304643 := by
  unfold tailWord_7049566
  simp only [CollatzResearch.WordTrace]
  refine ⟨32139849397329228358120069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 171412530119089217909973701 32139849397329228358120069)
  ·
    refine ⟨6026221761999230317147513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 32139849397329228358120069 6026221761999230317147513)
    ·
      refine ⟨4519666321499422737860635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6026221761999230317147513 4519666321499422737860635)
      ·
        refine ⟨6779499482249134106790953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4519666321499422737860635 6779499482249134106790953)
        ·
          refine ⟨5084624611686850580093215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6779499482249134106790953 5084624611686850580093215)
          ·
            refine ⟨7626936917530275870139823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5084624611686850580093215 7626936917530275870139823)
            ·
              refine ⟨11440405376295413805209735, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7626936917530275870139823 11440405376295413805209735)
              ·
                refine ⟨17160608064443120707814603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11440405376295413805209735 17160608064443120707814603)
                ·
                  refine ⟨25740912096664681061721905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17160608064443120707814603 25740912096664681061721905)
                  ·
                    refine ⟨19305684072498510796291429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25740912096664681061721905 19305684072498510796291429)
                    ·
                      refine ⟨3619815763593470774304643, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19305684072498510796291429 3619815763593470774304643)
                      ·
                        rfl

theorem cell23_7049566_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 2, 1, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 2, 1, 1, 1, 1, 2, 4].length) (baseStart_7049566 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7049566 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7049566 prefixEnd_7049566 := by exact prefixLift 7049566
  have htrace : WordTrace (prefixWord ++ tailWord_7049566) baseStart_7049566 baseEnd_7049566 := by
    simpa [prefixWord, tailWord_7049566, baseEnd_7049566] using wordTrace_append hprefix tailTrace_7049566
  have hstable : (prefixWord ++ tailWord_7049566).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7049566).length < 2 ^ (prefixWord ++ tailWord_7049566).sum := by decide
  have hdescent : baseEnd_7049566 < baseStart_7049566 := by decide
  rcases family_descends (prefixWord ++ tailWord_7049566) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7049575 : List Nat := [1, 1, 5, 1, 3, 3, 1, 1, 1, 4, 2]
def baseStart_7049575 : Nat := 118140960795 + 7049575 * 2 ^ 59
def prefixEnd_7049575 : Nat := 4983230072969 + 3 ^ 40 * 7049575 * 2
def baseEnd_7049575 : Nat := 3619820384919361239092101

theorem tailTrace_7049575 : CollatzResearch.WordTrace tailWord_7049575 prefixEnd_7049575 3619820384919361239092101 := by
  unfold tailWord_7049575
  simp only [CollatzResearch.WordTrace]
  refine ⟨257119123435601221402038179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171412748957067480934692119 257119123435601221402038179)
  ·
    refine ⟨385678685153401832103057269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 257119123435601221402038179 385678685153401832103057269)
    ·
      refine ⟨36157376733131421759661619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 385678685153401832103057269 36157376733131421759661619)
      ·
        refine ⟨54236065099697132639492429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36157376733131421759661619 54236065099697132639492429)
        ·
          refine ⟨20338524412386424739809661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 54236065099697132639492429 20338524412386424739809661)
          ·
            refine ⟨7626946654644909277428623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20338524412386424739809661 7626946654644909277428623)
            ·
              refine ⟨11440419981967363916142935, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7626946654644909277428623 11440419981967363916142935)
              ·
                refine ⟨17160629972951045874214403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11440419981967363916142935 17160629972951045874214403)
                ·
                  refine ⟨25740944959426568811321605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17160629972951045874214403 25740944959426568811321605)
                  ·
                    refine ⟨4826427179892481652122801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25740944959426568811321605 4826427179892481652122801)
                    ·
                      refine ⟨3619820384919361239092101, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4826427179892481652122801 3619820384919361239092101)
                      ·
                        rfl

theorem cell23_7049575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 3, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 3, 1, 1, 1, 4, 2].length) (baseStart_7049575 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7049575 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7049575 prefixEnd_7049575 := by exact prefixLift 7049575
  have htrace : WordTrace (prefixWord ++ tailWord_7049575) baseStart_7049575 baseEnd_7049575 := by
    simpa [prefixWord, tailWord_7049575, baseEnd_7049575] using wordTrace_append hprefix tailTrace_7049575
  have hstable : (prefixWord ++ tailWord_7049575).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7049575).length < 2 ^ (prefixWord ++ tailWord_7049575).sum := by decide
  have hdescent : baseEnd_7049575 < baseStart_7049575 := by decide
  rcases family_descends (prefixWord ++ tailWord_7049575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7049611 : List Nat := [1, 1, 1, 1, 4, 5, 1, 2, 2, 5]
def baseStart_7049611 : Nat := 118140960795 + 7049611 * 2 ^ 59
def prefixEnd_7049611 : Nat := 4983230072969 + 3 ^ 40 * 7049611 * 2
def baseEnd_7049611 : Nat := 1206612956740974366080645

theorem tailTrace_7049611 : CollatzResearch.WordTrace tailWord_7049611 prefixEnd_7049611 1206612956740974366080645 := by
  unfold tailWord_7049611
  simp only [CollatzResearch.WordTrace]
  refine ⟨257120436463470799550348687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171413624308980533033565791 257120436463470799550348687)
  ·
    refine ⟨385680654695206199325523031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 257120436463470799550348687 385680654695206199325523031)
    ·
      refine ⟨578520982042809298988284547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 385680654695206199325523031 578520982042809298988284547)
      ·
        refine ⟨867781473064213948482426821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 578520982042809298988284547 867781473064213948482426821)
        ·
          refine ⟨162709026199540115340455029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 867781473064213948482426821 162709026199540115340455029)
          ·
            refine ⟨15253971206206885813167659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 162709026199540115340455029 15253971206206885813167659)
            ·
              refine ⟨22880956809310328719751489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15253971206206885813167659 22880956809310328719751489)
              ·
                refine ⟨17160717606982746539813617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22880956809310328719751489 17160717606982746539813617)
                ·
                  refine ⟨12870538205237059904860213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17160717606982746539813617 12870538205237059904860213)
                  ·
                    refine ⟨1206612956740974366080645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12870538205237059904860213 1206612956740974366080645)
                    ·
                      rfl

theorem cell23_7049611_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 5, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 5, 1, 2, 2, 5].length) (baseStart_7049611 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7049611 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7049611 prefixEnd_7049611 := by exact prefixLift 7049611
  have htrace : WordTrace (prefixWord ++ tailWord_7049611) baseStart_7049611 baseEnd_7049611 := by
    simpa [prefixWord, tailWord_7049611, baseEnd_7049611] using wordTrace_append hprefix tailTrace_7049611
  have hstable : (prefixWord ++ tailWord_7049611).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7049611).length < 2 ^ (prefixWord ++ tailWord_7049611).sum := by decide
  have hdescent : baseEnd_7049611 < baseStart_7049611 := by decide
  rcases family_descends (prefixWord ++ tailWord_7049611) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7049631 : List Nat := [1, 1, 2, 5, 1, 1, 1, 2, 4, 1, 4]
def baseStart_7049631 : Nat := 118140960795 + 7049631 * 2 ^ 59
def prefixEnd_7049631 : Nat := 4983230072969 + 3 ^ 40 * 7049631 * 2
def baseEnd_7049631 : Nat := 3619849139836013019991843

theorem tailTrace_7049631 : CollatzResearch.WordTrace tailWord_7049631 prefixEnd_7049631 3619849139836013019991843 := by
  unfold tailWord_7049631
  simp only [CollatzResearch.WordTrace]
  refine ⟨257121165923398342966076747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171414110615598895310717831 257121165923398342966076747)
  ·
    refine ⟨385681748885097514449115121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 257121165923398342966076747 385681748885097514449115121)
    ·
      refine ⟨289261311663823135836836341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 385681748885097514449115121 289261311663823135836836341)
      ·
        refine ⟨27118247968483418984703407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 289261311663823135836836341 27118247968483418984703407)
        ·
          refine ⟨40677371952725128477055111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27118247968483418984703407 40677371952725128477055111)
          ·
            refine ⟨61016057929087692715582667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40677371952725128477055111 61016057929087692715582667)
            ·
              refine ⟨91524086893631539073374001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61016057929087692715582667 91524086893631539073374001)
              ·
                refine ⟨68643065170223654305030501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 91524086893631539073374001 68643065170223654305030501)
                ·
                  refine ⟨12870574719416935182193219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 68643065170223654305030501 12870574719416935182193219)
                  ·
                    refine ⟨19305862079125402773289829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12870574719416935182193219 19305862079125402773289829)
                    ·
                      refine ⟨3619849139836013019991843, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19305862079125402773289829 3619849139836013019991843)
                      ·
                        rfl

theorem cell23_7049631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 1, 2, 4, 1, 4].length) (baseStart_7049631 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7049631 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7049631 prefixEnd_7049631 := by exact prefixLift 7049631
  have htrace : WordTrace (prefixWord ++ tailWord_7049631) baseStart_7049631 baseEnd_7049631 := by
    simpa [prefixWord, tailWord_7049631, baseEnd_7049631] using wordTrace_append hprefix tailTrace_7049631
  have hstable : (prefixWord ++ tailWord_7049631).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7049631).length < 2 ^ (prefixWord ++ tailWord_7049631).sum := by decide
  have hdescent : baseEnd_7049631 < baseStart_7049631 := by decide
  rcases family_descends (prefixWord ++ tailWord_7049631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7049641 : List Nat := [1, 2, 1, 1, 1, 1, 3, 6, 3, 4]
def baseStart_7049641 : Nat := 118140960795 + 7049641 * 2 ^ 59
def prefixEnd_7049641 : Nat := 4983230072969 + 3 ^ 40 * 7049641 * 2
def baseEnd_7049641 : Nat := 1206618091547519326955599

theorem tailTrace_7049641 : CollatzResearch.WordTrace tailWord_7049641 prefixEnd_7049641 1206618091547519326955599 := by
  unfold tailWord_7049641
  simp only [CollatzResearch.WordTrace]
  refine ⟨257121530653362114673940777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171414353768908076449293851 257121530653362114673940777)
  ·
    refine ⟨192841147990021586005455583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 257121530653362114673940777 192841147990021586005455583)
    ·
      refine ⟨289261721985032379008183375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 192841147990021586005455583 289261721985032379008183375)
      ·
        refine ⟨433892582977548568512275063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 289261721985032379008183375 433892582977548568512275063)
        ·
          refine ⟨650838874466322852768412595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 433892582977548568512275063 650838874466322852768412595)
          ·
            refine ⟨976258311699484279152618893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 650838874466322852768412595 976258311699484279152618893)
            ·
              refine ⟨366096866887306604682232085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 976258311699484279152618893 366096866887306604682232085)
              ·
                refine ⟨17160790635342497094479629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 366096866887306604682232085 17160790635342497094479629)
                ·
                  refine ⟨6435296488253436410429861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17160790635342497094479629 6435296488253436410429861)
                  ·
                    refine ⟨1206618091547519326955599, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6435296488253436410429861 1206618091547519326955599)
                    ·
                      rfl

theorem cell23_7049641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 3, 6, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 3, 6, 3, 4].length) (baseStart_7049641 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7049641 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7049641 prefixEnd_7049641 := by exact prefixLift 7049641
  have htrace : WordTrace (prefixWord ++ tailWord_7049641) baseStart_7049641 baseEnd_7049641 := by
    simpa [prefixWord, tailWord_7049641, baseEnd_7049641] using wordTrace_append hprefix tailTrace_7049641
  have hstable : (prefixWord ++ tailWord_7049641).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7049641).length < 2 ^ (prefixWord ++ tailWord_7049641).sum := by decide
  have hdescent : baseEnd_7049641 < baseStart_7049641 := by decide
  rcases family_descends (prefixWord ++ tailWord_7049641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7049644 : List Nat := [2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 6]
def baseStart_7049644 : Nat := 118140960795 + 7049644 * 2 ^ 59
def prefixEnd_7049644 : Nat := 4983230072969 + 3 ^ 40 * 7049644 * 2
def baseEnd_7049644 : Nat := 3619855815084521469129283

theorem tailTrace_7049644 : CollatzResearch.WordTrace tailWord_7049644 prefixEnd_7049644 3619855815084521469129283 := by
  unfold tailWord_7049644
  simp only [CollatzResearch.WordTrace]
  refine ⟨128560820036175623093149993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 171414426714900830790866657 128560820036175623093149993)
  ·
    refine ⟨96420615027131717319862495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 128560820036175623093149993 96420615027131717319862495)
    ·
      refine ⟨144630922540697575979793743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96420615027131717319862495 144630922540697575979793743)
      ·
        refine ⟨216946383811046363969690615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 144630922540697575979793743 216946383811046363969690615)
        ·
          refine ⟨325419575716569545954535923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 216946383811046363969690615 325419575716569545954535923)
          ·
            refine ⟨488129363574854318931803885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 325419575716569545954535923 488129363574854318931803885)
            ·
              refine ⟨183048511340570369599426457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 488129363574854318931803885 183048511340570369599426457)
              ·
                refine ⟨137286383505427777199569843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 183048511340570369599426457 137286383505427777199569843)
                ·
                  refine ⟨205929575258141665799354765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 137286383505427777199569843 205929575258141665799354765)
                  ·
                    refine ⟨77223590721803124674758037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 205929575258141665799354765 77223590721803124674758037)
                    ·
                      refine ⟨3619855815084521469129283, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 77223590721803124674758037 3619855815084521469129283)
                      ·
                        rfl

theorem cell23_7049644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 6].length) (baseStart_7049644 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7049644 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7049644 prefixEnd_7049644 := by exact prefixLift 7049644
  have htrace : WordTrace (prefixWord ++ tailWord_7049644) baseStart_7049644 baseEnd_7049644 := by
    simpa [prefixWord, tailWord_7049644, baseEnd_7049644] using wordTrace_append hprefix tailTrace_7049644
  have hstable : (prefixWord ++ tailWord_7049644).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7049644).length < 2 ^ (prefixWord ++ tailWord_7049644).sum := by decide
  have hdescent : baseEnd_7049644 < baseStart_7049644 := by decide
  rcases family_descends (prefixWord ++ tailWord_7049644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7049645 : List Nat := [1, 5, 2, 2, 2, 1, 2, 1, 2, 5]
def baseStart_7049645 : Nat := 118140960795 + 7049645 * 2 ^ 59
def prefixEnd_7049645 : Nat := 4983230072969 + 3 ^ 40 * 7049645 * 2
def baseEnd_7049645 : Nat := 1206618776188391988405593

theorem tailTrace_7049645 : CollatzResearch.WordTrace tailWord_7049645 prefixEnd_7049645 1206618776188391988405593 := by
  unfold tailWord_7049645
  simp only [CollatzResearch.WordTrace]
  refine ⟨257121676545347623357086389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171414451030231748904724259 257121676545347623357086389)
  ·
    refine ⟨24105157176126339689726849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 257121676545347623357086389 24105157176126339689726849)
    ·
      refine ⟨18078867882094754767295137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24105157176126339689726849 18078867882094754767295137)
      ·
        refine ⟨13559150911571066075471353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18078867882094754767295137 13559150911571066075471353)
        ·
          refine ⟨10169363183678299556603515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13559150911571066075471353 10169363183678299556603515)
          ·
            refine ⟨15254044775517449334905273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10169363183678299556603515 15254044775517449334905273)
            ·
              refine ⟨11440533581638087001178955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15254044775517449334905273 11440533581638087001178955)
              ·
                refine ⟨17160800372457130501768433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11440533581638087001178955 17160800372457130501768433)
                ·
                  refine ⟨12870600279342847876326325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17160800372457130501768433 12870600279342847876326325)
                  ·
                    refine ⟨1206618776188391988405593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12870600279342847876326325 1206618776188391988405593)
                    ·
                      rfl

theorem cell23_7049645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 2, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 2, 1, 2, 1, 2, 5].length) (baseStart_7049645 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7049645 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7049645 prefixEnd_7049645 := by exact prefixLift 7049645
  have htrace : WordTrace (prefixWord ++ tailWord_7049645) baseStart_7049645 baseEnd_7049645 := by
    simpa [prefixWord, tailWord_7049645, baseEnd_7049645] using wordTrace_append hprefix tailTrace_7049645
  have hstable : (prefixWord ++ tailWord_7049645).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7049645).length < 2 ^ (prefixWord ++ tailWord_7049645).sum := by decide
  have hdescent : baseEnd_7049645 < baseStart_7049645 := by decide
  rcases family_descends (prefixWord ++ tailWord_7049645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7049671 : List Nat := [1, 1, 4, 1, 1, 4, 1, 4, 6]
def baseStart_7049671 : Nat := 118140960795 + 7049671 * 2 ^ 59
def prefixEnd_7049671 : Nat := 4983230072969 + 3 ^ 40 * 7049671 * 2
def baseEnd_7049671 : Nat := 402207742118021429276851

theorem tailTrace_7049671 : CollatzResearch.WordTrace tailWord_7049671 prefixEnd_7049671 402207742118021429276851 := by
  unfold tailWord_7049671
  simp only [CollatzResearch.WordTrace]
  refine ⟨257122624843253429797532867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171415083228835619865021911 257122624843253429797532867)
  ·
    refine ⟨385683937264880144696299301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 257122624843253429797532867 385683937264880144696299301)
    ·
      refine ⟨72315738237165027130556119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 385683937264880144696299301 72315738237165027130556119)
      ·
        refine ⟨108473607355747540695834179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72315738237165027130556119 108473607355747540695834179)
        ·
          refine ⟨162710411033621311043751269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 108473607355747540695834179 162710411033621311043751269)
          ·
            refine ⟨30508202068803995820703363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 162710411033621311043751269 30508202068803995820703363)
            ·
              refine ⟨45762303103205993731055045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30508202068803995820703363 45762303103205993731055045)
              ·
                refine ⟨8580431831851123824572821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 45762303103205993731055045 8580431831851123824572821)
                ·
                  refine ⟨402207742118021429276851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8580431831851123824572821 402207742118021429276851)
                  ·
                    rfl

theorem cell23_7049671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 4, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 4, 1, 4, 6].length) (baseStart_7049671 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7049671 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7049671 prefixEnd_7049671 := by exact prefixLift 7049671
  have htrace : WordTrace (prefixWord ++ tailWord_7049671) baseStart_7049671 baseEnd_7049671 := by
    simpa [prefixWord, tailWord_7049671, baseEnd_7049671] using wordTrace_append hprefix tailTrace_7049671
  have hstable : (prefixWord ++ tailWord_7049671).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7049671).length < 2 ^ (prefixWord ++ tailWord_7049671).sum := by decide
  have hdescent : baseEnd_7049671 < baseStart_7049671 := by decide
  rcases family_descends (prefixWord ++ tailWord_7049671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7049682 : List Nat := [3, 2, 2, 4, 1, 1, 1, 1, 2, 4, 2]
def baseStart_7049682 : Nat := 118140960795 + 7049682 * 2 ^ 59
def prefixEnd_7049682 : Nat := 4983230072969 + 3 ^ 40 * 7049682 * 2
def baseEnd_7049682 : Nat := 3619875327349392320454109

theorem tailTrace_7049682 : CollatzResearch.WordTrace tailWord_7049682 prefixEnd_7049682 3619875327349392320454109 := by
  unfold tailWord_7049682
  simp only [CollatzResearch.WordTrace]
  refine ⟨64280756511553394669045825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 171415350697475719117455533 64280756511553394669045825)
  ·
    refine ⟨48210567383665046001784369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64280756511553394669045825 48210567383665046001784369)
    ·
      refine ⟨36157925537748784501338277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48210567383665046001784369 36157925537748784501338277)
      ·
        refine ⟨6779611038327897094000927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 36157925537748784501338277 6779611038327897094000927)
        ·
          refine ⟨10169416557491845641001391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6779611038327897094000927 10169416557491845641001391)
          ·
            refine ⟨15254124836237768461502087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10169416557491845641001391 15254124836237768461502087)
            ·
              refine ⟨22881187254356652692253131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15254124836237768461502087 22881187254356652692253131)
              ·
                refine ⟨34321780881534979038379697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22881187254356652692253131 34321780881534979038379697)
                ·
                  refine ⟨25741335661151234278784773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34321780881534979038379697 25741335661151234278784773)
                  ·
                    refine ⟨4826500436465856427272145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25741335661151234278784773 4826500436465856427272145)
                    ·
                      refine ⟨3619875327349392320454109, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4826500436465856427272145 3619875327349392320454109)
                      ·
                        rfl

theorem cell23_7049682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 1, 1, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 1, 1, 1, 1, 2, 4, 2].length) (baseStart_7049682 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7049682 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7049682 prefixEnd_7049682 := by exact prefixLift 7049682
  have htrace : WordTrace (prefixWord ++ tailWord_7049682) baseStart_7049682 baseEnd_7049682 := by
    simpa [prefixWord, tailWord_7049682, baseEnd_7049682] using wordTrace_append hprefix tailTrace_7049682
  have hstable : (prefixWord ++ tailWord_7049682).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7049682).length < 2 ^ (prefixWord ++ tailWord_7049682).sum := by decide
  have hdescent : baseEnd_7049682 < baseStart_7049682 := by decide
  rcases family_descends (prefixWord ++ tailWord_7049682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7049708 : List Nat := [2, 2, 1, 1, 2, 1, 5, 1, 1, 5, 2]
def baseStart_7049708 : Nat := 118140960795 + 7049708 * 2 ^ 59
def prefixEnd_7049708 : Nat := 4983230072969 + 3 ^ 40 * 7049708 * 2
def baseEnd_7049708 : Nat := 3619888677846409218728989

theorem tailTrace_7049708 : CollatzResearch.WordTrace tailWord_7049708 prefixEnd_7049708 3619888677846409218728989 := by
  unfold tailWord_7049708
  simp only [CollatzResearch.WordTrace]
  refine ⟨128561987172059692558314889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 171415982896079590077753185 128561987172059692558314889)
  ·
    refine ⟨96421490379044769418736167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 128561987172059692558314889 96421490379044769418736167)
    ·
      refine ⟨144632235568567154128104251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96421490379044769418736167 144632235568567154128104251)
      ·
        refine ⟨216948353352850731192156377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 144632235568567154128104251 216948353352850731192156377)
        ·
          refine ⟨162711265014638048394117283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 216948353352850731192156377 162711265014638048394117283)
          ·
            refine ⟨244066897521957072591175925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 162711265014638048394117283 244066897521957072591175925)
            ·
              refine ⟨22881271642683475555422743, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 244066897521957072591175925 22881271642683475555422743)
              ·
                refine ⟨34321907464025213333134115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22881271642683475555422743 34321907464025213333134115)
                ·
                  refine ⟨51482861196037819999701173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34321907464025213333134115 51482861196037819999701173)
                  ·
                    refine ⟨4826518237128545624971985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 51482861196037819999701173 4826518237128545624971985)
                    ·
                      refine ⟨3619888677846409218728989, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4826518237128545624971985 3619888677846409218728989)
                      ·
                        rfl

theorem cell23_7049708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 5, 2].length) (baseStart_7049708 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7049708 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7049708 prefixEnd_7049708 := by exact prefixLift 7049708
  have htrace : WordTrace (prefixWord ++ tailWord_7049708) baseStart_7049708 baseEnd_7049708 := by
    simpa [prefixWord, tailWord_7049708, baseEnd_7049708] using wordTrace_append hprefix tailTrace_7049708
  have hstable : (prefixWord ++ tailWord_7049708).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7049708).length < 2 ^ (prefixWord ++ tailWord_7049708).sum := by decide
  have hdescent : baseEnd_7049708 < baseStart_7049708 := by decide
  rcases family_descends (prefixWord ++ tailWord_7049708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7049732 : List Nat := [2, 3, 2, 3, 1, 2, 2, 1, 3, 1, 3]
def baseStart_7049732 : Nat := 118140960795 + 7049732 * 2 ^ 59
def prefixEnd_7049732 : Nat := 4983230072969 + 3 ^ 40 * 7049732 * 2
def baseEnd_7049732 : Nat := 3619901001382117124828879

theorem tailTrace_7049732 : CollatzResearch.WordTrace tailWord_7049732 prefixEnd_7049732 3619901001382117124828879 := by
  unfold tailWord_7049732
  simp only [CollatzResearch.WordTrace]
  refine ⟨128562424848016218607751725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 171416566464021624810335633 128562424848016218607751725)
  ·
    refine ⟨48210909318006081977906897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 128562424848016218607751725 48210909318006081977906897)
    ·
      refine ⟨36158181988504561483430173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48210909318006081977906897 36158181988504561483430173)
      ·
        refine ⟨13559318245689210556286315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36158181988504561483430173 13559318245689210556286315)
        ·
          refine ⟨20338977368533815834429473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13559318245689210556286315 20338977368533815834429473)
          ·
            refine ⟨15254233026400361875822105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20338977368533815834429473 15254233026400361875822105)
            ·
              refine ⟨11440674769800271406866579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15254233026400361875822105 11440674769800271406866579)
              ·
                refine ⟨17161012154700407110299869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11440674769800271406866579 17161012154700407110299869)
                ·
                  refine ⟨6435379558012652666362451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17161012154700407110299869 6435379558012652666362451)
                  ·
                    refine ⟨9653069337018978999543677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6435379558012652666362451 9653069337018978999543677)
                    ·
                      refine ⟨3619901001382117124828879, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9653069337018978999543677 3619901001382117124828879)
                      ·
                        rfl

theorem cell23_7049732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 2, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 2, 2, 1, 3, 1, 3].length) (baseStart_7049732 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7049732 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7049732 prefixEnd_7049732 := by exact prefixLift 7049732
  have htrace : WordTrace (prefixWord ++ tailWord_7049732) baseStart_7049732 baseEnd_7049732 := by
    simpa [prefixWord, tailWord_7049732, baseEnd_7049732] using wordTrace_append hprefix tailTrace_7049732
  have hstable : (prefixWord ++ tailWord_7049732).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7049732).length < 2 ^ (prefixWord ++ tailWord_7049732).sum := by decide
  have hdescent : baseEnd_7049732 < baseStart_7049732 := by decide
  rcases family_descends (prefixWord ++ tailWord_7049732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7049761 : List Nat := [1, 2, 3, 2, 2, 1, 3, 9]
def baseStart_7049761 : Nat := 118140960795 + 7049761 * 2 ^ 59
def prefixEnd_7049761 : Nat := 4983230072969 + 3 ^ 40 * 7049761 * 2
def baseEnd_7049761 : Nat := 134070958974855463383935

theorem tailTrace_7049761 : CollatzResearch.WordTrace tailWord_7049761 prefixEnd_7049761 134070958974855463383935 := by
  unfold tailWord_7049761
  simp only [CollatzResearch.WordTrace]
  refine ⟨257125907412927375168309137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171417271608618250112206091 257125907412927375168309137)
  ·
    refine ⟨192844430559695531376231853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 257125907412927375168309137 192844430559695531376231853)
    ·
      refine ⟨72316661459885824266086945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 192844430559695531376231853 72316661459885824266086945)
      ·
        refine ⟨54237496094914368199565209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72316661459885824266086945 54237496094914368199565209)
        ·
          refine ⟨40678122071185776149673907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54237496094914368199565209 40678122071185776149673907)
          ·
            refine ⟨61017183106778664224510861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40678122071185776149673907 61017183106778664224510861)
            ·
              refine ⟨22881443665041999084191573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 61017183106778664224510861 22881443665041999084191573)
              ·
                refine ⟨134070958974855463383935, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 22881443665041999084191573 134070958974855463383935)
                ·
                  rfl

theorem cell23_7049761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 3, 9].length) (baseStart_7049761 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7049761 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7049761 prefixEnd_7049761 := by exact prefixLift 7049761
  have htrace : WordTrace (prefixWord ++ tailWord_7049761) baseStart_7049761 baseEnd_7049761 := by
    simpa [prefixWord, tailWord_7049761, baseEnd_7049761] using wordTrace_append hprefix tailTrace_7049761
  have hstable : (prefixWord ++ tailWord_7049761).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7049761).length < 2 ^ (prefixWord ++ tailWord_7049761).sum := by decide
  have hdescent : baseEnd_7049761 < baseStart_7049761 := by decide
  rcases family_descends (prefixWord ++ tailWord_7049761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7049789 : List Nat := [1, 4, 1, 3, 2, 3, 1, 1, 3, 2, 2]
def baseStart_7049789 : Nat := 118140960795 + 7049789 * 2 ^ 59
def prefixEnd_7049789 : Nat := 4983230072969 + 3 ^ 40 * 7049789 * 2
def baseEnd_7049789 : Nat := 3619930269779423401816117

theorem tailTrace_7049789 : CollatzResearch.WordTrace tailWord_7049789 prefixEnd_7049789 3619930269779423401816117 := by
  unfold tailWord_7049789
  simp only [CollatzResearch.WordTrace]
  refine ⟨257126928656825935950328421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171417952437883957300218947 257126928656825935950328421)
  ·
    refine ⟨48211299123154862990686579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 257126928656825935950328421 48211299123154862990686579)
    ·
      refine ⟨72316948684732294486029869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48211299123154862990686579 72316948684732294486029869)
      ·
        refine ⟨27118855756774610432261201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 72316948684732294486029869 27118855756774610432261201)
        ·
          refine ⟨20339141817580957824195901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27118855756774610432261201 20339141817580957824195901)
          ·
            refine ⟨7627178181592859184073463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20339141817580957824195901 7627178181592859184073463)
            ·
              refine ⟨11440767272389288776110195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7627178181592859184073463 11440767272389288776110195)
              ·
                refine ⟨17161150908583933164165293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11440767272389288776110195 17161150908583933164165293)
                ·
                  refine ⟨6435431590718974936561985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17161150908583933164165293 6435431590718974936561985)
                  ·
                    refine ⟨4826573693039231202421489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6435431590718974936561985 4826573693039231202421489)
                    ·
                      refine ⟨3619930269779423401816117, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4826573693039231202421489 3619930269779423401816117)
                      ·
                        rfl

theorem cell23_7049789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 3, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 3, 1, 1, 3, 2, 2].length) (baseStart_7049789 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7049789 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7049789 prefixEnd_7049789 := by exact prefixLift 7049789
  have htrace : WordTrace (prefixWord ++ tailWord_7049789) baseStart_7049789 baseEnd_7049789 := by
    simpa [prefixWord, tailWord_7049789, baseEnd_7049789] using wordTrace_append hprefix tailTrace_7049789
  have hstable : (prefixWord ++ tailWord_7049789).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7049789).length < 2 ^ (prefixWord ++ tailWord_7049789).sum := by decide
  have hdescent : baseEnd_7049789 < baseStart_7049789 := by decide
  rcases family_descends (prefixWord ++ tailWord_7049789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7049791 : List Nat := [1, 1, 2, 2, 3, 2, 2, 1, 2, 7]
def baseStart_7049791 : Nat := 118140960795 + 7049791 * 2 ^ 59
def prefixEnd_7049791 : Nat := 4983230072969 + 3 ^ 40 * 7049791 * 2
def baseEnd_7049791 : Nat := 1206643765580244131330369

theorem tailTrace_7049791 : CollatzResearch.WordTrace tailWord_7049791 prefixEnd_7049791 1206643765580244131330369 := by
  unfold tailWord_7049791
  simp only [CollatzResearch.WordTrace]
  refine ⟨257127001602818690291901227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171418001068545793527934151 257127001602818690291901227)
  ·
    refine ⟨385690502404228035437851841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 257127001602818690291901227 385690502404228035437851841)
    ·
      refine ⟨289267876803171026578388881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 385690502404228035437851841 289267876803171026578388881)
      ·
        refine ⟨216950907602378269933791661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 289267876803171026578388881 216950907602378269933791661)
        ·
          refine ⟨81356590350891851225171873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 216950907602378269933791661 81356590350891851225171873)
          ·
            refine ⟨61017442763168888418878905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 81356590350891851225171873 61017442763168888418878905)
            ·
              refine ⟨45763082072376666314159179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 61017442763168888418878905 45763082072376666314159179)
              ·
                refine ⟨68644623108564999471238769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45763082072376666314159179 68644623108564999471238769)
                ·
                  refine ⟨51483467331423749603429077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 68644623108564999471238769 51483467331423749603429077)
                  ·
                    refine ⟨1206643765580244131330369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 51483467331423749603429077 1206643765580244131330369)
                    ·
                      rfl

theorem cell23_7049791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 2, 1, 2, 7].length) (baseStart_7049791 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7049791 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7049791 prefixEnd_7049791 := by exact prefixLift 7049791
  have htrace : WordTrace (prefixWord ++ tailWord_7049791) baseStart_7049791 baseEnd_7049791 := by
    simpa [prefixWord, tailWord_7049791, baseEnd_7049791] using wordTrace_append hprefix tailTrace_7049791
  have hstable : (prefixWord ++ tailWord_7049791).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7049791).length < 2 ^ (prefixWord ++ tailWord_7049791).sum := by decide
  have hdescent : baseEnd_7049791 < baseStart_7049791 := by decide
  rcases family_descends (prefixWord ++ tailWord_7049791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7049815 : List Nat := [1, 1, 3, 2, 2, 2, 3, 1, 3, 3, 2]
def baseStart_7049815 : Nat := 118140960795 + 7049815 * 2 ^ 59
def prefixEnd_7049815 : Nat := 4983230072969 + 3 ^ 40 * 7049815 * 2
def baseEnd_7049815 : Nat := 3619943620276440300090997

theorem tailTrace_7049815 : CollatzResearch.WordTrace tailWord_7049815 prefixEnd_7049815 3619943620276440300090997 := by
  unfold tailWord_7049815
  simp only [CollatzResearch.WordTrace]
  refine ⟨257127876954731742390774899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171418584636487828260516599 257127876954731742390774899)
  ·
    refine ⟨385691815432097613586162349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 257127876954731742390774899 385691815432097613586162349)
    ·
      refine ⟨144634430787036605094810881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 385691815432097613586162349 144634430787036605094810881)
      ·
        refine ⟨108475823090277453821108161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 144634430787036605094810881 108475823090277453821108161)
        ·
          refine ⟨81356867317708090365831121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 108475823090277453821108161 81356867317708090365831121)
          ·
            refine ⟨61017650488281067774373341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 81356867317708090365831121 61017650488281067774373341)
            ·
              refine ⟨22881618933105400415390003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 61017650488281067774373341 22881618933105400415390003)
              ·
                refine ⟨34322428399658100623085005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22881618933105400415390003 34322428399658100623085005)
                ·
                  refine ⟨12870910649871787733656877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34322428399658100623085005 12870910649871787733656877)
                  ·
                    refine ⟨4826591493701920400121329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12870910649871787733656877 4826591493701920400121329)
                    ·
                      refine ⟨3619943620276440300090997, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4826591493701920400121329 3619943620276440300090997)
                      ·
                        rfl

theorem cell23_7049815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 3, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 3, 1, 3, 3, 2].length) (baseStart_7049815 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7049815 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7049815 prefixEnd_7049815 := by exact prefixLift 7049815
  have htrace : WordTrace (prefixWord ++ tailWord_7049815) baseStart_7049815 baseEnd_7049815 := by
    simpa [prefixWord, tailWord_7049815, baseEnd_7049815] using wordTrace_append hprefix tailTrace_7049815
  have hstable : (prefixWord ++ tailWord_7049815).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7049815).length < 2 ^ (prefixWord ++ tailWord_7049815).sum := by decide
  have hdescent : baseEnd_7049815 < baseStart_7049815 := by decide
  rcases family_descends (prefixWord ++ tailWord_7049815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7049826 : List Nat := [3, 3, 2, 3, 1, 1, 3, 1, 1, 2, 3]
def baseStart_7049826 : Nat := 118140960795 + 7049826 * 2 ^ 59
def prefixEnd_7049826 : Nat := 4983230072969 + 3 ^ 40 * 7049826 * 2
def baseEnd_7049826 : Nat := 3619949268563639757053447

theorem tailTrace_7049826 : CollatzResearch.WordTrace tailWord_7049826 prefixEnd_7049826 3619949268563639757053447 := by
  unfold tailWord_7049826
  simp only [CollatzResearch.WordTrace]
  refine ⟨64282069539422972817356333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 171418852105127927512950221 64282069539422972817356333)
  ·
    refine ⟨24105776077283614806508625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 64282069539422972817356333 24105776077283614806508625)
    ·
      refine ⟨18079332057962711104881469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24105776077283614806508625 18079332057962711104881469)
      ·
        refine ⟨6779749521736016664330551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18079332057962711104881469 6779749521736016664330551)
        ·
          refine ⟨10169624282604024996495827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6779749521736016664330551 10169624282604024996495827)
          ·
            refine ⟨15254436423906037494743741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10169624282604024996495827 15254436423906037494743741)
            ·
              refine ⟨5720413658964764060528903, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15254436423906037494743741 5720413658964764060528903)
              ·
                refine ⟨8580620488447146090793355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5720413658964764060528903 8580620488447146090793355)
                ·
                  refine ⟨12870930732670719136190033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8580620488447146090793355 12870930732670719136190033)
                  ·
                    refine ⟨9653198049503039352142525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12870930732670719136190033 9653198049503039352142525)
                    ·
                      refine ⟨3619949268563639757053447, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9653198049503039352142525 3619949268563639757053447)
                      ·
                        rfl

theorem cell23_7049826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 1, 1, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 1, 1, 3, 1, 1, 2, 3].length) (baseStart_7049826 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7049826 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7049826 prefixEnd_7049826 := by exact prefixLift 7049826
  have htrace : WordTrace (prefixWord ++ tailWord_7049826) baseStart_7049826 baseEnd_7049826 := by
    simpa [prefixWord, tailWord_7049826, baseEnd_7049826] using wordTrace_append hprefix tailTrace_7049826
  have hstable : (prefixWord ++ tailWord_7049826).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7049826).length < 2 ^ (prefixWord ++ tailWord_7049826).sum := by decide
  have hdescent : baseEnd_7049826 < baseStart_7049826 := by decide
  rcases family_descends (prefixWord ++ tailWord_7049826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7049841 : List Nat := [1, 2, 2, 2, 1, 1, 1, 1, 1, 5, 6]
def baseStart_7049841 : Nat := 118140960795 + 7049841 * 2 ^ 59
def prefixEnd_7049841 : Nat := 4983230072969 + 3 ^ 40 * 7049841 * 2
def baseEnd_7049841 : Nat := 3619956970773457198365877

theorem tailTrace_7049841 : CollatzResearch.WordTrace tailWord_7049841 prefixEnd_7049841 3619956970773457198365877 := by
  unfold tailWord_7049841
  simp only [CollatzResearch.WordTrace]
  refine ⟨257128825252637548831221377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171419216835091699220814251 257128825252637548831221377)
  ·
    refine ⟨192846618939478161623416033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 257128825252637548831221377 192846618939478161623416033)
    ·
      refine ⟨144634964204608621217562025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 192846618939478161623416033 144634964204608621217562025)
      ·
        refine ⟨108476223153456465913171519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 144634964204608621217562025 108476223153456465913171519)
        ·
          refine ⟨162714334730184698869757279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 108476223153456465913171519 162714334730184698869757279)
          ·
            refine ⟨244071502095277048304635919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 162714334730184698869757279 244071502095277048304635919)
            ·
              refine ⟨366107253142915572456953879, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 244071502095277048304635919 366107253142915572456953879)
              ·
                refine ⟨549160879714373358685430819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 366107253142915572456953879 549160879714373358685430819)
                ·
                  refine ⟨823741319571560038028146229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 549160879714373358685430819 823741319571560038028146229)
                  ·
                    refine ⟨77225748709833753565138709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 823741319571560038028146229 77225748709833753565138709)
                    ·
                      refine ⟨3619956970773457198365877, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 77225748709833753565138709 3619956970773457198365877)
                      ·
                        rfl

theorem cell23_7049841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 1, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 1, 1, 1, 5, 6].length) (baseStart_7049841 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7049841 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7049841 prefixEnd_7049841 := by exact prefixLift 7049841
  have htrace : WordTrace (prefixWord ++ tailWord_7049841) baseStart_7049841 baseEnd_7049841 := by
    simpa [prefixWord, tailWord_7049841, baseEnd_7049841] using wordTrace_append hprefix tailTrace_7049841
  have hstable : (prefixWord ++ tailWord_7049841).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7049841).length < 2 ^ (prefixWord ++ tailWord_7049841).sum := by decide
  have hdescent : baseEnd_7049841 < baseStart_7049841 := by decide
  rcases family_descends (prefixWord ++ tailWord_7049841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7049871 : List Nat := [1, 1, 2, 1, 1, 1, 1, 4, 2, 1, 8]
def baseStart_7049871 : Nat := 118140960795 + 7049871 * 2 ^ 59
def prefixEnd_7049871 : Nat := 4983230072969 + 3 ^ 40 * 7049871 * 2
def baseEnd_7049871 : Nat := 3619972375193092080990739

theorem tailTrace_7049871 : CollatzResearch.WordTrace tailWord_7049871 prefixEnd_7049871 3619972375193092080990739 := by
  unfold tailWord_7049871
  simp only [CollatzResearch.WordTrace]
  refine ⟨257129919442528863954813467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171419946295019242636542311 257129919442528863954813467)
  ·
    refine ⟨385694879163793295932220201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 257129919442528863954813467 385694879163793295932220201)
    ·
      refine ⟨289271159372844971949165151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 385694879163793295932220201 289271159372844971949165151)
      ·
        refine ⟨433906739059267457923747727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 289271159372844971949165151 433906739059267457923747727)
        ·
          refine ⟨650860108588901186885621591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 433906739059267457923747727 650860108588901186885621591)
          ·
            refine ⟨976290162883351780328432387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 650860108588901186885621591 976290162883351780328432387)
            ·
              refine ⟨1464435244325027670492648581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 976290162883351780328432387 1464435244325027670492648581)
              ·
                refine ⟨274581608310942688217371609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1464435244325027670492648581 274581608310942688217371609)
                ·
                  refine ⟨205936206233207016163028707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 274581608310942688217371609 205936206233207016163028707)
                  ·
                    refine ⟨308904309349810524244543061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 205936206233207016163028707 308904309349810524244543061)
                    ·
                      refine ⟨3619972375193092080990739, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 308904309349810524244543061 3619972375193092080990739)
                      ·
                        rfl

theorem cell23_7049871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 4, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 4, 2, 1, 8].length) (baseStart_7049871 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7049871 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7049871 prefixEnd_7049871 := by exact prefixLift 7049871
  have htrace : WordTrace (prefixWord ++ tailWord_7049871) baseStart_7049871 baseEnd_7049871 := by
    simpa [prefixWord, tailWord_7049871, baseEnd_7049871] using wordTrace_append hprefix tailTrace_7049871
  have hstable : (prefixWord ++ tailWord_7049871).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7049871).length < 2 ^ (prefixWord ++ tailWord_7049871).sum := by decide
  have hdescent : baseEnd_7049871 < baseStart_7049871 := by decide
  rcases family_descends (prefixWord ++ tailWord_7049871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7049885 : List Nat := [1, 4, 2, 1, 1, 1, 3, 5, 5]
def baseStart_7049885 : Nat := 118140960795 + 7049885 * 2 ^ 59
def prefixEnd_7049885 : Nat := 4983230072969 + 3 ^ 40 * 7049885 * 2
def baseEnd_7049885 : Nat := 402219951546917225135075

theorem tailTrace_7049885 : CollatzResearch.WordTrace tailWord_7049885 prefixEnd_7049885 402219951546917225135075 := by
  unfold tailWord_7049885
  simp only [CollatzResearch.WordTrace]
  refine ⟨257130430064478144345823109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171420286709652096230548739 257130430064478144345823109)
  ·
    refine ⟨48211955637089652064841833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 257130430064478144345823109 48211955637089652064841833)
    ·
      refine ⟨36158966727817239048631375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48211955637089652064841833 36158966727817239048631375)
      ·
        refine ⟨54238450091725858572947063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36158966727817239048631375 54238450091725858572947063)
        ·
          refine ⟨81357675137588787859420595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54238450091725858572947063 81357675137588787859420595)
          ·
            refine ⟨122036512706383181789130893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81357675137588787859420595 122036512706383181789130893)
            ·
              refine ⟨45763692264893693170924085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 122036512706383181789130893 45763692264893693170924085)
              ·
                refine ⟨4290346149833783734774133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 45763692264893693170924085 4290346149833783734774133)
                ·
                  refine ⟨402219951546917225135075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4290346149833783734774133 402219951546917225135075)
                  ·
                    rfl

theorem cell23_7049885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 3, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 3, 5, 5].length) (baseStart_7049885 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7049885 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7049885 prefixEnd_7049885 := by exact prefixLift 7049885
  have htrace : WordTrace (prefixWord ++ tailWord_7049885) baseStart_7049885 baseEnd_7049885 := by
    simpa [prefixWord, tailWord_7049885, baseEnd_7049885] using wordTrace_append hprefix tailTrace_7049885
  have hstable : (prefixWord ++ tailWord_7049885).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7049885).length < 2 ^ (prefixWord ++ tailWord_7049885).sum := by decide
  have hdescent : baseEnd_7049885 < baseStart_7049885 := by decide
  rcases family_descends (prefixWord ++ tailWord_7049885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7049902 : List Nat := [4, 1, 4, 1, 1, 2, 2, 1, 7]
def baseStart_7049902 : Nat := 118140960795 + 7049902 * 2 ^ 59
def prefixEnd_7049902 : Nat := 4983230072969 + 3 ^ 40 * 7049902 * 2
def baseEnd_7049902 : Nat := 402220921454820162189233

theorem tailTrace_7049902 : CollatzResearch.WordTrace tailWord_7049902 prefixEnd_7049902 402220921454820162189233 := by
  unfold tailWord_7049902
  simp only [CollatzResearch.WordTrace]
  refine ⟨32141381263177069531148995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 171420700070277704166127973 32141381263177069531148995)
  ·
    refine ⟨48212071894765604296723493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32141381263177069531148995 48212071894765604296723493)
    ·
      refine ⟨9039763480268550805635655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 48212071894765604296723493 9039763480268550805635655)
      ·
        refine ⟨13559645220402826208453483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9039763480268550805635655 13559645220402826208453483)
        ·
          refine ⟨20339467830604239312680225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13559645220402826208453483 20339467830604239312680225)
          ·
            refine ⟨15254600872953179484510169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20339467830604239312680225 15254600872953179484510169)
            ·
              refine ⟨11440950654714884613382627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15254600872953179484510169 11440950654714884613382627)
              ·
                refine ⟨17161425982072326920073941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11440950654714884613382627 17161425982072326920073941)
                ·
                  refine ⟨402220921454820162189233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17161425982072326920073941 402220921454820162189233)
                  ·
                    rfl

theorem cell23_7049902_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 2, 2, 1, 7].length) (baseStart_7049902 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7049902 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7049902 prefixEnd_7049902 := by exact prefixLift 7049902
  have htrace : WordTrace (prefixWord ++ tailWord_7049902) baseStart_7049902 baseEnd_7049902 := by
    simpa [prefixWord, tailWord_7049902, baseEnd_7049902] using wordTrace_append hprefix tailTrace_7049902
  have hstable : (prefixWord ++ tailWord_7049902).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7049902).length < 2 ^ (prefixWord ++ tailWord_7049902).sum := by decide
  have hdescent : baseEnd_7049902 < baseStart_7049902 := by decide
  rcases family_descends (prefixWord ++ tailWord_7049902) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7049978 : List Nat := [3, 1, 1, 1, 1, 3, 2, 2, 1, 2, 6]
def baseStart_7049978 : Nat := 118140960795 + 7049978 * 2 ^ 59
def prefixEnd_7049978 : Nat := 4983230072969 + 3 ^ 40 * 7049978 * 2
def baseEnd_7049978 : Nat := 3620027317623123162352747

theorem tailTrace_7049978 : CollatzResearch.WordTrace tailWord_7049978 prefixEnd_7049978 3620027317623123162352747 := by
  unfold tailWord_7049978
  simp only [CollatzResearch.WordTrace]
  refine ⟨64283455513285305307239647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 171422548035427480819305725 64283455513285305307239647)
  ·
    refine ⟨96425183269927957960859471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64283455513285305307239647 96425183269927957960859471)
    ·
      refine ⟨144637774904891936941289207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96425183269927957960859471 144637774904891936941289207)
      ·
        refine ⟨216956662357337905411933811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 144637774904891936941289207 216956662357337905411933811)
        ·
          refine ⟨325434993536006858117900717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 216956662357337905411933811 325434993536006858117900717)
          ·
            refine ⟨122038122576002571794212769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 325434993536006858117900717 122038122576002571794212769)
            ·
              refine ⟨91528591932001928845659577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 122038122576002571794212769 91528591932001928845659577)
              ·
                refine ⟨68646443949001446634244683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 91528591932001928845659577 68646443949001446634244683)
                ·
                  refine ⟨102969665923502169951367025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 68646443949001446634244683 102969665923502169951367025)
                  ·
                    refine ⟨77227249442626627463525269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 102969665923502169951367025 77227249442626627463525269)
                    ·
                      refine ⟨3620027317623123162352747, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 77227249442626627463525269 3620027317623123162352747)
                      ·
                        rfl

theorem cell23_7049978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 2, 2, 1, 2, 6].length) (baseStart_7049978 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7049978 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7049978 prefixEnd_7049978 := by exact prefixLift 7049978
  have htrace : WordTrace (prefixWord ++ tailWord_7049978) baseStart_7049978 baseEnd_7049978 := by
    simpa [prefixWord, tailWord_7049978, baseEnd_7049978] using wordTrace_append hprefix tailTrace_7049978
  have hstable : (prefixWord ++ tailWord_7049978).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7049978).length < 2 ^ (prefixWord ++ tailWord_7049978).sum := by decide
  have hdescent : baseEnd_7049978 < baseStart_7049978 := by decide
  rcases family_descends (prefixWord ++ tailWord_7049978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7050035 : List Nat := [1, 1, 1, 2, 6, 1, 1, 3, 1, 6]
def baseStart_7050035 : Nat := 118140960795 + 7050035 * 2 ^ 59
def prefixEnd_7050035 : Nat := 4983230072969 + 3 ^ 40 * 7050035 * 2
def baseEnd_7050035 : Nat := 1206685528673476479779995

theorem tailTrace_7050035 : CollatzResearch.WordTrace tailWord_7050035 prefixEnd_7050035 1206685528673476479779995 := by
  unfold tailWord_7050035
  simp only [CollatzResearch.WordTrace]
  refine ⟨257135901013934719963783559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171423934009289813309189039 257135901013934719963783559)
  ·
    refine ⟨385703851520902079945675339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 257135901013934719963783559 385703851520902079945675339)
    ·
      refine ⟨578555777281353119918513009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 385703851520902079945675339 578555777281353119918513009)
      ·
        refine ⟨433916832961014839938884757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 578555777281353119918513009 433916832961014839938884757)
        ·
          refine ⟨20339851545047570622135223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 433916832961014839938884757 20339851545047570622135223)
          ·
            refine ⟨30509777317571355933202835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20339851545047570622135223 30509777317571355933202835)
            ·
              refine ⟨45764665976357033899804253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30509777317571355933202835 45764665976357033899804253)
              ·
                refine ⟨17161749741133887712426595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 45764665976357033899804253 17161749741133887712426595)
                ·
                  refine ⟨25742624611700831568639893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17161749741133887712426595 25742624611700831568639893)
                  ·
                    refine ⟨1206685528673476479779995, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25742624611700831568639893 1206685528673476479779995)
                    ·
                      rfl

theorem cell23_7050035_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 1, 1, 3, 1, 6].length) (baseStart_7050035 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7050035 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7050035 prefixEnd_7050035 := by exact prefixLift 7050035
  have htrace : WordTrace (prefixWord ++ tailWord_7050035) baseStart_7050035 baseEnd_7050035 := by
    simpa [prefixWord, tailWord_7050035, baseEnd_7050035] using wordTrace_append hprefix tailTrace_7050035
  have hstable : (prefixWord ++ tailWord_7050035).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7050035).length < 2 ^ (prefixWord ++ tailWord_7050035).sum := by decide
  have hdescent : baseEnd_7050035 < baseStart_7050035 := by decide
  rcases family_descends (prefixWord ++ tailWord_7050035) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7050036 : List Nat := [2, 5, 1, 1, 3, 1, 1, 2, 3, 1, 3]
def baseStart_7050036 : Nat := 118140960795 + 7050036 * 2 ^ 59
def prefixEnd_7050036 : Nat := 4983230072969 + 3 ^ 40 * 7050036 * 2
def baseEnd_7050036 : Nat := 3620057099501083935427481

theorem tailTrace_7050036 : CollatzResearch.WordTrace tailWord_7050036 prefixEnd_7050036 3620057099501083935427481 := by
  unfold tailWord_7050036
  simp only [CollatzResearch.WordTrace]
  refine ⟨128567968743465548567284981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 171423958324620731423046641 128567968743465548567284981)
  ·
    refine ⟨12053247069699895178182967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 128567968743465548567284981 12053247069699895178182967)
    ·
      refine ⟨18079870604549842767274451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12053247069699895178182967 18079870604549842767274451)
      ·
        refine ⟨27119805906824764150911677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18079870604549842767274451 27119805906824764150911677)
        ·
          refine ⟨10169927215059286556591879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27119805906824764150911677 10169927215059286556591879)
          ·
            refine ⟨15254890822588929834887819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10169927215059286556591879 15254890822588929834887819)
            ·
              refine ⟨22882336233883394752331729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15254890822588929834887819 22882336233883394752331729)
              ·
                refine ⟨17161752175412546064248797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22882336233883394752331729 17161752175412546064248797)
                ·
                  refine ⟨6435657065779704774093299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17161752175412546064248797 6435657065779704774093299)
                  ·
                    refine ⟨9653485598669557161139949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6435657065779704774093299 9653485598669557161139949)
                    ·
                      refine ⟨3620057099501083935427481, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9653485598669557161139949 3620057099501083935427481)
                      ·
                        rfl

theorem cell23_7050036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 3, 1, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 3, 1, 1, 2, 3, 1, 3].length) (baseStart_7050036 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7050036 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7050036 prefixEnd_7050036 := by exact prefixLift 7050036
  have htrace : WordTrace (prefixWord ++ tailWord_7050036) baseStart_7050036 baseEnd_7050036 := by
    simpa [prefixWord, tailWord_7050036, baseEnd_7050036] using wordTrace_append hprefix tailTrace_7050036
  have hstable : (prefixWord ++ tailWord_7050036).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7050036).length < 2 ^ (prefixWord ++ tailWord_7050036).sum := by decide
  have hdescent : baseEnd_7050036 < baseStart_7050036 := by decide
  rcases family_descends (prefixWord ++ tailWord_7050036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7050048 : List Nat := [2, 1, 1, 2, 2, 1, 1, 13]
def baseStart_7050048 : Nat := 118140960795 + 7050048 * 2 ^ 59
def prefixEnd_7050048 : Nat := 4983230072969 + 3 ^ 40 * 7050048 * 2
def baseEnd_7050048 : Nat := 134076417084034736610275

theorem tailTrace_7050048 : CollatzResearch.WordTrace tailWord_7050048 prefixEnd_7050048 134076417084034736610275 := by
  unfold tailWord_7050048
  simp only [CollatzResearch.WordTrace]
  refine ⟨128568187581443811592003399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 171424250108591748789337865 128568187581443811592003399)
  ·
    refine ⟨192852281372165717388005099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128568187581443811592003399 192852281372165717388005099)
    ·
      refine ⟨289278422058248576082007649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 192852281372165717388005099 289278422058248576082007649)
      ·
        refine ⟨216958816543686432061505737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 289278422058248576082007649 216958816543686432061505737)
        ·
          refine ⟨162719112407764824046129303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 216958816543686432061505737 162719112407764824046129303)
          ·
            refine ⟨244078668611647236069193955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 162719112407764824046129303 244078668611647236069193955)
            ·
              refine ⟨366118002917470854103790933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 244078668611647236069193955 366118002917470854103790933)
              ·
                refine ⟨134076417084034736610275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 13 366118002917470854103790933 134076417084034736610275)
                ·
                  rfl

theorem cell23_7050048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 1, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 1, 13].length) (baseStart_7050048 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7050048 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7050048 prefixEnd_7050048 := by exact prefixLift 7050048
  have htrace : WordTrace (prefixWord ++ tailWord_7050048) baseStart_7050048 baseEnd_7050048 := by
    simpa [prefixWord, tailWord_7050048, baseEnd_7050048] using wordTrace_append hprefix tailTrace_7050048
  have hstable : (prefixWord ++ tailWord_7050048).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7050048).length < 2 ^ (prefixWord ++ tailWord_7050048).sum := by decide
  have hdescent : baseEnd_7050048 < baseStart_7050048 := by decide
  rcases family_descends (prefixWord ++ tailWord_7050048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7050065 : List Nat := [1, 2, 2, 1, 6, 1, 10]
def baseStart_7050065 : Nat := 118140960795 + 7050065 * 2 ^ 59
def prefixEnd_7050065 : Nat := 4983230072969 + 3 ^ 40 * 7050065 * 2
def baseEnd_7050065 : Nat := 44692246795556349653887

theorem tailTrace_7050065 : CollatzResearch.WordTrace tailWord_7050065 prefixEnd_7050065 44692246795556349653887 := by
  unfold tailWord_7050065
  simp only [CollatzResearch.WordTrace]
  refine ⟨257136995203826035087375649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171424663469217356724917099 257136995203826035087375649)
  ·
    refine ⟨192852746402869526315531737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 257136995203826035087375649 192852746402869526315531737)
    ·
      refine ⟨144639559802152144736648803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 192852746402869526315531737 144639559802152144736648803)
      ·
        refine ⟨216959339703228217104973205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 144639559802152144736648803 216959339703228217104973205)
        ·
          refine ⟨10169969048588822676795619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 216959339703228217104973205 10169969048588822676795619)
          ·
            refine ⟨15254953572883234015193429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10169969048588822676795619 15254953572883234015193429)
            ·
              refine ⟨44692246795556349653887, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 15254953572883234015193429 44692246795556349653887)
              ·
                rfl

theorem cell23_7050065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 6, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 6, 1, 10].length) (baseStart_7050065 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7050065 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7050065 prefixEnd_7050065 := by exact prefixLift 7050065
  have htrace : WordTrace (prefixWord ++ tailWord_7050065) baseStart_7050065 baseEnd_7050065 := by
    simpa [prefixWord, tailWord_7050065, baseEnd_7050065] using wordTrace_append hprefix tailTrace_7050065
  have hstable : (prefixWord ++ tailWord_7050065).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7050065).length < 2 ^ (prefixWord ++ tailWord_7050065).sum := by decide
  have hdescent : baseEnd_7050065 < baseStart_7050065 := by decide
  rcases family_descends (prefixWord ++ tailWord_7050065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7050076 : List Nat := [2, 2, 4, 2, 1, 1, 1, 3, 3, 2, 2]
def baseStart_7050076 : Nat := 118140960795 + 7050076 * 2 ^ 59
def prefixEnd_7050076 : Nat := 4983230072969 + 3 ^ 40 * 7050076 * 2
def baseEnd_7050076 : Nat := 3620077638727263778927297

theorem tailTrace_7050076 : CollatzResearch.WordTrace tailWord_7050076 prefixEnd_7050076 3620077638727263778927297 := by
  unfold tailWord_7050076
  simp only [CollatzResearch.WordTrace]
  refine ⟨128568698203393091983013041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 171424930937857455977350721 128568698203393091983013041)
  ·
    refine ⟨96426523652544818987259781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 128568698203393091983013041 96426523652544818987259781)
    ·
      refine ⟨18079973184852153560111209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 96426523652544818987259781 18079973184852153560111209)
      ·
        refine ⟨13559979888639115170083407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18079973184852153560111209 13559979888639115170083407)
        ·
          refine ⟨20339969832958672755125111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13559979888639115170083407 20339969832958672755125111)
          ·
            refine ⟨30509954749438009132687667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20339969832958672755125111 30509954749438009132687667)
            ·
              refine ⟨45764932124157013699031501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30509954749438009132687667 45764932124157013699031501)
              ·
                refine ⟨17161849546558880137136813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 45764932124157013699031501 17161849546558880137136813)
                ·
                  refine ⟨6435693579959580051426305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17161849546558880137136813 6435693579959580051426305)
                  ·
                    refine ⟨4826770184969685038569729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6435693579959580051426305 4826770184969685038569729)
                    ·
                      refine ⟨3620077638727263778927297, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4826770184969685038569729 3620077638727263778927297)
                      ·
                        rfl

theorem cell23_7050076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 1, 1, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 1, 1, 3, 3, 2, 2].length) (baseStart_7050076 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7050076 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7050076 prefixEnd_7050076 := by exact prefixLift 7050076
  have htrace : WordTrace (prefixWord ++ tailWord_7050076) baseStart_7050076 baseEnd_7050076 := by
    simpa [prefixWord, tailWord_7050076, baseEnd_7050076] using wordTrace_append hprefix tailTrace_7050076
  have hstable : (prefixWord ++ tailWord_7050076).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7050076).length < 2 ^ (prefixWord ++ tailWord_7050076).sum := by decide
  have hdescent : baseEnd_7050076 < baseStart_7050076 := by decide
  rcases family_descends (prefixWord ++ tailWord_7050076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7050105 : List Nat := [1, 2, 1, 3, 2, 3, 1, 1, 2, 2, 5]
def baseStart_7050105 : Nat := 118140960795 + 7050105 * 2 ^ 59
def prefixEnd_7050105 : Nat := 4983230072969 + 3 ^ 40 * 7050105 * 2
def baseEnd_7050105 : Nat := 3620092529666244165464663

theorem tailTrace_7050105 : CollatzResearch.WordTrace tailWord_7050105 prefixEnd_7050105 3620092529666244165464663 := by
  unfold tailWord_7050105
  simp only [CollatzResearch.WordTrace]
  refine ⟨257138454123681121918831769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171425636082454081279221179 257138454123681121918831769)
  ·
    refine ⟨192853840592760841439123827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 257138454123681121918831769 192853840592760841439123827)
    ·
      refine ⟨289280760889141262158685741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 192853840592760841439123827 289280760889141262158685741)
      ·
        refine ⟨108480285333427973309507153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 289280760889141262158685741 108480285333427973309507153)
        ·
          refine ⟨81360214000070979982130365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 108480285333427973309507153 81360214000070979982130365)
          ·
            refine ⟨30510080250026617493298887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 81360214000070979982130365 30510080250026617493298887)
            ·
              refine ⟨45765120375039926239948331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30510080250026617493298887 45765120375039926239948331)
              ·
                refine ⟨68647680562559889359922497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45765120375039926239948331 68647680562559889359922497)
                ·
                  refine ⟨51485760421919917019941873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 68647680562559889359922497 51485760421919917019941873)
                  ·
                    refine ⟨38614320316439937764956405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 51485760421919917019941873 38614320316439937764956405)
                    ·
                      refine ⟨3620092529666244165464663, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 38614320316439937764956405 3620092529666244165464663)
                      ·
                        rfl

theorem cell23_7050105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 3, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 3, 1, 1, 2, 2, 5].length) (baseStart_7050105 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7050105 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7050105 prefixEnd_7050105 := by exact prefixLift 7050105
  have htrace : WordTrace (prefixWord ++ tailWord_7050105) baseStart_7050105 baseEnd_7050105 := by
    simpa [prefixWord, tailWord_7050105, baseEnd_7050105] using wordTrace_append hprefix tailTrace_7050105
  have hstable : (prefixWord ++ tailWord_7050105).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7050105).length < 2 ^ (prefixWord ++ tailWord_7050105).sum := by decide
  have hdescent : baseEnd_7050105 < baseStart_7050105 := by decide
  rcases family_descends (prefixWord ++ tailWord_7050105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7050132 : List Nat := [2, 4, 2, 1, 1, 1, 2, 1, 2, 3, 4]
def baseStart_7050132 : Nat := 118140960795 + 7050132 * 2 ^ 59
def prefixEnd_7050132 : Nat := 4983230072969 + 3 ^ 40 * 7050132 * 2
def baseEnd_7050132 : Nat := 3620106393643915559827039

theorem tailTrace_7050132 : CollatzResearch.WordTrace tailWord_7050132 prefixEnd_7050132 3620106393643915559827039 := by
  unfold tailWord_7050132
  simp only [CollatzResearch.WordTrace]
  refine ⟨128569719447291652765032325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 171426292596388870353376433 128569719447291652765032325)
  ·
    refine ⟨24106822396367184893443561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 128569719447291652765032325 24106822396367184893443561)
    ·
      refine ⟨18080116797275388670082671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24106822396367184893443561 18080116797275388670082671)
      ·
        refine ⟨27120175195913083005124007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18080116797275388670082671 27120175195913083005124007)
        ·
          refine ⟨40680262793869624507686011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27120175195913083005124007 40680262793869624507686011)
          ·
            refine ⟨61020394190804436761529017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40680262793869624507686011 61020394190804436761529017)
            ·
              refine ⟨45765295643103327571146763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 61020394190804436761529017 45765295643103327571146763)
              ·
                refine ⟨68647943464654991356720145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45765295643103327571146763 68647943464654991356720145)
                ·
                  refine ⟨51485957598491243517540109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 68647943464654991356720145 51485957598491243517540109)
                  ·
                    refine ⟨19307234099434216319077541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 51485957598491243517540109 19307234099434216319077541)
                    ·
                      refine ⟨3620106393643915559827039, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19307234099434216319077541 3620106393643915559827039)
                      ·
                        rfl

theorem cell23_7050132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 2, 1, 2, 3, 4].length) (baseStart_7050132 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7050132 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7050132 prefixEnd_7050132 := by exact prefixLift 7050132
  have htrace : WordTrace (prefixWord ++ tailWord_7050132) baseStart_7050132 baseEnd_7050132 := by
    simpa [prefixWord, tailWord_7050132, baseEnd_7050132] using wordTrace_append hprefix tailTrace_7050132
  have hstable : (prefixWord ++ tailWord_7050132).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7050132).length < 2 ^ (prefixWord ++ tailWord_7050132).sum := by decide
  have hdescent : baseEnd_7050132 < baseStart_7050132 := by decide
  rcases family_descends (prefixWord ++ tailWord_7050132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7050135 : List Nat := [1, 1, 3, 3, 1, 2, 1, 2, 1, 3, 5]
def baseStart_7050135 : Nat := 118140960795 + 7050135 * 2 ^ 59
def prefixEnd_7050135 : Nat := 4983230072969 + 3 ^ 40 * 7050135 * 2
def baseEnd_7050135 : Nat := 3620107934085879048089525

theorem tailTrace_7050135 : CollatzResearch.WordTrace tailWord_7050135 prefixEnd_7050135 3620107934085879048089525 := by
  unfold tailWord_7050135
  simp only [CollatzResearch.WordTrace]
  refine ⟨257139548313572437042423859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171426365542381624694949239 257139548313572437042423859)
  ·
    refine ⟨385709322470358655563635789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 257139548313572437042423859 385709322470358655563635789)
    ·
      refine ⟨144640995926384495836363421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 385709322470358655563635789 144640995926384495836363421)
      ·
        refine ⟨54240373472394185938636283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 144640995926384495836363421 54240373472394185938636283)
        ·
          refine ⟨81360560208591278907954425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54240373472394185938636283 81360560208591278907954425)
          ·
            refine ⟨61020420156443459180965819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 81360560208591278907954425 61020420156443459180965819)
            ·
              refine ⟨91530630234665188771448729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61020420156443459180965819 91530630234665188771448729)
              ·
                refine ⟨68647972675998891578586547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 91530630234665188771448729 68647972675998891578586547)
                ·
                  refine ⟨102971959013998337367879821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 68647972675998891578586547 102971959013998337367879821)
                  ·
                    refine ⟨38614484630249376512954933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 102971959013998337367879821 38614484630249376512954933)
                    ·
                      refine ⟨3620107934085879048089525, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 38614484630249376512954933 3620107934085879048089525)
                      ·
                        rfl

theorem cell23_7050135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 1, 2, 1, 3, 5].length) (baseStart_7050135 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7050135 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7050135 prefixEnd_7050135 := by exact prefixLift 7050135
  have htrace : WordTrace (prefixWord ++ tailWord_7050135) baseStart_7050135 baseEnd_7050135 := by
    simpa [prefixWord, tailWord_7050135, baseEnd_7050135] using wordTrace_append hprefix tailTrace_7050135
  have hstable : (prefixWord ++ tailWord_7050135).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7050135).length < 2 ^ (prefixWord ++ tailWord_7050135).sum := by decide
  have hdescent : baseEnd_7050135 < baseStart_7050135 := by decide
  rcases family_descends (prefixWord ++ tailWord_7050135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7050143 : List Nat := [1, 1, 2, 5, 2, 3, 2, 1, 2, 1, 3]
def baseStart_7050143 : Nat := 118140960795 + 7050143 * 2 ^ 59
def prefixEnd_7050143 : Nat := 4983230072969 + 3 ^ 40 * 7050143 * 2
def baseEnd_7050143 : Nat := 3620112041931115016789489

theorem tailTrace_7050143 : CollatzResearch.WordTrace tailWord_7050143 prefixEnd_7050143 3620112041931115016789489 := by
  unfold tailWord_7050143
  simp only [CollatzResearch.WordTrace]
  refine ⟨257139840097543454408715083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171426560065028969605810055 257139840097543454408715083)
  ·
    refine ⟨385709760146315181613072625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 257139840097543454408715083 385709760146315181613072625)
    ·
      refine ⟨289282320109736386209804469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 385709760146315181613072625 289282320109736386209804469)
      ·
        refine ⟨27120217510287786207169169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 289282320109736386209804469 27120217510287786207169169)
        ·
          refine ⟨20340163132715839655376877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27120217510287786207169169 20340163132715839655376877)
          ·
            refine ⟨7627561174768439870766329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20340163132715839655376877 7627561174768439870766329)
            ·
              refine ⟨5720670881076329903074747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7627561174768439870766329 5720670881076329903074747)
              ·
                refine ⟨8581006321614494854612121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5720670881076329903074747 8581006321614494854612121)
                ·
                  refine ⟨6435754741210871140959091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8581006321614494854612121 6435754741210871140959091)
                  ·
                    refine ⟨9653632111816306711438637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6435754741210871140959091 9653632111816306711438637)
                    ·
                      refine ⟨3620112041931115016789489, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9653632111816306711438637 3620112041931115016789489)
                      ·
                        rfl

theorem cell23_7050143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 3, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 3, 2, 1, 2, 1, 3].length) (baseStart_7050143 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7050143 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7050143 prefixEnd_7050143 := by exact prefixLift 7050143
  have htrace : WordTrace (prefixWord ++ tailWord_7050143) baseStart_7050143 baseEnd_7050143 := by
    simpa [prefixWord, tailWord_7050143, baseEnd_7050143] using wordTrace_append hprefix tailTrace_7050143
  have hstable : (prefixWord ++ tailWord_7050143).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7050143).length < 2 ^ (prefixWord ++ tailWord_7050143).sum := by decide
  have hdescent : baseEnd_7050143 < baseStart_7050143 := by decide
  rcases family_descends (prefixWord ++ tailWord_7050143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7050232 : List Nat := [2, 1, 2, 1, 1, 3, 1, 1, 7, 4]
def baseStart_7050232 : Nat := 118140960795 + 7050232 * 2 ^ 59
def prefixEnd_7050232 : Nat := 4983230072969 + 3 ^ 40 * 7050232 * 2
def baseEnd_7050232 : Nat := 1206719247236455056192193

theorem tailTrace_7050232 : CollatzResearch.WordTrace tailWord_7050232 prefixEnd_7050232 1206719247236455056192193 := by
  unfold tailWord_7050232
  simp only [CollatzResearch.WordTrace]
  refine ⟨128571543097110511304352475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 171428724129480681739136633 128571543097110511304352475)
  ·
    refine ⟨192857314645665766956528713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128571543097110511304352475 192857314645665766956528713)
    ·
      refine ⟨144642985984249325217396535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 192857314645665766956528713 144642985984249325217396535)
      ·
        refine ⟨216964478976373987826094803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 144642985984249325217396535 216964478976373987826094803)
        ·
          refine ⟨325446718464560981739142205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 216964478976373987826094803 325446718464560981739142205)
          ·
            refine ⟨122042519424210368152178327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 325446718464560981739142205 122042519424210368152178327)
            ·
              refine ⟨183063779136315552228267491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 122042519424210368152178327 183063779136315552228267491)
              ·
                refine ⟨274595668704473328342401237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 183063779136315552228267491 274595668704473328342401237)
                ·
                  refine ⟨6435835985261093633025029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 274595668704473328342401237 6435835985261093633025029)
                  ·
                    refine ⟨1206719247236455056192193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6435835985261093633025029 1206719247236455056192193)
                    ·
                      rfl

theorem cell23_7050232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 1, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 1, 1, 7, 4].length) (baseStart_7050232 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7050232 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7050232 prefixEnd_7050232 := by exact prefixLift 7050232
  have htrace : WordTrace (prefixWord ++ tailWord_7050232) baseStart_7050232 baseEnd_7050232 := by
    simpa [prefixWord, tailWord_7050232, baseEnd_7050232] using wordTrace_append hprefix tailTrace_7050232
  have hstable : (prefixWord ++ tailWord_7050232).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7050232).length < 2 ^ (prefixWord ++ tailWord_7050232).sum := by decide
  have hdescent : baseEnd_7050232 < baseStart_7050232 := by decide
  rcases family_descends (prefixWord ++ tailWord_7050232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7050279 : List Nat := [1, 1, 7, 1, 1, 1, 1, 2, 8]
def baseStart_7050279 : Nat := 118140960795 + 7050279 * 2 ^ 59
def prefixEnd_7050279 : Nat := 4983230072969 + 3 ^ 40 * 7050279 * 2
def baseEnd_7050279 : Nat := 402242430588902942743207

theorem tailTrace_7050279 : CollatzResearch.WordTrace tailWord_7050279 prefixEnd_7050279 402242430588902942743207 := by
  unfold tailWord_7050279
  simp only [CollatzResearch.WordTrace]
  refine ⟨257144800425050749635665891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171429866950033833090443927 257144800425050749635665891)
  ·
    refine ⟨385717200637576124453498837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 257144800425050749635665891 385717200637576124453498837)
    ·
      refine ⟨9040246889943190416878879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 385717200637576124453498837 9040246889943190416878879)
      ·
        refine ⟨13560370334914785625318319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9040246889943190416878879 13560370334914785625318319)
        ·
          refine ⟨20340555502372178437977479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13560370334914785625318319 20340555502372178437977479)
          ·
            refine ⟨30510833253558267656966219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20340555502372178437977479 30510833253558267656966219)
            ·
              refine ⟨45766249880337401485449329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30510833253558267656966219 45766249880337401485449329)
              ·
                refine ⟨34324687410253051114086997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45766249880337401485449329 34324687410253051114086997)
                ·
                  refine ⟨402242430588902942743207, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 34324687410253051114086997 402242430588902942743207)
                  ·
                    rfl

theorem cell23_7050279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 1, 1, 2, 8].length) (baseStart_7050279 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7050279 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7050279 prefixEnd_7050279 := by exact prefixLift 7050279
  have htrace : WordTrace (prefixWord ++ tailWord_7050279) baseStart_7050279 baseEnd_7050279 := by
    simpa [prefixWord, tailWord_7050279, baseEnd_7050279] using wordTrace_append hprefix tailTrace_7050279
  have hstable : (prefixWord ++ tailWord_7050279).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7050279).length < 2 ^ (prefixWord ++ tailWord_7050279).sum := by decide
  have hdescent : baseEnd_7050279 < baseStart_7050279 := by decide
  rcases family_descends (prefixWord ++ tailWord_7050279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7050329 : List Nat := [1, 2, 1, 2, 2, 1, 2, 6, 1, 1, 4]
def baseStart_7050329 : Nat := 118140960795 + 7050329 * 2 ^ 59
def prefixEnd_7050329 : Nat := 4983230072969 + 3 ^ 40 * 7050329 * 2
def baseEnd_7050329 : Nat := 3620207549332851289063633

theorem tailTrace_7050329 : CollatzResearch.WordTrace tailWord_7050329 prefixEnd_7050329 3620207549332851289063633 := by
  unfold tailWord_7050329
  simp only [CollatzResearch.WordTrace]
  refine ⟨257146624074869608174986041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171431082716579738783324027 257146624074869608174986041)
  ·
    refine ⟨192859968056152206131239531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 257146624074869608174986041 192859968056152206131239531)
    ·
      refine ⟨289289952084228309196859297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 192859968056152206131239531 289289952084228309196859297)
      ·
        refine ⟨216967464063171231897644473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 289289952084228309196859297 216967464063171231897644473)
        ·
          refine ⟨162725598047378423923233355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 216967464063171231897644473 162725598047378423923233355)
          ·
            refine ⟨244088397071067635884850033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 162725598047378423923233355 244088397071067635884850033)
            ·
              refine ⟨183066297803300726913637525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 244088397071067635884850033 183066297803300726913637525)
              ·
                refine ⟨8581232709529721574076759, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 183066297803300726913637525 8581232709529721574076759)
                ·
                  refine ⟨12871849064294582361115139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8581232709529721574076759 12871849064294582361115139)
                  ·
                    refine ⟨19307773596441873541672709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12871849064294582361115139 19307773596441873541672709)
                    ·
                      refine ⟨3620207549332851289063633, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19307773596441873541672709 3620207549332851289063633)
                      ·
                        rfl

theorem cell23_7050329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 2, 6, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 2, 6, 1, 1, 4].length) (baseStart_7050329 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7050329 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7050329 prefixEnd_7050329 := by exact prefixLift 7050329
  have htrace : WordTrace (prefixWord ++ tailWord_7050329) baseStart_7050329 baseEnd_7050329 := by
    simpa [prefixWord, tailWord_7050329, baseEnd_7050329] using wordTrace_append hprefix tailTrace_7050329
  have hstable : (prefixWord ++ tailWord_7050329).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7050329).length < 2 ^ (prefixWord ++ tailWord_7050329).sum := by decide
  have hdescent : baseEnd_7050329 < baseStart_7050329 := by decide
  rcases family_descends (prefixWord ++ tailWord_7050329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7050357 : List Nat := [1, 3, 4, 3, 1, 1, 1, 4, 1, 1, 3]
def baseStart_7050357 : Nat := 118140960795 + 7050357 * 2 ^ 59
def prefixEnd_7050357 : Nat := 4983230072969 + 3 ^ 40 * 7050357 * 2
def baseEnd_7050357 : Nat := 3620221926791177179513505

theorem tailTrace_7050357 : CollatzResearch.WordTrace tailWord_7050357 prefixEnd_7050357 3620221926791177179513505 := by
  unfold tailWord_7050357
  simp only [CollatzResearch.WordTrace]
  refine ⟨257147645318768168957005325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171431763545845445971336883 257147645318768168957005325)
  ·
    refine ⟨96430366994538063358876997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 257147645318768168957005325 96430366994538063358876997)
    ·
      refine ⟨18080693811475886879789437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 96430366994538063358876997 18080693811475886879789437)
      ·
        refine ⟨6780260179303457579921039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18080693811475886879789437 6780260179303457579921039)
        ·
          refine ⟨10170390268955186369881559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6780260179303457579921039 10170390268955186369881559)
          ·
            refine ⟨15255585403432779554822339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10170390268955186369881559 15255585403432779554822339)
            ·
              refine ⟨22883378105149169332233509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15255585403432779554822339 22883378105149169332233509)
              ·
                refine ⟨4290633394715469249793783, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22883378105149169332233509 4290633394715469249793783)
                ·
                  refine ⟨6435950092073203874690675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4290633394715469249793783 6435950092073203874690675)
                  ·
                    refine ⟨9653925138109805812036013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6435950092073203874690675 9653925138109805812036013)
                    ·
                      refine ⟨3620221926791177179513505, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9653925138109805812036013 3620221926791177179513505)
                      ·
                        rfl

theorem cell23_7050357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 1, 1, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 1, 1, 1, 4, 1, 1, 3].length) (baseStart_7050357 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7050357 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7050357 prefixEnd_7050357 := by exact prefixLift 7050357
  have htrace : WordTrace (prefixWord ++ tailWord_7050357) baseStart_7050357 baseEnd_7050357 := by
    simpa [prefixWord, tailWord_7050357, baseEnd_7050357] using wordTrace_append hprefix tailTrace_7050357
  have hstable : (prefixWord ++ tailWord_7050357).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7050357).length < 2 ^ (prefixWord ++ tailWord_7050357).sum := by decide
  have hdescent : baseEnd_7050357 < baseStart_7050357 := by decide
  rcases family_descends (prefixWord ++ tailWord_7050357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7050369 : List Nat := [1, 2, 4, 2, 2, 1, 3, 8]
def baseStart_7050369 : Nat := 118140960795 + 7050369 * 2 ^ 59
def prefixEnd_7050369 : Nat := 4983230072969 + 3 ^ 40 * 7050369 * 2
def baseEnd_7050369 : Nat := 134082521798482634539387

theorem tailTrace_7050369 : CollatzResearch.WordTrace tailWord_7050369 prefixEnd_7050369 134082521798482634539387 := by
  unfold tailWord_7050369
  simp only [CollatzResearch.WordTrace]
  refine ⟨257148082994724695006442161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171432055329816463337628107 257148082994724695006442161)
  ·
    refine ⟨192861062246043521254831621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 257148082994724695006442161 192861062246043521254831621)
    ·
      refine ⟨36161449171133160235280929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 192861062246043521254831621 36161449171133160235280929)
      ·
        refine ⟨27121086878349870176460697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36161449171133160235280929 27121086878349870176460697)
        ·
          refine ⟨20340815158762402632345523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27121086878349870176460697 20340815158762402632345523)
          ·
            refine ⟨30511222738143603948518285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20340815158762402632345523 30511222738143603948518285)
            ·
              refine ⟨11441708526803851480694357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30511222738143603948518285 11441708526803851480694357)
              ·
                refine ⟨134082521798482634539387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 11441708526803851480694357 134082521798482634539387)
                ·
                  rfl

theorem cell23_7050369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 1, 3, 8].length) (baseStart_7050369 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7050369 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7050369 prefixEnd_7050369 := by exact prefixLift 7050369
  have htrace : WordTrace (prefixWord ++ tailWord_7050369) baseStart_7050369 baseEnd_7050369 := by
    simpa [prefixWord, tailWord_7050369, baseEnd_7050369] using wordTrace_append hprefix tailTrace_7050369
  have hstable : (prefixWord ++ tailWord_7050369).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7050369).length < 2 ^ (prefixWord ++ tailWord_7050369).sum := by decide
  have hdescent : baseEnd_7050369 < baseStart_7050369 := by decide
  rcases family_descends (prefixWord ++ tailWord_7050369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7050386 : List Nat := [3, 2, 3, 1, 1, 3, 3, 7]
def baseStart_7050386 : Nat := 118140960795 + 7050386 * 2 ^ 59
def prefixEnd_7050386 : Nat := 4983230072969 + 3 ^ 40 * 7050386 * 2
def baseEnd_7050386 : Nat := 134082845101116946890773

theorem tailTrace_7050386 : CollatzResearch.WordTrace tailWord_7050386 prefixEnd_7050386 134082845101116946890773 := by
  unfold tailWord_7050386
  simp only [CollatzResearch.WordTrace]
  refine ⟨64287175758915776727452753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 171432468690442071273207341 64287175758915776727452753)
  ·
    refine ⟨48215381819186832545589565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64287175758915776727452753 48215381819186832545589565)
    ·
      refine ⟨18080768182195062204596087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 48215381819186832545589565 18080768182195062204596087)
      ·
        refine ⟨27121152273292593306894131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18080768182195062204596087 27121152273292593306894131)
        ·
          refine ⟨40681728409938889960341197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27121152273292593306894131 40681728409938889960341197)
          ·
            refine ⟨15255648153727083735127949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40681728409938889960341197 15255648153727083735127949)
            ·
              refine ⟨5720868057647656400672981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15255648153727083735127949 5720868057647656400672981)
              ·
                refine ⟨134082845101116946890773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5720868057647656400672981 134082845101116946890773)
                ·
                  rfl

theorem cell23_7050386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 3, 3, 7].length) (baseStart_7050386 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7050386 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7050386 prefixEnd_7050386 := by exact prefixLift 7050386
  have htrace : WordTrace (prefixWord ++ tailWord_7050386) baseStart_7050386 baseEnd_7050386 := by
    simpa [prefixWord, tailWord_7050386, baseEnd_7050386] using wordTrace_append hprefix tailTrace_7050386
  have hstable : (prefixWord ++ tailWord_7050386).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7050386).length < 2 ^ (prefixWord ++ tailWord_7050386).sum := by decide
  have hdescent : baseEnd_7050386 < baseStart_7050386 := by decide
  rcases family_descends (prefixWord ++ tailWord_7050386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7050396 : List Nat := [2, 2, 3, 2, 1, 2, 2, 2, 1, 3, 3]
def baseStart_7050396 : Nat := 118140960795 + 7050396 * 2 ^ 59
def prefixEnd_7050396 : Nat := 4983230072969 + 3 ^ 40 * 7050396 * 2
def baseEnd_7050396 : Nat := 3620241952536702526925825

theorem tailTrace_7050396 : CollatzResearch.WordTrace tailWord_7050396 prefixEnd_7050396 3620241952536702526925825 := by
  unfold tailWord_7050396
  simp only [CollatzResearch.WordTrace]
  refine ⟨128574533882813439308837521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 171432711843751252411783361 128574533882813439308837521)
  ·
    refine ⟨96430900412110079481628141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 128574533882813439308837521 96430900412110079481628141)
    ·
      refine ⟨36161587654541279805610553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 96430900412110079481628141 36161587654541279805610553)
      ·
        refine ⟨27121190740905959854207915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36161587654541279805610553 27121190740905959854207915)
        ·
          refine ⟨40681786111358939781311873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27121190740905959854207915 40681786111358939781311873)
          ·
            refine ⟨30511339583519204835983905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40681786111358939781311873 30511339583519204835983905)
            ·
              refine ⟨22883504687639403626987929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30511339583519204835983905 22883504687639403626987929)
              ·
                refine ⟨17162628515729552720240947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22883504687639403626987929 17162628515729552720240947)
                ·
                  refine ⟨25743942773594329080361421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17162628515729552720240947 25743942773594329080361421)
                  ·
                    refine ⟨9653978540097873405135533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25743942773594329080361421 9653978540097873405135533)
                    ·
                      refine ⟨3620241952536702526925825, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9653978540097873405135533 3620241952536702526925825)
                      ·
                        rfl

theorem cell23_7050396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 2, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 2, 2, 2, 1, 3, 3].length) (baseStart_7050396 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7050396 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7050396 prefixEnd_7050396 := by exact prefixLift 7050396
  have htrace : WordTrace (prefixWord ++ tailWord_7050396) baseStart_7050396 baseEnd_7050396 := by
    simpa [prefixWord, tailWord_7050396, baseEnd_7050396] using wordTrace_append hprefix tailTrace_7050396
  have hstable : (prefixWord ++ tailWord_7050396).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7050396).length < 2 ^ (prefixWord ++ tailWord_7050396).sum := by decide
  have hdescent : baseEnd_7050396 < baseStart_7050396 := by decide
  rcases family_descends (prefixWord ++ tailWord_7050396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7050429 : List Nat := [1, 4, 1, 2, 1, 1, 4, 1, 2, 6]
def baseStart_7050429 : Nat := 118140960795 + 7050429 * 2 ^ 59
def prefixEnd_7050429 : Nat := 4983230072969 + 3 ^ 40 * 7050429 * 2
def baseEnd_7050429 : Nat := 1206752965799433632604391

theorem tailTrace_7050429 : CollatzResearch.WordTrace tailWord_7050429 prefixEnd_7050429 1206752965799433632604391 := by
  unfold tailWord_7050429
  simp only [CollatzResearch.WordTrace]
  refine ⟨257150271374507325253626341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171433514249671550169084227 257150271374507325253626341)
  ·
    refine ⟨48215675882720123485054939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 257150271374507325253626341 48215675882720123485054939)
    ·
      refine ⟨72323513824080185227582409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48215675882720123485054939 72323513824080185227582409)
      ·
        refine ⟨54242635368060138920686807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72323513824080185227582409 54242635368060138920686807)
        ·
          refine ⟨81363953052090208381030211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54242635368060138920686807 81363953052090208381030211)
          ·
            refine ⟨122045929578135312571545317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81363953052090208381030211 122045929578135312571545317)
            ·
              refine ⟨22883611795900371107164747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 122045929578135312571545317 22883611795900371107164747)
              ·
                refine ⟨34325417693850556660747121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22883611795900371107164747 34325417693850556660747121)
                ·
                  refine ⟨25744063270387917495560341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34325417693850556660747121 25744063270387917495560341)
                  ·
                    refine ⟨1206752965799433632604391, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25744063270387917495560341 1206752965799433632604391)
                    ·
                      rfl

theorem cell23_7050429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 4, 1, 2, 6].length) (baseStart_7050429 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7050429 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7050429 prefixEnd_7050429 := by exact prefixLift 7050429
  have htrace : WordTrace (prefixWord ++ tailWord_7050429) baseStart_7050429 baseEnd_7050429 := by
    simpa [prefixWord, tailWord_7050429, baseEnd_7050429] using wordTrace_append hprefix tailTrace_7050429
  have hstable : (prefixWord ++ tailWord_7050429).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7050429).length < 2 ^ (prefixWord ++ tailWord_7050429).sum := by decide
  have hdescent : baseEnd_7050429 < baseStart_7050429 := by decide
  rcases family_descends (prefixWord ++ tailWord_7050429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7050439 : List Nat := [1, 1, 4, 1, 1, 1, 1, 4, 2, 4, 3]
def baseStart_7050439 : Nat := 118140960795 + 7050439 * 2 ^ 59
def prefixEnd_7050439 : Nat := 4983230072969 + 3 ^ 40 * 7050439 * 2
def baseEnd_7050439 : Nat := 3620264032204845858688127

theorem tailTrace_7050439 : CollatzResearch.WordTrace tailWord_7050439 prefixEnd_7050439 3620264032204845858688127 := by
  unfold tailWord_7050439
  simp only [CollatzResearch.WordTrace]
  refine ⟨257150636104471096961490371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171433757402980731307660247 257150636104471096961490371)
  ·
    refine ⟨385725954156706645442235557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 257150636104471096961490371 385725954156706645442235557)
    ·
      refine ⟨72323616404382496020419167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 385725954156706645442235557 72323616404382496020419167)
      ·
        refine ⟨108485424606573744030628751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72323616404382496020419167 108485424606573744030628751)
        ·
          refine ⟨162728136909860616045943127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 108485424606573744030628751 162728136909860616045943127)
          ·
            refine ⟨244092205364790924068914691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 162728136909860616045943127 244092205364790924068914691)
            ·
              refine ⟨366138308047186386103372037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 244092205364790924068914691 366138308047186386103372037)
              ·
                refine ⟨68650932758847447394382257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 366138308047186386103372037 68650932758847447394382257)
                ·
                  refine ⟨51488199569135585545786693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 68650932758847447394382257 51488199569135585545786693)
                  ·
                    refine ⟨9654037419212922289835005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 51488199569135585545786693 9654037419212922289835005)
                    ·
                      refine ⟨3620264032204845858688127, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9654037419212922289835005 3620264032204845858688127)
                      ·
                        rfl

theorem cell23_7050439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 1, 4, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 1, 4, 2, 4, 3].length) (baseStart_7050439 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7050439 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7050439 prefixEnd_7050439 := by exact prefixLift 7050439
  have htrace : WordTrace (prefixWord ++ tailWord_7050439) baseStart_7050439 baseEnd_7050439 := by
    simpa [prefixWord, tailWord_7050439, baseEnd_7050439] using wordTrace_append hprefix tailTrace_7050439
  have hstable : (prefixWord ++ tailWord_7050439).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7050439).length < 2 ^ (prefixWord ++ tailWord_7050439).sum := by decide
  have hdescent : baseEnd_7050439 < baseStart_7050439 := by decide
  rcases family_descends (prefixWord ++ tailWord_7050439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7050456 : List Nat := [2, 1, 2, 2, 5, 1, 1, 1, 2, 1, 5]
def baseStart_7050456 : Nat := 118140960795 + 7050456 * 2 ^ 59
def prefixEnd_7050456 : Nat := 4983230072969 + 3 ^ 40 * 7050456 * 2
def baseEnd_7050456 : Nat := 3620272761375972292175549

theorem tailTrace_7050456 : CollatzResearch.WordTrace tailWord_7050456 prefixEnd_7050456 3620272761375972292175549 := by
  unfold tailWord_7050456
  simp only [CollatzResearch.WordTrace]
  refine ⟨128575628072704754432429611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 171434170763606339243239481 128575628072704754432429611)
  ·
    refine ⟨192863442109057131648644417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128575628072704754432429611 192863442109057131648644417)
    ·
      refine ⟨144647581581792848736483313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 192863442109057131648644417 144647581581792848736483313)
      ·
        refine ⟨108485686186344636552362485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 144647581581792848736483313 108485686186344636552362485)
        ·
          refine ⟨10170533079969809676783983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 108485686186344636552362485 10170533079969809676783983)
          ·
            refine ⟨15255799619954714515175975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10170533079969809676783983 15255799619954714515175975)
            ·
              refine ⟨22883699429932071772763963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15255799619954714515175975 22883699429932071772763963)
              ·
                refine ⟨34325549144898107659145945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22883699429932071772763963 34325549144898107659145945)
                ·
                  refine ⟨25744161858673580744359459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34325549144898107659145945 25744161858673580744359459)
                  ·
                    refine ⟨38616242788010371116539189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 25744161858673580744359459 38616242788010371116539189)
                    ·
                      refine ⟨3620272761375972292175549, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 38616242788010371116539189 3620272761375972292175549)
                      ·
                        rfl

theorem cell23_7050456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 5, 1, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 5, 1, 1, 1, 2, 1, 5].length) (baseStart_7050456 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7050456 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7050456 prefixEnd_7050456 := by exact prefixLift 7050456
  have htrace : WordTrace (prefixWord ++ tailWord_7050456) baseStart_7050456 baseEnd_7050456 := by
    simpa [prefixWord, tailWord_7050456, baseEnd_7050456] using wordTrace_append hprefix tailTrace_7050456
  have hstable : (prefixWord ++ tailWord_7050456).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7050456).length < 2 ^ (prefixWord ++ tailWord_7050456).sum := by decide
  have hdescent : baseEnd_7050456 < baseStart_7050456 := by decide
  rcases family_descends (prefixWord ++ tailWord_7050456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7050476 : List Nat := [2, 2, 1, 1, 2, 6, 1, 1, 7]
def baseStart_7050476 : Nat := 118140960795 + 7050476 * 2 ^ 59
def prefixEnd_7050476 : Nat := 4983230072969 + 3 ^ 40 * 7050476 * 2
def baseEnd_7050476 : Nat := 402253670109895801547273

theorem tailTrace_7050476 : CollatzResearch.WordTrace tailWord_7050476 prefixEnd_7050476 402253670109895801547273 := by
  unfold tailWord_7050476
  simp only [CollatzResearch.WordTrace]
  refine ⟨128575992802668526140293641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 171434657070224701520391521 128575992802668526140293641)
  ·
    refine ⟨96431994602001394605220231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 128575992802668526140293641 96431994602001394605220231)
    ·
      refine ⟨144647991903002091907830347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96431994602001394605220231 144647991903002091907830347)
      ·
        refine ⟨216971987854503137861745521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 144647991903002091907830347 216971987854503137861745521)
        ·
          refine ⟨162728990890877353396309141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 216971987854503137861745521 162728990890877353396309141)
          ·
            refine ⟨7627921448009875940451991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 162728990890877353396309141 7627921448009875940451991)
            ·
              refine ⟨11441882172014813910677987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7627921448009875940451991 11441882172014813910677987)
              ·
                refine ⟨17162823258022220866016981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11441882172014813910677987 17162823258022220866016981)
                ·
                  refine ⟨402253670109895801547273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17162823258022220866016981 402253670109895801547273)
                  ·
                    rfl

theorem cell23_7050476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 7].length) (baseStart_7050476 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7050476 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7050476 prefixEnd_7050476 := by exact prefixLift 7050476
  have htrace : WordTrace (prefixWord ++ tailWord_7050476) baseStart_7050476 baseEnd_7050476 := by
    simpa [prefixWord, tailWord_7050476, baseEnd_7050476] using wordTrace_append hprefix tailTrace_7050476
  have hstable : (prefixWord ++ tailWord_7050476).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7050476).length < 2 ^ (prefixWord ++ tailWord_7050476).sum := by decide
  have hdescent : baseEnd_7050476 < baseStart_7050476 := by decide
  rcases family_descends (prefixWord ++ tailWord_7050476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7050486 : List Nat := [5, 1, 1, 1, 1, 1, 1, 3, 1, 5, 3]
def baseStart_7050486 : Nat := 118140960795 + 7050486 * 2 ^ 59
def prefixEnd_7050486 : Nat := 4983230072969 + 3 ^ 40 * 7050486 * 2
def baseEnd_7050486 : Nat := 3620288165795607174800411

theorem tailTrace_7050486 : CollatzResearch.WordTrace tailWord_7050486 prefixEnd_7050486 3620288165795607174800411 := by
  unfold tailWord_7050486
  simp only [CollatzResearch.WordTrace]
  refine ⟨16072021895956301499278207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 171434900223533882658967541 16072021895956301499278207)
  ·
    refine ⟨24108032843934452248917311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16072021895956301499278207 24108032843934452248917311)
    ·
      refine ⟨36162049265901678373375967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24108032843934452248917311 36162049265901678373375967)
      ·
        refine ⟨54243073898852517560063951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36162049265901678373375967 54243073898852517560063951)
        ·
          refine ⟨81364610848278776340095927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54243073898852517560063951 81364610848278776340095927)
          ·
            refine ⟨122046916272418164510143891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81364610848278776340095927 122046916272418164510143891)
            ·
              refine ⟨183070374408627246765215837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 122046916272418164510143891 183070374408627246765215837)
              ·
                refine ⟨68651390403235217536955939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 183070374408627246765215837 68651390403235217536955939)
                ·
                  refine ⟨102977085604852826305433909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 68651390403235217536955939 102977085604852826305433909)
                  ·
                    refine ⟨9654101775454952466134429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 102977085604852826305433909 9654101775454952466134429)
                    ·
                      refine ⟨3620288165795607174800411, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9654101775454952466134429 3620288165795607174800411)
                      ·
                        rfl

theorem cell23_7050486_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 1, 3, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 1, 3, 1, 5, 3].length) (baseStart_7050486 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7050486 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7050486 prefixEnd_7050486 := by exact prefixLift 7050486
  have htrace : WordTrace (prefixWord ++ tailWord_7050486) baseStart_7050486 baseEnd_7050486 := by
    simpa [prefixWord, tailWord_7050486, baseEnd_7050486] using wordTrace_append hprefix tailTrace_7050486
  have hstable : (prefixWord ++ tailWord_7050486).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7050486).length < 2 ^ (prefixWord ++ tailWord_7050486).sum := by decide
  have hdescent : baseEnd_7050486 < baseStart_7050486 := by decide
  rcases family_descends (prefixWord ++ tailWord_7050486) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7050489 : List Nat := [1, 2, 1, 3, 1, 1, 3, 2, 4, 5]
def baseStart_7050489 : Nat := 118140960795 + 7050489 * 2 ^ 59
def prefixEnd_7050489 : Nat := 4983230072969 + 3 ^ 40 * 7050489 * 2
def baseEnd_7050489 : Nat := 1206763235412523554354299

theorem tailTrace_7050489 : CollatzResearch.WordTrace tailWord_7050489 prefixEnd_7050489 1206763235412523554354299 := by
  unfold tailWord_7050489
  simp only [CollatzResearch.WordTrace]
  refine ⟨257152459754289955500810521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171434973169526637000540347 257152459754289955500810521)
  ·
    refine ⟨192864344815717466625607891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 257152459754289955500810521 192864344815717466625607891)
    ·
      refine ⟨289296517223576199938411837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 192864344815717466625607891 289296517223576199938411837)
      ·
        refine ⟨108486193958841074976904439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 289296517223576199938411837 108486193958841074976904439)
        ·
          refine ⟨162729290938261612465356659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 108486193958841074976904439 162729290938261612465356659)
          ·
            refine ⟨244093936407392418698034989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 162729290938261612465356659 244093936407392418698034989)
            ·
              refine ⟨91535226152772157011763121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 244093936407392418698034989 91535226152772157011763121)
              ·
                refine ⟨68651419614579117758822341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 91535226152772157011763121 68651419614579117758822341)
                ·
                  refine ⟨12872141177733584579779189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 68651419614579117758822341 12872141177733584579779189)
                  ·
                    refine ⟨1206763235412523554354299, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12872141177733584579779189 1206763235412523554354299)
                    ·
                      rfl

theorem cell23_7050489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 3, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 3, 2, 4, 5].length) (baseStart_7050489 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7050489 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7050489 prefixEnd_7050489 := by exact prefixLift 7050489
  have htrace : WordTrace (prefixWord ++ tailWord_7050489) baseStart_7050489 baseEnd_7050489 := by
    simpa [prefixWord, tailWord_7050489, baseEnd_7050489] using wordTrace_append hprefix tailTrace_7050489
  have hstable : (prefixWord ++ tailWord_7050489).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7050489).length < 2 ^ (prefixWord ++ tailWord_7050489).sum := by decide
  have hdescent : baseEnd_7050489 < baseStart_7050489 := by decide
  rcases family_descends (prefixWord ++ tailWord_7050489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7050527 : List Nat := [1, 1, 2, 4, 5, 1, 2, 2, 5]
def baseStart_7050527 : Nat := 118140960795 + 7050527 * 2 ^ 59
def prefixEnd_7050527 : Nat := 4983230072969 + 3 ^ 40 * 7050527 * 2
def baseEnd_7050527 : Nat := 402256579833604612709747

theorem tailTrace_7050527 : CollatzResearch.WordTrace tailWord_7050527 prefixEnd_7050527 402256579833604612709747 := by
  unfold tailWord_7050527
  simp only [CollatzResearch.WordTrace]
  refine ⟨257153845728152287990693835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171435897152101525327129223 257153845728152287990693835)
  ·
    refine ⟨385730768592228431986040753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 257153845728152287990693835 385730768592228431986040753)
    ·
      refine ⟨289298076444171323989530565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 385730768592228431986040753 289298076444171323989530565)
      ·
        refine ⟨54243389333282123248036981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 289298076444171323989530565 54243389333282123248036981)
        ·
          refine ⟨5085317749995199054503467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 54243389333282123248036981 5085317749995199054503467)
          ·
            refine ⟨7627976624992798581755201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5085317749995199054503467 7627976624992798581755201)
            ·
              refine ⟨5720982468744598936316401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7627976624992798581755201 5720982468744598936316401)
              ·
                refine ⟨4290736851558449202237301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5720982468744598936316401 4290736851558449202237301)
                ·
                  refine ⟨402256579833604612709747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4290736851558449202237301 402256579833604612709747)
                  ·
                    rfl

theorem cell23_7050527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 5, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 5, 1, 2, 2, 5].length) (baseStart_7050527 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7050527 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7050527 prefixEnd_7050527 := by exact prefixLift 7050527
  have htrace : WordTrace (prefixWord ++ tailWord_7050527) baseStart_7050527 baseEnd_7050527 := by
    simpa [prefixWord, tailWord_7050527, baseEnd_7050527] using wordTrace_append hprefix tailTrace_7050527
  have hstable : (prefixWord ++ tailWord_7050527).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7050527).length < 2 ^ (prefixWord ++ tailWord_7050527).sum := by decide
  have hdescent : baseEnd_7050527 < baseStart_7050527 := by decide
  rcases family_descends (prefixWord ++ tailWord_7050527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7050529 : List Nat := [1, 2, 3, 2, 1, 1, 1, 1, 1, 5, 5]
def baseStart_7050529 : Nat := 118140960795 + 7050529 * 2 ^ 59
def prefixEnd_7050529 : Nat := 4983230072969 + 3 ^ 40 * 7050529 * 2
def baseEnd_7050529 : Nat := 3620310245463750506562713

theorem tailTrace_7050529 : CollatzResearch.WordTrace tailWord_7050529 prefixEnd_7050529 3620310245463750506562713 := by
  unfold tailWord_7050529
  simp only [CollatzResearch.WordTrace]
  refine ⟨257153918674145042332266641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171435945782763361554844427 257153918674145042332266641)
  ·
    refine ⟨192865439005608781749199981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 257153918674145042332266641 192865439005608781749199981)
    ·
      refine ⟨72324539627103293155949993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 192865439005608781749199981 72324539627103293155949993)
      ·
        refine ⟨54243404720327469866962495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72324539627103293155949993 54243404720327469866962495)
        ·
          refine ⟨81365107080491204800443743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54243404720327469866962495 81365107080491204800443743)
          ·
            refine ⟨122047660620736807200665615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81365107080491204800443743 122047660620736807200665615)
            ·
              refine ⟨183071490931105210800998423, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 122047660620736807200665615 183071490931105210800998423)
              ·
                refine ⟨274607236396657816201497635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 183071490931105210800998423 274607236396657816201497635)
                ·
                  refine ⟨411910854594986724302246453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 274607236396657816201497635 411910854594986724302246453)
                  ·
                    refine ⟨38616642618280005403335605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 411910854594986724302246453 38616642618280005403335605)
                    ·
                      refine ⟨3620310245463750506562713, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 38616642618280005403335605 3620310245463750506562713)
                      ·
                        rfl

theorem cell23_7050529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 1, 1, 1, 5, 5].length) (baseStart_7050529 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7050529 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7050529 prefixEnd_7050529 := by exact prefixLift 7050529
  have htrace : WordTrace (prefixWord ++ tailWord_7050529) baseStart_7050529 baseEnd_7050529 := by
    simpa [prefixWord, tailWord_7050529, baseEnd_7050529] using wordTrace_append hprefix tailTrace_7050529
  have hstable : (prefixWord ++ tailWord_7050529).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7050529).length < 2 ^ (prefixWord ++ tailWord_7050529).sum := by decide
  have hdescent : baseEnd_7050529 < baseStart_7050529 := by decide
  rcases family_descends (prefixWord ++ tailWord_7050529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7050557 : List Nat := [1, 4, 1, 5, 2, 1, 1, 1, 2, 5]
def baseStart_7050557 : Nat := 118140960795 + 7050557 * 2 ^ 59
def prefixEnd_7050557 : Nat := 4983230072969 + 3 ^ 40 * 7050557 * 2
def baseEnd_7050557 : Nat := 1206774874307358799004195

theorem tailTrace_7050557 : CollatzResearch.WordTrace tailWord_7050557 prefixEnd_7050557 1206774874307358799004195 := by
  unfold tailWord_7050557
  simp only [CollatzResearch.WordTrace]
  refine ⟨257154939918043603114285925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171436626612029068742857283 257154939918043603114285925)
  ·
    refine ⟨48216551234633175583928611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 257154939918043603114285925 48216551234633175583928611)
    ·
      refine ⟨72324826851949763375892917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48216551234633175583928611 72324826851949763375892917)
      ·
        refine ⟨6780452517370290316489961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 72324826851949763375892917 6780452517370290316489961)
        ·
          refine ⟨5085339388027717737367471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6780452517370290316489961 5085339388027717737367471)
          ·
            refine ⟨7628009082041576606051207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5085339388027717737367471 7628009082041576606051207)
            ·
              refine ⟨11442013623062364909076811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7628009082041576606051207 11442013623062364909076811)
              ·
                refine ⟨17163020434593547363615217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11442013623062364909076811 17163020434593547363615217)
                ·
                  refine ⟨12872265325945160522711413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17163020434593547363615217 12872265325945160522711413)
                  ·
                    refine ⟨1206774874307358799004195, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12872265325945160522711413 1206774874307358799004195)
                    ·
                      rfl

theorem cell23_7050557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 2, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 2, 1, 1, 1, 2, 5].length) (baseStart_7050557 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7050557 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7050557 prefixEnd_7050557 := by exact prefixLift 7050557
  have htrace : WordTrace (prefixWord ++ tailWord_7050557) baseStart_7050557 baseEnd_7050557 := by
    simpa [prefixWord, tailWord_7050557, baseEnd_7050557] using wordTrace_append hprefix tailTrace_7050557
  have hstable : (prefixWord ++ tailWord_7050557).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7050557).length < 2 ^ (prefixWord ++ tailWord_7050557).sum := by decide
  have hdescent : baseEnd_7050557 < baseStart_7050557 := by decide
  rcases family_descends (prefixWord ++ tailWord_7050557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7050583 : List Nat := [1, 1, 3, 2, 3, 4, 1, 2, 6]
def baseStart_7050583 : Nat := 118140960795 + 7050583 * 2 ^ 59
def prefixEnd_7050583 : Nat := 4983230072969 + 3 ^ 40 * 7050583 * 2
def baseEnd_7050583 : Nat := 402259774824343699476385

theorem tailTrace_7050583 : CollatzResearch.WordTrace tailWord_7050583 prefixEnd_7050583 402259774824343699476385 := by
  unfold tailWord_7050583
  simp only [CollatzResearch.WordTrace]
  refine ⟨257155888215949409554732403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171437258810632939703154935 257155888215949409554732403)
  ·
    refine ⟨385733832323924114332098605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 257155888215949409554732403 385733832323924114332098605)
    ·
      refine ⟨144650187121471542874536977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 385733832323924114332098605 144650187121471542874536977)
      ·
        refine ⟨108487640341103657155902733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 144650187121471542874536977 108487640341103657155902733)
        ·
          refine ⟨40682865127913871433463525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 108487640341103657155902733 40682865127913871433463525)
          ·
            refine ⟨7628037211483850893774411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 40682865127913871433463525 7628037211483850893774411)
            ·
              refine ⟨11442055817225776340661617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7628037211483850893774411 11442055817225776340661617)
              ·
                refine ⟨8581541862919332255496213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11442055817225776340661617 8581541862919332255496213)
                ·
                  refine ⟨402259774824343699476385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8581541862919332255496213 402259774824343699476385)
                  ·
                    rfl

theorem cell23_7050583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 4, 1, 2, 6].length) (baseStart_7050583 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7050583 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7050583 prefixEnd_7050583 := by exact prefixLift 7050583
  have htrace : WordTrace (prefixWord ++ tailWord_7050583) baseStart_7050583 baseEnd_7050583 := by
    simpa [prefixWord, tailWord_7050583, baseEnd_7050583] using wordTrace_append hprefix tailTrace_7050583
  have hstable : (prefixWord ++ tailWord_7050583).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7050583).length < 2 ^ (prefixWord ++ tailWord_7050583).sum := by decide
  have hdescent : baseEnd_7050583 < baseStart_7050583 := by decide
  rcases family_descends (prefixWord ++ tailWord_7050583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7050600 : List Nat := [2, 1, 4, 2, 3, 1, 3, 1, 6]
def baseStart_7050600 : Nat := 118140960795 + 7050600 * 2 ^ 59
def prefixEnd_7050600 : Nat := 4983230072969 + 3 ^ 40 * 7050600 * 2
def baseEnd_7050600 : Nat := 402260744732246636530543

theorem tailTrace_7050600 : CollatzResearch.WordTrace tailWord_7050600 prefixEnd_7050600 402260744732246636530543 := by
  unfold tailWord_7050600
  simp only [CollatzResearch.WordTrace]
  refine ⟨128578254128443910729050627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 171437672171258547638734169 128578254128443910729050627)
  ·
    refine ⟨192867381192665866093575941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128578254128443910729050627 192867381192665866093575941)
    ·
      refine ⟨36162633973624849892545489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 192867381192665866093575941 36162633973624849892545489)
      ·
        refine ⟨27121975480218637419409117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36162633973624849892545489 27121975480218637419409117)
        ·
          refine ⟨10170740805081989032278419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27121975480218637419409117 10170740805081989032278419)
          ·
            refine ⟨15256111207622983548417629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10170740805081989032278419 15256111207622983548417629)
            ·
              refine ⟨5721041702858618830656611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15256111207622983548417629 5721041702858618830656611)
              ·
                refine ⟨8581562554287928245984917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5721041702858618830656611 8581562554287928245984917)
                ·
                  refine ⟨402260744732246636530543, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8581562554287928245984917 402260744732246636530543)
                  ·
                    rfl

theorem cell23_7050600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 3, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 3, 1, 3, 1, 6].length) (baseStart_7050600 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7050600 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7050600 prefixEnd_7050600 := by exact prefixLift 7050600
  have htrace : WordTrace (prefixWord ++ tailWord_7050600) baseStart_7050600 baseEnd_7050600 := by
    simpa [prefixWord, tailWord_7050600, baseEnd_7050600] using wordTrace_append hprefix tailTrace_7050600
  have hstable : (prefixWord ++ tailWord_7050600).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7050600).length < 2 ^ (prefixWord ++ tailWord_7050600).sum := by decide
  have hdescent : baseEnd_7050600 < baseStart_7050600 := by decide
  rcases family_descends (prefixWord ++ tailWord_7050600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7050627 : List Nat := [1, 1, 1, 3, 5, 1, 3, 3, 1, 1, 3]
def baseStart_7050627 : Nat := 118140960795 + 7050627 * 2 ^ 59
def prefixEnd_7050627 : Nat := 4983230072969 + 3 ^ 40 * 7050627 * 2
def baseEnd_7050627 : Nat := 3620360566567891123137263

theorem tailTrace_7050627 : CollatzResearch.WordTrace tailWord_7050627 prefixEnd_7050627 3620360566567891123137263 := by
  unfold tailWord_7050627
  simp only [CollatzResearch.WordTrace]
  refine ⟨257157493027790005069334135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171438328685193336712889423 257157493027790005069334135)
  ·
    refine ⟨385736239541685007604001203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 257157493027790005069334135 385736239541685007604001203)
    ·
      refine ⟨578604359312527511406001805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 385736239541685007604001203 578604359312527511406001805)
      ·
        refine ⟨216976634742197816777250677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 578604359312527511406001805 216976634742197816777250677)
        ·
          refine ⟨20341559507081045322867251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 216976634742197816777250677 20341559507081045322867251)
          ·
            refine ⟨30512339260621567984300877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20341559507081045322867251 30512339260621567984300877)
            ·
              refine ⟨11442127222733087994112829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30512339260621567984300877 11442127222733087994112829)
              ·
                refine ⟨4290797708524907997792311, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11442127222733087994112829 4290797708524907997792311)
                ·
                  refine ⟨6436196562787361996688467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4290797708524907997792311 6436196562787361996688467)
                  ·
                    refine ⟨9654294844181042995032701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6436196562787361996688467 9654294844181042995032701)
                    ·
                      refine ⟨3620360566567891123137263, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9654294844181042995032701 3620360566567891123137263)
                      ·
                        rfl

theorem cell23_7050627_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 1, 3, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 1, 3, 3, 1, 1, 3].length) (baseStart_7050627 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7050627 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7050627 prefixEnd_7050627 := by exact prefixLift 7050627
  have htrace : WordTrace (prefixWord ++ tailWord_7050627) baseStart_7050627 baseEnd_7050627 := by
    simpa [prefixWord, tailWord_7050627, baseEnd_7050627] using wordTrace_append hprefix tailTrace_7050627
  have hstable : (prefixWord ++ tailWord_7050627).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7050627).length < 2 ^ (prefixWord ++ tailWord_7050627).sum := by decide
  have hdescent : baseEnd_7050627 < baseStart_7050627 := by decide
  rcases family_descends (prefixWord ++ tailWord_7050627) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
