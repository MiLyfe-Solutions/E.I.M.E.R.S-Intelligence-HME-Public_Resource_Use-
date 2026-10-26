import V185TrunkScan23Chunk1311

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_7770083 : List Nat := [1, 1, 1, 6, 1, 3, 3, 1, 1, 2, 3]
def baseStart_7770083 : Nat := 118140960795 + 7770083 * 2 ^ 59
def prefixEnd_7770083 : Nat := 4983230072969 + 3 ^ 40 * 7770083 * 2
def baseEnd_7770083 : Nat := 3989787304329028248228545

theorem tailTrace_7770083 : CollatzResearch.WordTrace tailWord_7770083 prefixEnd_7770083 3989787304329028248228545 := by
  unfold tailWord_7770083
  simp only [CollatzResearch.WordTrace]
  refine ⟨283398209109323790371690903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188932139406215860247793935 283398209109323790371690903)
  ·
    refine ⟨425097313663985685557536355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 283398209109323790371690903 425097313663985685557536355)
    ·
      refine ⟨637645970495978528336304533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 425097313663985685557536355 637645970495978528336304533)
      ·
        refine ⟨29889654866998993515764275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 637645970495978528336304533 29889654866998993515764275)
        ·
          refine ⟨44834482300498490273646413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29889654866998993515764275 44834482300498490273646413)
          ·
            refine ⟨16812930862686933852617405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 44834482300498490273646413 16812930862686933852617405)
            ·
              refine ⟨6304849073507600194731527, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16812930862686933852617405 6304849073507600194731527)
              ·
                refine ⟨9457273610261400292097291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6304849073507600194731527 9457273610261400292097291)
                ·
                  refine ⟨14185910415392100438145937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9457273610261400292097291 14185910415392100438145937)
                  ·
                    refine ⟨10639432811544075328609453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14185910415392100438145937 10639432811544075328609453)
                    ·
                      refine ⟨3989787304329028248228545, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10639432811544075328609453 3989787304329028248228545)
                      ·
                        rfl

theorem cell23_7770083_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 3, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 3, 3, 1, 1, 2, 3].length) (baseStart_7770083 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7770083 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7770083 prefixEnd_7770083 := by exact prefixLift 7770083
  have htrace : WordTrace (prefixWord ++ tailWord_7770083) baseStart_7770083 baseEnd_7770083 := by
    simpa [prefixWord, tailWord_7770083, baseEnd_7770083] using wordTrace_append hprefix tailTrace_7770083
  have hstable : (prefixWord ++ tailWord_7770083).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7770083).length < 2 ^ (prefixWord ++ tailWord_7770083).sum := by decide
  have hdescent : baseEnd_7770083 < baseStart_7770083 := by decide
  rcases family_descends (prefixWord ++ tailWord_7770083) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7770092 : List Nat := [2, 2, 1, 1, 2, 1, 1, 4, 2, 2, 5]
def baseStart_7770092 : Nat := 118140960795 + 7770092 * 2 ^ 59
def prefixEnd_7770092 : Nat := 4983230072969 + 3 ^ 40 * 7770092 * 2
def baseEnd_7770092 : Nat := 3989791925654918713016003

theorem tailTrace_7770092 : CollatzResearch.WordTrace tailWord_7770092 prefixEnd_7770092 3989791925654918713016003 := by
  unfold tailWord_7770092
  simp only [CollatzResearch.WordTrace]
  refine ⟨141699268683145592454384265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 188932358244194123272512353 141699268683145592454384265)
  ·
    refine ⟨106274451512359194340788199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 141699268683145592454384265 106274451512359194340788199)
    ·
      refine ⟨159411677268538791511182299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106274451512359194340788199 159411677268538791511182299)
      ·
        refine ⟨239117515902808187266773449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 159411677268538791511182299 239117515902808187266773449)
        ·
          refine ⟨179338136927106140450080087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 239117515902808187266773449 179338136927106140450080087)
          ·
            refine ⟨269007205390659210675120131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 179338136927106140450080087 269007205390659210675120131)
            ·
              refine ⟨403510808085988816012680197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 269007205390659210675120131 403510808085988816012680197)
              ·
                refine ⟨75658276516122903002377537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 403510808085988816012680197 75658276516122903002377537)
                ·
                  refine ⟨56743707387092177251783153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 75658276516122903002377537 56743707387092177251783153)
                  ·
                    refine ⟨42557780540319132938837365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 56743707387092177251783153 42557780540319132938837365)
                    ·
                      refine ⟨3989791925654918713016003, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 42557780540319132938837365 3989791925654918713016003)
                      ·
                        rfl

theorem cell23_7770092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 2, 5].length) (baseStart_7770092 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7770092 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7770092 prefixEnd_7770092 := by exact prefixLift 7770092
  have htrace : WordTrace (prefixWord ++ tailWord_7770092) baseStart_7770092 baseEnd_7770092 := by
    simpa [prefixWord, tailWord_7770092, baseEnd_7770092] using wordTrace_append hprefix tailTrace_7770092
  have hstable : (prefixWord ++ tailWord_7770092).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7770092).length < 2 ^ (prefixWord ++ tailWord_7770092).sum := by decide
  have hdescent : baseEnd_7770092 < baseStart_7770092 := by decide
  rcases family_descends (prefixWord ++ tailWord_7770092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7770096 : List Nat := [2, 1, 1, 1, 3, 2, 3, 4, 2, 1, 3]
def baseStart_7770096 : Nat := 118140960795 + 7770096 * 2 ^ 59
def prefixEnd_7770096 : Nat := 4983230072969 + 3 ^ 40 * 7770096 * 2
def baseEnd_7770096 : Nat := 3989793979577536697365985

theorem tailTrace_7770096 : CollatzResearch.WordTrace tailWord_7770096 prefixEnd_7770096 3989793979577536697365985 := by
  unfold tailWord_7770096
  simp only [CollatzResearch.WordTrace]
  refine ⟨141699341629138346795957071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 188932455505517795727942761 141699341629138346795957071)
  ·
    refine ⟨212549012443707520193935607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141699341629138346795957071 212549012443707520193935607)
    ·
      refine ⟨318823518665561280290903411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 212549012443707520193935607 318823518665561280290903411)
      ·
        refine ⟨478235277998341920436355117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 318823518665561280290903411 478235277998341920436355117)
        ·
          refine ⟨179338229249378220163633169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 478235277998341920436355117 179338229249378220163633169)
          ·
            refine ⟨134503671937033665122724877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 179338229249378220163633169 134503671937033665122724877)
            ·
              refine ⟨50438876976387624421021829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 134503671937033665122724877 50438876976387624421021829)
              ·
                refine ⟨9457289433072679578941593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 50438876976387624421021829 9457289433072679578941593)
                ·
                  refine ⟨7092967074804509684206195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9457289433072679578941593 7092967074804509684206195)
                  ·
                    refine ⟨10639450612206764526309293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7092967074804509684206195 10639450612206764526309293)
                    ·
                      refine ⟨3989793979577536697365985, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10639450612206764526309293 3989793979577536697365985)
                      ·
                        rfl

theorem cell23_7770096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 3, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 3, 4, 2, 1, 3].length) (baseStart_7770096 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7770096 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7770096 prefixEnd_7770096 := by exact prefixLift 7770096
  have htrace : WordTrace (prefixWord ++ tailWord_7770096) baseStart_7770096 baseEnd_7770096 := by
    simpa [prefixWord, tailWord_7770096, baseEnd_7770096] using wordTrace_append hprefix tailTrace_7770096
  have hstable : (prefixWord ++ tailWord_7770096).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7770096).length < 2 ^ (prefixWord ++ tailWord_7770096).sum := by decide
  have hdescent : baseEnd_7770096 < baseStart_7770096 := by decide
  rcases family_descends (prefixWord ++ tailWord_7770096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7770136 : List Nat := [2, 1, 2, 3, 2, 1, 1, 4, 1, 4, 2]
def baseStart_7770136 : Nat := 118140960795 + 7770136 * 2 ^ 59
def prefixEnd_7770136 : Nat := 4983230072969 + 3 ^ 40 * 7770136 * 2
def baseEnd_7770136 : Nat := 3989814518803716540865801

theorem tailTrace_7770136 : CollatzResearch.WordTrace tailWord_7770136 prefixEnd_7770136 3989814518803716540865801 := by
  unfold tailWord_7770136
  simp only [CollatzResearch.WordTrace]
  refine ⟨141700071089065890211685131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 188933428118754520282246841 141700071089065890211685131)
  ·
    refine ⟨212550106633598835317527697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141700071089065890211685131 212550106633598835317527697)
    ·
      refine ⟨159412579975199126488145773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 212550106633598835317527697 159412579975199126488145773)
      ·
        refine ⟨59779717490699672433054665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 159412579975199126488145773 59779717490699672433054665)
        ·
          refine ⟨44834788118024754324790999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59779717490699672433054665 44834788118024754324790999)
          ·
            refine ⟨67252182177037131487186499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44834788118024754324790999 67252182177037131487186499)
            ·
              refine ⟨100878273265555697230779749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67252182177037131487186499 100878273265555697230779749)
              ·
                refine ⟨18914676237291693230771203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 100878273265555697230779749 18914676237291693230771203)
                ·
                  refine ⟨28372014355937539846156805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18914676237291693230771203 28372014355937539846156805)
                  ·
                    refine ⟨5319752691738288721154401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28372014355937539846156805 5319752691738288721154401)
                    ·
                      refine ⟨3989814518803716540865801, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5319752691738288721154401 3989814518803716540865801)
                      ·
                        rfl

theorem cell23_7770136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 1, 4, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 1, 4, 1, 4, 2].length) (baseStart_7770136 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7770136 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7770136 prefixEnd_7770136 := by exact prefixLift 7770136
  have htrace : WordTrace (prefixWord ++ tailWord_7770136) baseStart_7770136 baseEnd_7770136 := by
    simpa [prefixWord, tailWord_7770136, baseEnd_7770136] using wordTrace_append hprefix tailTrace_7770136
  have hstable : (prefixWord ++ tailWord_7770136).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7770136).length < 2 ^ (prefixWord ++ tailWord_7770136).sum := by decide
  have hdescent : baseEnd_7770136 < baseStart_7770136 := by decide
  rcases family_descends (prefixWord ++ tailWord_7770136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7770140 : List Nat := [2, 2, 3, 1, 3, 1, 4, 1, 1, 3, 2]
def baseStart_7770140 : Nat := 118140960795 + 7770140 * 2 ^ 59
def prefixEnd_7770140 : Nat := 4983230072969 + 3 ^ 40 * 7770140 * 2
def baseEnd_7770140 : Nat := 3989816572726334525215783

theorem tailTrace_7770140 : CollatzResearch.WordTrace tailWord_7770140 prefixEnd_7770140 3989816572726334525215783 := by
  unfold tailWord_7770140
  simp only [CollatzResearch.WordTrace]
  refine ⟨141700144035058644553257937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 188933525380078192737677249 141700144035058644553257937)
  ·
    refine ⟨106275108026293983414943453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 141700144035058644553257937 106275108026293983414943453)
    ·
      refine ⟨39853165509860243780603795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 106275108026293983414943453 39853165509860243780603795)
      ·
        refine ⟨59779748264790365670905693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39853165509860243780603795 59779748264790365670905693)
        ·
          refine ⟨22417405599296387126589635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 59779748264790365670905693 22417405599296387126589635)
          ·
            refine ⟨33626108398944580689884453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22417405599296387126589635 33626108398944580689884453)
            ·
              refine ⟨6304895324802108879353335, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 33626108398944580689884453 6304895324802108879353335)
              ·
                refine ⟨9457342987203163319030003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6304895324802108879353335 9457342987203163319030003)
                ·
                  refine ⟨14186014480804744978545005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9457342987203163319030003 14186014480804744978545005)
                  ·
                    refine ⟨5319755430301779366954377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14186014480804744978545005 5319755430301779366954377)
                    ·
                      refine ⟨3989816572726334525215783, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5319755430301779366954377 3989816572726334525215783)
                      ·
                        rfl

theorem cell23_7770140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 1, 4, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 1, 4, 1, 1, 3, 2].length) (baseStart_7770140 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7770140 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7770140 prefixEnd_7770140 := by exact prefixLift 7770140
  have htrace : WordTrace (prefixWord ++ tailWord_7770140) baseStart_7770140 baseEnd_7770140 := by
    simpa [prefixWord, tailWord_7770140, baseEnd_7770140] using wordTrace_append hprefix tailTrace_7770140
  have hstable : (prefixWord ++ tailWord_7770140).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7770140).length < 2 ^ (prefixWord ++ tailWord_7770140).sum := by decide
  have hdescent : baseEnd_7770140 < baseStart_7770140 := by decide
  rcases family_descends (prefixWord ++ tailWord_7770140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7770149 : List Nat := [1, 3, 1, 2, 2, 3, 1, 2, 2, 2, 4]
def baseStart_7770149 : Nat := 118140960795 + 7770149 * 2 ^ 59
def prefixEnd_7770149 : Nat := 4983230072969 + 3 ^ 40 * 7770149 * 2
def baseEnd_7770149 : Nat := 3989821194052224990003241

theorem tailTrace_7770149 : CollatzResearch.WordTrace tailWord_7770149 prefixEnd_7770149 3989821194052224990003241 := by
  unfold tailWord_7770149
  simp only [CollatzResearch.WordTrace]
  refine ⟨283400616327084683643593501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188933744218056455762395667 283400616327084683643593501)
  ·
    refine ⟨106275231122656756366347563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 283400616327084683643593501 106275231122656756366347563)
    ·
      refine ⟨159412846683985134549521345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106275231122656756366347563 159412846683985134549521345)
      ·
        refine ⟨119559635012988850912141009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 159412846683985134549521345 119559635012988850912141009)
        ·
          refine ⟨89669726259741638184105757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 119559635012988850912141009 89669726259741638184105757)
          ·
            refine ⟨33626147347403114319039659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 89669726259741638184105757 33626147347403114319039659)
            ·
              refine ⟨50439221021104671478559489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33626147347403114319039659 50439221021104671478559489)
              ·
                refine ⟨37829415765828503608919617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50439221021104671478559489 37829415765828503608919617)
                ·
                  refine ⟨28372061824371377706689713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37829415765828503608919617 28372061824371377706689713)
                  ·
                    refine ⟨21279046368278533280017285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 28372061824371377706689713 21279046368278533280017285)
                    ·
                      refine ⟨3989821194052224990003241, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21279046368278533280017285 3989821194052224990003241)
                      ·
                        rfl

theorem cell23_7770149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 3, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 3, 1, 2, 2, 2, 4].length) (baseStart_7770149 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7770149 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7770149 prefixEnd_7770149 := by exact prefixLift 7770149
  have htrace : WordTrace (prefixWord ++ tailWord_7770149) baseStart_7770149 baseEnd_7770149 := by
    simpa [prefixWord, tailWord_7770149, baseEnd_7770149] using wordTrace_append hprefix tailTrace_7770149
  have hstable : (prefixWord ++ tailWord_7770149).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7770149).length < 2 ^ (prefixWord ++ tailWord_7770149).sum := by decide
  have hdescent : baseEnd_7770149 < baseStart_7770149 := by decide
  rcases family_descends (prefixWord ++ tailWord_7770149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7770166 : List Nat := [5, 1, 2, 1, 1, 1, 1, 3, 2, 2, 4]
def baseStart_7770166 : Nat := 118140960795 + 7770166 * 2 ^ 59
def prefixEnd_7770166 : Nat := 4983230072969 + 3 ^ 40 * 7770166 * 2
def baseEnd_7770166 : Nat := 3989829923223351423490663

theorem tailTrace_7770166 : CollatzResearch.WordTrace tailWord_7770166 prefixEnd_7770166 3989829923223351423490663 := by
  unfold tailWord_7770166
  simp only [CollatzResearch.WordTrace]
  refine ⟨17712577273001443471685147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 188934157578682063697974901 17712577273001443471685147)
  ·
    refine ⟨26568865909502165207527721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17712577273001443471685147 26568865909502165207527721)
    ·
      refine ⟨19926649432126623905645791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26568865909502165207527721 19926649432126623905645791)
      ·
        refine ⟨29889974148189935858468687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19926649432126623905645791 29889974148189935858468687)
        ·
          refine ⟨44834961222284903787703031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29889974148189935858468687 44834961222284903787703031)
          ·
            refine ⟨67252441833427355681554547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44834961222284903787703031 67252441833427355681554547)
            ·
              refine ⟨100878662750141033522331821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67252441833427355681554547 100878662750141033522331821)
              ·
                refine ⟨37829498531302887570874433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 100878662750141033522331821 37829498531302887570874433)
                ·
                  refine ⟨28372123898477165678155825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37829498531302887570874433 28372123898477165678155825)
                  ·
                    refine ⟨21279092923857874258616869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 28372123898477165678155825 21279092923857874258616869)
                    ·
                      refine ⟨3989829923223351423490663, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21279092923857874258616869 3989829923223351423490663)
                      ·
                        rfl

theorem cell23_7770166_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 1, 3, 2, 2, 4].length) (baseStart_7770166 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7770166 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7770166 prefixEnd_7770166 := by exact prefixLift 7770166
  have htrace : WordTrace (prefixWord ++ tailWord_7770166) baseStart_7770166 baseEnd_7770166 := by
    simpa [prefixWord, tailWord_7770166, baseEnd_7770166] using wordTrace_append hprefix tailTrace_7770166
  have hstable : (prefixWord ++ tailWord_7770166).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7770166).length < 2 ^ (prefixWord ++ tailWord_7770166).sum := by decide
  have hdescent : baseEnd_7770166 < baseStart_7770166 := by decide
  rcases family_descends (prefixWord ++ tailWord_7770166) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7770196 : List Nat := [2, 4, 1, 1, 1, 1, 1, 2, 1, 7, 2]
def baseStart_7770196 : Nat := 118140960795 + 7770196 * 2 ^ 59
def prefixEnd_7770196 : Nat := 4983230072969 + 3 ^ 40 * 7770196 * 2
def baseEnd_7770196 : Nat := 3989845327642986306115525

theorem tailTrace_7770196 : CollatzResearch.WordTrace tailWord_7770196 prefixEnd_7770196 3989845327642986306115525 := by
  unfold tailWord_7770196
  simp only [CollatzResearch.WordTrace]
  refine ⟨141701165278957205335277221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 188934887038609607113702961 141701165278957205335277221)
  ·
    refine ⟨26568968489804476000364479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 141701165278957205335277221 26568968489804476000364479)
    ·
      refine ⟨39853452734706714000546719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26568968489804476000364479 39853452734706714000546719)
      ·
        refine ⟨59780179102060071000820079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39853452734706714000546719 59780179102060071000820079)
        ·
          refine ⟨89670268653090106501230119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59780179102060071000820079 89670268653090106501230119)
          ·
            refine ⟨134505402979635159751845179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89670268653090106501230119 134505402979635159751845179)
            ·
              refine ⟨201758104469452739627767769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 134505402979635159751845179 201758104469452739627767769)
              ·
                refine ⟨151318578352089554720825827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 201758104469452739627767769 151318578352089554720825827)
                ·
                  refine ⟨226977867528134332081238741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 151318578352089554720825827 226977867528134332081238741)
                  ·
                    refine ⟨5319793770190648408154033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 226977867528134332081238741 5319793770190648408154033)
                    ·
                      refine ⟨3989845327642986306115525, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5319793770190648408154033 3989845327642986306115525)
                      ·
                        rfl

theorem cell23_7770196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 1, 2, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 1, 2, 1, 7, 2].length) (baseStart_7770196 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7770196 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7770196 prefixEnd_7770196 := by exact prefixLift 7770196
  have htrace : WordTrace (prefixWord ++ tailWord_7770196) baseStart_7770196 baseEnd_7770196 := by
    simpa [prefixWord, tailWord_7770196, baseEnd_7770196] using wordTrace_append hprefix tailTrace_7770196
  have hstable : (prefixWord ++ tailWord_7770196).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7770196).length < 2 ^ (prefixWord ++ tailWord_7770196).sum := by decide
  have hdescent : baseEnd_7770196 < baseStart_7770196 := by decide
  rcases family_descends (prefixWord ++ tailWord_7770196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7770210 : List Nat := [3, 3, 2, 2, 3, 1, 1, 1, 7]
def baseStart_7770210 : Nat := 118140960795 + 7770210 * 2 ^ 59
def prefixEnd_7770210 : Nat := 4983230072969 + 3 ^ 40 * 7770210 * 2
def baseEnd_7770210 : Nat := 443316946263572139037829

theorem tailTrace_7770210 : CollatzResearch.WordTrace tailWord_7770210 prefixEnd_7770210 443316946263572139037829 := by
  unfold tailWord_7770210
  simp only [CollatzResearch.WordTrace]
  refine ⟨70850710294965922765391021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 188935227453242460707709389 70850710294965922765391021)
  ·
    refine ⟨26569016360612221037021633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 70850710294965922765391021 26569016360612221037021633)
    ·
      refine ⟨19926762270459165777766225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26569016360612221037021633 19926762270459165777766225)
      ·
        refine ⟨14945071702844374333324669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19926762270459165777766225 14945071702844374333324669)
        ·
          refine ⟨5604401888566640374996751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14945071702844374333324669 5604401888566640374996751)
          ·
            refine ⟨8406602832849960562495127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5604401888566640374996751 8406602832849960562495127)
            ·
              refine ⟨12609904249274940843742691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8406602832849960562495127 12609904249274940843742691)
              ·
                refine ⟨18914856373912411265614037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12609904249274940843742691 18914856373912411265614037)
                ·
                  refine ⟨443316946263572139037829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18914856373912411265614037 443316946263572139037829)
                  ·
                    rfl

theorem cell23_7770210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 3, 1, 1, 1, 7].length) (baseStart_7770210 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7770210 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7770210 prefixEnd_7770210 := by exact prefixLift 7770210
  have htrace : WordTrace (prefixWord ++ tailWord_7770210) baseStart_7770210 baseEnd_7770210 := by
    simpa [prefixWord, tailWord_7770210, baseEnd_7770210] using wordTrace_append hprefix tailTrace_7770210
  have hstable : (prefixWord ++ tailWord_7770210).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7770210).length < 2 ^ (prefixWord ++ tailWord_7770210).sum := by decide
  have hdescent : baseEnd_7770210 < baseStart_7770210 := by decide
  rcases family_descends (prefixWord ++ tailWord_7770210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7770296 : List Nat := [2, 1, 2, 1, 2, 1, 4, 4, 1, 5]
def baseStart_7770296 : Nat := 118140960795 + 7770296 * 2 ^ 59
def prefixEnd_7770296 : Nat := 4983230072969 + 3 ^ 40 * 7770296 * 2
def baseEnd_7770296 : Nat := 1329965558569478638288355

theorem tailTrace_7770296 : CollatzResearch.WordTrace tailWord_7770296 prefixEnd_7770296 1329965558569478638288355 := by
  unfold tailWord_7770296
  simp only [CollatzResearch.WordTrace]
  refine ⟨141702988928776063874597371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 188937318571701418499463161 141702988928776063874597371)
  ·
    refine ⟨212554483393164095811896057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141702988928776063874597371 212554483393164095811896057)
    ·
      refine ⟨159415862544873071858922043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 212554483393164095811896057 159415862544873071858922043)
      ·
        refine ⟨239123793817309607788383065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 159415862544873071858922043 239123793817309607788383065)
        ·
          refine ⟨179342845362982205841287299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 239123793817309607788383065 179342845362982205841287299)
          ·
            refine ⟨269014268044473308761930949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 179342845362982205841287299 269014268044473308761930949)
            ·
              refine ⟨50440175258338745392862053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 269014268044473308761930949 50440175258338745392862053)
              ·
                refine ⟨9457532860938514761161635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 50440175258338745392862053 9457532860938514761161635)
                ·
                  refine ⟨14186299291407772141742453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9457532860938514761161635 14186299291407772141742453)
                  ·
                    refine ⟨1329965558569478638288355, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14186299291407772141742453 1329965558569478638288355)
                    ·
                      rfl

theorem cell23_7770296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 4, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 4, 4, 1, 5].length) (baseStart_7770296 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7770296 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7770296 prefixEnd_7770296 := by exact prefixLift 7770296
  have htrace : WordTrace (prefixWord ++ tailWord_7770296) baseStart_7770296 baseEnd_7770296 := by
    simpa [prefixWord, tailWord_7770296, baseEnd_7770296] using wordTrace_append hprefix tailTrace_7770296
  have hstable : (prefixWord ++ tailWord_7770296).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7770296).length < 2 ^ (prefixWord ++ tailWord_7770296).sum := by decide
  have hdescent : baseEnd_7770296 < baseStart_7770296 := by decide
  rcases family_descends (prefixWord ++ tailWord_7770296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7770336 : List Nat := [2, 1, 1, 3, 1, 3, 3, 2, 1, 1, 5]
def baseStart_7770336 : Nat := 118140960795 + 7770336 * 2 ^ 59
def prefixEnd_7770336 : Nat := 4983230072969 + 3 ^ 40 * 7770336 * 2
def baseEnd_7770336 : Nat := 3989917214934615758364881

theorem tailTrace_7770336 : CollatzResearch.WordTrace tailWord_7770336 prefixEnd_7770336 3989917214934615758364881 := by
  unfold tailWord_7770336
  simp only [CollatzResearch.WordTrace]
  refine ⟨141703718388703607290325431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 188938291184938143053767241 141703718388703607290325431)
  ·
    refine ⟨212555577583055410935488147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141703718388703607290325431 212555577583055410935488147)
    ·
      refine ⟨318833366374583116403232221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 212555577583055410935488147 318833366374583116403232221)
      ·
        refine ⟨119562512390468668651212083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 318833366374583116403232221 119562512390468668651212083)
        ·
          refine ⟨179343768585703002976818125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 119562512390468668651212083 179343768585703002976818125)
          ·
            refine ⟨67253913219638626116306797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 179343768585703002976818125 67253913219638626116306797)
            ·
              refine ⟨25220217457364484793615049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 67253913219638626116306797 25220217457364484793615049)
              ·
                refine ⟨18915163093023363595211287, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25220217457364484793615049 18915163093023363595211287)
                ·
                  refine ⟨28372744639535045392816931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18915163093023363595211287 28372744639535045392816931)
                  ·
                    refine ⟨42559116959302568089225397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 28372744639535045392816931 42559116959302568089225397)
                    ·
                      refine ⟨3989917214934615758364881, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 42559116959302568089225397 3989917214934615758364881)
                      ·
                        rfl

theorem cell23_7770336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 3, 2, 1, 1, 5].length) (baseStart_7770336 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7770336 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7770336 prefixEnd_7770336 := by exact prefixLift 7770336
  have htrace : WordTrace (prefixWord ++ tailWord_7770336) baseStart_7770336 baseEnd_7770336 := by
    simpa [prefixWord, tailWord_7770336, baseEnd_7770336] using wordTrace_append hprefix tailTrace_7770336
  have hstable : (prefixWord ++ tailWord_7770336).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7770336).length < 2 ^ (prefixWord ++ tailWord_7770336).sum := by decide
  have hdescent : baseEnd_7770336 < baseStart_7770336 := by decide
  rcases family_descends (prefixWord ++ tailWord_7770336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7770343 : List Nat := [1, 1, 5, 3, 1, 1, 3, 1, 1, 6]
def baseStart_7770343 : Nat := 118140960795 + 7770343 * 2 ^ 59
def prefixEnd_7770343 : Nat := 4983230072969 + 3 ^ 40 * 7770343 * 2
def baseEnd_7770343 : Nat := 1329973603099732410325783

theorem tailTrace_7770343 : CollatzResearch.WordTrace tailWord_7770343 prefixEnd_7770343 1329973603099732410325783 := by
  unfold tailWord_7770343
  simp only [CollatzResearch.WordTrace]
  refine ⟨283407692088381854776155683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188938461392254569850770455 283407692088381854776155683)
  ·
    refine ⟨425111538132572782164233525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 283407692088381854776155683 425111538132572782164233525)
    ·
      refine ⟨39854206699928698327896893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 425111538132572782164233525 39854206699928698327896893)
      ·
        refine ⟨14945327512473261872961335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39854206699928698327896893 14945327512473261872961335)
        ·
          refine ⟨22417991268709892809442003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14945327512473261872961335 22417991268709892809442003)
          ·
            refine ⟨33626986903064839214163005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22417991268709892809442003 33626986903064839214163005)
            ·
              refine ⟨12610120088649314705311127, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33626986903064839214163005 12610120088649314705311127)
              ·
                refine ⟨18915180132973972057966691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12610120088649314705311127 18915180132973972057966691)
                ·
                  refine ⟨28372770199460958086950037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18915180132973972057966691 28372770199460958086950037)
                  ·
                    refine ⟨1329973603099732410325783, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28372770199460958086950037 1329973603099732410325783)
                    ·
                      rfl

theorem cell23_7770343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 1, 3, 1, 1, 6].length) (baseStart_7770343 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7770343 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7770343 prefixEnd_7770343 := by exact prefixLift 7770343
  have htrace : WordTrace (prefixWord ++ tailWord_7770343) baseStart_7770343 baseEnd_7770343 := by
    simpa [prefixWord, tailWord_7770343, baseEnd_7770343] using wordTrace_append hprefix tailTrace_7770343
  have hstable : (prefixWord ++ tailWord_7770343).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7770343).length < 2 ^ (prefixWord ++ tailWord_7770343).sum := by decide
  have hdescent : baseEnd_7770343 < baseStart_7770343 := by decide
  rcases family_descends (prefixWord ++ tailWord_7770343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7770346 : List Nat := [3, 1, 3, 1, 1, 2, 3, 1, 1, 1, 6]
def baseStart_7770346 : Nat := 118140960795 + 7770346 * 2 ^ 59
def prefixEnd_7770346 : Nat := 4983230072969 + 3 ^ 40 * 7770346 * 2
def baseEnd_7770346 : Nat := 3989922349741160719239835

theorem tailTrace_7770346 : CollatzResearch.WordTrace tailWord_7770346 prefixEnd_7770346 3989922349741160719239835 := by
  unfold tailWord_7770346
  simp only [CollatzResearch.WordTrace]
  refine ⟨70851950376842746572128723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 188938534338247324192343261 70851950376842746572128723)
  ·
    refine ⟨106277925565264119858193085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70851950376842746572128723 106277925565264119858193085)
    ·
      refine ⟨39854222086974044946822407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 106277925565264119858193085 39854222086974044946822407)
      ·
        refine ⟨59781333130461067420233611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39854222086974044946822407 59781333130461067420233611)
        ·
          refine ⟨89671999695691601130350417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59781333130461067420233611 89671999695691601130350417)
          ·
            refine ⟨67253999771768700847762813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 89671999695691601130350417 67253999771768700847762813)
            ·
              refine ⟨25220249914413262817911055, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 67253999771768700847762813 25220249914413262817911055)
              ·
                refine ⟨37830374871619894226866583, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25220249914413262817911055 37830374871619894226866583)
                ·
                  refine ⟨56745562307429841340299875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37830374871619894226866583 56745562307429841340299875)
                  ·
                    refine ⟨85118343461144762010449813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 56745562307429841340299875 85118343461144762010449813)
                    ·
                      refine ⟨3989922349741160719239835, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 85118343461144762010449813 3989922349741160719239835)
                      ·
                        rfl

theorem cell23_7770346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 3, 1, 1, 1, 6].length) (baseStart_7770346 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7770346 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7770346 prefixEnd_7770346 := by exact prefixLift 7770346
  have htrace : WordTrace (prefixWord ++ tailWord_7770346) baseStart_7770346 baseEnd_7770346 := by
    simpa [prefixWord, tailWord_7770346, baseEnd_7770346] using wordTrace_append hprefix tailTrace_7770346
  have hstable : (prefixWord ++ tailWord_7770346).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7770346).length < 2 ^ (prefixWord ++ tailWord_7770346).sum := by decide
  have hdescent : baseEnd_7770346 < baseStart_7770346 := by decide
  rcases family_descends (prefixWord ++ tailWord_7770346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7770353 : List Nat := [1, 2, 2, 2, 2, 1, 3, 4, 1, 2, 3]
def baseStart_7770353 : Nat := 118140960795 + 7770353 * 2 ^ 59
def prefixEnd_7770353 : Nat := 4983230072969 + 3 ^ 40 * 7770353 * 2
def baseEnd_7770353 : Nat := 3989925944105742191852303

theorem tailTrace_7770353 : CollatzResearch.WordTrace tailWord_7770353 prefixEnd_7770353 3989925944105742191852303 := by
  unfold tailWord_7770353
  simp only [CollatzResearch.WordTrace]
  refine ⟨283408056818345626484019713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188938704545563750989346475 283408056818345626484019713)
  ·
    refine ⟨212556042613759219863014785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 283408056818345626484019713 212556042613759219863014785)
    ·
      refine ⟨159417031960319414897261089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 212556042613759219863014785 159417031960319414897261089)
      ·
        refine ⟨119562773970239561172945817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 159417031960319414897261089 119562773970239561172945817)
        ·
          refine ⟨89672080477679670879709363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 119562773970239561172945817 89672080477679670879709363)
          ·
            refine ⟨134508120716519506319564045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89672080477679670879709363 134508120716519506319564045)
            ·
              refine ⟨50440545268694814869836517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 134508120716519506319564045 50440545268694814869836517)
              ·
                refine ⟨9457602237880277788094347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 50440545268694814869836517 9457602237880277788094347)
                ·
                  refine ⟨14186403356820416682141521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9457602237880277788094347 14186403356820416682141521)
                  ·
                    refine ⟨10639802517615312511606141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14186403356820416682141521 10639802517615312511606141)
                    ·
                      refine ⟨3989925944105742191852303, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10639802517615312511606141 3989925944105742191852303)
                      ·
                        rfl

theorem cell23_7770353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 3, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 3, 4, 1, 2, 3].length) (baseStart_7770353 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7770353 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7770353 prefixEnd_7770353 := by exact prefixLift 7770353
  have htrace : WordTrace (prefixWord ++ tailWord_7770353) baseStart_7770353 baseEnd_7770353 := by
    simpa [prefixWord, tailWord_7770353, baseEnd_7770353] using wordTrace_append hprefix tailTrace_7770353
  have hstable : (prefixWord ++ tailWord_7770353).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7770353).length < 2 ^ (prefixWord ++ tailWord_7770353).sum := by decide
  have hdescent : baseEnd_7770353 < baseStart_7770353 := by decide
  rcases family_descends (prefixWord ++ tailWord_7770353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7770370 : List Nat := [3, 4, 1, 1, 2, 2, 2, 1, 1, 1, 5]
def baseStart_7770370 : Nat := 118140960795 + 7770370 * 2 ^ 59
def prefixEnd_7770370 : Nat := 4983230072969 + 3 ^ 40 * 7770370 * 2
def baseEnd_7770370 : Nat := 3989934673276868625339725

theorem tailTrace_7770370 : CollatzResearch.WordTrace tailWord_7770370 prefixEnd_7770370 3989934673276868625339725 := by
  unfold tailWord_7770370
  simp only [CollatzResearch.WordTrace]
  refine ⟨70852169214821009596847141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 188939117906189358924925709 70852169214821009596847141)
  ·
    refine ⟨13284781727778939299408839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 70852169214821009596847141 13284781727778939299408839)
    ·
      refine ⟨19927172591668408949113259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13284781727778939299408839 19927172591668408949113259)
      ·
        refine ⟨29890758887502613423669889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19927172591668408949113259 29890758887502613423669889)
        ·
          refine ⟨22418069165626960067752417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29890758887502613423669889 22418069165626960067752417)
          ·
            refine ⟨16813551874220220050814313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22418069165626960067752417 16813551874220220050814313)
            ·
              refine ⟨12610163905665165038110735, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16813551874220220050814313 12610163905665165038110735)
              ·
                refine ⟨18915245858497747557166103, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12610163905665165038110735 18915245858497747557166103)
                ·
                  refine ⟨28372868787746621335749155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18915245858497747557166103 28372868787746621335749155)
                  ·
                    refine ⟨42559303181619932003623733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 28372868787746621335749155 42559303181619932003623733)
                    ·
                      refine ⟨3989934673276868625339725, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 42559303181619932003623733 3989934673276868625339725)
                      ·
                        rfl

theorem cell23_7770370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 2, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 2, 2, 1, 1, 1, 5].length) (baseStart_7770370 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7770370 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7770370 prefixEnd_7770370 := by exact prefixLift 7770370
  have htrace : WordTrace (prefixWord ++ tailWord_7770370) baseStart_7770370 baseEnd_7770370 := by
    simpa [prefixWord, tailWord_7770370, baseEnd_7770370] using wordTrace_append hprefix tailTrace_7770370
  have hstable : (prefixWord ++ tailWord_7770370).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7770370).length < 2 ^ (prefixWord ++ tailWord_7770370).sum := by decide
  have hdescent : baseEnd_7770370 < baseStart_7770370 := by decide
  rcases family_descends (prefixWord ++ tailWord_7770370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7770394 : List Nat := [3, 1, 1, 3, 5, 1, 2, 1, 2, 4]
def baseStart_7770394 : Nat := 118140960795 + 7770394 * 2 ^ 59
def prefixEnd_7770394 : Nat := 4983230072969 + 3 ^ 40 * 7770394 * 2
def baseEnd_7770394 : Nat := 1329982332270858843813205

theorem tailTrace_7770394 : CollatzResearch.WordTrace tailWord_7770394 prefixEnd_7770394 1329982332270858843813205 := by
  unfold tailWord_7770394
  simp only [CollatzResearch.WordTrace]
  refine ⟨70852388052799272621565559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 188939701474131393657508157 70852388052799272621565559)
  ·
    refine ⟨106278582079198908932348339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70852388052799272621565559 106278582079198908932348339)
    ·
      refine ⟨159417873118798363398522509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106278582079198908932348339 159417873118798363398522509)
      ·
        refine ⟨59781702419549386274445941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 159417873118798363398522509 59781702419549386274445941)
        ·
          refine ⟨5604534601832754963229307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 59781702419549386274445941 5604534601832754963229307)
          ·
            refine ⟨8406801902749132444843961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5604534601832754963229307 8406801902749132444843961)
            ·
              refine ⟨6305101427061849333632971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8406801902749132444843961 6305101427061849333632971)
              ·
                refine ⟨9457652140592774000449457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6305101427061849333632971 9457652140592774000449457)
                ·
                  refine ⟨7093239105444580500337093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9457652140592774000449457 7093239105444580500337093)
                  ·
                    refine ⟨1329982332270858843813205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7093239105444580500337093 1329982332270858843813205)
                    ·
                      rfl

theorem cell23_7770394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 5, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 5, 1, 2, 1, 2, 4].length) (baseStart_7770394 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7770394 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7770394 prefixEnd_7770394 := by exact prefixLift 7770394
  have htrace : WordTrace (prefixWord ++ tailWord_7770394) baseStart_7770394 baseEnd_7770394 := by
    simpa [prefixWord, tailWord_7770394, baseEnd_7770394] using wordTrace_append hprefix tailTrace_7770394
  have hstable : (prefixWord ++ tailWord_7770394).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7770394).length < 2 ^ (prefixWord ++ tailWord_7770394).sum := by decide
  have hdescent : baseEnd_7770394 < baseStart_7770394 := by decide
  rcases family_descends (prefixWord ++ tailWord_7770394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7770440 : List Nat := [2, 1, 3, 1, 1, 2, 2, 3, 4, 2, 2]
def baseStart_7770440 : Nat := 118140960795 + 7770440 * 2 ^ 59
def prefixEnd_7770440 : Nat := 4983230072969 + 3 ^ 40 * 7770440 * 2
def baseEnd_7770440 : Nat := 3989970616922683351464403

theorem tailTrace_7770440 : CollatzResearch.WordTrace tailWord_7770440 prefixEnd_7770440 3989970616922683351464403 := by
  unfold tailWord_7770440
  simp only [CollatzResearch.WordTrace]
  refine ⟨141705614984515220171218387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 188940819979353626894957849 141705614984515220171218387)
  ·
    refine ⟨212558422476772830256827581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141705614984515220171218387 212558422476772830256827581)
    ·
      refine ⟨79709408428789811346310343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 212558422476772830256827581 79709408428789811346310343)
      ·
        refine ⟨119564112643184717019465515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79709408428789811346310343 119564112643184717019465515)
        ·
          refine ⟨179346168964777075529198273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 119564112643184717019465515 179346168964777075529198273)
          ·
            refine ⟨134509626723582806646898705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 179346168964777075529198273 134509626723582806646898705)
            ·
              refine ⟨100882220042687104985174029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 134509626723582806646898705 100882220042687104985174029)
              ·
                refine ⟨37830832516007664369440261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 100882220042687104985174029 37830832516007664369440261)
                ·
                  refine ⟨7093281096751437069270049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 37830832516007664369440261 7093281096751437069270049)
                  ·
                    refine ⟨5319960822563577801952537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7093281096751437069270049 5319960822563577801952537)
                    ·
                      refine ⟨3989970616922683351464403, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5319960822563577801952537 3989970616922683351464403)
                      ·
                        rfl

theorem cell23_7770440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 2, 3, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 2, 3, 4, 2, 2].length) (baseStart_7770440 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7770440 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7770440 prefixEnd_7770440 := by exact prefixLift 7770440
  have htrace : WordTrace (prefixWord ++ tailWord_7770440) baseStart_7770440 baseEnd_7770440 := by
    simpa [prefixWord, tailWord_7770440, baseEnd_7770440] using wordTrace_append hprefix tailTrace_7770440
  have hstable : (prefixWord ++ tailWord_7770440).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7770440).length < 2 ^ (prefixWord ++ tailWord_7770440).sum := by decide
  have hdescent : baseEnd_7770440 < baseStart_7770440 := by decide
  rcases family_descends (prefixWord ++ tailWord_7770440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7770480 : List Nat := [2, 1, 1, 1, 4, 4, 2, 3, 5]
def baseStart_7770480 : Nat := 118140960795 + 7770480 * 2 ^ 59
def prefixEnd_7770480 : Nat := 4983230072969 + 3 ^ 40 * 7770480 * 2
def baseEnd_7770480 : Nat := 443332350683207021662691

theorem tailTrace_7770480 : CollatzResearch.WordTrace tailWord_7770480 prefixEnd_7770480 443332350683207021662691 := by
  unfold tailWord_7770480
  simp only [CollatzResearch.WordTrace]
  refine ⟨141706344444442763586946447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 188941792592590351449261929 141706344444442763586946447)
  ·
    refine ⟨212559516666664145380419671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141706344444442763586946447 212559516666664145380419671)
    ·
      refine ⟨318839274999996218070629507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 212559516666664145380419671 318839274999996218070629507)
      ·
        refine ⟨478258912499994327105944261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 318839274999996218070629507 478258912499994327105944261)
        ·
          refine ⟨89673546093748936332364549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 478258912499994327105944261 89673546093748936332364549)
          ·
            refine ⟨16813789892577925562318353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 89673546093748936332364549 16813789892577925562318353)
            ·
              refine ⟨12610342419433444171738765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16813789892577925562318353 12610342419433444171738765)
              ·
                refine ⟨4728878407287541564402037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12610342419433444171738765 4728878407287541564402037)
                ·
                  refine ⟨443332350683207021662691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4728878407287541564402037 443332350683207021662691)
                  ·
                    rfl

theorem cell23_7770480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 4, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 4, 2, 3, 5].length) (baseStart_7770480 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7770480 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7770480 prefixEnd_7770480 := by exact prefixLift 7770480
  have htrace : WordTrace (prefixWord ++ tailWord_7770480) baseStart_7770480 baseEnd_7770480 := by
    simpa [prefixWord, tailWord_7770480, baseEnd_7770480] using wordTrace_append hprefix tailTrace_7770480
  have hstable : (prefixWord ++ tailWord_7770480).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7770480).length < 2 ^ (prefixWord ++ tailWord_7770480).sum := by decide
  have hdescent : baseEnd_7770480 < baseStart_7770480 := by decide
  rcases family_descends (prefixWord ++ tailWord_7770480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7770483 : List Nat := [1, 1, 1, 2, 2, 1, 2, 2, 4, 5, 2]
def baseStart_7770483 : Nat := 118140960795 + 7770483 * 2 ^ 59
def prefixEnd_7770483 : Nat := 4983230072969 + 3 ^ 40 * 7770483 * 2
def baseEnd_7770483 : Nat := 3989992696590826683226705

theorem tailTrace_7770483 : CollatzResearch.WordTrace tailWord_7770483 prefixEnd_7770483 3989992696590826683226705 := by
  unfold tailWord_7770483
  simp only [CollatzResearch.WordTrace]
  refine ⟨283412798307874658686252103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188941865538583105790834735 283412798307874658686252103)
  ·
    refine ⟨425119197461811988029378155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 283412798307874658686252103 425119197461811988029378155)
    ·
      refine ⟨637678796192717982044067233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 425119197461811988029378155 637678796192717982044067233)
      ·
        refine ⟨478259097144538486533050425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 637678796192717982044067233 478259097144538486533050425)
        ·
          refine ⟨358694322858403864899787819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 478259097144538486533050425 358694322858403864899787819)
          ·
            refine ⟨538041484287605797349681729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 358694322858403864899787819 538041484287605797349681729)
            ·
              refine ⟨403531113215704348012261297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 538041484287605797349681729 403531113215704348012261297)
              ·
                refine ⟨302648334911778261009195973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 403531113215704348012261297 302648334911778261009195973)
                ·
                  refine ⟨56746562795958423939224245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 302648334911778261009195973 56746562795958423939224245)
                  ·
                    refine ⟨5319990262121102244302273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 56746562795958423939224245 5319990262121102244302273)
                    ·
                      refine ⟨3989992696590826683226705, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5319990262121102244302273 3989992696590826683226705)
                      ·
                        rfl

theorem cell23_7770483_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 2, 2, 4, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 2, 2, 4, 5, 2].length) (baseStart_7770483 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7770483 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7770483 prefixEnd_7770483 := by exact prefixLift 7770483
  have htrace : WordTrace (prefixWord ++ tailWord_7770483) baseStart_7770483 baseEnd_7770483 := by
    simpa [prefixWord, tailWord_7770483, baseEnd_7770483] using wordTrace_append hprefix tailTrace_7770483
  have hstable : (prefixWord ++ tailWord_7770483).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7770483).length < 2 ^ (prefixWord ++ tailWord_7770483).sum := by decide
  have hdescent : baseEnd_7770483 < baseStart_7770483 := by decide
  rcases family_descends (prefixWord ++ tailWord_7770483) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7770530 : List Nat := [3, 3, 1, 2, 1, 1, 2, 3, 2, 1, 4]
def baseStart_7770530 : Nat := 118140960795 + 7770530 * 2 ^ 59
def prefixEnd_7770530 : Nat := 4983230072969 + 3 ^ 40 * 7770530 * 2
def baseEnd_7770530 : Nat := 3990016830181587999338989

theorem tailTrace_7770530 : CollatzResearch.WordTrace tailWord_7770530 prefixEnd_7770530 3990016830181587999338989 := by
  unfold tailWord_7770530
  simp only [CollatzResearch.WordTrace]
  refine ⟨70853628134676096428303261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 188943008359136257142142029 70853628134676096428303261)
  ·
    refine ⟨26570110550503536160613723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 70853628134676096428303261 26570110550503536160613723)
    ·
      refine ⟨39855165825755304240920585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26570110550503536160613723 39855165825755304240920585)
      ·
        refine ⟨29891374369316478180690439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39855165825755304240920585 29891374369316478180690439)
        ·
          refine ⟨44837061553974717271035659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29891374369316478180690439 44837061553974717271035659)
          ·
            refine ⟨67255592330962075906553489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44837061553974717271035659 67255592330962075906553489)
            ·
              refine ⟨50441694248221556929915117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 67255592330962075906553489 50441694248221556929915117)
              ·
                refine ⟨18915635343083083848718169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 50441694248221556929915117 18915635343083083848718169)
                ·
                  refine ⟨14186726507312312886538627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18915635343083083848718169 14186726507312312886538627)
                  ·
                    refine ⟨21280089760968469329807941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14186726507312312886538627 21280089760968469329807941)
                    ·
                      refine ⟨3990016830181587999338989, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21280089760968469329807941 3990016830181587999338989)
                      ·
                        rfl

theorem cell23_7770530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 2, 3, 2, 1, 4].length) (baseStart_7770530 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7770530 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7770530 prefixEnd_7770530 := by exact prefixLift 7770530
  have htrace : WordTrace (prefixWord ++ tailWord_7770530) baseStart_7770530 baseEnd_7770530 := by
    simpa [prefixWord, tailWord_7770530, baseEnd_7770530] using wordTrace_append hprefix tailTrace_7770530
  have hstable : (prefixWord ++ tailWord_7770530).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7770530).length < 2 ^ (prefixWord ++ tailWord_7770530).sum := by decide
  have hdescent : baseEnd_7770530 < baseStart_7770530 := by decide
  rcases family_descends (prefixWord ++ tailWord_7770530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7770533 : List Nat := [1, 3, 1, 2, 1, 1, 3, 3, 1, 4, 3]
def baseStart_7770533 : Nat := 118140960795 + 7770533 * 2 ^ 59
def prefixEnd_7770533 : Nat := 4983230072969 + 3 ^ 40 * 7770533 * 2
def baseEnd_7770533 : Nat := 3990018370623551487601475

theorem tailTrace_7770533 : CollatzResearch.WordTrace tailWord_7770533 prefixEnd_7770533 3990018370623551487601475 := by
  unfold tailWord_7770533
  simp only [CollatzResearch.WordTrace]
  refine ⟨283414621957693517225572253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188943081305129011483714835 283414621957693517225572253)
  ·
    refine ⟨106280483234135068959589595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 283414621957693517225572253 106280483234135068959589595)
    ·
      refine ⟨159420724851202603439384393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106280483234135068959589595 159420724851202603439384393)
      ·
        refine ⟨119565543638401952579538295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 159420724851202603439384393 119565543638401952579538295)
        ·
          refine ⟨179348315457602928869307443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 119565543638401952579538295 179348315457602928869307443)
          ·
            refine ⟨269022473186404393303961165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 179348315457602928869307443 269022473186404393303961165)
            ·
              refine ⟨100883427444901647488985437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 269022473186404393303961165 100883427444901647488985437)
              ·
                refine ⟨37831285291838117808369539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 100883427444901647488985437 37831285291838117808369539)
                ·
                  refine ⟨56746927937757176712554309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37831285291838117808369539 56746927937757176712554309)
                  ·
                    refine ⟨10640048988329470633603933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 56746927937757176712554309 10640048988329470633603933)
                    ·
                      refine ⟨3990018370623551487601475, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10640048988329470633603933 3990018370623551487601475)
                      ·
                        rfl

theorem cell23_7770533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 3, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 3, 3, 1, 4, 3].length) (baseStart_7770533 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7770533 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7770533 prefixEnd_7770533 := by exact prefixLift 7770533
  have htrace : WordTrace (prefixWord ++ tailWord_7770533) baseStart_7770533 baseEnd_7770533 := by
    simpa [prefixWord, tailWord_7770533, baseEnd_7770533] using wordTrace_append hprefix tailTrace_7770533
  have hstable : (prefixWord ++ tailWord_7770533).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7770533).length < 2 ^ (prefixWord ++ tailWord_7770533).sum := by decide
  have hdescent : baseEnd_7770533 < baseStart_7770533 := by decide
  rcases family_descends (prefixWord ++ tailWord_7770533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7770553 : List Nat := [1, 2, 1, 4, 3, 1, 2, 1, 8]
def baseStart_7770553 : Nat := 118140960795 + 7770553 * 2 ^ 59
def prefixEnd_7770553 : Nat := 4983230072969 + 3 ^ 40 * 7770553 * 2
def baseEnd_7770553 : Nat := 443336515581849045483487

theorem tailTrace_7770553 : CollatzResearch.WordTrace tailWord_7770553 prefixEnd_7770553 443336515581849045483487 := by
  unfold tailWord_7770553
  simp only [CollatzResearch.WordTrace]
  refine ⟨283415351417621060641300313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188943567611747373760866875 283415351417621060641300313)
  ·
    refine ⟨212561513563215795480975235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 283415351417621060641300313 212561513563215795480975235)
    ·
      refine ⟨318842270344823693221462853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 212561513563215795480975235 318842270344823693221462853)
      ·
        refine ⟨59782925689654442479024285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 318842270344823693221462853 59782925689654442479024285)
        ·
          refine ⟨22418597133620415929634107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 59782925689654442479024285 22418597133620415929634107)
          ·
            refine ⟨33627895700430623894451161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22418597133620415929634107 33627895700430623894451161)
            ·
              refine ⟨25220921775322967920838371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33627895700430623894451161 25220921775322967920838371)
              ·
                refine ⟨37831382662984451881257557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25220921775322967920838371 37831382662984451881257557)
                ·
                  refine ⟨443336515581849045483487, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 37831382662984451881257557 443336515581849045483487)
                  ·
                    rfl

theorem cell23_7770553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 1, 2, 1, 8].length) (baseStart_7770553 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7770553 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7770553 prefixEnd_7770553 := by exact prefixLift 7770553
  have htrace : WordTrace (prefixWord ++ tailWord_7770553) baseStart_7770553 baseEnd_7770553 := by
    simpa [prefixWord, tailWord_7770553, baseEnd_7770553] using wordTrace_append hprefix tailTrace_7770553
  have hstable : (prefixWord ++ tailWord_7770553).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7770553).length < 2 ^ (prefixWord ++ tailWord_7770553).sum := by decide
  have hdescent : baseEnd_7770553 < baseStart_7770553 := by decide
  rcases family_descends (prefixWord ++ tailWord_7770553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7770557 : List Nat := [1, 4, 1, 2, 2, 4, 1, 1, 3, 4]
def baseStart_7770557 : Nat := 118140960795 + 7770557 * 2 ^ 59
def prefixEnd_7770557 : Nat := 4983230072969 + 3 ^ 40 * 7770557 * 2
def baseEnd_7770557 : Nat := 1330010231386419797900455

theorem tailTrace_7770557 : CollatzResearch.WordTrace tailWord_7770557 prefixEnd_7770557 1330010231386419797900455 := by
  unfold tailWord_7770557
  simp only [CollatzResearch.WordTrace]
  refine ⟨283415497309606569324445925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188943664873071046216297283 283415497309606569324445925)
  ·
    refine ⟨53140405745551231748333611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 283415497309606569324445925 53140405745551231748333611)
    ·
      refine ⟨79710608618326847622500417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53140405745551231748333611 79710608618326847622500417)
      ·
        refine ⟨59782956463745135716875313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79710608618326847622500417 59782956463745135716875313)
        ·
          refine ⟨44837217347808851787656485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59782956463745135716875313 44837217347808851787656485)
          ·
            refine ⟨8406978252714159710185591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 44837217347808851787656485 8406978252714159710185591)
            ·
              refine ⟨12610467379071239565278387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8406978252714159710185591 12610467379071239565278387)
              ·
                refine ⟨18915701068606859347917581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12610467379071239565278387 18915701068606859347917581)
                ·
                  refine ⟨7093387900727572255469093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18915701068606859347917581 7093387900727572255469093)
                  ·
                    refine ⟨1330010231386419797900455, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7093387900727572255469093 1330010231386419797900455)
                    ·
                      rfl

theorem cell23_7770557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 4, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 4, 1, 1, 3, 4].length) (baseStart_7770557 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7770557 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7770557 prefixEnd_7770557 := by exact prefixLift 7770557
  have htrace : WordTrace (prefixWord ++ tailWord_7770557) baseStart_7770557 baseEnd_7770557 := by
    simpa [prefixWord, tailWord_7770557, baseEnd_7770557] using wordTrace_append hprefix tailTrace_7770557
  have hstable : (prefixWord ++ tailWord_7770557).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7770557).length < 2 ^ (prefixWord ++ tailWord_7770557).sum := by decide
  have hdescent : baseEnd_7770557 < baseStart_7770557 := by decide
  rcases family_descends (prefixWord ++ tailWord_7770557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7770620 : List Nat := [2, 2, 2, 1, 2, 1, 1, 2, 2, 6, 2]
def baseStart_7770620 : Nat := 118140960795 + 7770620 * 2 ^ 59
def prefixEnd_7770620 : Nat := 4983230072969 + 3 ^ 40 * 7770620 * 2
def baseEnd_7770620 : Nat := 3990063043440492647213575

theorem tailTrace_7770620 : CollatzResearch.WordTrace tailWord_7770620 prefixEnd_7770620 3990063043440492647213575 := by
  unfold tailWord_7770620
  simp only [CollatzResearch.WordTrace]
  refine ⟨141708897554189165541994657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 188945196738918887389326209 141708897554189165541994657)
  ·
    refine ⟨106281673165641874156495993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 141708897554189165541994657 106281673165641874156495993)
    ·
      refine ⟨79711254874231405617371995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 106281673165641874156495993 79711254874231405617371995)
      ·
        refine ⟨119566882311347108426057993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79711254874231405617371995 119566882311347108426057993)
        ·
          refine ⟨89675161733510331319543495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 119566882311347108426057993 89675161733510331319543495)
          ·
            refine ⟨134512742600265496979315243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89675161733510331319543495 134512742600265496979315243)
            ·
              refine ⟨201769113900398245468972865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 134512742600265496979315243 201769113900398245468972865)
              ·
                refine ⟨151326835425298684101729649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 201769113900398245468972865 151326835425298684101729649)
                ·
                  refine ⟨113495126568974013076297237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 151326835425298684101729649 113495126568974013076297237)
                  ·
                    refine ⟨5320084057920656862951433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 113495126568974013076297237 5320084057920656862951433)
                    ·
                      refine ⟨3990063043440492647213575, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5320084057920656862951433 3990063043440492647213575)
                      ·
                        rfl

theorem cell23_7770620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 1, 2, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 1, 2, 2, 6, 2].length) (baseStart_7770620 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7770620 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7770620 prefixEnd_7770620 := by exact prefixLift 7770620
  have htrace : WordTrace (prefixWord ++ tailWord_7770620) baseStart_7770620 baseEnd_7770620 := by
    simpa [prefixWord, tailWord_7770620, baseEnd_7770620] using wordTrace_append hprefix tailTrace_7770620
  have hstable : (prefixWord ++ tailWord_7770620).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7770620).length < 2 ^ (prefixWord ++ tailWord_7770620).sum := by decide
  have hdescent : baseEnd_7770620 < baseStart_7770620 := by decide
  rcases family_descends (prefixWord ++ tailWord_7770620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7770623 : List Nat := [1, 1, 2, 2, 1, 2, 4, 1, 3, 1, 5]
def baseStart_7770623 : Nat := 118140960795 + 7770623 * 2 ^ 59
def prefixEnd_7770623 : Nat := 4983230072969 + 3 ^ 40 * 7770623 * 2
def baseEnd_7770623 : Nat := 3990064583882456135476061

theorem tailTrace_7770623 : CollatzResearch.WordTrace tailWord_7770623 prefixEnd_7770623 3990064583882456135476061 := by
  unfold tailWord_7770623
  simp only [CollatzResearch.WordTrace]
  refine ⟨283417904527367462596348523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188945269684911641730899015 283417904527367462596348523)
  ·
    refine ⟨425126856791051193894522785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 283417904527367462596348523 425126856791051193894522785)
    ·
      refine ⟨318845142593288395420892089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 425126856791051193894522785 318845142593288395420892089)
      ·
        refine ⟨239133856944966296565669067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 318845142593288395420892089 239133856944966296565669067)
        ·
          refine ⟨358700785417449444848503601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 239133856944966296565669067 358700785417449444848503601)
          ·
            refine ⟨269025589063087083636377701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 358700785417449444848503601 269025589063087083636377701)
            ·
              refine ⟨50442297949328828181820819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 269025589063087083636377701 50442297949328828181820819)
              ·
                refine ⟨75663446923993242272731229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50442297949328828181820819 75663446923993242272731229)
                ·
                  refine ⟨28373792596497465852274211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 75663446923993242272731229 28373792596497465852274211)
                  ·
                    refine ⟨42560688894746198778411317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 28373792596497465852274211 42560688894746198778411317)
                    ·
                      refine ⟨3990064583882456135476061, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 42560688894746198778411317 3990064583882456135476061)
                      ·
                        rfl

theorem cell23_7770623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 4, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 4, 1, 3, 1, 5].length) (baseStart_7770623 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7770623 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7770623 prefixEnd_7770623 := by exact prefixLift 7770623
  have htrace : WordTrace (prefixWord ++ tailWord_7770623) baseStart_7770623 baseEnd_7770623 := by
    simpa [prefixWord, tailWord_7770623, baseEnd_7770623] using wordTrace_append hprefix tailTrace_7770623
  have hstable : (prefixWord ++ tailWord_7770623).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7770623).length < 2 ^ (prefixWord ++ tailWord_7770623).sum := by decide
  have hdescent : baseEnd_7770623 < baseStart_7770623 := by decide
  rcases family_descends (prefixWord ++ tailWord_7770623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7770650 : List Nat := [3, 1, 1, 3, 1, 1, 4, 2, 1, 2, 4]
def baseStart_7770650 : Nat := 118140960795 + 7770650 * 2 ^ 59
def prefixEnd_7770650 : Nat := 4983230072969 + 3 ^ 40 * 7770650 * 2
def baseEnd_7770650 : Nat := 3990078447860127529838437

theorem tailTrace_7770650 : CollatzResearch.WordTrace tailWord_7770650 prefixEnd_7770650 3990078447860127529838437 := by
  unfold tailWord_7770650
  simp only [CollatzResearch.WordTrace]
  refine ⟨70854722324567411551895351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 188945926198846430805054269 70854722324567411551895351)
  ·
    refine ⟨106282083486851117327843027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70854722324567411551895351 106282083486851117327843027)
    ·
      refine ⟨159423125230276675991764541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106282083486851117327843027 159423125230276675991764541)
      ·
        refine ⟨59783671961353753496911703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 159423125230276675991764541 59783671961353753496911703)
        ·
          refine ⟨89675507942030630245367555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59783671961353753496911703 89675507942030630245367555)
          ·
            refine ⟨134513261913045945368051333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89675507942030630245367555 134513261913045945368051333)
            ·
              refine ⟨25221236608696114756509625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 134513261913045945368051333 25221236608696114756509625)
              ·
                refine ⟨18915927456522086067382219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25221236608696114756509625 18915927456522086067382219)
                ·
                  refine ⟨28373891184783129101073329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18915927456522086067382219 28373891184783129101073329)
                  ·
                    refine ⟨21280418388587346825804997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 28373891184783129101073329 21280418388587346825804997)
                    ·
                      refine ⟨3990078447860127529838437, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21280418388587346825804997 3990078447860127529838437)
                      ·
                        rfl

theorem cell23_7770650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 4, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 4, 2, 1, 2, 4].length) (baseStart_7770650 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7770650 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7770650 prefixEnd_7770650 := by exact prefixLift 7770650
  have htrace : WordTrace (prefixWord ++ tailWord_7770650) baseStart_7770650 baseEnd_7770650 := by
    simpa [prefixWord, tailWord_7770650, baseEnd_7770650] using wordTrace_append hprefix tailTrace_7770650
  have hstable : (prefixWord ++ tailWord_7770650).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7770650).length < 2 ^ (prefixWord ++ tailWord_7770650).sum := by decide
  have hdescent : baseEnd_7770650 < baseStart_7770650 := by decide
  rcases family_descends (prefixWord ++ tailWord_7770650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7770657 : List Nat := [1, 2, 3, 2, 2, 1, 3, 3, 1, 2, 3]
def baseStart_7770657 : Nat := 118140960795 + 7770657 * 2 ^ 59
def prefixEnd_7770657 : Nat := 4983230072969 + 3 ^ 40 * 7770657 * 2
def baseEnd_7770657 : Nat := 3990082042224709002450905

theorem tailTrace_7770657 : CollatzResearch.WordTrace tailWord_7770657 prefixEnd_7770657 3990082042224709002450905 := by
  unfold tailWord_7770657
  simp only [CollatzResearch.WordTrace]
  refine ⟨283419144609244286403086225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188946096406162857602057483 283419144609244286403086225)
  ·
    refine ⟨212564358456933214802314669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 283419144609244286403086225 212564358456933214802314669)
    ·
      refine ⟨79711634421349955550868001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 212564358456933214802314669 79711634421349955550868001)
      ·
        refine ⟨59783725816012466663151001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79711634421349955550868001 59783725816012466663151001)
        ·
          refine ⟨44837794362009349997363251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59783725816012466663151001 44837794362009349997363251)
          ·
            refine ⟨67256691543014024996044877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44837794362009349997363251 67256691543014024996044877)
            ·
              refine ⟨25221259328630259373516829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 67256691543014024996044877 25221259328630259373516829)
              ·
                refine ⟨9457972248236347265068811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25221259328630259373516829 9457972248236347265068811)
                ·
                  refine ⟨14186958372354520897603217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9457972248236347265068811 14186958372354520897603217)
                  ·
                    refine ⟨10640218779265890673202413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14186958372354520897603217 10640218779265890673202413)
                    ·
                      refine ⟨3990082042224709002450905, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10640218779265890673202413 3990082042224709002450905)
                      ·
                        rfl

theorem cell23_7770657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 3, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 3, 3, 1, 2, 3].length) (baseStart_7770657 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7770657 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7770657 prefixEnd_7770657 := by exact prefixLift 7770657
  have htrace : WordTrace (prefixWord ++ tailWord_7770657) baseStart_7770657 baseEnd_7770657 := by
    simpa [prefixWord, tailWord_7770657, baseEnd_7770657] using wordTrace_append hprefix tailTrace_7770657
  have hstable : (prefixWord ++ tailWord_7770657).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7770657).length < 2 ^ (prefixWord ++ tailWord_7770657).sum := by decide
  have hdescent : baseEnd_7770657 < baseStart_7770657 := by decide
  rcases family_descends (prefixWord ++ tailWord_7770657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7770664 : List Nat := [2, 1, 5, 2, 1, 1, 3, 2, 2, 4]
def baseStart_7770664 : Nat := 118140960795 + 7770664 * 2 ^ 59
def prefixEnd_7770664 : Nat := 4983230072969 + 3 ^ 40 * 7770664 * 2
def baseEnd_7770664 : Nat := 1330028545529763491687791

theorem tailTrace_7770664 : CollatzResearch.WordTrace tailWord_7770664 prefixEnd_7770664 1330028545529763491687791 := by
  unfold tailWord_7770664
  simp only [CollatzResearch.WordTrace]
  refine ⟨141709699960109463299295523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 188946266613479284399060697 141709699960109463299295523)
  ·
    refine ⟨212564549940164194948943285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141709699960109463299295523 212564549940164194948943285)
    ·
      refine ⟨19927926556890393276463433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 212564549940164194948943285 19927926556890393276463433)
      ·
        refine ⟨14945944917667794957347575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19927926556890393276463433 14945944917667794957347575)
        ·
          refine ⟨22418917376501692436021363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14945944917667794957347575 22418917376501692436021363)
          ·
            refine ⟨33628376064752538654032045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22418917376501692436021363 33628376064752538654032045)
            ·
              refine ⟨12610641024282201995262017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33628376064752538654032045 12610641024282201995262017)
              ·
                refine ⟨9457980768211651496446513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12610641024282201995262017 9457980768211651496446513)
                ·
                  refine ⟨7093485576158738622334885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9457980768211651496446513 7093485576158738622334885)
                  ·
                    refine ⟨1330028545529763491687791, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7093485576158738622334885 1330028545529763491687791)
                    ·
                      rfl

theorem cell23_7770664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 1, 3, 2, 2, 4].length) (baseStart_7770664 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7770664 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7770664 prefixEnd_7770664 := by exact prefixLift 7770664
  have htrace : WordTrace (prefixWord ++ tailWord_7770664) baseStart_7770664 baseEnd_7770664 := by
    simpa [prefixWord, tailWord_7770664, baseEnd_7770664] using wordTrace_append hprefix tailTrace_7770664
  have hstable : (prefixWord ++ tailWord_7770664).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7770664).length < 2 ^ (prefixWord ++ tailWord_7770664).sum := by decide
  have hdescent : baseEnd_7770664 < baseStart_7770664 := by decide
  rcases family_descends (prefixWord ++ tailWord_7770664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7770673 : List Nat := [1, 2, 2, 3, 1, 1, 2, 1, 1, 9]
def baseStart_7770673 : Nat := 118140960795 + 7770673 * 2 ^ 59
def prefixEnd_7770673 : Nat := 4983230072969 + 3 ^ 40 * 7770673 * 2
def baseEnd_7770673 : Nat := 1330030085971726979950277

theorem tailTrace_7770673 : CollatzResearch.WordTrace tailWord_7770673 prefixEnd_7770673 1330030085971726979950277 := by
  unfold tailWord_7770673
  simp only [CollatzResearch.WordTrace]
  refine ⟨283419728177186321135668673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188946485451457547423779115 283419728177186321135668673)
  ·
    refine ⟨212564796132889740851751505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 283419728177186321135668673 212564796132889740851751505)
    ·
      refine ⟨159423597099667305638813629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 212564796132889740851751505 159423597099667305638813629)
      ·
        refine ⟨59783848912375239614555111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 159423597099667305638813629 59783848912375239614555111)
        ·
          refine ⟨89675773368562859421832667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59783848912375239614555111 89675773368562859421832667)
          ·
            refine ⟨134513660052844289132749001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89675773368562859421832667 134513660052844289132749001)
            ·
              refine ⟨100885245039633216849561751, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 134513660052844289132749001 100885245039633216849561751)
              ·
                refine ⟨151327867559449825274342627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 100885245039633216849561751 151327867559449825274342627)
                ·
                  refine ⟨226991801339174737911513941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 151327867559449825274342627 226991801339174737911513941)
                  ·
                    refine ⟨1330030085971726979950277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 226991801339174737911513941 1330030085971726979950277)
                    ·
                      rfl

theorem cell23_7770673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 2, 1, 1, 9].length) (baseStart_7770673 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7770673 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7770673 prefixEnd_7770673 := by exact prefixLift 7770673
  have htrace : WordTrace (prefixWord ++ tailWord_7770673) baseStart_7770673 baseEnd_7770673 := by
    simpa [prefixWord, tailWord_7770673, baseEnd_7770673] using wordTrace_append hprefix tailTrace_7770673
  have hstable : (prefixWord ++ tailWord_7770673).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7770673).length < 2 ^ (prefixWord ++ tailWord_7770673).sum := by decide
  have hdescent : baseEnd_7770673 < baseStart_7770673 := by decide
  rcases family_descends (prefixWord ++ tailWord_7770673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7770694 : List Nat := [6, 1, 1, 1, 2, 1, 4, 7]
def baseStart_7770694 : Nat := 118140960795 + 7770694 * 2 ^ 59
def prefixEnd_7770694 : Nat := 4983230072969 + 3 ^ 40 * 7770694 * 2
def baseEnd_7770694 : Nat := 147781520037367605840305

theorem tailTrace_7770694 : CollatzResearch.WordTrace tailWord_7770694 prefixEnd_7770694 147781520037367605840305 := by
  unfold tailWord_7770694
  simp only [CollatzResearch.WordTrace]
  refine ⟨8856890440940945053818223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 188946996073406827814788757 8856890440940945053818223)
  ·
    refine ⟨13285335661411417580727335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8856890440940945053818223 13285335661411417580727335)
    ·
      refine ⟨19928003492117126371091003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13285335661411417580727335 19928003492117126371091003)
      ·
        refine ⟨29892005238175689556636505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19928003492117126371091003 29892005238175689556636505)
        ·
          refine ⟨22419003928631767167477379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29892005238175689556636505 22419003928631767167477379)
          ·
            refine ⟨33628505892947650751216069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22419003928631767167477379 33628505892947650751216069)
            ·
              refine ⟨6305344854927684515853013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 33628505892947650751216069 6305344854927684515853013)
              ·
                refine ⟨147781520037367605840305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6305344854927684515853013 147781520037367605840305)
                ·
                  rfl

theorem cell23_7770694_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 1, 4, 7].length) (baseStart_7770694 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7770694 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7770694 prefixEnd_7770694 := by exact prefixLift 7770694
  have htrace : WordTrace (prefixWord ++ tailWord_7770694) baseStart_7770694 baseEnd_7770694 := by
    simpa [prefixWord, tailWord_7770694, baseEnd_7770694] using wordTrace_append hprefix tailTrace_7770694
  have hstable : (prefixWord ++ tailWord_7770694).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7770694).length < 2 ^ (prefixWord ++ tailWord_7770694).sum := by decide
  have hdescent : baseEnd_7770694 < baseStart_7770694 := by decide
  rcases family_descends (prefixWord ++ tailWord_7770694) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7770703 : List Nat := [1, 1, 2, 1, 1, 2, 4, 2, 1, 8]
def baseStart_7770703 : Nat := 118140960795 + 7770703 * 2 ^ 59
def prefixEnd_7770703 : Nat := 4983230072969 + 3 ^ 40 * 7770703 * 2
def baseEnd_7770703 : Nat := 1330035220778271940825231

theorem tailTrace_7770703 : CollatzResearch.WordTrace tailWord_7770703 prefixEnd_7770703 1330035220778271940825231 := by
  unfold tailWord_7770703
  simp only [CollatzResearch.WordTrace]
  refine ⟨283420822367077636259260763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188947214911385090839507175 283420822367077636259260763)
  ·
    refine ⟨425131233550616454388891145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 283420822367077636259260763 425131233550616454388891145)
    ·
      refine ⟨318848425162962340791668359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 425131233550616454388891145 318848425162962340791668359)
      ·
        refine ⟨478272637744443511187502539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 318848425162962340791668359 478272637744443511187502539)
        ·
          refine ⟨717408956616665266781253809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 478272637744443511187502539 717408956616665266781253809)
          ·
            refine ⟨538056717462498950085940357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 717408956616665266781253809 538056717462498950085940357)
            ·
              refine ⟨100885634524218553141113817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 538056717462498950085940357 100885634524218553141113817)
              ·
                refine ⟨75664225893163914855835363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 100885634524218553141113817 75664225893163914855835363)
                ·
                  refine ⟨113496338839745872283753045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 75664225893163914855835363 113496338839745872283753045)
                  ·
                    refine ⟨1330035220778271940825231, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 113496338839745872283753045 1330035220778271940825231)
                    ·
                      rfl

theorem cell23_7770703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 4, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 4, 2, 1, 8].length) (baseStart_7770703 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7770703 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7770703 prefixEnd_7770703 := by exact prefixLift 7770703
  have htrace : WordTrace (prefixWord ++ tailWord_7770703) baseStart_7770703 baseEnd_7770703 := by
    simpa [prefixWord, tailWord_7770703, baseEnd_7770703] using wordTrace_append hprefix tailTrace_7770703
  have hstable : (prefixWord ++ tailWord_7770703).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7770703).length < 2 ^ (prefixWord ++ tailWord_7770703).sum := by decide
  have hdescent : baseEnd_7770703 < baseStart_7770703 := by decide
  rcases family_descends (prefixWord ++ tailWord_7770703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7770722 : List Nat := [3, 3, 2, 3, 1, 1, 3, 2, 1, 2, 2]
def baseStart_7770722 : Nat := 118140960795 + 7770722 * 2 ^ 59
def prefixEnd_7770722 : Nat := 4983230072969 + 3 ^ 40 * 7770722 * 2
def baseEnd_7770722 : Nat := 3990115418467251248138107

theorem tailTrace_7770722 : CollatzResearch.WordTrace tailWord_7770722 prefixEnd_7770722 3990115418467251248138107 := by
  unfold tailWord_7770722
  simp only [CollatzResearch.WordTrace]
  refine ⟨70855378838502200626050605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 188947676902672535002801613 70855378838502200626050605)
  ·
    refine ⟨26570767064438325234768977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 70855378838502200626050605 26570767064438325234768977)
    ·
      refine ⟨19928075298328743926076733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26570767064438325234768977 19928075298328743926076733)
      ·
        refine ⟨7473028236873278972278775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19928075298328743926076733 7473028236873278972278775)
        ·
          refine ⟨11209542355309918458418163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7473028236873278972278775 11209542355309918458418163)
          ·
            refine ⟨16814313532964877687627245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11209542355309918458418163 16814313532964877687627245)
            ·
              refine ⟨6305367574861829132860217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16814313532964877687627245 6305367574861829132860217)
              ·
                refine ⟨4729025681146371849645163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6305367574861829132860217 4729025681146371849645163)
                ·
                  refine ⟨7093538521719557774467745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4729025681146371849645163 7093538521719557774467745)
                  ·
                    refine ⟨5320153891289668330850809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7093538521719557774467745 5320153891289668330850809)
                    ·
                      refine ⟨3990115418467251248138107, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5320153891289668330850809 3990115418467251248138107)
                      ·
                        rfl

theorem cell23_7770722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 1, 1, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 1, 1, 3, 2, 1, 2, 2].length) (baseStart_7770722 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7770722 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7770722 prefixEnd_7770722 := by exact prefixLift 7770722
  have htrace : WordTrace (prefixWord ++ tailWord_7770722) baseStart_7770722 baseEnd_7770722 := by
    simpa [prefixWord, tailWord_7770722, baseEnd_7770722] using wordTrace_append hprefix tailTrace_7770722
  have hstable : (prefixWord ++ tailWord_7770722).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7770722).length < 2 ^ (prefixWord ++ tailWord_7770722).sum := by decide
  have hdescent : baseEnd_7770722 < baseStart_7770722 := by decide
  rcases family_descends (prefixWord ++ tailWord_7770722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7770730 : List Nat := [3, 1, 3, 2, 1, 1, 1, 2, 1, 3, 5]
def baseStart_7770730 : Nat := 118140960795 + 7770730 * 2 ^ 59
def prefixEnd_7770730 : Nat := 4983230072969 + 3 ^ 40 * 7770730 * 2
def baseEnd_7770730 : Nat := 3990119526312487216838069

theorem tailTrace_7770730 : CollatzResearch.WordTrace tailWord_7770730 prefixEnd_7770730 3990119526312487216838069 := by
  unfold tailWord_7770730
  simp only [CollatzResearch.WordTrace]
  refine ⟨70855451784494954967623411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 188947871425319879913662429 70855451784494954967623411)
  ·
    refine ⟨106283177676742432451435117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70855451784494954967623411 106283177676742432451435117)
    ·
      refine ⟨39856191628778412169288169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 106283177676742432451435117 39856191628778412169288169)
      ·
        refine ⟨29892143721583809126966127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39856191628778412169288169 29892143721583809126966127)
        ·
          refine ⟨44838215582375713690449191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29892143721583809126966127 44838215582375713690449191)
          ·
            refine ⟨67257323373563570535673787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44838215582375713690449191 67257323373563570535673787)
            ·
              refine ⟨100885985060345355803510681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67257323373563570535673787 100885985060345355803510681)
              ·
                refine ⟨75664488795259016852633011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 100885985060345355803510681 75664488795259016852633011)
                ·
                  refine ⟨113496733192888525278949517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 75664488795259016852633011 113496733192888525278949517)
                  ·
                    refine ⟨42561274947333196979606069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 113496733192888525278949517 42561274947333196979606069)
                    ·
                      refine ⟨3990119526312487216838069, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 42561274947333196979606069 3990119526312487216838069)
                      ·
                        rfl

theorem cell23_7770730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 1, 2, 1, 3, 5].length) (baseStart_7770730 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7770730 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7770730 prefixEnd_7770730 := by exact prefixLift 7770730
  have htrace : WordTrace (prefixWord ++ tailWord_7770730) baseStart_7770730 baseEnd_7770730 := by
    simpa [prefixWord, tailWord_7770730, baseEnd_7770730] using wordTrace_append hprefix tailTrace_7770730
  have hstable : (prefixWord ++ tailWord_7770730).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7770730).length < 2 ^ (prefixWord ++ tailWord_7770730).sum := by decide
  have hdescent : baseEnd_7770730 < baseStart_7770730 := by decide
  rcases family_descends (prefixWord ++ tailWord_7770730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7770738 : List Nat := [3, 2, 1, 2, 4, 2, 2, 1, 2, 1, 3]
def baseStart_7770738 : Nat := 118140960795 + 7770738 * 2 ^ 59
def prefixEnd_7770738 : Nat := 4983230072969 + 3 ^ 40 * 7770738 * 2
def baseEnd_7770738 : Nat := 3990123634157723185538033

theorem tailTrace_7770738 : CollatzResearch.WordTrace tailWord_7770738 prefixEnd_7770738 3990123634157723185538033 := by
  unfold tailWord_7770738
  simp only [CollatzResearch.WordTrace]
  refine ⟨70855524730487709309196217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 188948065947967224824523245 70855524730487709309196217)
  ·
    refine ⟨53141643547865781981897163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70855524730487709309196217 53141643547865781981897163)
    ·
      refine ⟨79712465321798672972845745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53141643547865781981897163 79712465321798672972845745)
      ·
        refine ⟨59784348991349004729634309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79712465321798672972845745 59784348991349004729634309)
        ·
          refine ⟨11209565435877938386806433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 59784348991349004729634309 11209565435877938386806433)
          ·
            refine ⟨8407174076908453790104825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11209565435877938386806433 8407174076908453790104825)
            ·
              refine ⟨6305380557681340342578619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8407174076908453790104825 6305380557681340342578619)
              ·
                refine ⟨9458070836522010513867929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6305380557681340342578619 9458070836522010513867929)
                ·
                  refine ⟨7093553127391507885400947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9458070836522010513867929 7093553127391507885400947)
                  ·
                    refine ⟨10640329691087261828101421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7093553127391507885400947 10640329691087261828101421)
                    ·
                      refine ⟨3990123634157723185538033, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10640329691087261828101421 3990123634157723185538033)
                      ·
                        rfl

theorem cell23_7770738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 4, 2, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 4, 2, 2, 1, 2, 1, 3].length) (baseStart_7770738 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7770738 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7770738 prefixEnd_7770738 := by exact prefixLift 7770738
  have htrace : WordTrace (prefixWord ++ tailWord_7770738) baseStart_7770738 baseEnd_7770738 := by
    simpa [prefixWord, tailWord_7770738, baseEnd_7770738] using wordTrace_append hprefix tailTrace_7770738
  have hstable : (prefixWord ++ tailWord_7770738).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7770738).length < 2 ^ (prefixWord ++ tailWord_7770738).sum := by decide
  have hdescent : baseEnd_7770738 < baseStart_7770738 := by decide
  rcases family_descends (prefixWord ++ tailWord_7770738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7770744 : List Nat := [2, 1, 2, 1, 1, 1, 2, 7, 2, 2, 2]
def baseStart_7770744 : Nat := 118140960795 + 7770744 * 2 ^ 59
def prefixEnd_7770744 : Nat := 4983230072969 + 3 ^ 40 * 7770744 * 2
def baseEnd_7770744 : Nat := 3990126715041650162063005

theorem tailTrace_7770744 : CollatzResearch.WordTrace tailWord_7770744 prefixEnd_7770744 3990126715041650162063005 := by
  unfold tailWord_7770744
  simp only [CollatzResearch.WordTrace]
  refine ⟨141711158879964550130751643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 188948211839952733507668857 141711158879964550130751643)
  ·
    refine ⟨212566738319946825196127465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141711158879964550130751643 212566738319946825196127465)
    ·
      refine ⟨159425053739960118897095599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 212566738319946825196127465 159425053739960118897095599)
      ·
        refine ⟨239137580609940178345643399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 159425053739960118897095599 239137580609940178345643399)
        ·
          refine ⟨358706370914910267518465099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 239137580609940178345643399 358706370914910267518465099)
          ·
            refine ⟨538059556372365401277697649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 358706370914910267518465099 538059556372365401277697649)
            ·
              refine ⟨403544667279274050958273237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 538059556372365401277697649 403544667279274050958273237)
              ·
                refine ⟨9458078139357985569334529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 403544667279274050958273237 9458078139357985569334529)
                ·
                  refine ⟨7093558604518489177000897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9458078139357985569334529 7093558604518489177000897)
                  ·
                    refine ⟨5320168953388866882750673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7093558604518489177000897 5320168953388866882750673)
                    ·
                      refine ⟨3990126715041650162063005, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5320168953388866882750673 3990126715041650162063005)
                      ·
                        rfl

theorem cell23_7770744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 7, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 7, 2, 2, 2].length) (baseStart_7770744 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7770744 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7770744 prefixEnd_7770744 := by exact prefixLift 7770744
  have htrace : WordTrace (prefixWord ++ tailWord_7770744) baseStart_7770744 baseEnd_7770744 := by
    simpa [prefixWord, tailWord_7770744, baseEnd_7770744] using wordTrace_append hprefix tailTrace_7770744
  have hstable : (prefixWord ++ tailWord_7770744).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7770744).length < 2 ^ (prefixWord ++ tailWord_7770744).sum := by decide
  have hdescent : baseEnd_7770744 < baseStart_7770744 := by decide
  rcases family_descends (prefixWord ++ tailWord_7770744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7770784 : List Nat := [2, 1, 1, 4, 4, 1, 1, 4, 5]
def baseStart_7770784 : Nat := 118140960795 + 7770784 * 2 ^ 59
def prefixEnd_7770784 : Nat := 4983230072969 + 3 ^ 40 * 7770784 * 2
def baseEnd_7770784 : Nat := 443349694918647778395869

theorem tailTrace_7770784 : CollatzResearch.WordTrace tailWord_7770784 prefixEnd_7770784 443349694918647778395869 := by
  unfold tailWord_7770784
  simp only [CollatzResearch.WordTrace]
  refine ⟨141711888339892093546479703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 188949184453189458061972937 141711888339892093546479703)
  ·
    refine ⟨212567832509838140319719555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141711888339892093546479703 212567832509838140319719555)
    ·
      refine ⟨318851748764757210479579333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 212567832509838140319719555 318851748764757210479579333)
      ·
        refine ⟨59784702893391976964921125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 318851748764757210479579333 59784702893391976964921125)
        ·
          refine ⟨11209631792510995680922711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 59784702893391976964921125 11209631792510995680922711)
          ·
            refine ⟨16814447688766493521384067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11209631792510995680922711 16814447688766493521384067)
            ·
              refine ⟨25221671533149740282076101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16814447688766493521384067 25221671533149740282076101)
              ·
                refine ⟨4729063412465576302889269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25221671533149740282076101 4729063412465576302889269)
                ·
                  refine ⟨443349694918647778395869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4729063412465576302889269 443349694918647778395869)
                  ·
                    rfl

theorem cell23_7770784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 4, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 4, 1, 1, 4, 5].length) (baseStart_7770784 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7770784 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7770784 prefixEnd_7770784 := by exact prefixLift 7770784
  have htrace : WordTrace (prefixWord ++ tailWord_7770784) baseStart_7770784 baseEnd_7770784 := by
    simpa [prefixWord, tailWord_7770784, baseEnd_7770784] using wordTrace_append hprefix tailTrace_7770784
  have hstable : (prefixWord ++ tailWord_7770784).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7770784).length < 2 ^ (prefixWord ++ tailWord_7770784).sum := by decide
  have hdescent : baseEnd_7770784 < baseStart_7770784 := by decide
  rcases family_descends (prefixWord ++ tailWord_7770784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7770800 : List Nat := [2, 1, 1, 1, 2, 1, 3, 4, 1, 3, 4]
def baseStart_7770800 : Nat := 118140960795 + 7770800 * 2 ^ 59
def prefixEnd_7770800 : Nat := 4983230072969 + 3 ^ 40 * 7770800 * 2
def baseEnd_7770800 : Nat := 3990155469958301942962747

theorem tailTrace_7770800 : CollatzResearch.WordTrace tailWord_7770800 prefixEnd_7770800 3990155469958301942962747 := by
  unfold tailWord_7770800
  simp only [CollatzResearch.WordTrace]
  refine ⟨141712180123863110912770927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 188949573498484147883694569 141712180123863110912770927)
  ·
    refine ⟨212568270185794666369156391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141712180123863110912770927 212568270185794666369156391)
    ·
      refine ⟨318852405278691999553734587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 212568270185794666369156391 318852405278691999553734587)
      ·
        refine ⟨478278607918037999330601881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 318852405278691999553734587 478278607918037999330601881)
        ·
          refine ⟨358708955938528499497951411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 478278607918037999330601881 358708955938528499497951411)
          ·
            refine ⟨538063433907792749246927117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 358708955938528499497951411 538063433907792749246927117)
            ·
              refine ⟨201773787715422280967597669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 538063433907792749246927117 201773787715422280967597669)
              ·
                refine ⟨37832585196641677681424563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 201773787715422280967597669 37832585196641677681424563)
                ·
                  refine ⟨56748877794962516522136845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37832585196641677681424563 56748877794962516522136845)
                  ·
                    refine ⟨21280829173110943695801317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 56748877794962516522136845 21280829173110943695801317)
                    ·
                      refine ⟨3990155469958301942962747, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21280829173110943695801317 3990155469958301942962747)
                      ·
                        rfl

theorem cell23_7770800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 3, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 3, 4, 1, 3, 4].length) (baseStart_7770800 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7770800 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7770800 prefixEnd_7770800 := by exact prefixLift 7770800
  have htrace : WordTrace (prefixWord ++ tailWord_7770800) baseStart_7770800 baseEnd_7770800 := by
    simpa [prefixWord, tailWord_7770800, baseEnd_7770800] using wordTrace_append hprefix tailTrace_7770800
  have hstable : (prefixWord ++ tailWord_7770800).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7770800).length < 2 ^ (prefixWord ++ tailWord_7770800).sum := by decide
  have hdescent : baseEnd_7770800 < baseStart_7770800 := by decide
  rcases family_descends (prefixWord ++ tailWord_7770800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7770860 : List Nat := [2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 6]
def baseStart_7770860 : Nat := 118140960795 + 7770860 * 2 ^ 59
def prefixEnd_7770860 : Nat := 4983230072969 + 3 ^ 40 * 7770860 * 2
def baseEnd_7770860 : Nat := 3990186278797571708212471

theorem tailTrace_7770860 : CollatzResearch.WordTrace tailWord_7770860 prefixEnd_7770860 3990186278797571708212471 := by
  unfold tailWord_7770860
  simp only [CollatzResearch.WordTrace]
  refine ⟨141713274313754426036363017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 188951032418339234715150689 141713274313754426036363017)
  ·
    refine ⟨106284955735315819527272263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 141713274313754426036363017 106284955735315819527272263)
    ·
      refine ⟨159427433602973729290908395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106284955735315819527272263 159427433602973729290908395)
      ·
        refine ⟨239141150404460593936362593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 159427433602973729290908395 239141150404460593936362593)
        ·
          refine ⟨179355862803345445452271945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 239141150404460593936362593 179355862803345445452271945)
          ·
            refine ⟨134516897102509084089203959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 179355862803345445452271945 134516897102509084089203959)
            ·
              refine ⟨201775345653763626133805939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 134516897102509084089203959 201775345653763626133805939)
              ·
                refine ⟨302663018480645439200708909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 201775345653763626133805939 302663018480645439200708909)
                ·
                  refine ⟨113498631930242039700265841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 302663018480645439200708909 113498631930242039700265841)
                  ·
                    refine ⟨85123973947681529775199381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 113498631930242039700265841 85123973947681529775199381)
                    ·
                      refine ⟨3990186278797571708212471, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 85123973947681529775199381 3990186278797571708212471)
                      ·
                        rfl

theorem cell23_7770860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 6].length) (baseStart_7770860 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7770860 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7770860 prefixEnd_7770860 := by exact prefixLift 7770860
  have htrace : WordTrace (prefixWord ++ tailWord_7770860) baseStart_7770860 baseEnd_7770860 := by
    simpa [prefixWord, tailWord_7770860, baseEnd_7770860] using wordTrace_append hprefix tailTrace_7770860
  have hstable : (prefixWord ++ tailWord_7770860).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7770860).length < 2 ^ (prefixWord ++ tailWord_7770860).sum := by decide
  have hdescent : baseEnd_7770860 < baseStart_7770860 := by decide
  rcases family_descends (prefixWord ++ tailWord_7770860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7770878 : List Nat := [4, 2, 2, 1, 2, 1, 3, 3, 1, 4]
def baseStart_7770878 : Nat := 118140960795 + 7770878 * 2 ^ 59
def prefixEnd_7770878 : Nat := 4983230072969 + 3 ^ 40 * 7770878 * 2
def baseEnd_7770878 : Nat := 1330065173816450879262463

theorem tailTrace_7770878 : CollatzResearch.WordTrace tailWord_7770878 prefixEnd_7770878 1330065173816450879262463 := by
  unfold tailWord_7770878
  simp only [CollatzResearch.WordTrace]
  refine ⟨35428400642680455143360161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 188951470094295760764587525 35428400642680455143360161)
  ·
    refine ⟨26571300482010341357520121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35428400642680455143360161 26571300482010341357520121)
    ·
      refine ⟨19928475361507756018140091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26571300482010341357520121 19928475361507756018140091)
      ·
        refine ⟨29892713042261634027210137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19928475361507756018140091 29892713042261634027210137)
        ·
          refine ⟨22419534781696225520407603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29892713042261634027210137 22419534781696225520407603)
          ·
            refine ⟨33629302172544338280611405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22419534781696225520407603 33629302172544338280611405)
            ·
              refine ⟨12610988314704126855229277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33629302172544338280611405 12610988314704126855229277)
              ·
                refine ⟨4729120618014047570710979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12610988314704126855229277 4729120618014047570710979)
                ·
                  refine ⟨7093680927021071356066469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4729120618014047570710979 7093680927021071356066469)
                  ·
                    refine ⟨1330065173816450879262463, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7093680927021071356066469 1330065173816450879262463)
                    ·
                      rfl

theorem cell23_7770878_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 1, 3, 3, 1, 4].length) (baseStart_7770878 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7770878 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7770878 prefixEnd_7770878 := by exact prefixLift 7770878
  have htrace : WordTrace (prefixWord ++ tailWord_7770878) baseStart_7770878 baseEnd_7770878 := by
    simpa [prefixWord, tailWord_7770878, baseEnd_7770878] using wordTrace_append hprefix tailTrace_7770878
  have hstable : (prefixWord ++ tailWord_7770878).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7770878).length < 2 ^ (prefixWord ++ tailWord_7770878).sum := by decide
  have hdescent : baseEnd_7770878 < baseStart_7770878 := by decide
  rcases family_descends (prefixWord ++ tailWord_7770878) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7770880 : List Nat := [2, 1, 1, 2, 1, 1, 2, 1, 1, 6, 5]
def baseStart_7770880 : Nat := 118140960795 + 7770880 * 2 ^ 59
def prefixEnd_7770880 : Nat := 4983230072969 + 3 ^ 40 * 7770880 * 2
def baseEnd_7770880 : Nat := 3990196548410661629962379

theorem tailTrace_7770880 : CollatzResearch.WordTrace tailWord_7770880 prefixEnd_7770880 3990196548410661629962379 := by
  unfold tailWord_7770880
  simp only [CollatzResearch.WordTrace]
  refine ⟨141713639043718197744227047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 188951518724957596992302729 141713639043718197744227047)
  ·
    refine ⟨212570458565577296616340571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141713639043718197744227047 212570458565577296616340571)
    ·
      refine ⟨318855687848365944924510857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 212570458565577296616340571 318855687848365944924510857)
      ·
        refine ⟨239141765886274458693383143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 318855687848365944924510857 239141765886274458693383143)
        ·
          refine ⟨358712648829411688040074715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 239141765886274458693383143 358712648829411688040074715)
          ·
            refine ⟨538068973244117532060112073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 358712648829411688040074715 538068973244117532060112073)
            ·
              refine ⟨403551729933088149045084055, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 538068973244117532060112073 403551729933088149045084055)
              ·
                refine ⟨605327594899632223567626083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 403551729933088149045084055 605327594899632223567626083)
                ·
                  refine ⟨907991392349448335351439125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 605327594899632223567626083 907991392349448335351439125)
                  ·
                    refine ⟨42562096516380390719598709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 907991392349448335351439125 42562096516380390719598709)
                    ·
                      refine ⟨3990196548410661629962379, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 42562096516380390719598709 3990196548410661629962379)
                      ·
                        rfl

theorem cell23_7770880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 1, 1, 6, 5].length) (baseStart_7770880 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7770880 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7770880 prefixEnd_7770880 := by exact prefixLift 7770880
  have htrace : WordTrace (prefixWord ++ tailWord_7770880) baseStart_7770880 baseEnd_7770880 := by
    simpa [prefixWord, tailWord_7770880, baseEnd_7770880] using wordTrace_append hprefix tailTrace_7770880
  have hstable : (prefixWord ++ tailWord_7770880).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7770880).length < 2 ^ (prefixWord ++ tailWord_7770880).sum := by decide
  have hdescent : baseEnd_7770880 < baseStart_7770880 := by decide
  rcases family_descends (prefixWord ++ tailWord_7770880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7770917 : List Nat := [1, 3, 1, 2, 3, 1, 2, 3, 1, 6]
def baseStart_7770917 : Nat := 118140960795 + 7770917 * 2 ^ 59
def prefixEnd_7770917 : Nat := 4983230072969 + 3 ^ 40 * 7770917 * 2
def baseEnd_7770917 : Nat := 1330071849064959328399903

theorem tailTrace_7770917 : CollatzResearch.WordTrace tailWord_7770917 prefixEnd_7770917 1330071849064959328399903 := by
  unfold tailWord_7770917
  simp only [CollatzResearch.WordTrace]
  refine ⟨283428627588302350807551005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188952418392201567205034003 283428627588302350807551005)
  ·
    refine ⟨106285735345613381552831627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 283428627588302350807551005 106285735345613381552831627)
    ·
      refine ⟨159428603018420072329247441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106285735345613381552831627 159428603018420072329247441)
      ·
        refine ⟨119571452263815054246935581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 159428603018420072329247441 119571452263815054246935581)
        ·
          refine ⟨44839294598930645342600843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 119571452263815054246935581 44839294598930645342600843)
          ·
            refine ⟨67258941898395968013901265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44839294598930645342600843 67258941898395968013901265)
            ·
              refine ⟨50444206423796976010425949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 67258941898395968013901265 50444206423796976010425949)
              ·
                refine ⟨18916577408923866003909731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 50444206423796976010425949 18916577408923866003909731)
                ·
                  refine ⟨28374866113385799005864597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18916577408923866003909731 28374866113385799005864597)
                  ·
                    refine ⟨1330071849064959328399903, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28374866113385799005864597 1330071849064959328399903)
                    ·
                      rfl

theorem cell23_7770917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 2, 3, 1, 6].length) (baseStart_7770917 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7770917 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7770917 prefixEnd_7770917 := by exact prefixLift 7770917
  have htrace : WordTrace (prefixWord ++ tailWord_7770917) baseStart_7770917 baseEnd_7770917 := by
    simpa [prefixWord, tailWord_7770917, baseEnd_7770917] using wordTrace_append hprefix tailTrace_7770917
  have hstable : (prefixWord ++ tailWord_7770917).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7770917).length < 2 ^ (prefixWord ++ tailWord_7770917).sum := by decide
  have hdescent : baseEnd_7770917 < baseStart_7770917 := by decide
  rcases family_descends (prefixWord ++ tailWord_7770917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7770944 : List Nat := [2, 1, 1, 2, 2, 1, 1, 7, 1, 2, 3]
def baseStart_7770944 : Nat := 118140960795 + 7770944 * 2 ^ 59
def prefixEnd_7770944 : Nat := 4983230072969 + 3 ^ 40 * 7770944 * 2
def baseEnd_7770944 : Nat := 3990229411172549379562085

theorem tailTrace_7770944 : CollatzResearch.WordTrace tailWord_7770944 prefixEnd_7770944 3990229411172549379562085 := by
  unfold tailWord_7770944
  simp only [CollatzResearch.WordTrace]
  refine ⟨141714806179602267209391943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 188953074906136356279189257 141714806179602267209391943)
  ·
    refine ⟨212572209269403400814087915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141714806179602267209391943 212572209269403400814087915)
    ·
      refine ⟨318858313904105101221131873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 212572209269403400814087915 318858313904105101221131873)
      ·
        refine ⟨239143735428078825915848905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 318858313904105101221131873 239143735428078825915848905)
        ·
          refine ⟨179357801571059119436886679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 239143735428078825915848905 179357801571059119436886679)
          ·
            refine ⟨269036702356588679155330019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 179357801571059119436886679 269036702356588679155330019)
            ·
              refine ⟨403555053534883018732995029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 269036702356588679155330019 403555053534883018732995029)
              ·
                refine ⟨9458321567223820751554571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 403555053534883018732995029 9458321567223820751554571)
                ·
                  refine ⟨14187482350835731127331857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9458321567223820751554571 14187482350835731127331857)
                  ·
                    refine ⟨10640611763126798345498893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14187482350835731127331857 10640611763126798345498893)
                    ·
                      refine ⟨3990229411172549379562085, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10640611763126798345498893 3990229411172549379562085)
                      ·
                        rfl

theorem cell23_7770944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 1, 7, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 1, 7, 1, 2, 3].length) (baseStart_7770944 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7770944 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7770944 prefixEnd_7770944 := by exact prefixLift 7770944
  have htrace : WordTrace (prefixWord ++ tailWord_7770944) baseStart_7770944 baseEnd_7770944 := by
    simpa [prefixWord, tailWord_7770944, baseEnd_7770944] using wordTrace_append hprefix tailTrace_7770944
  have hstable : (prefixWord ++ tailWord_7770944).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7770944).length < 2 ^ (prefixWord ++ tailWord_7770944).sum := by decide
  have hdescent : baseEnd_7770944 < baseStart_7770944 := by decide
  rcases family_descends (prefixWord ++ tailWord_7770944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7771007 : List Nat := [1, 1, 2, 2, 1, 1, 5, 2, 2, 6]
def baseStart_7771007 : Nat := 118140960795 + 7771007 * 2 ^ 59
def prefixEnd_7771007 : Nat := 4983230072969 + 3 ^ 40 * 7771007 * 2
def baseEnd_7771007 : Nat := 1330087253484594211024765

theorem tailTrace_7771007 : CollatzResearch.WordTrace tailWord_7771007 prefixEnd_7771007 1330087253484594211024765 := by
  unfold tailWord_7771007
  simp only [CollatzResearch.WordTrace]
  refine ⟨283431910157976296178327275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188954606771984197452218183 283431910157976296178327275)
  ·
    refine ⟨425147865236964444267490913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 283431910157976296178327275 425147865236964444267490913)
    ·
      refine ⟨318860898927723333200618185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 425147865236964444267490913 318860898927723333200618185)
      ·
        refine ⟨239145674195792499900463639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 318860898927723333200618185 239145674195792499900463639)
        ·
          refine ⟨358718511293688749850695459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 239145674195792499900463639 358718511293688749850695459)
          ·
            refine ⟨538077766940533124776043189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 358718511293688749850695459 538077766940533124776043189)
            ·
              refine ⟨50444790650674980447754049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 538077766940533124776043189 50444790650674980447754049)
              ·
                refine ⟨37833592988006235335815537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50444790650674980447754049 37833592988006235335815537)
                ·
                  refine ⟨28375194741004676501861653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37833592988006235335815537 28375194741004676501861653)
                  ·
                    refine ⟨1330087253484594211024765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28375194741004676501861653 1330087253484594211024765)
                    ·
                      rfl

theorem cell23_7771007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 5, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 5, 2, 2, 6].length) (baseStart_7771007 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7771007 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7771007 prefixEnd_7771007 := by exact prefixLift 7771007
  have htrace : WordTrace (prefixWord ++ tailWord_7771007) baseStart_7771007 baseEnd_7771007 := by
    simpa [prefixWord, tailWord_7771007, baseEnd_7771007] using wordTrace_append hprefix tailTrace_7771007
  have hstable : (prefixWord ++ tailWord_7771007).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7771007).length < 2 ^ (prefixWord ++ tailWord_7771007).sum := by decide
  have hdescent : baseEnd_7771007 < baseStart_7771007 := by decide
  rcases family_descends (prefixWord ++ tailWord_7771007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7771027 : List Nat := [1, 1, 1, 2, 1, 2, 1, 5, 1, 4, 4]
def baseStart_7771027 : Nat := 118140960795 + 7771027 * 2 ^ 59
def prefixEnd_7771027 : Nat := 4983230072969 + 3 ^ 40 * 7771027 * 2
def baseEnd_7771027 : Nat := 3990272030066872554824203

theorem tailTrace_7771027 : CollatzResearch.WordTrace tailWord_7771027 prefixEnd_7771027 3990272030066872554824203 := by
  unfold tailWord_7771027
  simp only [CollatzResearch.WordTrace]
  refine ⟨283432639617903839594055335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188955093078602559729370223 283432639617903839594055335)
  ·
    refine ⟨425148959426855759391083003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 283432639617903839594055335 425148959426855759391083003)
    ·
      refine ⟨637723439140283639086624505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 425148959426855759391083003 637723439140283639086624505)
      ·
        refine ⟨478292579355212729314968379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 637723439140283639086624505 478292579355212729314968379)
        ·
          refine ⟨717438869032819093972452569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 478292579355212729314968379 717438869032819093972452569)
          ·
            refine ⟨538079151774614320479339427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 717438869032819093972452569 538079151774614320479339427)
            ·
              refine ⟨807118727661921480719009141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 538079151774614320479339427 807118727661921480719009141)
              ·
                refine ⟨75667380718305138817407107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 807118727661921480719009141 75667380718305138817407107)
                ·
                  refine ⟨113501071077457708226110661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 75667380718305138817407107 113501071077457708226110661)
                  ·
                    refine ⟨21281450827023320292395749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 113501071077457708226110661 21281450827023320292395749)
                    ·
                      refine ⟨3990272030066872554824203, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21281450827023320292395749 3990272030066872554824203)
                      ·
                        rfl

theorem cell23_7771027_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 5, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 5, 1, 4, 4].length) (baseStart_7771027 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7771027 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7771027 prefixEnd_7771027 := by exact prefixLift 7771027
  have htrace : WordTrace (prefixWord ++ tailWord_7771027) baseStart_7771027 baseEnd_7771027 := by
    simpa [prefixWord, tailWord_7771027, baseEnd_7771027] using wordTrace_append hprefix tailTrace_7771027
  have hstable : (prefixWord ++ tailWord_7771027).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7771027).length < 2 ^ (prefixWord ++ tailWord_7771027).sum := by decide
  have hdescent : baseEnd_7771027 < baseStart_7771027 := by decide
  rcases family_descends (prefixWord ++ tailWord_7771027) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7771084 : List Nat := [2, 2, 1, 4, 1, 1, 1, 2, 4, 5]
def baseStart_7771084 : Nat := 118140960795 + 7771084 * 2 ^ 59
def prefixEnd_7771084 : Nat := 4983230072969 + 3 ^ 40 * 7771084 * 2
def baseEnd_7771084 : Nat := 1330100432821392943937147

theorem tailTrace_7771084 : CollatzResearch.WordTrace tailWord_7771084 prefixEnd_7771084 1330100432821392943937147 := by
  unfold tailWord_7771084
  simp only [CollatzResearch.WordTrace]
  refine ⟨141717359289348669164440153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 188956479052464892219253537 141717359289348669164440153)
  ·
    refine ⟨106288019467011501873330115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 141717359289348669164440153 106288019467011501873330115)
    ·
      refine ⟨159432029200517252809995173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106288019467011501873330115 159432029200517252809995173)
      ·
        refine ⟨29893505475096984901874095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 159432029200517252809995173 29893505475096984901874095)
        ·
          refine ⟨44840258212645477352811143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29893505475096984901874095 44840258212645477352811143)
          ·
            refine ⟨67260387318968216029216715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44840258212645477352811143 67260387318968216029216715)
            ·
              refine ⟨100890580978452324043825073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67260387318968216029216715 100890580978452324043825073)
              ·
                refine ⟨75667935733839243032868805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 100890580978452324043825073 75667935733839243032868805)
                ·
                  refine ⟨14187737950094858068662901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 75667935733839243032868805 14187737950094858068662901)
                  ·
                    refine ⟨1330100432821392943937147, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14187737950094858068662901 1330100432821392943937147)
                    ·
                      rfl

theorem cell23_7771084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 1, 2, 4, 5].length) (baseStart_7771084 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7771084 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7771084 prefixEnd_7771084 := by exact prefixLift 7771084
  have htrace : WordTrace (prefixWord ++ tailWord_7771084) baseStart_7771084 baseEnd_7771084 := by
    simpa [prefixWord, tailWord_7771084, baseEnd_7771084] using wordTrace_append hprefix tailTrace_7771084
  have hstable : (prefixWord ++ tailWord_7771084).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7771084).length < 2 ^ (prefixWord ++ tailWord_7771084).sum := by decide
  have hdescent : baseEnd_7771084 < baseStart_7771084 := by decide
  rcases family_descends (prefixWord ++ tailWord_7771084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7771101 : List Nat := [1, 4, 3, 1, 2, 1, 1, 3, 2, 5]
def baseStart_7771101 : Nat := 118140960795 + 7771101 * 2 ^ 59
def prefixEnd_7771101 : Nat := 4983230072969 + 3 ^ 40 * 7771101 * 2
def baseEnd_7771101 : Nat := 1330103342545101755099621

theorem tailTrace_7771101 : CollatzResearch.WordTrace tailWord_7771101 prefixEnd_7771101 1330103342545101755099621 := by
  unfold tailWord_7771101
  simp only [CollatzResearch.WordTrace]
  refine ⟨283435338619635750232249157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188956892413090500154832771 283435338619635750232249157)
  ·
    refine ⟨53144125991181703168546717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 283435338619635750232249157 53144125991181703168546717)
    ·
      refine ⟨19929047246693138688205019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 53144125991181703168546717 19929047246693138688205019)
      ·
        refine ⟨29893570870039708032307529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19929047246693138688205019 29893570870039708032307529)
        ·
          refine ⟨22420178152529781024230647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29893570870039708032307529 22420178152529781024230647)
          ·
            refine ⟨33630267228794671536345971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22420178152529781024230647 33630267228794671536345971)
            ·
              refine ⟨50445400843192007304518957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33630267228794671536345971 50445400843192007304518957)
              ·
                refine ⟨18917025316197002739194609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 50445400843192007304518957 18917025316197002739194609)
                ·
                  refine ⟨14187768987147752054395957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18917025316197002739194609 14187768987147752054395957)
                  ·
                    refine ⟨1330103342545101755099621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14187768987147752054395957 1330103342545101755099621)
                    ·
                      rfl

theorem cell23_7771101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 1, 1, 3, 2, 5].length) (baseStart_7771101 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7771101 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7771101 prefixEnd_7771101 := by exact prefixLift 7771101
  have htrace : WordTrace (prefixWord ++ tailWord_7771101) baseStart_7771101 baseEnd_7771101 := by
    simpa [prefixWord, tailWord_7771101, baseEnd_7771101] using wordTrace_append hprefix tailTrace_7771101
  have hstable : (prefixWord ++ tailWord_7771101).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7771101).length < 2 ^ (prefixWord ++ tailWord_7771101).sum := by decide
  have hdescent : baseEnd_7771101 < baseStart_7771101 := by decide
  rcases family_descends (prefixWord ++ tailWord_7771101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7771121 : List Nat := [1, 2, 2, 2, 4, 1, 2, 2, 2, 1, 4]
def baseStart_7771121 : Nat := 118140960795 + 7771121 * 2 ^ 59
def prefixEnd_7771121 : Nat := 4983230072969 + 3 ^ 40 * 7771121 * 2
def baseEnd_7771121 : Nat := 3990320297248395187048771

theorem tailTrace_7771121 : CollatzResearch.WordTrace tailWord_7771121 prefixEnd_7771121 3990320297248395187048771 := by
  unfold tailWord_7771121
  simp only [CollatzResearch.WordTrace]
  refine ⟨283436068079563293647977217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188957378719708862431984811 283436068079563293647977217)
  ·
    refine ⟨212577051059672470235982913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 283436068079563293647977217 212577051059672470235982913)
    ·
      refine ⟨159432788294754352676987185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 212577051059672470235982913 159432788294754352676987185)
      ·
        refine ⟨119574591221065764507740389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 159432788294754352676987185 119574591221065764507740389)
        ·
          refine ⟨22420235853949830845201323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 119574591221065764507740389 22420235853949830845201323)
          ·
            refine ⟨33630353780924746267801985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22420235853949830845201323 33630353780924746267801985)
            ·
              refine ⟨25222765335693559700851489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33630353780924746267801985 25222765335693559700851489)
              ·
                refine ⟨18917074001770169775638617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25222765335693559700851489 18917074001770169775638617)
                ·
                  refine ⟨14187805501327627331728963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18917074001770169775638617 14187805501327627331728963)
                  ·
                    refine ⟨21281708251991440997593445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14187805501327627331728963 21281708251991440997593445)
                    ·
                      refine ⟨3990320297248395187048771, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21281708251991440997593445 3990320297248395187048771)
                      ·
                        rfl

theorem cell23_7771121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 1, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 1, 2, 2, 2, 1, 4].length) (baseStart_7771121 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7771121 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7771121 prefixEnd_7771121 := by exact prefixLift 7771121
  have htrace : WordTrace (prefixWord ++ tailWord_7771121) baseStart_7771121 baseEnd_7771121 := by
    simpa [prefixWord, tailWord_7771121, baseEnd_7771121] using wordTrace_append hprefix tailTrace_7771121
  have hstable : (prefixWord ++ tailWord_7771121).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7771121).length < 2 ^ (prefixWord ++ tailWord_7771121).sum := by decide
  have hdescent : baseEnd_7771121 < baseStart_7771121 := by decide
  rcases family_descends (prefixWord ++ tailWord_7771121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7771122 : List Nat := [3, 2, 1, 5, 1, 2, 2, 2, 5]
def baseStart_7771122 : Nat := 118140960795 + 7771122 * 2 ^ 59
def prefixEnd_7771122 : Nat := 4983230072969 + 3 ^ 40 * 7771122 * 2
def baseEnd_7771122 : Nat := 443368978969894409237363

theorem tailTrace_7771122 : CollatzResearch.WordTrace tailWord_7771122 prefixEnd_7771122 443368978969894409237363 := by
  unfold tailWord_7771122
  simp only [CollatzResearch.WordTrace]
  refine ⟨70859026138139917704690905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 188957403035039780545842413 70859026138139917704690905)
  ·
    refine ⟨53144269603604938278518179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70859026138139917704690905 53144269603604938278518179)
    ·
      refine ⟨79716404405407407417777269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53144269603604938278518179 79716404405407407417777269)
      ·
        refine ⟨7473412913006944445416619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 79716404405407407417777269 7473412913006944445416619)
        ·
          refine ⟨11210119369510416668124929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7473412913006944445416619 11210119369510416668124929)
          ·
            refine ⟨8407589527132812501093697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11210119369510416668124929 8407589527132812501093697)
            ·
              refine ⟨6305692145349609375820273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8407589527132812501093697 6305692145349609375820273)
              ·
                refine ⟨4729269109012207031865205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6305692145349609375820273 4729269109012207031865205)
                ·
                  refine ⟨443368978969894409237363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4729269109012207031865205 443368978969894409237363)
                  ·
                    rfl

theorem cell23_7771122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 1, 2, 2, 2, 5].length) (baseStart_7771122 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7771122 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7771122 prefixEnd_7771122 := by exact prefixLift 7771122
  have htrace : WordTrace (prefixWord ++ tailWord_7771122) baseStart_7771122 baseEnd_7771122 := by
    simpa [prefixWord, tailWord_7771122, baseEnd_7771122] using wordTrace_append hprefix tailTrace_7771122
  have hstable : (prefixWord ++ tailWord_7771122).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7771122).length < 2 ^ (prefixWord ++ tailWord_7771122).sum := by decide
  have hdescent : baseEnd_7771122 < baseStart_7771122 := by decide
  rcases family_descends (prefixWord ++ tailWord_7771122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7771221 : List Nat := [1, 3, 2, 2, 1, 2, 1, 1, 6, 4]
def baseStart_7771221 : Nat := 118140960795 + 7771221 * 2 ^ 59
def prefixEnd_7771221 : Nat := 4983230072969 + 3 ^ 40 * 7771221 * 2
def baseEnd_7771221 : Nat := 1330123881771281598599437

theorem tailTrace_7771221 : CollatzResearch.WordTrace tailWord_7771221 prefixEnd_7771221 1330123881771281598599437 := by
  unfold tailWord_7771221
  simp only [CollatzResearch.WordTrace]
  refine ⟨283439715379201010726617517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188959810252800673817745011 283439715379201010726617517)
  ·
    refine ⟨106289893267200379022481569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 283439715379201010726617517 106289893267200379022481569)
    ·
      refine ⟨79717419950400284266861177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 106289893267200379022481569 79717419950400284266861177)
      ·
        refine ⟨59788064962800213200145883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79717419950400284266861177 59788064962800213200145883)
        ·
          refine ⟨89682097444200319800218825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59788064962800213200145883 89682097444200319800218825)
          ·
            refine ⟨67261573083150239850164119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 89682097444200319800218825 67261573083150239850164119)
            ·
              refine ⟨100892359624725359775246179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67261573083150239850164119 100892359624725359775246179)
              ·
                refine ⟨151338539437088039662869269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 100892359624725359775246179 151338539437088039662869269)
                ·
                  refine ⟨7093994036113501859196997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 151338539437088039662869269 7093994036113501859196997)
                  ·
                    refine ⟨1330123881771281598599437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7093994036113501859196997 1330123881771281598599437)
                    ·
                      rfl

theorem cell23_7771221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 1, 1, 6, 4].length) (baseStart_7771221 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7771221 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7771221 prefixEnd_7771221 := by exact prefixLift 7771221
  have htrace : WordTrace (prefixWord ++ tailWord_7771221) baseStart_7771221 baseEnd_7771221 := by
    simpa [prefixWord, tailWord_7771221, baseEnd_7771221] using wordTrace_append hprefix tailTrace_7771221
  have hstable : (prefixWord ++ tailWord_7771221).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7771221).length < 2 ^ (prefixWord ++ tailWord_7771221).sum := by decide
  have hdescent : baseEnd_7771221 < baseStart_7771221 := by decide
  rcases family_descends (prefixWord ++ tailWord_7771221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7771228 : List Nat := [2, 2, 4, 1, 1, 1, 1, 5, 1, 1, 4]
def baseStart_7771228 : Nat := 118140960795 + 7771228 * 2 ^ 59
def prefixEnd_7771228 : Nat := 4983230072969 + 3 ^ 40 * 7771228 * 2
def baseEnd_7771228 : Nat := 3990375239678426268410779

theorem tailTrace_7771228 : CollatzResearch.WordTrace tailWord_7771228 prefixEnd_7771228 3990375239678426268410779 := by
  unfold tailWord_7771228
  simp only [CollatzResearch.WordTrace]
  refine ⟨141719985345087825461061169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 188959980460117100614748225 141719985345087825461061169)
  ·
    refine ⟨106289989008815869095795877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 141719985345087825461061169 106289989008815869095795877)
    ·
      refine ⟨19929372939152975455461727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 106289989008815869095795877 19929372939152975455461727)
      ·
        refine ⟨29894059408729463183192591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19929372939152975455461727 29894059408729463183192591)
        ·
          refine ⟨44841089113094194774788887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29894059408729463183192591 44841089113094194774788887)
          ·
            refine ⟨67261633669641292162183331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44841089113094194774788887 67261633669641292162183331)
            ·
              refine ⟨100892450504461938243274997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67261633669641292162183331 100892450504461938243274997)
              ·
                refine ⟨9458667234793306710307031, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 100892450504461938243274997 9458667234793306710307031)
                ·
                  refine ⟨14188000852189960065460547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9458667234793306710307031 14188000852189960065460547)
                  ·
                    refine ⟨21282001278284940098190821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14188000852189960065460547 21282001278284940098190821)
                    ·
                      refine ⟨3990375239678426268410779, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21282001278284940098190821 3990375239678426268410779)
                      ·
                        rfl

theorem cell23_7771228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 1, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 1, 5, 1, 1, 4].length) (baseStart_7771228 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7771228 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7771228 prefixEnd_7771228 := by exact prefixLift 7771228
  have htrace : WordTrace (prefixWord ++ tailWord_7771228) baseStart_7771228 baseEnd_7771228 := by
    simpa [prefixWord, tailWord_7771228, baseEnd_7771228] using wordTrace_append hprefix tailTrace_7771228
  have hstable : (prefixWord ++ tailWord_7771228).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7771228).length < 2 ^ (prefixWord ++ tailWord_7771228).sum := by decide
  have hdescent : baseEnd_7771228 < baseStart_7771228 := by decide
  rcases family_descends (prefixWord ++ tailWord_7771228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7771231 : List Nat := [1, 1, 2, 3, 1, 1, 6, 1, 1, 1, 5]
def baseStart_7771231 : Nat := 118140960795 + 7771231 * 2 ^ 59
def prefixEnd_7771231 : Nat := 4983230072969 + 3 ^ 40 * 7771231 * 2
def baseEnd_7771231 : Nat := 3990376780120389756673265

theorem tailTrace_7771231 : CollatzResearch.WordTrace tailWord_7771231 prefixEnd_7771231 3990376780120389756673265 := by
  unfold tailWord_7771231
  simp only [CollatzResearch.WordTrace]
  refine ⟨283440080109164782434481547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188960053406109854956321031 283440080109164782434481547)
  ·
    refine ⟨425160120163747173651722321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 283440080109164782434481547 425160120163747173651722321)
    ·
      refine ⟨318870090122810380238791741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 425160120163747173651722321 318870090122810380238791741)
      ·
        refine ⟨119576283796053892589546903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 318870090122810380238791741 119576283796053892589546903)
        ·
          refine ⟨179364425694080838884320355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 119576283796053892589546903 179364425694080838884320355)
          ·
            refine ⟨269046638541121258326480533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 179364425694080838884320355 269046638541121258326480533)
            ·
              refine ⟨12611561181615058984053775, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 269046638541121258326480533 12611561181615058984053775)
              ·
                refine ⟨18917341772422588476080663, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12611561181615058984053775 18917341772422588476080663)
                ·
                  refine ⟨28376012658633882714120995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18917341772422588476080663 28376012658633882714120995)
                  ·
                    refine ⟨42564018987950824071181493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 28376012658633882714120995 42564018987950824071181493)
                    ·
                      refine ⟨3990376780120389756673265, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 42564018987950824071181493 3990376780120389756673265)
                      ·
                        rfl

theorem cell23_7771231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 6, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 6, 1, 1, 1, 5].length) (baseStart_7771231 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7771231 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7771231 prefixEnd_7771231 := by exact prefixLift 7771231
  have htrace : WordTrace (prefixWord ++ tailWord_7771231) baseStart_7771231 baseEnd_7771231 := by
    simpa [prefixWord, tailWord_7771231, baseEnd_7771231] using wordTrace_append hprefix tailTrace_7771231
  have hstable : (prefixWord ++ tailWord_7771231).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7771231).length < 2 ^ (prefixWord ++ tailWord_7771231).sum := by decide
  have hdescent : baseEnd_7771231 < baseStart_7771231 := by decide
  rcases family_descends (prefixWord ++ tailWord_7771231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7771265 : List Nat := [1, 2, 4, 2, 2, 1, 3, 2, 1, 2, 3]
def baseStart_7771265 : Nat := 118140960795 + 7771265 * 2 ^ 59
def prefixEnd_7771265 : Nat := 4983230072969 + 3 ^ 40 * 7771265 * 2
def baseEnd_7771265 : Nat := 3990394238462642623648109

theorem tailTrace_7771265 : CollatzResearch.WordTrace tailWord_7771265 prefixEnd_7771265 3990394238462642623648109 := by
  unfold tailWord_7771265
  simp only [CollatzResearch.WordTrace]
  refine ⟨283441320191041606241219249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188960880127361070827479499 283441320191041606241219249)
  ·
    refine ⟨212580990143281204680914437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 283441320191041606241219249 212580990143281204680914437)
    ·
      refine ⟨39858935651865225877671457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 212580990143281204680914437 39858935651865225877671457)
      ·
        refine ⟨29894201738898919408253593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39858935651865225877671457 29894201738898919408253593)
        ·
          refine ⟨22420651304174189556190195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29894201738898919408253593 22420651304174189556190195)
          ·
            refine ⟨33630976956261284334285293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22420651304174189556190195 33630976956261284334285293)
            ·
              refine ⟨12611616358597981625356985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33630976956261284334285293 12611616358597981625356985)
              ·
                refine ⟨9458712268948486219017739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12611616358597981625356985 9458712268948486219017739)
                ·
                  refine ⟨14188068403422729328526609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9458712268948486219017739 14188068403422729328526609)
                  ·
                    refine ⟨10641051302567046996394957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14188068403422729328526609 10641051302567046996394957)
                    ·
                      refine ⟨3990394238462642623648109, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10641051302567046996394957 3990394238462642623648109)
                      ·
                        rfl

theorem cell23_7771265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 1, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 1, 3, 2, 1, 2, 3].length) (baseStart_7771265 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7771265 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7771265 prefixEnd_7771265 := by exact prefixLift 7771265
  have htrace : WordTrace (prefixWord ++ tailWord_7771265) baseStart_7771265 baseEnd_7771265 := by
    simpa [prefixWord, tailWord_7771265, baseEnd_7771265] using wordTrace_append hprefix tailTrace_7771265
  have hstable : (prefixWord ++ tailWord_7771265).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7771265).length < 2 ^ (prefixWord ++ tailWord_7771265).sum := by decide
  have hdescent : baseEnd_7771265 < baseStart_7771265 := by decide
  rcases family_descends (prefixWord ++ tailWord_7771265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7771278 : List Nat := [4, 1, 1, 3, 2, 1, 1, 1, 3, 3, 3]
def baseStart_7771278 : Nat := 118140960795 + 7771278 * 2 ^ 59
def prefixEnd_7771278 : Nat := 4983230072969 + 3 ^ 40 * 7771278 * 2
def baseEnd_7771278 : Nat := 3990400913711151072785549

theorem tailTrace_7771278 : CollatzResearch.WordTrace tailWord_7771278 prefixEnd_7771278 3990400913711151072785549 := by
  unfold tailWord_7771278
  simp only [CollatzResearch.WordTrace]
  refine ⟨35430224292499313682680311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 188961196226663006307628325 35430224292499313682680311)
  ·
    refine ⟨53145336438748970524020467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35430224292499313682680311 53145336438748970524020467)
    ·
      refine ⟨79718004658123455786030701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53145336438748970524020467 79718004658123455786030701)
      ·
        refine ⟨29894251746796295919761513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 79718004658123455786030701 29894251746796295919761513)
        ·
          refine ⟨22420688810097221939821135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29894251746796295919761513 22420688810097221939821135)
          ·
            refine ⟨33631033215145832909731703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22420688810097221939821135 33631033215145832909731703)
            ·
              refine ⟨50446549822718749364597555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33631033215145832909731703 50446549822718749364597555)
              ·
                refine ⟨75669824734078124046896333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50446549822718749364597555 75669824734078124046896333)
                ·
                  refine ⟨28376184275279296517586125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 75669824734078124046896333 28376184275279296517586125)
                  ·
                    refine ⟨10641069103229736194094797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 28376184275279296517586125 10641069103229736194094797)
                    ·
                      refine ⟨3990400913711151072785549, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10641069103229736194094797 3990400913711151072785549)
                      ·
                        rfl

theorem cell23_7771278_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 1, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 1, 1, 1, 3, 3, 3].length) (baseStart_7771278 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7771278 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7771278 prefixEnd_7771278 := by exact prefixLift 7771278
  have htrace : WordTrace (prefixWord ++ tailWord_7771278) baseStart_7771278 baseEnd_7771278 := by
    simpa [prefixWord, tailWord_7771278, baseEnd_7771278] using wordTrace_append hprefix tailTrace_7771278
  have hstable : (prefixWord ++ tailWord_7771278).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7771278).length < 2 ^ (prefixWord ++ tailWord_7771278).sum := by decide
  have hdescent : baseEnd_7771278 < baseStart_7771278 := by decide
  rcases family_descends (prefixWord ++ tailWord_7771278) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7771282 : List Nat := [3, 2, 3, 1, 1, 3, 3, 1, 1, 2, 3]
def baseStart_7771282 : Nat := 118140960795 + 7771282 * 2 ^ 59
def prefixEnd_7771282 : Nat := 4983230072969 + 3 ^ 40 * 7771282 * 2
def baseEnd_7771282 : Nat := 3990402967633769057135531

theorem tailTrace_7771282 : CollatzResearch.WordTrace tailWord_7771282 prefixEnd_7771282 3990402967633769057135531 := by
  unfold tailWord_7771282
  simp only [CollatzResearch.WordTrace]
  refine ⟨70860485057995004536147025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 188961293487986678763058733 70860485057995004536147025)
  ·
    refine ⟨53145363793496253402110269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70860485057995004536147025 53145363793496253402110269)
    ·
      refine ⟨19929511422561095025791351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 53145363793496253402110269 19929511422561095025791351)
      ·
        refine ⟨29894267133841642538687027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19929511422561095025791351 29894267133841642538687027)
        ·
          refine ⟨44841400700762463808030541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29894267133841642538687027 44841400700762463808030541)
          ·
            refine ⟨16815525262785923928011453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 44841400700762463808030541 16815525262785923928011453)
            ·
              refine ⟨6305821973544721473004295, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16815525262785923928011453 6305821973544721473004295)
              ·
                refine ⟨9458732960317082209506443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6305821973544721473004295 9458732960317082209506443)
                ·
                  refine ⟨14188099440475623314259665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9458732960317082209506443 14188099440475623314259665)
                  ·
                    refine ⟨10641074580356717485694749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14188099440475623314259665 10641074580356717485694749)
                    ·
                      refine ⟨3990402967633769057135531, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10641074580356717485694749 3990402967633769057135531)
                      ·
                        rfl

theorem cell23_7771282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 3, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 3, 3, 1, 1, 2, 3].length) (baseStart_7771282 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7771282 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7771282 prefixEnd_7771282 := by exact prefixLift 7771282
  have htrace : WordTrace (prefixWord ++ tailWord_7771282) baseStart_7771282 baseEnd_7771282 := by
    simpa [prefixWord, tailWord_7771282, baseEnd_7771282] using wordTrace_append hprefix tailTrace_7771282
  have hstable : (prefixWord ++ tailWord_7771282).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7771282).length < 2 ^ (prefixWord ++ tailWord_7771282).sum := by decide
  have hdescent : baseEnd_7771282 < baseStart_7771282 := by decide
  rcases family_descends (prefixWord ++ tailWord_7771282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7771301 : List Nat := [1, 3, 1, 2, 1, 4, 1, 1, 2, 3, 4]
def baseStart_7771301 : Nat := 118140960795 + 7771301 * 2 ^ 59
def prefixEnd_7771301 : Nat := 4983230072969 + 3 ^ 40 * 7771301 * 2
def baseEnd_7771301 : Nat := 3990412723766204482797943

theorem tailTrace_7771301 : CollatzResearch.WordTrace tailWord_7771301 prefixEnd_7771301 3990412723766204482797943 := by
  unfold tailWord_7771301
  simp only [CollatzResearch.WordTrace]
  refine ⟨283442633218911184389529757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188961755479274122926353171 283442633218911184389529757)
  ·
    refine ⟨106290987457091694146073659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 283442633218911184389529757 106290987457091694146073659)
    ·
      refine ⟨159436481185637541219110489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106290987457091694146073659 159436481185637541219110489)
      ·
        refine ⟨119577360889228155914332867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 159436481185637541219110489 119577360889228155914332867)
        ·
          refine ⟨179366041333842233871499301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 119577360889228155914332867 179366041333842233871499301)
          ·
            refine ⟨33631132750095418850906119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 179366041333842233871499301 33631132750095418850906119)
            ·
              refine ⟨50446699125143128276359179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33631132750095418850906119 50446699125143128276359179)
              ·
                refine ⟨75670048687714692414538769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50446699125143128276359179 75670048687714692414538769)
                ·
                  refine ⟨56752536515786019310904077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 75670048687714692414538769 56752536515786019310904077)
                  ·
                    refine ⟨21282201193419757241589029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 56752536515786019310904077 21282201193419757241589029)
                    ·
                      refine ⟨3990412723766204482797943, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21282201193419757241589029 3990412723766204482797943)
                      ·
                        rfl

theorem cell23_7771301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 4, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 4, 1, 1, 2, 3, 4].length) (baseStart_7771301 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7771301 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7771301 prefixEnd_7771301 := by exact prefixLift 7771301
  have htrace : WordTrace (prefixWord ++ tailWord_7771301) baseStart_7771301 baseEnd_7771301 := by
    simpa [prefixWord, tailWord_7771301, baseEnd_7771301] using wordTrace_append hprefix tailTrace_7771301
  have hstable : (prefixWord ++ tailWord_7771301).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7771301).length < 2 ^ (prefixWord ++ tailWord_7771301).sum := by decide
  have hdescent : baseEnd_7771301 < baseStart_7771301 := by decide
  rcases family_descends (prefixWord ++ tailWord_7771301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7771352 : List Nat := [2, 1, 2, 2, 5, 1, 1, 1, 4, 2, 2]
def baseStart_7771352 : Nat := 118140960795 + 7771352 * 2 ^ 59
def prefixEnd_7771352 : Nat := 4983230072969 + 3 ^ 40 * 7771352 * 2
def baseEnd_7771352 : Nat := 3990438911279583783260209

theorem tailTrace_7771352 : CollatzResearch.WordTrace tailWord_7771352 prefixEnd_7771352 3990438911279583783260209 := by
  unfold tailWord_7771352
  simp only [CollatzResearch.WordTrace]
  refine ⟨141722246670863210049818155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 188962995561150946733090873 141722246670863210049818155)
  ·
    refine ⟨212583370006294815074727233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141722246670863210049818155 212583370006294815074727233)
    ·
      refine ⟨159437527504721111306045425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 212583370006294815074727233 159437527504721111306045425)
      ·
        refine ⟨119578145628540833479534069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 159437527504721111306045425 119578145628540833479534069)
        ·
          refine ⟨11210451152675703138706319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 119578145628540833479534069 11210451152675703138706319)
          ·
            refine ⟨16815676729013554708059479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11210451152675703138706319 16815676729013554708059479)
            ·
              refine ⟨25223515093520332062089219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16815676729013554708059479 25223515093520332062089219)
              ·
                refine ⟨37835272640280498093133829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25223515093520332062089219 37835272640280498093133829)
                ·
                  refine ⟨7094113620052593392462593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 37835272640280498093133829 7094113620052593392462593)
                  ·
                    refine ⟨5320585215039445044346945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7094113620052593392462593 5320585215039445044346945)
                    ·
                      refine ⟨3990438911279583783260209, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5320585215039445044346945 3990438911279583783260209)
                      ·
                        rfl

theorem cell23_7771352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 5, 1, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 5, 1, 1, 1, 4, 2, 2].length) (baseStart_7771352 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7771352 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7771352 prefixEnd_7771352 := by exact prefixLift 7771352
  have htrace : WordTrace (prefixWord ++ tailWord_7771352) baseStart_7771352 baseEnd_7771352 := by
    simpa [prefixWord, tailWord_7771352, baseEnd_7771352] using wordTrace_append hprefix tailTrace_7771352
  have hstable : (prefixWord ++ tailWord_7771352).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7771352).length < 2 ^ (prefixWord ++ tailWord_7771352).sum := by decide
  have hdescent : baseEnd_7771352 < baseStart_7771352 := by decide
  rcases family_descends (prefixWord ++ tailWord_7771352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7771368 : List Nat := [2, 1, 4, 1, 2, 1, 1, 3, 2, 3, 3]
def baseStart_7771368 : Nat := 118140960795 + 7771368 * 2 ^ 59
def prefixEnd_7771368 : Nat := 4983230072969 + 3 ^ 40 * 7771368 * 2
def baseEnd_7771368 : Nat := 3990447126970055720660135

theorem tailTrace_7771368 : CollatzResearch.WordTrace tailWord_7771368 prefixEnd_7771368 3990447126970055720660135 := by
  unfold tailWord_7771368
  simp only [CollatzResearch.WordTrace]
  refine ⟨141722538454834227416109379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 188963384606445636554812505 141722538454834227416109379)
  ·
    refine ⟨212583807682251341124164069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141722538454834227416109379 212583807682251341124164069)
    ·
      refine ⟨39859463940422126460780763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 212583807682251341124164069 39859463940422126460780763)
      ·
        refine ⟨59789195910633189691171145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39859463940422126460780763 59789195910633189691171145)
        ·
          refine ⟨44841896932974892268378359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59789195910633189691171145 44841896932974892268378359)
          ·
            refine ⟨67262845399462338402567539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44841896932974892268378359 67262845399462338402567539)
            ·
              refine ⟨100894268099193507603851309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67262845399462338402567539 100894268099193507603851309)
              ·
                refine ⟨37835350537197565351444241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 100894268099193507603851309 37835350537197565351444241)
                ·
                  refine ⟨28376512902898174013583181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37835350537197565351444241 28376512902898174013583181)
                  ·
                    refine ⟨10641192338586815255093693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 28376512902898174013583181 10641192338586815255093693)
                    ·
                      refine ⟨3990447126970055720660135, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10641192338586815255093693 3990447126970055720660135)
                      ·
                        rfl

theorem cell23_7771368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 1, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 1, 3, 2, 3, 3].length) (baseStart_7771368 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7771368 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7771368 prefixEnd_7771368 := by exact prefixLift 7771368
  have htrace : WordTrace (prefixWord ++ tailWord_7771368) baseStart_7771368 baseEnd_7771368 := by
    simpa [prefixWord, tailWord_7771368, baseEnd_7771368] using wordTrace_append hprefix tailTrace_7771368
  have hstable : (prefixWord ++ tailWord_7771368).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7771368).length < 2 ^ (prefixWord ++ tailWord_7771368).sum := by decide
  have hdescent : baseEnd_7771368 < baseStart_7771368 := by decide
  rcases family_descends (prefixWord ++ tailWord_7771368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7771371 : List Nat := [1, 1, 1, 1, 2, 6, 1, 2, 1, 7]
def baseStart_7771371 : Nat := 118140960795 + 7771371 * 2 ^ 59
def prefixEnd_7771371 : Nat := 4983230072969 + 3 ^ 40 * 7771371 * 2
def baseEnd_7771371 : Nat := 1330149555804006402974207

theorem tailTrace_7771371 : CollatzResearch.WordTrace tailWord_7771371 prefixEnd_7771371 1330149555804006402974207 := by
  unfold tailWord_7771371
  simp only [CollatzResearch.WordTrace]
  refine ⟨283445186328657586344577967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188963457552438390896385311 283445186328657586344577967)
  ·
    refine ⟨425167779492986379516866951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 283445186328657586344577967 425167779492986379516866951)
    ·
      refine ⟨637751669239479569275300427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 425167779492986379516866951 637751669239479569275300427)
      ·
        refine ⟨956627503859219353912950641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 637751669239479569275300427 956627503859219353912950641)
        ·
          refine ⟨717470627894414515434712981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 956627503859219353912950641 717470627894414515434712981)
          ·
            refine ⟨33631435682550680411002171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 717470627894414515434712981 33631435682550680411002171)
            ·
              refine ⟨50447153523826020616503257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33631435682550680411002171 50447153523826020616503257)
              ·
                refine ⟨37835365142869515462377443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50447153523826020616503257 37835365142869515462377443)
                ·
                  refine ⟨56753047714304273193566165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37835365142869515462377443 56753047714304273193566165)
                  ·
                    refine ⟨1330149555804006402974207, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 56753047714304273193566165 1330149555804006402974207)
                    ·
                      rfl

theorem cell23_7771371_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 6, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 6, 1, 2, 1, 7].length) (baseStart_7771371 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7771371 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7771371 prefixEnd_7771371 := by exact prefixLift 7771371
  have htrace : WordTrace (prefixWord ++ tailWord_7771371) baseStart_7771371 baseEnd_7771371 := by
    simpa [prefixWord, tailWord_7771371, baseEnd_7771371] using wordTrace_append hprefix tailTrace_7771371
  have hstable : (prefixWord ++ tailWord_7771371).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7771371).length < 2 ^ (prefixWord ++ tailWord_7771371).sum := by decide
  have hdescent : baseEnd_7771371 < baseStart_7771371 := by decide
  rcases family_descends (prefixWord ++ tailWord_7771371) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7771445 : List Nat := [1, 3, 3, 1, 2, 2, 1, 3, 2, 2, 3]
def baseStart_7771445 : Nat := 118140960795 + 7771445 * 2 ^ 59
def prefixEnd_7771445 : Nat := 4983230072969 + 3 ^ 40 * 7771445 * 2
def baseEnd_7771445 : Nat := 3990486664980451919397281

theorem tailTrace_7771445 : CollatzResearch.WordTrace tailWord_7771445 prefixEnd_7771445 3990486664980451919397281 := by
  unfold tailWord_7771445
  simp only [CollatzResearch.WordTrace]
  refine ⟨283447885330389496982771789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188965256886926331321847859 283447885330389496982771789)
  ·
    refine ⟨106292956998896061368539421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 283447885330389496982771789 106292956998896061368539421)
    ·
      refine ⟨39859858874586023013202283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 106292956998896061368539421 39859858874586023013202283)
      ·
        refine ⟨59789788311879034519803425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39859858874586023013202283 59789788311879034519803425)
        ·
          refine ⟨44842341233909275889852569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59789788311879034519803425 44842341233909275889852569)
          ·
            refine ⟨33631755925431956917389427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44842341233909275889852569 33631755925431956917389427)
            ·
              refine ⟨50447633888147935376084141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33631755925431956917389427 50447633888147935376084141)
              ·
                refine ⟨18917862708055475766031553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 50447633888147935376084141 18917862708055475766031553)
                ·
                  refine ⟨14188397031041606824523665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18917862708055475766031553 14188397031041606824523665)
                  ·
                    refine ⟨10641297773281205118392749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14188397031041606824523665 10641297773281205118392749)
                    ·
                      refine ⟨3990486664980451919397281, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10641297773281205118392749 3990486664980451919397281)
                      ·
                        rfl

theorem cell23_7771445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 2, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 2, 1, 3, 2, 2, 3].length) (baseStart_7771445 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7771445 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7771445 prefixEnd_7771445 := by exact prefixLift 7771445
  have htrace : WordTrace (prefixWord ++ tailWord_7771445) baseStart_7771445 baseEnd_7771445 := by
    simpa [prefixWord, tailWord_7771445, baseEnd_7771445] using wordTrace_append hprefix tailTrace_7771445
  have hstable : (prefixWord ++ tailWord_7771445).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7771445).length < 2 ^ (prefixWord ++ tailWord_7771445).sum := by decide
  have hdescent : baseEnd_7771445 < baseStart_7771445 := by decide
  rcases family_descends (prefixWord ++ tailWord_7771445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7771475 : List Nat := [1, 1, 1, 2, 1, 1, 6, 3, 3, 1, 3]
def baseStart_7771475 : Nat := 118140960795 + 7771475 * 2 ^ 59
def prefixEnd_7771475 : Nat := 4983230072969 + 3 ^ 40 * 7771475 * 2
def baseEnd_7771475 : Nat := 3990502069400086802022143

theorem tailTrace_7771475 : CollatzResearch.WordTrace tailWord_7771475 prefixEnd_7771475 3990502069400086802022143 := by
  unfold tailWord_7771475
  simp only [CollatzResearch.WordTrace]
  refine ⟨283448979520280812106363879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188965986346853874737575919 283448979520280812106363879)
  ·
    refine ⟨425173469280421218159545819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 283448979520280812106363879 425173469280421218159545819)
    ·
      refine ⟨637760203920631827239318729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 425173469280421218159545819 637760203920631827239318729)
      ·
        refine ⟨478320152940473870429489047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 637760203920631827239318729 478320152940473870429489047)
        ·
          refine ⟨717480229410710805644233571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 478320152940473870429489047 717480229410710805644233571)
          ·
            refine ⟨1076220344116066208466350357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 717480229410710805644233571 1076220344116066208466350357)
            ·
              refine ⟨50447828630440603521860173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 1076220344116066208466350357 50447828630440603521860173)
              ·
                refine ⟨18917935736415226320697565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 50447828630440603521860173 18917935736415226320697565)
                ·
                  refine ⟨7094225901155709870261587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18917935736415226320697565 7094225901155709870261587)
                  ·
                    refine ⟨10641338851733564805392381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7094225901155709870261587 10641338851733564805392381)
                    ·
                      refine ⟨3990502069400086802022143, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10641338851733564805392381 3990502069400086802022143)
                      ·
                        rfl

theorem cell23_7771475_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 6, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 6, 3, 3, 1, 3].length) (baseStart_7771475 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7771475 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7771475 prefixEnd_7771475 := by exact prefixLift 7771475
  have htrace : WordTrace (prefixWord ++ tailWord_7771475) baseStart_7771475 baseEnd_7771475 := by
    simpa [prefixWord, tailWord_7771475, baseEnd_7771475] using wordTrace_append hprefix tailTrace_7771475
  have hstable : (prefixWord ++ tailWord_7771475).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7771475).length < 2 ^ (prefixWord ++ tailWord_7771475).sum := by decide
  have hdescent : baseEnd_7771475 < baseStart_7771475 := by decide
  rcases family_descends (prefixWord ++ tailWord_7771475) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7771492 : List Nat := [2, 3, 1, 1, 3, 3, 1, 2, 3, 1, 3]
def baseStart_7771492 : Nat := 118140960795 + 7771492 * 2 ^ 59
def prefixEnd_7771492 : Nat := 4983230072969 + 3 ^ 40 * 7771492 * 2
def baseEnd_7771492 : Nat := 3990510798571213235509565

theorem tailTrace_7771492 : CollatzResearch.WordTrace tailWord_7771492 prefixEnd_7771492 3990510798571213235509565 := by
  unfold tailWord_7771492
  simp only [CollatzResearch.WordTrace]
  refine ⟨141724799780609612004866365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 188966399707479482673155153 141724799780609612004866365)
  ·
    refine ⟨53146799917728604501824887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 141724799780609612004866365 53146799917728604501824887)
    ·
      refine ⟨79720199876592906752737331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53146799917728604501824887 79720199876592906752737331)
      ·
        refine ⟨119580299814889360129105997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79720199876592906752737331 119580299814889360129105997)
        ·
          refine ⟨44842612430583510048414749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 119580299814889360129105997 44842612430583510048414749)
          ·
            refine ⟨16815979661468816268155531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 44842612430583510048414749 16815979661468816268155531)
            ·
              refine ⟨25223969492203224402233297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16815979661468816268155531 25223969492203224402233297)
              ·
                refine ⟨18917977119152418301674973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25223969492203224402233297 18917977119152418301674973)
                ·
                  refine ⟨7094241419682156863128115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18917977119152418301674973 7094241419682156863128115)
                  ·
                    refine ⟨10641362129523235294692173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7094241419682156863128115 10641362129523235294692173)
                    ·
                      refine ⟨3990510798571213235509565, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10641362129523235294692173 3990510798571213235509565)
                      ·
                        rfl

theorem cell23_7771492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 3, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 3, 1, 2, 3, 1, 3].length) (baseStart_7771492 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7771492 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7771492 prefixEnd_7771492 := by exact prefixLift 7771492
  have htrace : WordTrace (prefixWord ++ tailWord_7771492) baseStart_7771492 baseEnd_7771492 := by
    simpa [prefixWord, tailWord_7771492, baseEnd_7771492] using wordTrace_append hprefix tailTrace_7771492
  have hstable : (prefixWord ++ tailWord_7771492).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7771492).length < 2 ^ (prefixWord ++ tailWord_7771492).sum := by decide
  have hdescent : baseEnd_7771492 < baseStart_7771492 := by decide
  rcases family_descends (prefixWord ++ tailWord_7771492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7771515 : List Nat := [1, 1, 1, 1, 1, 6, 3, 3, 1, 1, 4]
def baseStart_7771515 : Nat := 118140960795 + 7771515 * 2 ^ 59
def prefixEnd_7771515 : Nat := 4983230072969 + 3 ^ 40 * 7771515 * 2
def baseEnd_7771515 : Nat := 3990522608626266645521959

theorem tailTrace_7771515 : CollatzResearch.WordTrace tailWord_7771515 prefixEnd_7771515 3990522608626266645521959 := by
  unfold tailWord_7771515
  simp only [CollatzResearch.WordTrace]
  refine ⟨283450438440135898937819999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188966958960090599291879999 283450438440135898937819999)
  ·
    refine ⟨425175657660203848406729999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 283450438440135898937819999 425175657660203848406729999)
    ·
      refine ⟨637763486490305772610094999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 425175657660203848406729999 637763486490305772610094999)
      ·
        refine ⟨956645229735458658915142499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 637763486490305772610094999 956645229735458658915142499)
        ·
          refine ⟨1434967844603187988372713749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 956645229735458658915142499 1434967844603187988372713749)
          ·
            refine ⟨67264117715774436954970957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 1434967844603187988372713749 67264117715774436954970957)
            ·
              refine ⟨25224044143415413858114109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 67264117715774436954970957 25224044143415413858114109)
              ·
                refine ⟨9459016553780780196792791, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25224044143415413858114109 9459016553780780196792791)
                ·
                  refine ⟨14188524830671170295189187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9459016553780780196792791 14188524830671170295189187)
                  ·
                    refine ⟨21282787246006755442783781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14188524830671170295189187 21282787246006755442783781)
                    ·
                      refine ⟨3990522608626266645521959, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21282787246006755442783781 3990522608626266645521959)
                      ·
                        rfl

theorem cell23_7771515_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 3, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 3, 3, 1, 1, 4].length) (baseStart_7771515 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7771515 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7771515 prefixEnd_7771515 := by exact prefixLift 7771515
  have htrace : WordTrace (prefixWord ++ tailWord_7771515) baseStart_7771515 baseEnd_7771515 := by
    simpa [prefixWord, tailWord_7771515, baseEnd_7771515] using wordTrace_append hprefix tailTrace_7771515
  have hstable : (prefixWord ++ tailWord_7771515).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7771515).length < 2 ^ (prefixWord ++ tailWord_7771515).sum := by decide
  have hdescent : baseEnd_7771515 < baseStart_7771515 := by decide
  rcases family_descends (prefixWord ++ tailWord_7771515) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7771545 : List Nat := [1, 2, 1, 2, 1, 5, 3, 1, 1, 2, 4]
def baseStart_7771545 : Nat := 118140960795 + 7771545 * 2 ^ 59
def prefixEnd_7771545 : Nat := 4983230072969 + 3 ^ 40 * 7771545 * 2
def baseEnd_7771545 : Nat := 3990538013045901528146821

theorem tailTrace_7771545 : CollatzResearch.WordTrace tailWord_7771545 prefixEnd_7771545 3990538013045901528146821 := by
  unfold tailWord_7771545
  simp only [CollatzResearch.WordTrace]
  refine ⟨283451532630027214061412089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188967688420018142707608059 283451532630027214061412089)
  ·
    refine ⟨212588649472520410546059067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 283451532630027214061412089 212588649472520410546059067)
    ·
      refine ⟨318882974208780615819088601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 212588649472520410546059067 318882974208780615819088601)
      ·
        refine ⟨239162230656585461864316451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 318882974208780615819088601 239162230656585461864316451)
        ·
          refine ⟨358743345984878192796474677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 239162230656585461864316451 358743345984878192796474677)
          ·
            refine ⟨33632188686082330574669501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 358743345984878192796474677 33632188686082330574669501)
            ·
              refine ⟨12612070757280873965501063, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33632188686082330574669501 12612070757280873965501063)
              ·
                refine ⟨18918106135921310948251595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12612070757280873965501063 18918106135921310948251595)
                ·
                  refine ⟨28377159203881966422377393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18918106135921310948251595 28377159203881966422377393)
                  ·
                    refine ⟨21282869402911474816783045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 28377159203881966422377393 21282869402911474816783045)
                    ·
                      refine ⟨3990538013045901528146821, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21282869402911474816783045 3990538013045901528146821)
                      ·
                        rfl

theorem cell23_7771545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 5, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 5, 3, 1, 1, 2, 4].length) (baseStart_7771545 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7771545 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7771545 prefixEnd_7771545 := by exact prefixLift 7771545
  have htrace : WordTrace (prefixWord ++ tailWord_7771545) baseStart_7771545 baseEnd_7771545 := by
    simpa [prefixWord, tailWord_7771545, baseEnd_7771545] using wordTrace_append hprefix tailTrace_7771545
  have hstable : (prefixWord ++ tailWord_7771545).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7771545).length < 2 ^ (prefixWord ++ tailWord_7771545).sum := by decide
  have hdescent : baseEnd_7771545 < baseStart_7771545 := by decide
  rcases family_descends (prefixWord ++ tailWord_7771545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7771549 : List Nat := [1, 4, 2, 1, 3, 1, 2, 2, 3, 2, 2]
def baseStart_7771549 : Nat := 118140960795 + 7771549 * 2 ^ 59
def prefixEnd_7771549 : Nat := 4983230072969 + 3 ^ 40 * 7771549 * 2
def baseEnd_7771549 : Nat := 3990540066968519512496803

theorem tailTrace_7771549 : CollatzResearch.WordTrace tailWord_7771549 prefixEnd_7771549 3990540066968519512496803 := by
  unfold tailWord_7771549
  simp only [CollatzResearch.WordTrace]
  refine ⟨283451678522012722744557701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188967785681341815163038467 283451678522012722744557701)
  ·
    refine ⟨53147189722877385514604569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 283451678522012722744557701 53147189722877385514604569)
    ·
      refine ⟨39860392292158039135953427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53147189722877385514604569 39860392292158039135953427)
      ·
        refine ⟨59790588438237058703930141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39860392292158039135953427 59790588438237058703930141)
        ·
          refine ⟨22421470664338897013973803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 59790588438237058703930141 22421470664338897013973803)
          ·
            refine ⟨33632205996508345520960705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22421470664338897013973803 33632205996508345520960705)
            ·
              refine ⟨25224154497381259140720529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33632205996508345520960705 25224154497381259140720529)
              ·
                refine ⟨18918115873035944355540397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25224154497381259140720529 18918115873035944355540397)
                ·
                  refine ⟨7094293452388479133327649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18918115873035944355540397 7094293452388479133327649)
                  ·
                    refine ⟨5320720089291359349995737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7094293452388479133327649 5320720089291359349995737)
                    ·
                      refine ⟨3990540066968519512496803, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5320720089291359349995737 3990540066968519512496803)
                      ·
                        rfl

theorem cell23_7771549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 1, 2, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 1, 2, 2, 3, 2, 2].length) (baseStart_7771549 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7771549 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7771549 prefixEnd_7771549 := by exact prefixLift 7771549
  have htrace : WordTrace (prefixWord ++ tailWord_7771549) baseStart_7771549 baseEnd_7771549 := by
    simpa [prefixWord, tailWord_7771549, baseEnd_7771549] using wordTrace_append hprefix tailTrace_7771549
  have hstable : (prefixWord ++ tailWord_7771549).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7771549).length < 2 ^ (prefixWord ++ tailWord_7771549).sum := by decide
  have hdescent : baseEnd_7771549 < baseStart_7771549 := by decide
  rcases family_descends (prefixWord ++ tailWord_7771549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7771552 : List Nat := [2, 1, 1, 4, 1, 2, 4, 2, 1, 2, 3]
def baseStart_7771552 : Nat := 118140960795 + 7771552 * 2 ^ 59
def prefixEnd_7771552 : Nat := 4983230072969 + 3 ^ 40 * 7771552 * 2
def baseEnd_7771552 : Nat := 3990541607410483000759289

theorem tailTrace_7771552 : CollatzResearch.WordTrace tailWord_7771552 prefixEnd_7771552 3990541607410483000759289 := by
  unfold tailWord_7771552
  simp only [CollatzResearch.WordTrace]
  refine ⟨141725893970500927128458455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 188967858627334569504611273 141725893970500927128458455)
  ·
    refine ⟨212588840955751390692687683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141725893970500927128458455 212588840955751390692687683)
    ·
      refine ⟨318883261433627086039031525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 212588840955751390692687683 318883261433627086039031525)
      ·
        refine ⟨59790611518805078632318411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 318883261433627086039031525 59790611518805078632318411)
        ·
          refine ⟨89685917278207617948477617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59790611518805078632318411 89685917278207617948477617)
          ·
            refine ⟨67264437958655713461358213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 89685917278207617948477617 67264437958655713461358213)
            ·
              refine ⟨12612082117247946274004665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 67264437958655713461358213 12612082117247946274004665)
              ·
                refine ⟨9459061587935959705503499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12612082117247946274004665 9459061587935959705503499)
                ·
                  refine ⟨14188592381903939558255249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9459061587935959705503499 14188592381903939558255249)
                  ·
                    refine ⟨10641444286427954668691437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14188592381903939558255249 10641444286427954668691437)
                    ·
                      refine ⟨3990541607410483000759289, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10641444286427954668691437 3990541607410483000759289)
                      ·
                        rfl

theorem cell23_7771552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 4, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 4, 2, 1, 2, 3].length) (baseStart_7771552 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7771552 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7771552 prefixEnd_7771552 := by exact prefixLift 7771552
  have htrace : WordTrace (prefixWord ++ tailWord_7771552) baseStart_7771552 baseEnd_7771552 := by
    simpa [prefixWord, tailWord_7771552, baseEnd_7771552] using wordTrace_append hprefix tailTrace_7771552
  have hstable : (prefixWord ++ tailWord_7771552).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7771552).length < 2 ^ (prefixWord ++ tailWord_7771552).sum := by decide
  have hdescent : baseEnd_7771552 < baseStart_7771552 := by decide
  rcases family_descends (prefixWord ++ tailWord_7771552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7771560 : List Nat := [2, 1, 6, 1, 3, 1, 1, 3, 1, 1, 3]
def baseStart_7771560 : Nat := 118140960795 + 7771560 * 2 ^ 59
def prefixEnd_7771560 : Nat := 4983230072969 + 3 ^ 40 * 7771560 * 2
def baseEnd_7771560 : Nat := 3990545715255718969459253

theorem tailTrace_7771560 : CollatzResearch.WordTrace tailWord_7771560 prefixEnd_7771560 3990545715255718969459253 := by
  unfold tailWord_7771560
  simp only [CollatzResearch.WordTrace]
  refine ⟨141726039862486435811604067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 188968053149981914415472089 141726039862486435811604067)
  ·
    refine ⟨212589059793729653717406101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141726039862486435811604067 212589059793729653717406101)
    ·
      refine ⟨9965112177831077518003411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 212589059793729653717406101 9965112177831077518003411)
      ·
        refine ⟨14947668266746616277005117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9965112177831077518003411 14947668266746616277005117)
        ·
          refine ⟨5605375600029981103876919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14947668266746616277005117 5605375600029981103876919)
          ·
            refine ⟨8408063400044971655815379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5605375600029981103876919 8408063400044971655815379)
            ·
              refine ⟨12612095100067457483723069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8408063400044971655815379 12612095100067457483723069)
              ·
                refine ⟨4729535662525296556396151, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12612095100067457483723069 4729535662525296556396151)
                ·
                  refine ⟨7094303493787944834594227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4729535662525296556396151 7094303493787944834594227)
                  ·
                    refine ⟨10641455240681917251891341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7094303493787944834594227 10641455240681917251891341)
                    ·
                      refine ⟨3990545715255718969459253, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10641455240681917251891341 3990545715255718969459253)
                      ·
                        rfl

theorem cell23_7771560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 3, 1, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 3, 1, 1, 3, 1, 1, 3].length) (baseStart_7771560 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7771560 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7771560 prefixEnd_7771560 := by exact prefixLift 7771560
  have htrace : WordTrace (prefixWord ++ tailWord_7771560) baseStart_7771560 baseEnd_7771560 := by
    simpa [prefixWord, tailWord_7771560, baseEnd_7771560] using wordTrace_append hprefix tailTrace_7771560
  have hstable : (prefixWord ++ tailWord_7771560).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7771560).length < 2 ^ (prefixWord ++ tailWord_7771560).sum := by decide
  have hdescent : baseEnd_7771560 < baseStart_7771560 := by decide
  rcases family_descends (prefixWord ++ tailWord_7771560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7771592 : List Nat := [2, 1, 3, 1, 3, 1, 2, 2, 3, 3, 2]
def baseStart_7771592 : Nat := 118140960795 + 7771592 * 2 ^ 59
def prefixEnd_7771592 : Nat := 4983230072969 + 3 ^ 40 * 7771592 * 2
def baseEnd_7771592 : Nat := 3990562146636662844259105

theorem tailTrace_7771592 : CollatzResearch.WordTrace tailWord_7771592 prefixEnd_7771592 3990562146636662844259105 := by
  unfold tailWord_7771592
  simp only [CollatzResearch.WordTrace]
  refine ⟨141726623430428470544186515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 188968831240571294058915353 141726623430428470544186515)
  ·
    refine ⟨212589935145642705816279773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141726623430428470544186515 212589935145642705816279773)
    ·
      refine ⟨79721225679616014681104915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 212589935145642705816279773 79721225679616014681104915)
      ·
        refine ⟨119581838519424022021657373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79721225679616014681104915 119581838519424022021657373)
        ·
          refine ⟨44843189444784008258121515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 119581838519424022021657373 44843189444784008258121515)
          ·
            refine ⟨67264784167176012387182273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44843189444784008258121515 67264784167176012387182273)
            ·
              refine ⟨50448588125382009290386705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 67264784167176012387182273 50448588125382009290386705)
              ·
                refine ⟨37836441094036506967790029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50448588125382009290386705 37836441094036506967790029)
                ·
                  refine ⟨14188665410263690112921261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 37836441094036506967790029 14188665410263690112921261)
                  ·
                    refine ⟨5320749528848883792345473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14188665410263690112921261 5320749528848883792345473)
                    ·
                      refine ⟨3990562146636662844259105, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5320749528848883792345473 3990562146636662844259105)
                      ·
                        rfl

theorem cell23_7771592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 2, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 2, 2, 3, 3, 2].length) (baseStart_7771592 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7771592 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7771592 prefixEnd_7771592 := by exact prefixLift 7771592
  have htrace : WordTrace (prefixWord ++ tailWord_7771592) baseStart_7771592 baseEnd_7771592 := by
    simpa [prefixWord, tailWord_7771592, baseEnd_7771592] using wordTrace_append hprefix tailTrace_7771592
  have hstable : (prefixWord ++ tailWord_7771592).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7771592).length < 2 ^ (prefixWord ++ tailWord_7771592).sum := by decide
  have hdescent : baseEnd_7771592 < baseStart_7771592 := by decide
  rcases family_descends (prefixWord ++ tailWord_7771592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7771599 : List Nat := [1, 1, 2, 1, 1, 4, 6, 1, 2, 1, 3]
def baseStart_7771599 : Nat := 118140960795 + 7771599 * 2 ^ 59
def prefixEnd_7771599 : Nat := 4983230072969 + 3 ^ 40 * 7771599 * 2
def baseEnd_7771599 : Nat := 3990565741001244316871573

theorem tailTrace_7771599 : CollatzResearch.WordTrace tailWord_7771599 prefixEnd_7771599 3990565741001244316871573 := by
  unfold tailWord_7771599
  simp only [CollatzResearch.WordTrace]
  refine ⟨283453502171831581283877851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188969001447887720855918567 283453502171831581283877851)
  ·
    refine ⟨425180253257747371925816777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 283453502171831581283877851 425180253257747371925816777)
    ·
      refine ⟨318885189943310528944362583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 425180253257747371925816777 318885189943310528944362583)
      ·
        refine ⟨478327784914965793416543875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 318885189943310528944362583 478327784914965793416543875)
        ·
          refine ⟨717491677372448690124815813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 478327784914965793416543875 717491677372448690124815813)
          ·
            refine ⟨134529689507334129398402965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 717491677372448690124815813 134529689507334129398402965)
            ·
              refine ⟨6306079195656287315550139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 134529689507334129398402965 6306079195656287315550139)
              ·
                refine ⟨9459118793484430973325209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6306079195656287315550139 9459118793484430973325209)
                ·
                  refine ⟨7094339095113323229993907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9459118793484430973325209 7094339095113323229993907)
                  ·
                    refine ⟨10641508642669984844990861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7094339095113323229993907 10641508642669984844990861)
                    ·
                      refine ⟨3990565741001244316871573, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10641508642669984844990861 3990565741001244316871573)
                      ·
                        rfl

theorem cell23_7771599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 6, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 6, 1, 2, 1, 3].length) (baseStart_7771599 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7771599 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7771599 prefixEnd_7771599 := by exact prefixLift 7771599
  have htrace : WordTrace (prefixWord ++ tailWord_7771599) baseStart_7771599 baseEnd_7771599 := by
    simpa [prefixWord, tailWord_7771599, baseEnd_7771599] using wordTrace_append hprefix tailTrace_7771599
  have hstable : (prefixWord ++ tailWord_7771599).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7771599).length < 2 ^ (prefixWord ++ tailWord_7771599).sum := by decide
  have hdescent : baseEnd_7771599 < baseStart_7771599 := by decide
  rcases family_descends (prefixWord ++ tailWord_7771599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7771609 : List Nat := [1, 2, 1, 2, 4, 2, 3, 2, 1, 3, 2]
def baseStart_7771609 : Nat := 118140960795 + 7771609 * 2 ^ 59
def prefixEnd_7771609 : Nat := 4983230072969 + 3 ^ 40 * 7771609 * 2
def baseEnd_7771609 : Nat := 3990570875807789277746527

theorem tailTrace_7771609 : CollatzResearch.WordTrace tailWord_7771609 prefixEnd_7771609 3990570875807789277746527 := by
  unfold tailWord_7771609
  simp only [CollatzResearch.WordTrace]
  refine ⟨283453866901795352991741881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188969244601196901994494587 283453866901795352991741881)
  ·
    refine ⟨212590400176346514743806411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 283453866901795352991741881 212590400176346514743806411)
    ·
      refine ⟨318885600264519772115709617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 212590400176346514743806411 318885600264519772115709617)
      ·
        refine ⟨239164200198389829086782213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 318885600264519772115709617 239164200198389829086782213)
        ·
          refine ⟨44843287537198092953771665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 239164200198389829086782213 44843287537198092953771665)
          ·
            refine ⟨33632465652898569715328749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44843287537198092953771665 33632465652898569715328749)
            ·
              refine ⟨12612174619836963643248281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33632465652898569715328749 12612174619836963643248281)
              ·
                refine ⟨9459130964877722732436211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12612174619836963643248281 9459130964877722732436211)
                ·
                  refine ⟨14188696447316584098654317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9459130964877722732436211 14188696447316584098654317)
                  ·
                    refine ⟨5320761167743719036995369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14188696447316584098654317 5320761167743719036995369)
                    ·
                      refine ⟨3990570875807789277746527, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5320761167743719036995369 3990570875807789277746527)
                      ·
                        rfl

theorem cell23_7771609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 2, 3, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 2, 3, 2, 1, 3, 2].length) (baseStart_7771609 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7771609 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7771609 prefixEnd_7771609 := by exact prefixLift 7771609
  have htrace : WordTrace (prefixWord ++ tailWord_7771609) baseStart_7771609 baseEnd_7771609 := by
    simpa [prefixWord, tailWord_7771609, baseEnd_7771609] using wordTrace_append hprefix tailTrace_7771609
  have hstable : (prefixWord ++ tailWord_7771609).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7771609).length < 2 ^ (prefixWord ++ tailWord_7771609).sum := by decide
  have hdescent : baseEnd_7771609 < baseStart_7771609 := by decide
  rcases family_descends (prefixWord ++ tailWord_7771609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7771628 : List Nat := [2, 2, 1, 1, 2, 1, 2, 1, 11]
def baseStart_7771628 : Nat := 118140960795 + 7771628 * 2 ^ 59
def prefixEnd_7771628 : Nat := 4983230072969 + 3 ^ 40 * 7771628 * 2
def baseEnd_7771628 : Nat := 443397847993358300378771

theorem tailTrace_7771628 : CollatzResearch.WordTrace tailWord_7771628 prefixEnd_7771628 443397847993358300378771 := by
  unfold tailWord_7771628
  simp only [CollatzResearch.WordTrace]
  refine ⟨141727279944363259618341769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 188969706592484346157789025 141727279944363259618341769)
  ·
    refine ⟨106295459958272444713756327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 141727279944363259618341769 106295459958272444713756327)
    ·
      refine ⟨159443189937408667070634491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106295459958272444713756327 159443189937408667070634491)
      ·
        refine ⟨239164784906113000605951737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 159443189937408667070634491 239164784906113000605951737)
        ·
          refine ⟨179373588679584750454463803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 239164784906113000605951737 179373588679584750454463803)
          ·
            refine ⟨269060383019377125681695705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 179373588679584750454463803 269060383019377125681695705)
            ·
              refine ⟨201795287264532844261271779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 269060383019377125681695705 201795287264532844261271779)
              ·
                refine ⟨302692930896799266391907669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 201795287264532844261271779 302692930896799266391907669)
                ·
                  refine ⟨443397847993358300378771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 11 302692930896799266391907669 443397847993358300378771)
                  ·
                    rfl

theorem cell23_7771628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 11].length) (baseStart_7771628 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7771628 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7771628 prefixEnd_7771628 := by exact prefixLift 7771628
  have htrace : WordTrace (prefixWord ++ tailWord_7771628) baseStart_7771628 baseEnd_7771628 := by
    simpa [prefixWord, tailWord_7771628, baseEnd_7771628] using wordTrace_append hprefix tailTrace_7771628
  have hstable : (prefixWord ++ tailWord_7771628).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7771628).length < 2 ^ (prefixWord ++ tailWord_7771628).sum := by decide
  have hdescent : baseEnd_7771628 < baseStart_7771628 := by decide
  rcases family_descends (prefixWord ++ tailWord_7771628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7771662 : List Nat := [4, 1, 1, 2, 4, 1, 1, 2, 7]
def baseStart_7771662 : Nat := 118140960795 + 7771662 * 2 ^ 59
def prefixEnd_7771662 : Nat := 4983230072969 + 3 ^ 40 * 7771662 * 2
def baseEnd_7771662 : Nat := 443399787809164174487087

theorem tailTrace_7771662 : CollatzResearch.WordTrace tailWord_7771662 prefixEnd_7771662 443399787809164174487087 := by
  unfold tailWord_7771662
  simp only [CollatzResearch.WordTrace]
  refine ⟨35431974996325417880427655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 188970533313735562028947493 35431974996325417880427655)
  ·
    refine ⟨53147962494488126820641483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35431974996325417880427655 53147962494488126820641483)
    ·
      refine ⟨79721943741732190230962225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53147962494488126820641483 79721943741732190230962225)
      ·
        refine ⟨59791457806299142673221669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79721943741732190230962225 59791457806299142673221669)
        ·
          refine ⟨11210898338681089251229063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 59791457806299142673221669 11210898338681089251229063)
          ·
            refine ⟨16816347508021633876843595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11210898338681089251229063 16816347508021633876843595)
            ·
              refine ⟨25224521262032450815265393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16816347508021633876843595 25224521262032450815265393)
              ·
                refine ⟨18918390946524338111449045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25224521262032450815265393 18918390946524338111449045)
                ·
                  refine ⟨443399787809164174487087, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18918390946524338111449045 443399787809164174487087)
                  ·
                    rfl

theorem cell23_7771662_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 4, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 4, 1, 1, 2, 7].length) (baseStart_7771662 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7771662 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7771662 prefixEnd_7771662 := by exact prefixLift 7771662
  have htrace : WordTrace (prefixWord ++ tailWord_7771662) baseStart_7771662 baseEnd_7771662 := by
    simpa [prefixWord, tailWord_7771662, baseEnd_7771662] using wordTrace_append hprefix tailTrace_7771662
  have hstable : (prefixWord ++ tailWord_7771662).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7771662).length < 2 ^ (prefixWord ++ tailWord_7771662).sum := by decide
  have hdescent : baseEnd_7771662 < baseStart_7771662 := by decide
  rcases family_descends (prefixWord ++ tailWord_7771662) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7771722 : List Nat := [3, 1, 2, 1, 1, 3, 1, 4, 3, 4]
def baseStart_7771722 : Nat := 118140960795 + 7771722 * 2 ^ 59
def prefixEnd_7771722 : Nat := 4983230072969 + 3 ^ 40 * 7771722 * 2
def baseEnd_7771722 : Nat := 1330209633040582445211169

theorem tailTrace_7771722 : CollatzResearch.WordTrace tailWord_7771722 prefixEnd_7771722 1330209633040582445211169 := by
  unfold tailWord_7771722
  simp only [CollatzResearch.WordTrace]
  refine ⟨70864497087596493322651355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 188971992233590648860403613 70864497087596493322651355)
  ·
    refine ⟨106296745631394739983977033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70864497087596493322651355 106296745631394739983977033)
    ·
      refine ⟨79722559223546054987982775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 106296745631394739983977033 79722559223546054987982775)
      ·
        refine ⟨119583838835319082481974163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79722559223546054987982775 119583838835319082481974163)
        ·
          refine ⟨179375758252978623722961245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 119583838835319082481974163 179375758252978623722961245)
          ·
            refine ⟨67265909344866983896110467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 179375758252978623722961245 67265909344866983896110467)
            ·
              refine ⟨100898864017300475844165701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67265909344866983896110467 100898864017300475844165701)
              ·
                refine ⟨18918537003243839220781069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 100898864017300475844165701 18918537003243839220781069)
                ·
                  refine ⟨7094451376216439707792901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18918537003243839220781069 7094451376216439707792901)
                  ·
                    refine ⟨1330209633040582445211169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7094451376216439707792901 1330209633040582445211169)
                    ·
                      rfl

theorem cell23_7771722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 1, 4, 3, 4].length) (baseStart_7771722 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7771722 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7771722 prefixEnd_7771722 := by exact prefixLift 7771722
  have htrace : WordTrace (prefixWord ++ tailWord_7771722) baseStart_7771722 baseEnd_7771722 := by
    simpa [prefixWord, tailWord_7771722, baseEnd_7771722] using wordTrace_append hprefix tailTrace_7771722
  have hstable : (prefixWord ++ tailWord_7771722).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7771722).length < 2 ^ (prefixWord ++ tailWord_7771722).sum := by decide
  have hdescent : baseEnd_7771722 < baseStart_7771722 := by decide
  rcases family_descends (prefixWord ++ tailWord_7771722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7771732 : List Nat := [2, 4, 1, 1, 1, 2, 1, 3, 1, 4, 3]
def baseStart_7771732 : Nat := 118140960795 + 7771732 * 2 ^ 59
def prefixEnd_7771732 : Nat := 4983230072969 + 3 ^ 40 * 7771732 * 2
def baseEnd_7771732 : Nat := 3990634033928292296508461

theorem tailTrace_7771732 : CollatzResearch.WordTrace tailWord_7771732 prefixEnd_7771732 3990634033928292296508461 := by
  unfold tailWord_7771732
  simp only [CollatzResearch.WordTrace]
  refine ⟨141729176540174872499234725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 188972235386899829998979633 141729176540174872499234725)
  ·
    refine ⟨26574220601282788593606511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 141729176540174872499234725 26574220601282788593606511)
    ·
      refine ⟨39861330901924182890409767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26574220601282788593606511 39861330901924182890409767)
      ·
        refine ⟨59791996352886274335614651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39861330901924182890409767 59791996352886274335614651)
        ·
          refine ⟨89687994529329411503421977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59791996352886274335614651 89687994529329411503421977)
          ·
            refine ⟨67265995896997058627566483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 89687994529329411503421977 67265995896997058627566483)
            ·
              refine ⟨100898993845495587941349725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67265995896997058627566483 100898993845495587941349725)
              ·
                refine ⟨37837122692060845478006147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 100898993845495587941349725 37837122692060845478006147)
                ·
                  refine ⟨56755684038091268217009221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37837122692060845478006147 56755684038091268217009221)
                  ·
                    refine ⟨10641690757142112790689229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 56755684038091268217009221 10641690757142112790689229)
                    ·
                      refine ⟨3990634033928292296508461, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10641690757142112790689229 3990634033928292296508461)
                      ·
                        rfl

theorem cell23_7771732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 1, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 1, 3, 1, 4, 3].length) (baseStart_7771732 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7771732 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7771732 prefixEnd_7771732 := by exact prefixLift 7771732
  have htrace : WordTrace (prefixWord ++ tailWord_7771732) baseStart_7771732 baseEnd_7771732 := by
    simpa [prefixWord, tailWord_7771732, baseEnd_7771732] using wordTrace_append hprefix tailTrace_7771732
  have hstable : (prefixWord ++ tailWord_7771732).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7771732).length < 2 ^ (prefixWord ++ tailWord_7771732).sum := by decide
  have hdescent : baseEnd_7771732 < baseStart_7771732 := by decide
  rcases family_descends (prefixWord ++ tailWord_7771732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7771735 : List Nat := [1, 1, 3, 2, 2, 3, 1, 2, 8]
def baseStart_7771735 : Nat := 118140960795 + 7771735 * 2 ^ 59
def prefixEnd_7771735 : Nat := 4983230072969 + 3 ^ 40 * 7771735 * 2
def baseEnd_7771735 : Nat := 443403952707806198307883

theorem tailTrace_7771735 : CollatzResearch.WordTrace tailWord_7771735 prefixEnd_7771735 443403952707806198307883 := by
  unfold tailWord_7771735
  simp only [CollatzResearch.WordTrace]
  refine ⟨283458462499338876510828659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188972308332892584340552439 283458462499338876510828659)
  ·
    refine ⟨425187693749008314766242989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 283458462499338876510828659 425187693749008314766242989)
    ·
      refine ⟨159445385155878118037341121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 425187693749008314766242989 159445385155878118037341121)
      ·
        refine ⟨119584038866908588528005841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 159445385155878118037341121 119584038866908588528005841)
        ·
          refine ⟨89688029150181441396004381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 119584038866908588528005841 89688029150181441396004381)
          ·
            refine ⟨33633010931318040523501643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 89688029150181441396004381 33633010931318040523501643)
            ·
              refine ⟨50449516396977060785252465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33633010931318040523501643 50449516396977060785252465)
              ·
                refine ⟨37837137297732795588939349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50449516396977060785252465 37837137297732795588939349)
                ·
                  refine ⟨443403952707806198307883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 37837137297732795588939349 443403952707806198307883)
                  ·
                    rfl

theorem cell23_7771735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 3, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 3, 1, 2, 8].length) (baseStart_7771735 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7771735 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7771735 prefixEnd_7771735 := by exact prefixLift 7771735
  have htrace : WordTrace (prefixWord ++ tailWord_7771735) baseStart_7771735 baseEnd_7771735 := by
    simpa [prefixWord, tailWord_7771735, baseEnd_7771735] using wordTrace_append hprefix tailTrace_7771735
  have hstable : (prefixWord ++ tailWord_7771735).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7771735).length < 2 ^ (prefixWord ++ tailWord_7771735).sum := by decide
  have hdescent : baseEnd_7771735 < baseStart_7771735 := by decide
  rcases family_descends (prefixWord ++ tailWord_7771735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7771749 : List Nat := [1, 3, 1, 3, 3, 2, 1, 2, 2, 2, 3]
def baseStart_7771749 : Nat := 118140960795 + 7771749 * 2 ^ 59
def prefixEnd_7771749 : Nat := 4983230072969 + 3 ^ 40 * 7771749 * 2
def baseEnd_7771749 : Nat := 3990642763099418729995883

theorem tailTrace_7771749 : CollatzResearch.WordTrace tailWord_7771749 prefixEnd_7771749 3990642763099418729995883 := by
  unfold tailWord_7771749
  simp only [CollatzResearch.WordTrace]
  refine ⟨283458973121288156901838301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188972648747525437934558867 283458973121288156901838301)
  ·
    refine ⟨106297114920483058838189363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 283458973121288156901838301 106297114920483058838189363)
    ·
      refine ⟨159445672380724588257284045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106297114920483058838189363 159445672380724588257284045)
      ·
        refine ⟨59792127142771720596481517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 159445672380724588257284045 59792127142771720596481517)
        ·
          refine ⟨22422047678539395223680569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 59792127142771720596481517 22422047678539395223680569)
          ·
            refine ⟨16816535758904546417760427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22422047678539395223680569 16816535758904546417760427)
            ·
              refine ⟨25224803638356819626640641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16816535758904546417760427 25224803638356819626640641)
              ·
                refine ⟨18918602728767614719980481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25224803638356819626640641 18918602728767614719980481)
                ·
                  refine ⟨14188952046575711039985361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18918602728767614719980481 14188952046575711039985361)
                  ·
                    refine ⟨10641714034931783279989021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14188952046575711039985361 10641714034931783279989021)
                    ·
                      refine ⟨3990642763099418729995883, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10641714034931783279989021 3990642763099418729995883)
                      ·
                        rfl

theorem cell23_7771749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 2, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 2, 1, 2, 2, 2, 3].length) (baseStart_7771749 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7771749 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7771749 prefixEnd_7771749 := by exact prefixLift 7771749
  have htrace : WordTrace (prefixWord ++ tailWord_7771749) baseStart_7771749 baseEnd_7771749 := by
    simpa [prefixWord, tailWord_7771749, baseEnd_7771749] using wordTrace_append hprefix tailTrace_7771749
  have hstable : (prefixWord ++ tailWord_7771749).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7771749).length < 2 ^ (prefixWord ++ tailWord_7771749).sum := by decide
  have hdescent : baseEnd_7771749 < baseStart_7771749 := by decide
  rcases family_descends (prefixWord ++ tailWord_7771749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7771752 : List Nat := [2, 1, 4, 3, 1, 1, 2, 1, 8]
def baseStart_7771752 : Nat := 118140960795 + 7771752 * 2 ^ 59
def prefixEnd_7771752 : Nat := 4983230072969 + 3 ^ 40 * 7771752 * 2
def baseEnd_7771752 : Nat := 443404922615709135362041

theorem tailTrace_7771752 : CollatzResearch.WordTrace tailWord_7771752 prefixEnd_7771752 443404922615709135362041 := by
  unfold tailWord_7771752
  simp only [CollatzResearch.WordTrace]
  refine ⟨141729541270138644207098755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 188972721693518192276131673 141729541270138644207098755)
  ·
    refine ⟨212594311905207966310648133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141729541270138644207098755 212594311905207966310648133)
    ·
      refine ⟨39861433482226493683246525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 212594311905207966310648133 39861433482226493683246525)
      ·
        refine ⟨14948037555834935131217447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39861433482226493683246525 14948037555834935131217447)
        ·
          refine ⟨22422056333752402696826171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14948037555834935131217447 22422056333752402696826171)
          ·
            refine ⟨33633084500628604045239257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22422056333752402696826171 33633084500628604045239257)
            ·
              refine ⟨25224813375471453033929443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33633084500628604045239257 25224813375471453033929443)
              ·
                refine ⟨37837220063207179550894165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25224813375471453033929443 37837220063207179550894165)
                ·
                  refine ⟨443404922615709135362041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 37837220063207179550894165 443404922615709135362041)
                  ·
                    rfl

theorem cell23_7771752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 1, 2, 1, 8].length) (baseStart_7771752 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7771752 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7771752 prefixEnd_7771752 := by exact prefixLift 7771752
  have htrace : WordTrace (prefixWord ++ tailWord_7771752) baseStart_7771752 baseEnd_7771752 := by
    simpa [prefixWord, tailWord_7771752, baseEnd_7771752] using wordTrace_append hprefix tailTrace_7771752
  have hstable : (prefixWord ++ tailWord_7771752).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7771752).length < 2 ^ (prefixWord ++ tailWord_7771752).sum := by decide
  have hdescent : baseEnd_7771752 < baseStart_7771752 := by decide
  rcases family_descends (prefixWord ++ tailWord_7771752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7771807 : List Nat := [1, 1, 2, 7, 2, 1, 2, 2, 1, 4]
def baseStart_7771807 : Nat := 118140960795 + 7771807 * 2 ^ 59
def prefixEnd_7771807 : Nat := 4983230072969 + 3 ^ 40 * 7771807 * 2
def baseEnd_7771807 : Nat := 1330224181659126501023539

theorem tailTrace_7771807 : CollatzResearch.WordTrace tailWord_7771807 prefixEnd_7771807 1330224181659126501023539 := by
  unfold tailWord_7771807
  simp only [CollatzResearch.WordTrace]
  refine ⟨283461088555078032807449675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188974059036718688538299783 283461088555078032807449675)
  ·
    refine ⟨425191632832617049211174513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 283461088555078032807449675 425191632832617049211174513)
    ·
      refine ⟨318893724624462786908380885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 425191632832617049211174513 318893724624462786908380885)
      ·
        refine ⟨7474071670885846568165177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 318893724624462786908380885 7474071670885846568165177)
        ·
          refine ⟨5605553753164384926123883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7474071670885846568165177 5605553753164384926123883)
          ·
            refine ⟨8408330629746577389185825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5605553753164384926123883 8408330629746577389185825)
            ·
              refine ⟨6306247972309933041889369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8408330629746577389185825 6306247972309933041889369)
              ·
                refine ⟨4729685979232449781417027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6306247972309933041889369 4729685979232449781417027)
                ·
                  refine ⟨7094528968848674672125541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4729685979232449781417027 7094528968848674672125541)
                  ·
                    refine ⟨1330224181659126501023539, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7094528968848674672125541 1330224181659126501023539)
                    ·
                      rfl

theorem cell23_7771807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 2, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 2, 1, 2, 2, 1, 4].length) (baseStart_7771807 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7771807 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7771807 prefixEnd_7771807 := by exact prefixLift 7771807
  have htrace : WordTrace (prefixWord ++ tailWord_7771807) baseStart_7771807 baseEnd_7771807 := by
    simpa [prefixWord, tailWord_7771807, baseEnd_7771807] using wordTrace_append hprefix tailTrace_7771807
  have hstable : (prefixWord ++ tailWord_7771807).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7771807).length < 2 ^ (prefixWord ++ tailWord_7771807).sum := by decide
  have hdescent : baseEnd_7771807 < baseStart_7771807 := by decide
  rcases family_descends (prefixWord ++ tailWord_7771807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7771813 : List Nat := [1, 3, 1, 2, 1, 2, 6, 2, 1, 1, 3]
def baseStart_7771813 : Nat := 118140960795 + 7771813 * 2 ^ 59
def prefixEnd_7771813 : Nat := 4983230072969 + 3 ^ 40 * 7771813 * 2
def baseEnd_7771813 : Nat := 3990675625861306479595589

theorem tailTrace_7771813 : CollatzResearch.WordTrace tailWord_7771813 prefixEnd_7771813 3990675625861306479595589 := by
  unfold tailWord_7771813
  simp only [CollatzResearch.WordTrace]
  refine ⟨283461307393056295832168093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188974204928704197221445395 283461307393056295832168093)
  ·
    refine ⟨106297990272396110937063035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 283461307393056295832168093 106297990272396110937063035)
    ·
      refine ⟨159446985408594166405594553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106297990272396110937063035 159446985408594166405594553)
      ·
        refine ⟨119585239056445624804195915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 159446985408594166405594553 119585239056445624804195915)
        ·
          refine ⟨179377858584668437206293873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 119585239056445624804195915 179377858584668437206293873)
          ·
            refine ⟨134533393938501327904720405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 179377858584668437206293873 134533393938501327904720405)
            ·
              refine ⟨6306252840867249745533769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 134533393938501327904720405 6306252840867249745533769)
              ·
                refine ⟨4729689630650437309150327, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6306252840867249745533769 4729689630650437309150327)
                ·
                  refine ⟨7094534445975655963725491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4729689630650437309150327 7094534445975655963725491)
                  ·
                    refine ⟨10641801668963483945588237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7094534445975655963725491 10641801668963483945588237)
                    ·
                      refine ⟨3990675625861306479595589, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10641801668963483945588237 3990675625861306479595589)
                      ·
                        rfl

theorem cell23_7771813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 6, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 6, 2, 1, 1, 3].length) (baseStart_7771813 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7771813 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7771813 prefixEnd_7771813 := by exact prefixLift 7771813
  have htrace : WordTrace (prefixWord ++ tailWord_7771813) baseStart_7771813 baseEnd_7771813 := by
    simpa [prefixWord, tailWord_7771813, baseEnd_7771813] using wordTrace_append hprefix tailTrace_7771813
  have hstable : (prefixWord ++ tailWord_7771813).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7771813).length < 2 ^ (prefixWord ++ tailWord_7771813).sum := by decide
  have hdescent : baseEnd_7771813 < baseStart_7771813 := by decide
  rcases family_descends (prefixWord ++ tailWord_7771813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7771835 : List Nat := [1, 1, 1, 1, 1, 2, 3, 2, 2, 2, 7]
def baseStart_7771835 : Nat := 118140960795 + 7771835 * 2 ^ 59
def prefixEnd_7771835 : Nat := 4983230072969 + 3 ^ 40 * 7771835 * 2
def baseEnd_7771835 : Nat := 3990686922435705393520487

theorem tailTrace_7771835 : CollatzResearch.WordTrace tailWord_7771835 prefixEnd_7771835 3990686922435705393520487 := by
  unfold tailWord_7771835
  simp only [CollatzResearch.WordTrace]
  refine ⟨283462109798976593589468959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188974739865984395726312639 283462109798976593589468959)
  ·
    refine ⟨425193164698464890384203439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 283462109798976593589468959 425193164698464890384203439)
    ·
      refine ⟨637789747047697335576305159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 425193164698464890384203439 637789747047697335576305159)
      ·
        refine ⟨956684620571546003364457739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 637789747047697335576305159 956684620571546003364457739)
        ·
          refine ⟨1435026930857319005046686609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 956684620571546003364457739 1435026930857319005046686609)
          ·
            refine ⟨1076270198142989253785014957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1435026930857319005046686609 1076270198142989253785014957)
            ·
              refine ⟨403601324303620970169380609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1076270198142989253785014957 403601324303620970169380609)
              ·
                refine ⟨302700993227715727627035457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 403601324303620970169380609 302700993227715727627035457)
                ·
                  refine ⟨227025744920786795720276593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 302700993227715727627035457 227025744920786795720276593)
                  ·
                    refine ⟨170269308690590096790207445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 227025744920786795720276593 170269308690590096790207445)
                    ·
                      refine ⟨3990686922435705393520487, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 170269308690590096790207445 3990686922435705393520487)
                      ·
                        rfl

theorem cell23_7771835_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 3, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 3, 2, 2, 2, 7].length) (baseStart_7771835 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7771835 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7771835 prefixEnd_7771835 := by exact prefixLift 7771835
  have htrace : WordTrace (prefixWord ++ tailWord_7771835) baseStart_7771835 baseEnd_7771835 := by
    simpa [prefixWord, tailWord_7771835, baseEnd_7771835] using wordTrace_append hprefix tailTrace_7771835
  have hstable : (prefixWord ++ tailWord_7771835).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7771835).length < 2 ^ (prefixWord ++ tailWord_7771835).sum := by decide
  have hdescent : baseEnd_7771835 < baseStart_7771835 := by decide
  rcases family_descends (prefixWord ++ tailWord_7771835) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7771836 : List Nat := [2, 2, 2, 3, 1, 2, 1, 1, 5, 2, 2]
def baseStart_7771836 : Nat := 118140960795 + 7771836 * 2 ^ 59
def prefixEnd_7771836 : Nat := 4983230072969 + 3 ^ 40 * 7771836 * 2
def baseEnd_7771836 : Nat := 3990687435916359889607983

theorem tailTrace_7771836 : CollatzResearch.WordTrace tailWord_7771836 prefixEnd_7771836 3990687435916359889607983 := by
  unfold tailWord_7771836
  simp only [CollatzResearch.WordTrace]
  refine ⟨141731073135986485380127681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 188974764181315313840170241 141731073135986485380127681)
  ·
    refine ⟨106298304851989864035095761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 141731073135986485380127681 106298304851989864035095761)
    ·
      refine ⟨79723728638992398026321821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 106298304851989864035095761 79723728638992398026321821)
      ·
        refine ⟨29896398239622149259870683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 79723728638992398026321821 29896398239622149259870683)
        ·
          refine ⟨44844597359433223889806025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29896398239622149259870683 44844597359433223889806025)
          ·
            refine ⟨33633448019574917917354519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44844597359433223889806025 33633448019574917917354519)
            ·
              refine ⟨50450172029362376876031779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33633448019574917917354519 50450172029362376876031779)
              ·
                refine ⟨75675258044043565314047669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50450172029362376876031779 75675258044043565314047669)
                ·
                  refine ⟨7094555441629084248191969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 75675258044043565314047669 7094555441629084248191969)
                  ·
                    refine ⟨5320916581221813186143977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7094555441629084248191969 5320916581221813186143977)
                    ·
                      refine ⟨3990687435916359889607983, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5320916581221813186143977 3990687435916359889607983)
                      ·
                        rfl

theorem cell23_7771836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 2, 1, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 2, 1, 1, 5, 2, 2].length) (baseStart_7771836 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7771836 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7771836 prefixEnd_7771836 := by exact prefixLift 7771836
  have htrace : WordTrace (prefixWord ++ tailWord_7771836) baseStart_7771836 baseEnd_7771836 := by
    simpa [prefixWord, tailWord_7771836, baseEnd_7771836] using wordTrace_append hprefix tailTrace_7771836
  have hstable : (prefixWord ++ tailWord_7771836).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7771836).length < 2 ^ (prefixWord ++ tailWord_7771836).sum := by decide
  have hdescent : baseEnd_7771836 < baseStart_7771836 := by decide
  rcases family_descends (prefixWord ++ tailWord_7771836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7771839 : List Nat := [1, 1, 2, 2, 2, 3, 2, 4, 1, 2, 3]
def baseStart_7771839 : Nat := 118140960795 + 7771839 * 2 ^ 59
def prefixEnd_7771839 : Nat := 4983230072969 + 3 ^ 40 * 7771839 * 2
def baseEnd_7771839 : Nat := 3990688976358323377870469

theorem tailTrace_7771839 : CollatzResearch.WordTrace tailWord_7771839 prefixEnd_7771839 3990688976358323377870469 := by
  unfold tailWord_7771839
  simp only [CollatzResearch.WordTrace]
  refine ⟨283462255690962102272614571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188974837127308068181743047 283462255690962102272614571)
  ·
    refine ⟨425193383536443153408921857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 283462255690962102272614571 425193383536443153408921857)
    ·
      refine ⟨318895037652332365056691393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 425193383536443153408921857 318895037652332365056691393)
      ·
        refine ⟨239171278239249273792518545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 318895037652332365056691393 239171278239249273792518545)
        ·
          refine ⟨179378458679436955344388909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 239171278239249273792518545 179378458679436955344388909)
          ·
            refine ⟨67266922004788858254145841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 179378458679436955344388909 67266922004788858254145841)
            ·
              refine ⟨50450191503591643690609381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 67266922004788858254145841 50450191503591643690609381)
              ·
                refine ⟨9459410906923433191989259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 50450191503591643690609381 9459410906923433191989259)
                ·
                  refine ⟨14189116360385149787983889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9459410906923433191989259 14189116360385149787983889)
                  ·
                    refine ⟨10641837270288862340987917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14189116360385149787983889 10641837270288862340987917)
                    ·
                      refine ⟨3990688976358323377870469, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10641837270288862340987917 3990688976358323377870469)
                      ·
                        rfl

theorem cell23_7771839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 2, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 2, 4, 1, 2, 3].length) (baseStart_7771839 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7771839 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7771839 prefixEnd_7771839 := by exact prefixLift 7771839
  have htrace : WordTrace (prefixWord ++ tailWord_7771839) baseStart_7771839 baseEnd_7771839 := by
    simpa [prefixWord, tailWord_7771839, baseEnd_7771839] using wordTrace_append hprefix tailTrace_7771839
  have hstable : (prefixWord ++ tailWord_7771839).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7771839).length < 2 ^ (prefixWord ++ tailWord_7771839).sum := by decide
  have hdescent : baseEnd_7771839 < baseStart_7771839 := by decide
  rcases family_descends (prefixWord ++ tailWord_7771839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7771853 : List Nat := [1, 6, 2, 1, 1, 2, 1, 3, 1, 1, 4]
def baseStart_7771853 : Nat := 118140960795 + 7771853 * 2 ^ 59
def prefixEnd_7771853 : Nat := 4983230072969 + 3 ^ 40 * 7771853 * 2
def baseEnd_7771853 : Nat := 3990696165087486323095405

theorem tailTrace_7771853 : CollatzResearch.WordTrace tailWord_7771853 prefixEnd_7771853 3990696165087486323095405 := by
  unfold tailWord_7771853
  simp only [CollatzResearch.WordTrace]
  refine ⟨283462766312911382663624213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188975177541940921775749475 283462766312911382663624213)
  ·
    refine ⟨13287317170917721062357385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 283462766312911382663624213 13287317170917721062357385)
    ·
      refine ⟨9965487878188290796768039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13287317170917721062357385 9965487878188290796768039)
      ·
        refine ⟨14948231817282436195152059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9965487878188290796768039 14948231817282436195152059)
        ·
          refine ⟨22422347725923654292728089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14948231817282436195152059 22422347725923654292728089)
          ·
            refine ⟨16816760794442740719546067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22422347725923654292728089 16816760794442740719546067)
            ·
              refine ⟨25225141191664111079319101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16816760794442740719546067 25225141191664111079319101)
              ·
                refine ⟨9459427946874041654744663, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25225141191664111079319101 9459427946874041654744663)
                ·
                  refine ⟨14189141920311062482116995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9459427946874041654744663 14189141920311062482116995)
                  ·
                    refine ⟨21283712880466593723175493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14189141920311062482116995 21283712880466593723175493)
                    ·
                      refine ⟨3990696165087486323095405, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21283712880466593723175493 3990696165087486323095405)
                      ·
                        rfl

theorem cell23_7771853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 2, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 2, 1, 3, 1, 1, 4].length) (baseStart_7771853 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7771853 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7771853 prefixEnd_7771853 := by exact prefixLift 7771853
  have htrace : WordTrace (prefixWord ++ tailWord_7771853) baseStart_7771853 baseEnd_7771853 := by
    simpa [prefixWord, tailWord_7771853, baseEnd_7771853] using wordTrace_append hprefix tailTrace_7771853
  have hstable : (prefixWord ++ tailWord_7771853).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7771853).length < 2 ^ (prefixWord ++ tailWord_7771853).sum := by decide
  have hdescent : baseEnd_7771853 < baseStart_7771853 := by decide
  rcases family_descends (prefixWord ++ tailWord_7771853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7771986 : List Nat := [3, 2, 2, 1, 1, 3, 1, 1, 2, 5, 2]
def baseStart_7771986 : Nat := 118140960795 + 7771986 * 2 ^ 59
def prefixEnd_7771986 : Nat := 4983230072969 + 3 ^ 40 * 7771986 * 2
def baseEnd_7771986 : Nat := 3990764458014534302732293

theorem tailTrace_7771986 : CollatzResearch.WordTrace tailWord_7771986 prefixEnd_7771986 3990764458014534302732293 := by
  unfold tailWord_7771986
  simp only [CollatzResearch.WordTrace]
  refine ⟨70866904305357386594553953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 188978411480953030918810541 70866904305357386594553953)
  ·
    refine ⟨53150178229018039945915465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70866904305357386594553953 53150178229018039945915465)
    ·
      refine ⟨39862633671763529959436599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53150178229018039945915465 39862633671763529959436599)
      ·
        refine ⟨59793950507645294939154899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39862633671763529959436599 59793950507645294939154899)
        ·
          refine ⟨89690925761467942408732349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59793950507645294939154899 89690925761467942408732349)
          ·
            refine ⟨33634097160550478403274631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 89690925761467942408732349 33634097160550478403274631)
            ·
              refine ⟨50451145740825717604911947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33634097160550478403274631 50451145740825717604911947)
              ·
                refine ⟨75676718611238576407367921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50451145740825717604911947 75676718611238576407367921)
                ·
                  refine ⟨56757538958428932305525941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 75676718611238576407367921 56757538958428932305525941)
                  ·
                    refine ⟨5321019277352712403643057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 56757538958428932305525941 5321019277352712403643057)
                    ·
                      refine ⟨3990764458014534302732293, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5321019277352712403643057 3990764458014534302732293)
                      ·
                        rfl

theorem cell23_7771986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 3, 1, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 3, 1, 1, 2, 5, 2].length) (baseStart_7771986 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7771986 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7771986 prefixEnd_7771986 := by exact prefixLift 7771986
  have htrace : WordTrace (prefixWord ++ tailWord_7771986) baseStart_7771986 baseEnd_7771986 := by
    simpa [prefixWord, tailWord_7771986, baseEnd_7771986] using wordTrace_append hprefix tailTrace_7771986
  have hstable : (prefixWord ++ tailWord_7771986).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7771986).length < 2 ^ (prefixWord ++ tailWord_7771986).sum := by decide
  have hdescent : baseEnd_7771986 < baseStart_7771986 := by decide
  rcases family_descends (prefixWord ++ tailWord_7771986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7771989 : List Nat := [1, 3, 2, 2, 2, 2, 2, 1, 1, 2, 5]
def baseStart_7771989 : Nat := 118140960795 + 7771989 * 2 ^ 59
def prefixEnd_7771989 : Nat := 4983230072969 + 3 ^ 40 * 7771989 * 2
def baseEnd_7771989 : Nat := 3990765998456497790994779

theorem tailTrace_7771989 : CollatzResearch.WordTrace tailWord_7771989 prefixEnd_7771989 3990765998456497790994779 := by
  unfold tailWord_7771989
  simp only [CollatzResearch.WordTrace]
  refine ⟨283467726640418677890575021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188978484426945785260383347 283467726640418677890575021)
  ·
    refine ⟨106300397490157004208965633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 283467726640418677890575021 106300397490157004208965633)
    ·
      refine ⟨79725298117617753156724225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 106300397490157004208965633 79725298117617753156724225)
      ·
        refine ⟨59793973588213314867543169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79725298117617753156724225 59793973588213314867543169)
        ·
          refine ⟨44845480191159986150657377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59793973588213314867543169 44845480191159986150657377)
          ·
            refine ⟨33634110143369989612993033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44845480191159986150657377 33634110143369989612993033)
            ·
              refine ⟨25225582607527492209744775, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33634110143369989612993033 25225582607527492209744775)
              ·
                refine ⟨37838373911291238314617163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25225582607527492209744775 37838373911291238314617163)
                ·
                  refine ⟨56757560866936857471925745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37838373911291238314617163 56757560866936857471925745)
                  ·
                    refine ⟨42568170650202643103944309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 56757560866936857471925745 42568170650202643103944309)
                    ·
                      refine ⟨3990765998456497790994779, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 42568170650202643103944309 3990765998456497790994779)
                      ·
                        rfl

theorem cell23_7771989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 2, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 2, 2, 1, 1, 2, 5].length) (baseStart_7771989 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7771989 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7771989 prefixEnd_7771989 := by exact prefixLift 7771989
  have htrace : WordTrace (prefixWord ++ tailWord_7771989) baseStart_7771989 baseEnd_7771989 := by
    simpa [prefixWord, tailWord_7771989, baseEnd_7771989] using wordTrace_append hprefix tailTrace_7771989
  have hstable : (prefixWord ++ tailWord_7771989).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7771989).length < 2 ^ (prefixWord ++ tailWord_7771989).sum := by decide
  have hdescent : baseEnd_7771989 < baseStart_7771989 := by decide
  rcases family_descends (prefixWord ++ tailWord_7771989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7771992 : List Nat := [2, 1, 2, 2, 1, 1, 1, 1, 4, 8]
def baseStart_7771992 : Nat := 118140960795 + 7771992 * 2 ^ 59
def prefixEnd_7771992 : Nat := 4983230072969 + 3 ^ 40 * 7771992 * 2
def baseEnd_7771992 : Nat := 1330255846299487093085755

theorem tailTrace_7771992 : CollatzResearch.WordTrace tailWord_7771992 prefixEnd_7771992 1330255846299487093085755 := by
  unfold tailWord_7771992
  simp only [CollatzResearch.WordTrace]
  refine ⟨141733918029703904701467115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 188978557372938539601956153 141733918029703904701467115)
  ·
    refine ⟨212600877044555857052200673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141733918029703904701467115 212600877044555857052200673)
    ·
      refine ⟨159450657783416892789150505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 212600877044555857052200673 159450657783416892789150505)
      ·
        refine ⟨119587993337562669591862879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 159450657783416892789150505 119587993337562669591862879)
        ·
          refine ⟨179381990006344004387794319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 119587993337562669591862879 179381990006344004387794319)
          ·
            refine ⟨269072985009516006581691479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 179381990006344004387794319 269072985009516006581691479)
            ·
              refine ⟨403609477514274009872537219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 269072985009516006581691479 403609477514274009872537219)
              ·
                refine ⟨605414216271411014808805829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 403609477514274009872537219 605414216271411014808805829)
                ·
                  refine ⟨113515165550889565276651093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 605414216271411014808805829 113515165550889565276651093)
                  ·
                    refine ⟨1330255846299487093085755, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 113515165550889565276651093 1330255846299487093085755)
                    ·
                      rfl

theorem cell23_7771992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 1, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 1, 1, 4, 8].length) (baseStart_7771992 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7771992 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7771992 prefixEnd_7771992 := by exact prefixLift 7771992
  have htrace : WordTrace (prefixWord ++ tailWord_7771992) baseStart_7771992 baseEnd_7771992 := by
    simpa [prefixWord, tailWord_7771992, baseEnd_7771992] using wordTrace_append hprefix tailTrace_7771992
  have hstable : (prefixWord ++ tailWord_7771992).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7771992).length < 2 ^ (prefixWord ++ tailWord_7771992).sum := by decide
  have hdescent : baseEnd_7771992 < baseStart_7771992 := by decide
  rcases family_descends (prefixWord ++ tailWord_7771992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7772036 : List Nat := [2, 3, 2, 1, 1, 1, 2, 4, 2, 2, 3]
def baseStart_7772036 : Nat := 118140960795 + 7772036 * 2 ^ 59
def prefixEnd_7772036 : Nat := 4983230072969 + 3 ^ 40 * 7772036 * 2
def baseEnd_7772036 : Nat := 3990790132047259107107063

theorem tailTrace_7772036 : CollatzResearch.WordTrace tailWord_7772036 prefixEnd_7772036 3990790132047259107107063 := by
  unfold tailWord_7772036
  simp only [CollatzResearch.WordTrace]
  refine ⟨141734720435624202458767981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 188979627247498936611690641 141734720435624202458767981)
  ·
    refine ⟨53150520163359075922037993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 141734720435624202458767981 53150520163359075922037993)
    ·
      refine ⟨39862890122519306941528495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53150520163359075922037993 39862890122519306941528495)
      ·
        refine ⟨59794335183778960412292743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39862890122519306941528495 59794335183778960412292743)
        ·
          refine ⟨89691502775668440618439115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59794335183778960412292743 89691502775668440618439115)
          ·
            refine ⟨134537254163502660927658673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89691502775668440618439115 134537254163502660927658673)
            ·
              refine ⟨100902940622626995695744005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 134537254163502660927658673 100902940622626995695744005)
              ·
                refine ⟨18919301366742561692952001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 100902940622626995695744005 18919301366742561692952001)
                ·
                  refine ⟨14189476025056921269714001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18919301366742561692952001 14189476025056921269714001)
                  ·
                    refine ⟨10642107018792690952285501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14189476025056921269714001 10642107018792690952285501)
                    ·
                      refine ⟨3990790132047259107107063, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10642107018792690952285501 3990790132047259107107063)
                      ·
                        rfl

theorem cell23_7772036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 2, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 2, 4, 2, 2, 3].length) (baseStart_7772036 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7772036 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7772036 prefixEnd_7772036 := by exact prefixLift 7772036
  have htrace : WordTrace (prefixWord ++ tailWord_7772036) baseStart_7772036 baseEnd_7772036 := by
    simpa [prefixWord, tailWord_7772036, baseEnd_7772036] using wordTrace_append hprefix tailTrace_7772036
  have hstable : (prefixWord ++ tailWord_7772036).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7772036).length < 2 ^ (prefixWord ++ tailWord_7772036).sum := by decide
  have hdescent : baseEnd_7772036 < baseStart_7772036 := by decide
  rcases family_descends (prefixWord ++ tailWord_7772036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7772069 : List Nat := [1, 3, 1, 2, 1, 1, 1, 5, 3, 5]
def baseStart_7772069 : Nat := 118140960795 + 7772069 * 2 ^ 59
def prefixEnd_7772069 : Nat := 4983230072969 + 3 ^ 40 * 7772069 * 2
def baseEnd_7772069 : Nat := 1330269025636285825998137

theorem tailTrace_7772069 : CollatzResearch.WordTrace tailWord_7772069 prefixEnd_7772069 1330269025636285825998137 := by
  unfold tailWord_7772069
  simp only [CollatzResearch.WordTrace]
  refine ⟨283470644480128851553487261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188980429653419234368991507 283470644480128851553487261)
  ·
    refine ⟨106301491680048319332557723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 283470644480128851553487261 106301491680048319332557723)
    ·
      refine ⟨159452237520072478998836585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106301491680048319332557723 159452237520072478998836585)
      ·
        refine ⟨119589178140054359249127439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 159452237520072478998836585 119589178140054359249127439)
        ·
          refine ⟨179383767210081538873691159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 119589178140054359249127439 179383767210081538873691159)
          ·
            refine ⟨269075650815122308310536739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 179383767210081538873691159 269075650815122308310536739)
            ·
              refine ⟨403613476222683462465805109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 269075650815122308310536739 403613476222683462465805109)
              ·
                refine ⟨37838763395876574606169229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 403613476222683462465805109 37838763395876574606169229)
                ·
                  refine ⟨14189536273453715477313461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 37838763395876574606169229 14189536273453715477313461)
                  ·
                    refine ⟨1330269025636285825998137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14189536273453715477313461 1330269025636285825998137)
                    ·
                      rfl

theorem cell23_7772069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 1, 5, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 1, 5, 3, 5].length) (baseStart_7772069 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7772069 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7772069 prefixEnd_7772069 := by exact prefixLift 7772069
  have htrace : WordTrace (prefixWord ++ tailWord_7772069) baseStart_7772069 baseEnd_7772069 := by
    simpa [prefixWord, tailWord_7772069, baseEnd_7772069] using wordTrace_append hprefix tailTrace_7772069
  have hstable : (prefixWord ++ tailWord_7772069).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7772069).length < 2 ^ (prefixWord ++ tailWord_7772069).sum := by decide
  have hdescent : baseEnd_7772069 < baseStart_7772069 := by decide
  rcases family_descends (prefixWord ++ tailWord_7772069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7772093 : List Nat := [1, 4, 1, 2, 3, 1, 1, 1, 4, 3, 2]
def baseStart_7772093 : Nat := 118140960795 + 7772093 * 2 ^ 59
def prefixEnd_7772093 : Nat := 4983230072969 + 3 ^ 40 * 7772093 * 2
def baseEnd_7772093 : Nat := 3990819400444565384094301

theorem tailTrace_7772093 : CollatzResearch.WordTrace tailWord_7772093 prefixEnd_7772093 3990819400444565384094301 := by
  unfold tailWord_7772093
  simp only [CollatzResearch.WordTrace]
  refine ⟨283471519832041903652360933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188981013221361269101573955 283471519832041903652360933)
  ·
    refine ⟨53150909968507856934817675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 283471519832041903652360933 53150909968507856934817675)
    ·
      refine ⟨79726364952761785402226513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53150909968507856934817675 79726364952761785402226513)
      ·
        refine ⟨59794773714571339051669885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79726364952761785402226513 59794773714571339051669885)
        ·
          refine ⟨22423040142964252144376207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 59794773714571339051669885 22423040142964252144376207)
          ·
            refine ⟨33634560214446378216564311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22423040142964252144376207 33634560214446378216564311)
            ·
              refine ⟨50451840321669567324846467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33634560214446378216564311 50451840321669567324846467)
              ·
                refine ⟨75677760482504350987269701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50451840321669567324846467 75677760482504350987269701)
                ·
                  refine ⟨14189580090469565810113069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 75677760482504350987269701 14189580090469565810113069)
                  ·
                    refine ⟨5321092533926087178792401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14189580090469565810113069 5321092533926087178792401)
                    ·
                      refine ⟨3990819400444565384094301, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5321092533926087178792401 3990819400444565384094301)
                      ·
                        rfl

theorem cell23_7772093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 1, 1, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 1, 1, 1, 4, 3, 2].length) (baseStart_7772093 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7772093 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7772093 prefixEnd_7772093 := by exact prefixLift 7772093
  have htrace : WordTrace (prefixWord ++ tailWord_7772093) baseStart_7772093 baseEnd_7772093 := by
    simpa [prefixWord, tailWord_7772093, baseEnd_7772093] using wordTrace_append hprefix tailTrace_7772093
  have hstable : (prefixWord ++ tailWord_7772093).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7772093).length < 2 ^ (prefixWord ++ tailWord_7772093).sum := by decide
  have hdescent : baseEnd_7772093 < baseStart_7772093 := by decide
  rcases family_descends (prefixWord ++ tailWord_7772093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7772116 : List Nat := [2, 4, 1, 2, 1, 1, 2, 3, 1, 6]
def baseStart_7772116 : Nat := 118140960795 + 7772116 * 2 ^ 59
def prefixEnd_7772116 : Nat := 4983230072969 + 3 ^ 40 * 7772116 * 2
def baseEnd_7772116 : Nat := 1330277070166539598035565

theorem tailTrace_7772116 : CollatzResearch.WordTrace tailWord_7772116 prefixEnd_7772116 1330277070166539598035565 := by
  unfold tailWord_7772116
  simp only [CollatzResearch.WordTrace]
  refine ⟨141736179355479289290224101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 188981572473972385720298801 141736179355479289290224101)
  ·
    refine ⟨26575533629152366741917019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 141736179355479289290224101 26575533629152366741917019)
    ·
      refine ⟨39863300443728550112875529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26575533629152366741917019 39863300443728550112875529)
      ·
        refine ⟨29897475332796412584656647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39863300443728550112875529 29897475332796412584656647)
        ·
          refine ⟨44846212999194618876984971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29897475332796412584656647 44846212999194618876984971)
          ·
            refine ⟨67269319498791928315477457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44846212999194618876984971 67269319498791928315477457)
            ·
              refine ⟨50451989624093946236608093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 67269319498791928315477457 50451989624093946236608093)
              ·
                refine ⟨18919496109035229838728035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 50451989624093946236608093 18919496109035229838728035)
                ·
                  refine ⟨28379244163552844758092053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18919496109035229838728035 28379244163552844758092053)
                  ·
                    refine ⟨1330277070166539598035565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28379244163552844758092053 1330277070166539598035565)
                    ·
                      rfl

theorem cell23_7772116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 2, 3, 1, 6].length) (baseStart_7772116 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7772116 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7772116 prefixEnd_7772116 := by exact prefixLift 7772116
  have htrace : WordTrace (prefixWord ++ tailWord_7772116) baseStart_7772116 baseEnd_7772116 := by
    simpa [prefixWord, tailWord_7772116, baseEnd_7772116] using wordTrace_append hprefix tailTrace_7772116
  have hstable : (prefixWord ++ tailWord_7772116).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7772116).length < 2 ^ (prefixWord ++ tailWord_7772116).sum := by decide
  have hdescent : baseEnd_7772116 < baseStart_7772116 := by decide
  rcases family_descends (prefixWord ++ tailWord_7772116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7772119 : List Nat := [1, 1, 3, 2, 1, 1, 3, 3, 1, 1, 6]
def baseStart_7772119 : Nat := 118140960795 + 7772119 * 2 ^ 59
def prefixEnd_7772119 : Nat := 4983230072969 + 3 ^ 40 * 7772119 * 2
def baseEnd_7772119 : Nat := 3990832750941582282369181

theorem tailTrace_7772119 : CollatzResearch.WordTrace tailWord_7772119 prefixEnd_7772119 3990832750941582282369181 := by
  unfold tailWord_7772119
  simp only [CollatzResearch.WordTrace]
  refine ⟨283472468129947710092807411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188981645419965140061871607 283472468129947710092807411)
  ·
    refine ⟨425208702194921565139211117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 283472468129947710092807411 425208702194921565139211117)
    ·
      refine ⟨159453263323095586927204169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 425208702194921565139211117 159453263323095586927204169)
      ·
        refine ⟨119589947492321690195403127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 159453263323095586927204169 119589947492321690195403127)
        ·
          refine ⟨179384921238482535293104691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 119589947492321690195403127 179384921238482535293104691)
          ·
            refine ⟨269077381857723802939657037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 179384921238482535293104691 269077381857723802939657037)
            ·
              refine ⟨100904018196646426102371389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 269077381857723802939657037 100904018196646426102371389)
              ·
                refine ⟨37839006823742409788389271, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 100904018196646426102371389 37839006823742409788389271)
                ·
                  refine ⟨56758510235613614682583907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37839006823742409788389271 56758510235613614682583907)
                  ·
                    refine ⟨85137765353420422023875861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 56758510235613614682583907 85137765353420422023875861)
                    ·
                      refine ⟨3990832750941582282369181, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 85137765353420422023875861 3990832750941582282369181)
                      ·
                        rfl

theorem cell23_7772119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 3, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 3, 3, 1, 1, 6].length) (baseStart_7772119 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7772119 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7772119 prefixEnd_7772119 := by exact prefixLift 7772119
  have htrace : WordTrace (prefixWord ++ tailWord_7772119) baseStart_7772119 baseEnd_7772119 := by
    simpa [prefixWord, tailWord_7772119, baseEnd_7772119] using wordTrace_append hprefix tailTrace_7772119
  have hstable : (prefixWord ++ tailWord_7772119).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7772119).length < 2 ^ (prefixWord ++ tailWord_7772119).sum := by decide
  have hdescent : baseEnd_7772119 < baseStart_7772119 := by decide
  rcases family_descends (prefixWord ++ tailWord_7772119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7772129 : List Nat := [1, 2, 3, 1, 2, 1, 4, 9]
def baseStart_7772129 : Nat := 118140960795 + 7772129 * 2 ^ 59
def prefixEnd_7772129 : Nat := 4983230072969 + 3 ^ 40 * 7772129 * 2
def baseEnd_7772129 : Nat := 147808810583263971972005

theorem tailTrace_7772129 : CollatzResearch.WordTrace tailWord_7772129 prefixEnd_7772129 147808810583263971972005 := by
  unfold tailWord_7772129
  simp only [CollatzResearch.WordTrace]
  refine ⟨283472832859911481800671441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188981888573274321200447627 283472832859911481800671441)
  ·
    refine ⟨212604624644933611350503581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 283472832859911481800671441 212604624644933611350503581)
    ·
      refine ⟨79726734241850104256438843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 212604624644933611350503581 79726734241850104256438843)
      ·
        refine ⟨119590101362775156384658265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79726734241850104256438843 119590101362775156384658265)
        ·
          refine ⟨89692576022081367288493699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 119590101362775156384658265 89692576022081367288493699)
          ·
            refine ⟨134538864033122050932740549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89692576022081367288493699 134538864033122050932740549)
            ·
              refine ⟨25226037006210384549888853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 134538864033122050932740549 25226037006210384549888853)
              ·
                refine ⟨147808810583263971972005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 25226037006210384549888853 147808810583263971972005)
                ·
                  rfl

theorem cell23_7772129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 4, 9].length) (baseStart_7772129 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7772129 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7772129 prefixEnd_7772129 := by exact prefixLift 7772129
  have htrace : WordTrace (prefixWord ++ tailWord_7772129) baseStart_7772129 baseEnd_7772129 := by
    simpa [prefixWord, tailWord_7772129, baseEnd_7772129] using wordTrace_append hprefix tailTrace_7772129
  have hstable : (prefixWord ++ tailWord_7772129).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7772129).length < 2 ^ (prefixWord ++ tailWord_7772129).sum := by decide
  have hdescent : baseEnd_7772129 < baseStart_7772129 := by decide
  rcases family_descends (prefixWord ++ tailWord_7772129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7772156 : List Nat := [2, 2, 2, 1, 2, 2, 1, 2, 3, 3, 3]
def baseStart_7772156 : Nat := 118140960795 + 7772156 * 2 ^ 59
def prefixEnd_7772156 : Nat := 4983230072969 + 3 ^ 40 * 7772156 * 2
def baseEnd_7772156 : Nat := 3990851749725798637606511

theorem tailTrace_7772156 : CollatzResearch.WordTrace tailWord_7772156 prefixEnd_7772156 3990851749725798637606511 := by
  unfold tailWord_7772156
  simp only [CollatzResearch.WordTrace]
  refine ⟨141736908815406832705952161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 188982545087209110274602881 141736908815406832705952161)
  ·
    refine ⟨106302681611555124529464121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 141736908815406832705952161 106302681611555124529464121)
    ·
      refine ⟨79727011208666343397098091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 106302681611555124529464121 79727011208666343397098091)
      ·
        refine ⟨119590516812999515095647137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79727011208666343397098091 119590516812999515095647137)
        ·
          refine ⟨89692887609749636321735353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 119590516812999515095647137 89692887609749636321735353)
          ·
            refine ⟨67269665707312227241301515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 89692887609749636321735353 67269665707312227241301515)
            ·
              refine ⟨100904498560968340861952273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67269665707312227241301515 100904498560968340861952273)
              ·
                refine ⟨75678373920726255646464205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 100904498560968340861952273 75678373920726255646464205)
                ·
                  refine ⟨28379390220272345867424077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 75678373920726255646464205 28379390220272345867424077)
                  ·
                    refine ⟨10642271332602129700284029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 28379390220272345867424077 10642271332602129700284029)
                    ·
                      refine ⟨3990851749725798637606511, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10642271332602129700284029 3990851749725798637606511)
                      ·
                        rfl

theorem cell23_7772156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 1, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 1, 2, 3, 3, 3].length) (baseStart_7772156 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7772156 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7772156 prefixEnd_7772156 := by exact prefixLift 7772156
  have htrace : WordTrace (prefixWord ++ tailWord_7772156) baseStart_7772156 baseEnd_7772156 := by
    simpa [prefixWord, tailWord_7772156, baseEnd_7772156] using wordTrace_append hprefix tailTrace_7772156
  have hstable : (prefixWord ++ tailWord_7772156).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7772156).length < 2 ^ (prefixWord ++ tailWord_7772156).sum := by decide
  have hdescent : baseEnd_7772156 < baseStart_7772156 := by decide
  rcases family_descends (prefixWord ++ tailWord_7772156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7772169 : List Nat := [1, 2, 1, 1, 3, 1, 1, 1, 3, 4, 5]
def baseStart_7772169 : Nat := 118140960795 + 7772169 * 2 ^ 59
def prefixEnd_7772169 : Nat := 4983230072969 + 3 ^ 40 * 7772169 * 2
def baseEnd_7772169 : Nat := 3990858424974307086743951

theorem tailTrace_7772169 : CollatzResearch.WordTrace tailWord_7772169 prefixEnd_7772169 3990858424974307086743951 := by
  unfold tailWord_7772169
  simp only [CollatzResearch.WordTrace]
  refine ⟨283474291779766568632127561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188982861186511045754751707 283474291779766568632127561)
  ·
    refine ⟨212605718834824926474095671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 283474291779766568632127561 212605718834824926474095671)
    ·
      refine ⟨318908578252237389711143507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 212605718834824926474095671 318908578252237389711143507)
      ·
        refine ⟨478362867378356084566715261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 318908578252237389711143507 478362867378356084566715261)
        ·
          refine ⟨179386075266883531712518223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 478362867378356084566715261 179386075266883531712518223)
          ·
            refine ⟨269079112900325297568777335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 179386075266883531712518223 269079112900325297568777335)
            ·
              refine ⟨403618669350487946353166003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 269079112900325297568777335 403618669350487946353166003)
              ·
                refine ⟨605428004025731919529749005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 403618669350487946353166003 605428004025731919529749005)
                ·
                  refine ⟨227035501509649469823655877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 605428004025731919529749005 227035501509649469823655877)
                  ·
                    refine ⟨42569156533059275591935477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 227035501509649469823655877 42569156533059275591935477)
                    ·
                      refine ⟨3990858424974307086743951, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 42569156533059275591935477 3990858424974307086743951)
                      ·
                        rfl

theorem cell23_7772169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 1, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 1, 1, 3, 4, 5].length) (baseStart_7772169 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7772169 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7772169 prefixEnd_7772169 := by exact prefixLift 7772169
  have htrace : WordTrace (prefixWord ++ tailWord_7772169) baseStart_7772169 baseEnd_7772169 := by
    simpa [prefixWord, tailWord_7772169, baseEnd_7772169] using wordTrace_append hprefix tailTrace_7772169
  have hstable : (prefixWord ++ tailWord_7772169).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7772169).length < 2 ^ (prefixWord ++ tailWord_7772169).sum := by decide
  have hdescent : baseEnd_7772169 < baseStart_7772169 := by decide
  rcases family_descends (prefixWord ++ tailWord_7772169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7772213 : List Nat := [1, 3, 3, 1, 1, 1, 2, 2, 3, 4, 2]
def baseStart_7772213 : Nat := 118140960795 + 7772213 * 2 ^ 59
def prefixEnd_7772213 : Nat := 4983230072969 + 3 ^ 40 * 7772213 * 2
def baseEnd_7772213 : Nat := 3990881018123104914593749

theorem tailTrace_7772213 : CollatzResearch.WordTrace tailWord_7772213 prefixEnd_7772213 3990881018123104914593749 := by
  unfold tailWord_7772213
  simp only [CollatzResearch.WordTrace]
  refine ⟨283475896591607164146729293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188983931061071442764486195 283475896591607164146729293)
  ·
    refine ⟨106303461221852686555023485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 283475896591607164146729293 106303461221852686555023485)
    ·
      refine ⟨39863797958194757458133807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 106303461221852686555023485 39863797958194757458133807)
      ·
        refine ⟨59795696937292136187200711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39863797958194757458133807 59795696937292136187200711)
        ·
          refine ⟨89693545405938204280801067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59795696937292136187200711 89693545405938204280801067)
          ·
            refine ⟨134540318108907306421201601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89693545405938204280801067 134540318108907306421201601)
            ·
              refine ⟨100905238581680479815901201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 134540318108907306421201601 100905238581680479815901201)
              ·
                refine ⟨75678928936260359861925901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 100905238581680479815901201 75678928936260359861925901)
                ·
                  refine ⟨28379598351097634948222213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 75678928936260359861925901 28379598351097634948222213)
                  ·
                    refine ⟨5321174690830806552791665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28379598351097634948222213 5321174690830806552791665)
                    ·
                      refine ⟨3990881018123104914593749, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5321174690830806552791665 3990881018123104914593749)
                      ·
                        rfl

theorem cell23_7772213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 2, 2, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 2, 2, 3, 4, 2].length) (baseStart_7772213 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7772213 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7772213 prefixEnd_7772213 := by exact prefixLift 7772213
  have htrace : WordTrace (prefixWord ++ tailWord_7772213) baseStart_7772213 baseEnd_7772213 := by
    simpa [prefixWord, tailWord_7772213, baseEnd_7772213] using wordTrace_append hprefix tailTrace_7772213
  have hstable : (prefixWord ++ tailWord_7772213).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7772213).length < 2 ^ (prefixWord ++ tailWord_7772213).sum := by decide
  have hdescent : baseEnd_7772213 < baseStart_7772213 := by decide
  rcases family_descends (prefixWord ++ tailWord_7772213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7772219 : List Nat := [1, 1, 1, 1, 1, 2, 1, 4, 11]
def baseStart_7772219 : Nat := 118140960795 + 7772219 * 2 ^ 59
def prefixEnd_7772219 : Nat := 4983230072969 + 3 ^ 40 * 7772219 * 2
def baseEnd_7772219 : Nat := 443431566556336876790969

theorem tailTrace_7772219 : CollatzResearch.WordTrace tailWord_7772219 prefixEnd_7772219 443431566556336876790969 := by
  unfold tailWord_7772219
  simp only [CollatzResearch.WordTrace]
  refine ⟨283476115429585427171447711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188984076953056951447631807 283476115429585427171447711)
  ·
    refine ⟨425214173144378140757171567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 283476115429585427171447711 425214173144378140757171567)
    ·
      refine ⟨637821259716567211135757351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 425214173144378140757171567 637821259716567211135757351)
      ·
        refine ⟨956731889574850816703636027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 637821259716567211135757351 956731889574850816703636027)
        ·
          refine ⟨1435097834362276225055454041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 956731889574850816703636027 1435097834362276225055454041)
          ·
            refine ⟨1076323375771707168791590531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1435097834362276225055454041 1076323375771707168791590531)
            ·
              refine ⟨1614485063657560753187385797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1076323375771707168791590531 1614485063657560753187385797)
              ·
                refine ⟨302715949435792641222634837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1614485063657560753187385797 302715949435792641222634837)
                ·
                  refine ⟨443431566556336876790969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 11 302715949435792641222634837 443431566556336876790969)
                  ·
                    rfl

theorem cell23_7772219_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 4, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 4, 11].length) (baseStart_7772219 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7772219 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7772219 prefixEnd_7772219 := by exact prefixLift 7772219
  have htrace : WordTrace (prefixWord ++ tailWord_7772219) baseStart_7772219 baseEnd_7772219 := by
    simpa [prefixWord, tailWord_7772219, baseEnd_7772219] using wordTrace_append hprefix tailTrace_7772219
  have hstable : (prefixWord ++ tailWord_7772219).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7772219).length < 2 ^ (prefixWord ++ tailWord_7772219).sum := by decide
  have hdescent : baseEnd_7772219 < baseStart_7772219 := by decide
  rcases family_descends (prefixWord ++ tailWord_7772219) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7772236 : List Nat := [2, 2, 1, 3, 1, 1, 4, 2, 7]
def baseStart_7772236 : Nat := 118140960795 + 7772236 * 2 ^ 59
def prefixEnd_7772236 : Nat := 4983230072969 + 3 ^ 40 * 7772236 * 2
def baseEnd_7772236 : Nat := 443432536464239813845127

theorem tailTrace_7772236 : CollatzResearch.WordTrace tailWord_7772236 prefixEnd_7772236 443432536464239813845127 := by
  unfold tailWord_7772236
  simp only [CollatzResearch.WordTrace]
  refine ⟨141738367735261919537408281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 188984490313682559383211041 141738367735261919537408281)
  ·
    refine ⟨106303775801446439653056211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 141738367735261919537408281 106303775801446439653056211)
    ·
      refine ⟨159455663702169659479584317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106303775801446439653056211 159455663702169659479584317)
      ·
        refine ⟨59795873888313622304844119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 159455663702169659479584317 59795873888313622304844119)
        ·
          refine ⟨89693810832470433457266179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59795873888313622304844119 89693810832470433457266179)
          ·
            refine ⟨134540716248705650185899269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89693810832470433457266179 134540716248705650185899269)
            ·
              refine ⟨25226384296632309409856113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 134540716248705650185899269 25226384296632309409856113)
              ·
                refine ⟨18919788222474232057392085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25226384296632309409856113 18919788222474232057392085)
                ·
                  refine ⟨443432536464239813845127, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18919788222474232057392085 443432536464239813845127)
                  ·
                    rfl

theorem cell23_7772236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 4, 2, 7].length) (baseStart_7772236 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7772236 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7772236 prefixEnd_7772236 := by exact prefixLift 7772236
  have htrace : WordTrace (prefixWord ++ tailWord_7772236) baseStart_7772236 baseEnd_7772236 := by
    simpa [prefixWord, tailWord_7772236, baseEnd_7772236] using wordTrace_append hprefix tailTrace_7772236
  have hstable : (prefixWord ++ tailWord_7772236).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7772236).length < 2 ^ (prefixWord ++ tailWord_7772236).sum := by decide
  have hdescent : baseEnd_7772236 < baseStart_7772236 := by decide
  rcases family_descends (prefixWord ++ tailWord_7772236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7772273 : List Nat := [1, 2, 2, 2, 1, 1, 4, 1, 2, 5, 2]
def baseStart_7772273 : Nat := 118140960795 + 7772273 * 2 ^ 59
def prefixEnd_7772273 : Nat := 4983230072969 + 3 ^ 40 * 7772273 * 2
def baseEnd_7772273 : Nat := 3990911826962374679843473

theorem tailTrace_7772273 : CollatzResearch.WordTrace tailWord_7772273 prefixEnd_7772273 3990911826962374679843473 := by
  unfold tailWord_7772273
  simp only [CollatzResearch.WordTrace]
  refine ⟨283478084971389794393913473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188985389980926529595942315 283478084971389794393913473)
  ·
    refine ⟨212608563728542345795435105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 283478084971389794393913473 212608563728542345795435105)
    ·
      refine ⟨159456422796406759346576329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 212608563728542345795435105 159456422796406759346576329)
      ·
        refine ⟨119592317097305069509932247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 159456422796406759346576329 119592317097305069509932247)
        ·
          refine ⟨179388475645957604264898371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 119592317097305069509932247 179388475645957604264898371)
          ·
            refine ⟨269082713468936406397347557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 179388475645957604264898371 269082713468936406397347557)
            ·
              refine ⟨50453008775425576199502667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 269082713468936406397347557 50453008775425576199502667)
              ·
                refine ⟨75679513163138364299254001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50453008775425576199502667 75679513163138364299254001)
                ·
                  refine ⟨56759634872353773224440501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 75679513163138364299254001 56759634872353773224440501)
                  ·
                    refine ⟨5321215769283166239791297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 56759634872353773224440501 5321215769283166239791297)
                    ·
                      refine ⟨3990911826962374679843473, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5321215769283166239791297 3990911826962374679843473)
                      ·
                        rfl

theorem cell23_7772273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 4, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 4, 1, 2, 5, 2].length) (baseStart_7772273 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7772273 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7772273 prefixEnd_7772273 := by exact prefixLift 7772273
  have htrace : WordTrace (prefixWord ++ tailWord_7772273) baseStart_7772273 baseEnd_7772273 := by
    simpa [prefixWord, tailWord_7772273, baseEnd_7772273] using wordTrace_append hprefix tailTrace_7772273
  have hstable : (prefixWord ++ tailWord_7772273).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7772273).length < 2 ^ (prefixWord ++ tailWord_7772273).sum := by decide
  have hdescent : baseEnd_7772273 < baseStart_7772273 := by decide
  rcases family_descends (prefixWord ++ tailWord_7772273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7772337 : List Nat := [1, 2, 2, 5, 2, 1, 1, 1, 2, 4, 2]
def baseStart_7772337 : Nat := 118140960795 + 7772337 * 2 ^ 59
def prefixEnd_7772337 : Nat := 4983230072969 + 3 ^ 40 * 7772337 * 2
def baseEnd_7772337 : Nat := 3990944689724262429443179

theorem tailTrace_7772337 : CollatzResearch.WordTrace tailWord_7772337 prefixEnd_7772337 3990944689724262429443179 := by
  unfold tailWord_7772337
  simp only [CollatzResearch.WordTrace]
  refine ⟨283480419243157933324243265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188986946162105288882828843 283480419243157933324243265)
  ·
    refine ⟨212610314432368449993182449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 283480419243157933324243265 212610314432368449993182449)
    ·
      refine ⟨159457735824276337494886837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 212610314432368449993182449 159457735824276337494886837)
      ·
        refine ⟨14949162733525906640145641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 159457735824276337494886837 14949162733525906640145641)
        ·
          refine ⟨11211872050144429980109231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14949162733525906640145641 11211872050144429980109231)
          ·
            refine ⟨16817808075216644970163847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11211872050144429980109231 16817808075216644970163847)
            ·
              refine ⟨25226712112824967455245771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16817808075216644970163847 25226712112824967455245771)
              ·
                refine ⟨37840068169237451182868657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25226712112824967455245771 37840068169237451182868657)
                ·
                  refine ⟨28380051126928088387151493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37840068169237451182868657 28380051126928088387151493)
                  ·
                    refine ⟨5321259586299016572590905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28380051126928088387151493 5321259586299016572590905)
                    ·
                      refine ⟨3990944689724262429443179, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5321259586299016572590905 3990944689724262429443179)
                      ·
                        rfl

theorem cell23_7772337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 2, 1, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 2, 1, 1, 1, 2, 4, 2].length) (baseStart_7772337 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7772337 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7772337 prefixEnd_7772337 := by exact prefixLift 7772337
  have htrace : WordTrace (prefixWord ++ tailWord_7772337) baseStart_7772337 baseEnd_7772337 := by
    simpa [prefixWord, tailWord_7772337, baseEnd_7772337] using wordTrace_append hprefix tailTrace_7772337
  have hstable : (prefixWord ++ tailWord_7772337).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7772337).length < 2 ^ (prefixWord ++ tailWord_7772337).sum := by decide
  have hdescent : baseEnd_7772337 < baseStart_7772337 := by decide
  rcases family_descends (prefixWord ++ tailWord_7772337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7772343 : List Nat := [1, 1, 3, 1, 4, 2, 2, 3, 6]
def baseStart_7772343 : Nat := 118140960795 + 7772343 * 2 ^ 59
def prefixEnd_7772343 : Nat := 4983230072969 + 3 ^ 40 * 7772343 * 2
def baseEnd_7772343 : Nat := 443438641178687711774239

theorem tailTrace_7772343 : CollatzResearch.WordTrace tailWord_7772343 prefixEnd_7772343 443438641178687711774239 := by
  unfold tailWord_7772343
  simp only [CollatzResearch.WordTrace]
  refine ⟨283480638081136196348961683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188987092054090797565974455 283480638081136196348961683)
  ·
    refine ⟨425220957121704294523442525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 283480638081136196348961683 425220957121704294523442525)
    ·
      refine ⟨159457858920639110446290947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 425220957121704294523442525 159457858920639110446290947)
      ·
        refine ⟨239186788380958665669436421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 159457858920639110446290947 239186788380958665669436421)
        ·
          refine ⟨44847522821429749813019329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 239186788380958665669436421 44847522821429749813019329)
          ·
            refine ⟨33635642116072312359764497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44847522821429749813019329 33635642116072312359764497)
            ·
              refine ⟨25226731587054234269823373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33635642116072312359764497 25226731587054234269823373)
              ·
                refine ⟨9460024345145337851183765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25226731587054234269823373 9460024345145337851183765)
                ·
                  refine ⟨443438641178687711774239, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9460024345145337851183765 443438641178687711774239)
                  ·
                    rfl

theorem cell23_7772343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 2, 2, 3, 6].length) (baseStart_7772343 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7772343 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7772343 prefixEnd_7772343 := by exact prefixLift 7772343
  have htrace : WordTrace (prefixWord ++ tailWord_7772343) baseStart_7772343 baseEnd_7772343 := by
    simpa [prefixWord, tailWord_7772343, baseEnd_7772343] using wordTrace_append hprefix tailTrace_7772343
  have hstable : (prefixWord ++ tailWord_7772343).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7772343).length < 2 ^ (prefixWord ++ tailWord_7772343).sum := by decide
  have hdescent : baseEnd_7772343 < baseStart_7772343 := by decide
  rcases family_descends (prefixWord ++ tailWord_7772343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7772354 : List Nat := [3, 5, 1, 1, 1, 1, 3, 1, 2, 1, 4]
def baseStart_7772354 : Nat := 118140960795 + 7772354 * 2 ^ 59
def prefixEnd_7772354 : Nat := 4983230072969 + 3 ^ 40 * 7772354 * 2
def baseEnd_7772354 : Nat := 3990953418895388862930601

theorem tailTrace_7772354 : CollatzResearch.WordTrace tailWord_7772354 prefixEnd_7772354 3990953418895388862930601 := by
  unfold tailWord_7772354
  simp only [CollatzResearch.WordTrace]
  refine ⟨70870259821024086306903029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 188987359522730896818408077 70870259821024086306903029)
  ·
    refine ⟨6644086858221008091272159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 70870259821024086306903029 6644086858221008091272159)
    ·
      refine ⟨9966130287331512136908239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6644086858221008091272159 9966130287331512136908239)
      ·
        refine ⟨14949195430997268205362359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9966130287331512136908239 14949195430997268205362359)
        ·
          refine ⟨22423793146495902308043539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14949195430997268205362359 22423793146495902308043539)
          ·
            refine ⟨33635689719743853462065309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22423793146495902308043539 33635689719743853462065309)
            ·
              refine ⟨12613383644903945048274491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33635689719743853462065309 12613383644903945048274491)
              ·
                refine ⟨18920075467355917572411737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12613383644903945048274491 18920075467355917572411737)
                ·
                  refine ⟨14190056600516938179308803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18920075467355917572411737 14190056600516938179308803)
                  ·
                    refine ⟨21285084900775407268963205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14190056600516938179308803 21285084900775407268963205)
                    ·
                      refine ⟨3990953418895388862930601, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21285084900775407268963205 3990953418895388862930601)
                      ·
                        rfl

theorem cell23_7772354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 1, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 1, 3, 1, 2, 1, 4].length) (baseStart_7772354 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7772354 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7772354 prefixEnd_7772354 := by exact prefixLift 7772354
  have htrace : WordTrace (prefixWord ++ tailWord_7772354) baseStart_7772354 baseEnd_7772354 := by
    simpa [prefixWord, tailWord_7772354, baseEnd_7772354] using wordTrace_append hprefix tailTrace_7772354
  have hstable : (prefixWord ++ tailWord_7772354).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7772354).length < 2 ^ (prefixWord ++ tailWord_7772354).sum := by decide
  have hdescent : baseEnd_7772354 < baseStart_7772354 := by decide
  rcases family_descends (prefixWord ++ tailWord_7772354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7772410 : List Nat := [3, 1, 1, 1, 1, 5, 1, 4, 1, 1, 4]
def baseStart_7772410 : Nat := 118140960795 + 7772410 * 2 ^ 59
def prefixEnd_7772410 : Nat := 4983230072969 + 3 ^ 40 * 7772410 * 2
def baseEnd_7772410 : Nat := 3990982173812040643830343

theorem tailTrace_7772410 : CollatzResearch.WordTrace tailWord_7772410 prefixEnd_7772410 3990982173812040643830343 := by
  unfold tailWord_7772410
  simp only [CollatzResearch.WordTrace]
  refine ⟨70870770442973366697912671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 188988721181262311194433789 70870770442973366697912671)
  ·
    refine ⟨106306155664460050046869007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70870770442973366697912671 106306155664460050046869007)
    ·
      refine ⟨159459233496690075070303511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106306155664460050046869007 159459233496690075070303511)
      ·
        refine ⟨239188850245035112605455267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 159459233496690075070303511 239188850245035112605455267)
        ·
          refine ⟨358783275367552668908182901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 239188850245035112605455267 358783275367552668908182901)
          ·
            refine ⟨33635932065708062710142147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 358783275367552668908182901 33635932065708062710142147)
            ·
              refine ⟨50453898098562094065213221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33635932065708062710142147 50453898098562094065213221)
              ·
                refine ⟨9460105893480392637227479, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 50453898098562094065213221 9460105893480392637227479)
                ·
                  refine ⟨14190158840220588955841219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9460105893480392637227479 14190158840220588955841219)
                  ·
                    refine ⟨21285238260330883433761829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14190158840220588955841219 21285238260330883433761829)
                    ·
                      refine ⟨3990982173812040643830343, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21285238260330883433761829 3990982173812040643830343)
                      ·
                        rfl

theorem cell23_7772410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 5, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 5, 1, 4, 1, 1, 4].length) (baseStart_7772410 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7772410 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7772410 prefixEnd_7772410 := by exact prefixLift 7772410
  have htrace : WordTrace (prefixWord ++ tailWord_7772410) baseStart_7772410 baseEnd_7772410 := by
    simpa [prefixWord, tailWord_7772410, baseEnd_7772410] using wordTrace_append hprefix tailTrace_7772410
  have hstable : (prefixWord ++ tailWord_7772410).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7772410).length < 2 ^ (prefixWord ++ tailWord_7772410).sum := by decide
  have hdescent : baseEnd_7772410 < baseStart_7772410 := by decide
  rcases family_descends (prefixWord ++ tailWord_7772410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7772413 : List Nat := [1, 4, 1, 1, 1, 1, 1, 2, 2, 6, 3]
def baseStart_7772413 : Nat := 118140960795 + 7772413 * 2 ^ 59
def prefixEnd_7772413 : Nat := 4983230072969 + 3 ^ 40 * 7772413 * 2
def baseEnd_7772413 : Nat := 3990983714254004132092829

theorem tailTrace_7772413 : CollatzResearch.WordTrace tailWord_7772413 prefixEnd_7772413 3990983714254004132092829 := by
  unfold tailWord_7772413
  simp only [CollatzResearch.WordTrace]
  refine ⟨283483191190882598304009893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188988794127255065536006595 283483191190882598304009893)
  ·
    refine ⟨53153098348290487182001855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 283483191190882598304009893 53153098348290487182001855)
    ·
      refine ⟨79729647522435730773002783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53153098348290487182001855 79729647522435730773002783)
      ·
        refine ⟨119594471283653596159504175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79729647522435730773002783 119594471283653596159504175)
        ·
          refine ⟨179391706925480394239256263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 119594471283653596159504175 179391706925480394239256263)
          ·
            refine ⟨269087560388220591358884395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 179391706925480394239256263 269087560388220591358884395)
            ·
              refine ⟨403631340582330887038326593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 269087560388220591358884395 403631340582330887038326593)
              ·
                refine ⟨302723505436748165278744945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 403631340582330887038326593 302723505436748165278744945)
                ·
                  refine ⟨227042629077561123959058709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 302723505436748165278744945 227042629077561123959058709)
                  ·
                    refine ⟨10642623238010677685580877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 227042629077561123959058709 10642623238010677685580877)
                    ·
                      refine ⟨3990983714254004132092829, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10642623238010677685580877 3990983714254004132092829)
                      ·
                        rfl

theorem cell23_7772413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 1, 2, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 1, 2, 2, 6, 3].length) (baseStart_7772413 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7772413 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7772413 prefixEnd_7772413 := by exact prefixLift 7772413
  have htrace : WordTrace (prefixWord ++ tailWord_7772413) baseStart_7772413 baseEnd_7772413 := by
    simpa [prefixWord, tailWord_7772413, baseEnd_7772413] using wordTrace_append hprefix tailTrace_7772413
  have hstable : (prefixWord ++ tailWord_7772413).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7772413).length < 2 ^ (prefixWord ++ tailWord_7772413).sum := by decide
  have hdescent : baseEnd_7772413 < baseStart_7772413 := by decide
  rcases family_descends (prefixWord ++ tailWord_7772413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7772430 : List Nat := [4, 1, 1, 2, 1, 2, 4, 1, 1, 1, 5]
def baseStart_7772430 : Nat := 118140960795 + 7772430 * 2 ^ 59
def prefixEnd_7772430 : Nat := 4983230072969 + 3 ^ 40 * 7772430 * 2
def baseEnd_7772430 : Nat := 3990992443425130565580251

theorem tailTrace_7772430 : CollatzResearch.WordTrace tailWord_7772430 prefixEnd_7772430 3990992443425130565580251 := by
  unfold tailWord_7772430
  simp only [CollatzResearch.WordTrace]
  refine ⟨35435476403977626275922343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 188989207487880673471585829 35435476403977626275922343)
  ·
    refine ⟨53153214605966439413883515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35435476403977626275922343 53153214605966439413883515)
    ·
      refine ⟨79729821908949659120825273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53153214605966439413883515 79729821908949659120825273)
      ·
        refine ⟨59797366431712244340618955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79729821908949659120825273 59797366431712244340618955)
        ·
          refine ⟨89696049647568366510928433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59797366431712244340618955 89696049647568366510928433)
          ·
            refine ⟨67272037235676274883196325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 89696049647568366510928433 67272037235676274883196325)
            ·
              refine ⟨12613506981689301540599311, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 67272037235676274883196325 12613506981689301540599311)
              ·
                refine ⟨18920260472533952310898967, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12613506981689301540599311 18920260472533952310898967)
                ·
                  refine ⟨28380390708800928466348451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18920260472533952310898967 28380390708800928466348451)
                  ·
                    refine ⟨42570586063201392699522677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 28380390708800928466348451 42570586063201392699522677)
                    ·
                      refine ⟨3990992443425130565580251, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 42570586063201392699522677 3990992443425130565580251)
                      ·
                        rfl

theorem cell23_7772430_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 4, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 4, 1, 1, 1, 5].length) (baseStart_7772430 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7772430 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7772430 prefixEnd_7772430 := by exact prefixLift 7772430
  have htrace : WordTrace (prefixWord ++ tailWord_7772430) baseStart_7772430 baseEnd_7772430 := by
    simpa [prefixWord, tailWord_7772430, baseEnd_7772430] using wordTrace_append hprefix tailTrace_7772430
  have hstable : (prefixWord ++ tailWord_7772430).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7772430).length < 2 ^ (prefixWord ++ tailWord_7772430).sum := by decide
  have hdescent : baseEnd_7772430 < baseStart_7772430 := by decide
  rcases family_descends (prefixWord ++ tailWord_7772430) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7772433 : List Nat := [1, 2, 2, 1, 1, 7, 9]
def baseStart_7772433 : Nat := 118140960795 + 7772433 * 2 ^ 59
def prefixEnd_7772433 : Nat := 4983230072969 + 3 ^ 40 * 7772433 * 2
def baseEnd_7772433 : Nat := 49271530665025852516577

theorem tailTrace_7772433 : CollatzResearch.WordTrace tailWord_7772433 prefixEnd_7772433 49271530665025852516577 := by
  unfold tailWord_7772433
  simp only [CollatzResearch.WordTrace]
  refine ⟨283483920650810141719737953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188989280433873427813158635 283483920650810141719737953)
  ·
    refine ⟨212612940488107606289803465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 283483920650810141719737953 212612940488107606289803465)
    ·
      refine ⟨159459705366080704717352599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 212612940488107606289803465 159459705366080704717352599)
      ·
        refine ⟨239189558049121057076028899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 159459705366080704717352599 239189558049121057076028899)
        ·
          refine ⟨358784337073681585614043349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 239189558049121057076028899 358784337073681585614043349)
          ·
            refine ⟨8409007900164412162829141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 358784337073681585614043349 8409007900164412162829141)
            ·
              refine ⟨49271530665025852516577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 8409007900164412162829141 49271530665025852516577)
              ·
                rfl

theorem cell23_7772433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 7, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 7, 9].length) (baseStart_7772433 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7772433 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7772433 prefixEnd_7772433 := by exact prefixLift 7772433
  have htrace : WordTrace (prefixWord ++ tailWord_7772433) baseStart_7772433 baseEnd_7772433 := by
    simpa [prefixWord, tailWord_7772433, baseEnd_7772433] using wordTrace_append hprefix tailTrace_7772433
  have hstable : (prefixWord ++ tailWord_7772433).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7772433).length < 2 ^ (prefixWord ++ tailWord_7772433).sum := by decide
  have hdescent : baseEnd_7772433 < baseStart_7772433 := by decide
  rcases family_descends (prefixWord ++ tailWord_7772433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7772450 : List Nat := [3, 3, 1, 1, 3, 2, 2, 8]
def baseStart_7772450 : Nat := 118140960795 + 7772450 * 2 ^ 59
def prefixEnd_7772450 : Nat := 4983230072969 + 3 ^ 40 * 7772450 * 2
def baseEnd_7772450 : Nat := 147814915297711869901117

theorem tailTrace_7772450 : CollatzResearch.WordTrace tailWord_7772450 prefixEnd_7772450 147814915297711869901117 := by
  unfold tailWord_7772450
  simp only [CollatzResearch.WordTrace]
  refine ⟨70871135172937138405776701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 188989693794499035748737869 70871135172937138405776701)
  ·
    refine ⟨26576675689851426902166263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 70871135172937138405776701 26576675689851426902166263)
    ·
      refine ⟨39865013534777140353249395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26576675689851426902166263 39865013534777140353249395)
      ·
        refine ⟨59797520302165710529874093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39865013534777140353249395 59797520302165710529874093)
        ·
          refine ⟨22424070113312141448702785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 59797520302165710529874093 22424070113312141448702785)
          ·
            refine ⟨16818052584984106086527089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22424070113312141448702785 16818052584984106086527089)
            ·
              refine ⟨12613539438738079564895317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16818052584984106086527089 12613539438738079564895317)
              ·
                refine ⟨147814915297711869901117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 12613539438738079564895317 147814915297711869901117)
                ·
                  rfl

theorem cell23_7772450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 2, 2, 8].length) (baseStart_7772450 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7772450 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7772450 prefixEnd_7772450 := by exact prefixLift 7772450
  have htrace : WordTrace (prefixWord ++ tailWord_7772450) baseStart_7772450 baseEnd_7772450 := by
    simpa [prefixWord, tailWord_7772450, baseEnd_7772450] using wordTrace_append hprefix tailTrace_7772450
  have hstable : (prefixWord ++ tailWord_7772450).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7772450).length < 2 ^ (prefixWord ++ tailWord_7772450).sum := by decide
  have hdescent : baseEnd_7772450 < baseStart_7772450 := by decide
  rcases family_descends (prefixWord ++ tailWord_7772450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7772461 : List Nat := [1, 5, 3, 1, 2, 2, 1, 2, 1, 1, 4]
def baseStart_7772461 : Nat := 118140960795 + 7772461 * 2 ^ 59
def prefixEnd_7772461 : Nat := 4983230072969 + 3 ^ 40 * 7772461 * 2
def baseEnd_7772461 : Nat := 3991008361325419944292609

theorem tailTrace_7772461 : CollatzResearch.WordTrace tailWord_7772461 prefixEnd_7772461 3991008361325419944292609 := by
  unfold tailWord_7772461
  simp only [CollatzResearch.WordTrace]
  refine ⟨283484941894708702501757237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188989961263139135001171491 283484941894708702501757237)
  ·
    refine ⟨26576713302628940859539741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 283484941894708702501757237 26576713302628940859539741)
    ·
      refine ⟨9966267488485852822327403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26576713302628940859539741 9966267488485852822327403)
      ·
        refine ⟨14949401232728779233491105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9966267488485852822327403 14949401232728779233491105)
        ·
          refine ⟨11212050924546584425118329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14949401232728779233491105 11212050924546584425118329)
          ·
            refine ⟨8409038193409938318838747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11212050924546584425118329 8409038193409938318838747)
            ·
              refine ⟨12613557290114907478258121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8409038193409938318838747 12613557290114907478258121)
              ·
                refine ⟨9460167967586180608693591, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12613557290114907478258121 9460167967586180608693591)
                ·
                  refine ⟨14190251951379270913040387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9460167967586180608693591 14190251951379270913040387)
                  ·
                    refine ⟨21285377927068906369560581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14190251951379270913040387 21285377927068906369560581)
                    ·
                      refine ⟨3991008361325419944292609, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21285377927068906369560581 3991008361325419944292609)
                      ·
                        rfl

theorem cell23_7772461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 2, 2, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 2, 2, 1, 2, 1, 1, 4].length) (baseStart_7772461 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7772461 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7772461 prefixEnd_7772461 := by exact prefixLift 7772461
  have htrace : WordTrace (prefixWord ++ tailWord_7772461) baseStart_7772461 baseEnd_7772461 := by
    simpa [prefixWord, tailWord_7772461, baseEnd_7772461] using wordTrace_append hprefix tailTrace_7772461
  have hstable : (prefixWord ++ tailWord_7772461).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7772461).length < 2 ^ (prefixWord ++ tailWord_7772461).sum := by decide
  have hdescent : baseEnd_7772461 < baseStart_7772461 := by decide
  rcases family_descends (prefixWord ++ tailWord_7772461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7772481 : List Nat := [1, 2, 5, 2, 2, 1, 3, 1, 1, 2, 3]
def baseStart_7772481 : Nat := 118140960795 + 7772481 * 2 ^ 59
def prefixEnd_7772481 : Nat := 4983230072969 + 3 ^ 40 * 7772481 * 2
def baseEnd_7772481 : Nat := 3991018630938509866042517

theorem tailTrace_7772481 : CollatzResearch.WordTrace tailWord_7772481 prefixEnd_7772481 3991018630938509866042517 := by
  unfold tailWord_7772481
  simp only [CollatzResearch.WordTrace]
  refine ⟨283485671354636245917485297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188990447569757497278323531 283485671354636245917485297)
  ·
    refine ⟨212614253515977184438113973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 283485671354636245917485297 212614253515977184438113973)
    ·
      refine ⟨19932586267122861041073185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 212614253515977184438113973 19932586267122861041073185)
      ·
        refine ⟨14949439700342145780804889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19932586267122861041073185 14949439700342145780804889)
        ·
          refine ⟨11212079775256609335603667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14949439700342145780804889 11212079775256609335603667)
          ·
            refine ⟨16818119662884914003405501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11212079775256609335603667 16818119662884914003405501)
            ·
              refine ⟨6306794873581842751277063, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16818119662884914003405501 6306794873581842751277063)
              ·
                refine ⟨9460192310372764126915595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6306794873581842751277063 9460192310372764126915595)
                ·
                  refine ⟨14190288465559146190373393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9460192310372764126915595 14190288465559146190373393)
                  ·
                    refine ⟨10642716349169359642780045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14190288465559146190373393 10642716349169359642780045)
                    ·
                      refine ⟨3991018630938509866042517, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10642716349169359642780045 3991018630938509866042517)
                      ·
                        rfl

theorem cell23_7772481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 2, 1, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 2, 1, 3, 1, 1, 2, 3].length) (baseStart_7772481 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7772481 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7772481 prefixEnd_7772481 := by exact prefixLift 7772481
  have htrace : WordTrace (prefixWord ++ tailWord_7772481) baseStart_7772481 baseEnd_7772481 := by
    simpa [prefixWord, tailWord_7772481, baseEnd_7772481] using wordTrace_append hprefix tailTrace_7772481
  have hstable : (prefixWord ++ tailWord_7772481).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7772481).length < 2 ^ (prefixWord ++ tailWord_7772481).sum := by decide
  have hdescent : baseEnd_7772481 < baseStart_7772481 := by decide
  rcases family_descends (prefixWord ++ tailWord_7772481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7772500 : List Nat := [2, 4, 1, 1, 2, 2, 1, 1, 2, 3, 4]
def baseStart_7772500 : Nat := 118140960795 + 7772500 * 2 ^ 59
def prefixEnd_7772500 : Nat := 4983230072969 + 3 ^ 40 * 7772500 * 2
def baseEnd_7772500 : Nat := 3991028387070945291704929

theorem tailTrace_7772500 : CollatzResearch.WordTrace tailWord_7772500 prefixEnd_7772500 3991028387070945291704929 := by
  unfold tailWord_7772500
  simp only [CollatzResearch.WordTrace]
  refine ⟨141743182170783706081213477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 188990909561044941441617969 141743182170783706081213477)
  ·
    refine ⟨26576846657021944890227527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 141743182170783706081213477 26576846657021944890227527)
    ·
      refine ⟨39865269985532917335341291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26576846657021944890227527 39865269985532917335341291)
      ·
        refine ⟨59797904978299376003011937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39865269985532917335341291 59797904978299376003011937)
        ·
          refine ⟨44848428733724532002258953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59797904978299376003011937 44848428733724532002258953)
          ·
            refine ⟨33636321550293399001694215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44848428733724532002258953 33636321550293399001694215)
            ·
              refine ⟨50454482325440098502541323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33636321550293399001694215 50454482325440098502541323)
              ·
                refine ⟨75681723488160147753811985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50454482325440098502541323 75681723488160147753811985)
                ·
                  refine ⟨56761292616120110815358989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 75681723488160147753811985 56761292616120110815358989)
                  ·
                    refine ⟨21285484731045041555759621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 56761292616120110815358989 21285484731045041555759621)
                    ·
                      refine ⟨3991028387070945291704929, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21285484731045041555759621 3991028387070945291704929)
                      ·
                        rfl

theorem cell23_7772500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 2, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 2, 1, 1, 2, 3, 4].length) (baseStart_7772500 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7772500 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7772500 prefixEnd_7772500 := by exact prefixLift 7772500
  have htrace : WordTrace (prefixWord ++ tailWord_7772500) baseStart_7772500 baseEnd_7772500 := by
    simpa [prefixWord, tailWord_7772500, baseEnd_7772500] using wordTrace_append hprefix tailTrace_7772500
  have hstable : (prefixWord ++ tailWord_7772500).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7772500).length < 2 ^ (prefixWord ++ tailWord_7772500).sum := by decide
  have hdescent : baseEnd_7772500 < baseStart_7772500 := by decide
  rcases family_descends (prefixWord ++ tailWord_7772500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7772517 : List Nat := [1, 3, 1, 3, 1, 3, 1, 3, 1, 4, 2]
def baseStart_7772517 : Nat := 118140960795 + 7772517 * 2 ^ 59
def prefixEnd_7772517 : Nat := 4983230072969 + 3 ^ 40 * 7772517 * 2
def baseEnd_7772517 : Nat := 3991037116242071725192351

theorem tailTrace_7772517 : CollatzResearch.WordTrace tailWord_7772517 prefixEnd_7772517 3991037116242071725192351 := by
  unfold tailWord_7772517
  simp only [CollatzResearch.WordTrace]
  refine ⟨283486984382505824065795805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188991322921670549377197203 283486984382505824065795805)
  ·
    refine ⟨106307619143439684024673427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 283486984382505824065795805 106307619143439684024673427)
    ·
      refine ⟨159461428715159526037010141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106307619143439684024673427 159461428715159526037010141)
      ·
        refine ⟨59798035768184822263878803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 159461428715159526037010141 59798035768184822263878803)
        ·
          refine ⟨89697053652277233395818205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59798035768184822263878803 89697053652277233395818205)
          ·
            refine ⟨33636395119603962523431827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 89697053652277233395818205 33636395119603962523431827)
            ·
              refine ⟨50454592679405943785147741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33636395119603962523431827 50454592679405943785147741)
              ·
                refine ⟨18920472254777228919430403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 50454592679405943785147741 18920472254777228919430403)
                ·
                  refine ⟨28380708382165843379145605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18920472254777228919430403 28380708382165843379145605)
                  ·
                    refine ⟨5321382821656095633589801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28380708382165843379145605 5321382821656095633589801)
                    ·
                      refine ⟨3991037116242071725192351, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5321382821656095633589801 3991037116242071725192351)
                      ·
                        rfl

theorem cell23_7772517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 3, 1, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 3, 1, 3, 1, 4, 2].length) (baseStart_7772517 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7772517 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7772517 prefixEnd_7772517 := by exact prefixLift 7772517
  have htrace : WordTrace (prefixWord ++ tailWord_7772517) baseStart_7772517 baseEnd_7772517 := by
    simpa [prefixWord, tailWord_7772517, baseEnd_7772517] using wordTrace_append hprefix tailTrace_7772517
  have hstable : (prefixWord ++ tailWord_7772517).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7772517).length < 2 ^ (prefixWord ++ tailWord_7772517).sum := by decide
  have hdescent : baseEnd_7772517 < baseStart_7772517 := by decide
  rcases family_descends (prefixWord ++ tailWord_7772517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7772523 : List Nat := [1, 1, 1, 1, 2, 2, 2, 6, 7]
def baseStart_7772523 : Nat := 118140960795 + 7772523 * 2 ^ 59
def prefixEnd_7772523 : Nat := 4983230072969 + 3 ^ 40 * 7772523 * 2
def baseEnd_7772523 : Nat := 443448910791777633524147

theorem tailTrace_7772523 : CollatzResearch.WordTrace tailWord_7772523 prefixEnd_7772523 443448910791777633524147 := by
  unfold tailWord_7772523
  simp only [CollatzResearch.WordTrace]
  refine ⟨283487203220484087090514223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188991468813656058060342815 283487203220484087090514223)
  ·
    refine ⟨425230804830726130635771335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 283487203220484087090514223 425230804830726130635771335)
    ·
      refine ⟨637846207246089195953657003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 425230804830726130635771335 637846207246089195953657003)
      ·
        refine ⟨956769310869133793930485505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 637846207246089195953657003 956769310869133793930485505)
        ·
          refine ⟨717576983151850345447864129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 956769310869133793930485505 717576983151850345447864129)
          ·
            refine ⟨538182737363887759085898097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 717576983151850345447864129 538182737363887759085898097)
            ·
              refine ⟨403637053022915819314423573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 538182737363887759085898097 403637053022915819314423573)
              ·
                refine ⟨18920486860449179030363605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 403637053022915819314423573 18920486860449179030363605)
                ·
                  refine ⟨443448910791777633524147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18920486860449179030363605 443448910791777633524147)
                  ·
                    rfl

theorem cell23_7772523_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 2, 6, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 2, 6, 7].length) (baseStart_7772523 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7772523 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7772523 prefixEnd_7772523 := by exact prefixLift 7772523
  have htrace : WordTrace (prefixWord ++ tailWord_7772523) baseStart_7772523 baseEnd_7772523 := by
    simpa [prefixWord, tailWord_7772523, baseEnd_7772523] using wordTrace_append hprefix tailTrace_7772523
  have hstable : (prefixWord ++ tailWord_7772523).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7772523).length < 2 ^ (prefixWord ++ tailWord_7772523).sum := by decide
  have hdescent : baseEnd_7772523 < baseStart_7772523 := by decide
  rcases family_descends (prefixWord ++ tailWord_7772523) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7772568 : List Nat := [2, 1, 2, 5, 1, 2, 3, 1, 2, 2, 2]
def baseStart_7772568 : Nat := 118140960795 + 7772568 * 2 ^ 59
def prefixEnd_7772568 : Nat := 4983230072969 + 3 ^ 40 * 7772568 * 2
def baseEnd_7772568 : Nat := 3991063303755451025654617

theorem tailTrace_7772568 : CollatzResearch.WordTrace tailWord_7772568 prefixEnd_7772568 3991063303755451025654617 := by
  unfold tailWord_7772568
  simp only [CollatzResearch.WordTrace]
  refine ⟨141744422252660529887951179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 188992563003547373183934905 141744422252660529887951179)
  ·
    refine ⟨212616633378990794831926769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141744422252660529887951179 212616633378990794831926769)
    ·
      refine ⟨159462475034243096123945077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 212616633378990794831926769 159462475034243096123945077)
      ·
        refine ⟨14949607034460290261619851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 159462475034243096123945077 14949607034460290261619851)
        ·
          refine ⟨22424410551690435392429777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14949607034460290261619851 22424410551690435392429777)
          ·
            refine ⟨16818307913767826544322333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22424410551690435392429777 16818307913767826544322333)
            ·
              refine ⟨6306865467662934954120875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16818307913767826544322333 6306865467662934954120875)
              ·
                refine ⟨9460298201494402431181313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6306865467662934954120875 9460298201494402431181313)
                ·
                  refine ⟨7095223651120801823385985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9460298201494402431181313 7095223651120801823385985)
                  ·
                    refine ⟨5321417738340601367539489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7095223651120801823385985 5321417738340601367539489)
                    ·
                      refine ⟨3991063303755451025654617, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5321417738340601367539489 3991063303755451025654617)
                      ·
                        rfl

theorem cell23_7772568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 2, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 2, 3, 1, 2, 2, 2].length) (baseStart_7772568 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7772568 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7772568 prefixEnd_7772568 := by exact prefixLift 7772568
  have htrace : WordTrace (prefixWord ++ tailWord_7772568) baseStart_7772568 baseEnd_7772568 := by
    simpa [prefixWord, tailWord_7772568, baseEnd_7772568] using wordTrace_append hprefix tailTrace_7772568
  have hstable : (prefixWord ++ tailWord_7772568).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7772568).length < 2 ^ (prefixWord ++ tailWord_7772568).sum := by decide
  have hdescent : baseEnd_7772568 < baseStart_7772568 := by decide
  rcases family_descends (prefixWord ++ tailWord_7772568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7772570 : List Nat := [3, 1, 1, 4, 1, 2, 1, 2, 1, 7]
def baseStart_7772570 : Nat := 118140960795 + 7772570 * 2 ^ 59
def prefixEnd_7772570 : Nat := 4983230072969 + 3 ^ 40 * 7772570 * 2
def baseEnd_7772570 : Nat := 1330354776905586672609869

theorem tailTrace_7772570 : CollatzResearch.WordTrace tailWord_7772570 prefixEnd_7772570 1330354776905586672609869 := by
  unfold tailWord_7772570
  simp only [CollatzResearch.WordTrace]
  refine ⟨70872229362828453529368791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 188992611634209209411650109 70872229362828453529368791)
  ·
    refine ⟨106308344044242680294053187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70872229362828453529368791 106308344044242680294053187)
    ·
      refine ⟨159462516066364020441079781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106308344044242680294053187 159462516066364020441079781)
      ·
        refine ⟨29899221762443253832702459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 159462516066364020441079781 29899221762443253832702459)
        ·
          refine ⟨44848832643664880749053689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29899221762443253832702459 44848832643664880749053689)
          ·
            refine ⟨33636624482748660561790267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44848832643664880749053689 33636624482748660561790267)
            ·
              refine ⟨50454936724122990842685401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33636624482748660561790267 50454936724122990842685401)
              ·
                refine ⟨37841202543092243132014051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50454936724122990842685401 37841202543092243132014051)
                ·
                  refine ⟨56761803814638364698021077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37841202543092243132014051 56761803814638364698021077)
                  ·
                    refine ⟨1330354776905586672609869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 56761803814638364698021077 1330354776905586672609869)
                    ·
                      rfl

theorem cell23_7772570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 2, 1, 2, 1, 7].length) (baseStart_7772570 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7772570 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7772570 prefixEnd_7772570 := by exact prefixLift 7772570
  have htrace : WordTrace (prefixWord ++ tailWord_7772570) baseStart_7772570 baseEnd_7772570 := by
    simpa [prefixWord, tailWord_7772570, baseEnd_7772570] using wordTrace_append hprefix tailTrace_7772570
  have hstable : (prefixWord ++ tailWord_7772570).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7772570).length < 2 ^ (prefixWord ++ tailWord_7772570).sum := by decide
  have hdescent : baseEnd_7772570 < baseStart_7772570 := by decide
  rcases family_descends (prefixWord ++ tailWord_7772570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7772617 : List Nat := [1, 2, 1, 1, 2, 1, 7, 1, 3, 4]
def baseStart_7772617 : Nat := 118140960795 + 7772617 * 2 ^ 59
def prefixEnd_7772617 : Nat := 4983230072969 + 3 ^ 40 * 7772617 * 2
def baseEnd_7772617 : Nat := 1330362821435840444647297

theorem tailTrace_7772617 : CollatzResearch.WordTrace tailWord_7772617 prefixEnd_7772617 1330362821435840444647297 := by
  unfold tailWord_7772617
  simp only [CollatzResearch.WordTrace]
  refine ⟨283490631682143541144436105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188993754454762360762957403 283490631682143541144436105)
  ·
    refine ⟨212617973761607655858327079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 283490631682143541144436105 212617973761607655858327079)
    ·
      refine ⟨318926960642411483787490619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 212617973761607655858327079 318926960642411483787490619)
      ·
        refine ⟨478390440963617225681235929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 318926960642411483787490619 478390440963617225681235929)
        ·
          refine ⟨358792830722712919260926947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 478390440963617225681235929 358792830722712919260926947)
          ·
            refine ⟨538189246084069378891390421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 358792830722712919260926947 538189246084069378891390421)
            ·
              refine ⟨12613810455095376067766963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 538189246084069378891390421 12613810455095376067766963)
              ·
                refine ⟨18920715682643064101650445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12613810455095376067766963 18920715682643064101650445)
                ·
                  refine ⟨7095268380991149038118917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18920715682643064101650445 7095268380991149038118917)
                  ·
                    refine ⟨1330362821435840444647297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7095268380991149038118917 1330362821435840444647297)
                    ·
                      rfl

theorem cell23_7772617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 7, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 7, 1, 3, 4].length) (baseStart_7772617 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7772617 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7772617 prefixEnd_7772617 := by exact prefixLift 7772617
  have htrace : WordTrace (prefixWord ++ tailWord_7772617) baseStart_7772617 baseEnd_7772617 := by
    simpa [prefixWord, tailWord_7772617, baseEnd_7772617] using wordTrace_append hprefix tailTrace_7772617
  have hstable : (prefixWord ++ tailWord_7772617).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7772617).length < 2 ^ (prefixWord ++ tailWord_7772617).sum := by decide
  have hdescent : baseEnd_7772617 < baseStart_7772617 := by decide
  rcases family_descends (prefixWord ++ tailWord_7772617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7772697 : List Nat := [1, 2, 1, 2, 1, 1, 2, 3, 2, 6, 2]
def baseStart_7772697 : Nat := 118140960795 + 7772697 * 2 ^ 59
def prefixEnd_7772697 : Nat := 4983230072969 + 3 ^ 40 * 7772697 * 2
def baseEnd_7772697 : Nat := 3991129542759881020941523

theorem tailTrace_7772697 : CollatzResearch.WordTrace tailWord_7772697 prefixEnd_7772697 3991129542759881020941523 := by
  unfold tailWord_7772697
  simp only [CollatzResearch.WordTrace]
  refine ⟨283493549521853714807348345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188995699681235809871565563 283493549521853714807348345)
  ·
    refine ⟨212620162141390286105511259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 283493549521853714807348345 212620162141390286105511259)
    ·
      refine ⟨318930243212085429158266889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 212620162141390286105511259 318930243212085429158266889)
      ·
        refine ⟨239197682409064071868700167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 318930243212085429158266889 239197682409064071868700167)
        ·
          refine ⟨358796523613596107803050251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 239197682409064071868700167 358796523613596107803050251)
          ·
            refine ⟨538194785420394161704575377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 358796523613596107803050251 538194785420394161704575377)
            ·
              refine ⟨403646089065295621278431533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 538194785420394161704575377 403646089065295621278431533)
              ·
                refine ⟨151367283399485857979411825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 403646089065295621278431533 151367283399485857979411825)
                ·
                  refine ⟨113525462549614393484558869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 151367283399485857979411825 113525462549614393484558869)
                  ·
                    refine ⟨5321506057013174694588697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 113525462549614393484558869 5321506057013174694588697)
                    ·
                      refine ⟨3991129542759881020941523, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5321506057013174694588697 3991129542759881020941523)
                      ·
                        rfl

theorem cell23_7772697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 2, 3, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 2, 3, 2, 6, 2].length) (baseStart_7772697 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7772697 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7772697 prefixEnd_7772697 := by exact prefixLift 7772697
  have htrace : WordTrace (prefixWord ++ tailWord_7772697) baseStart_7772697 baseEnd_7772697 := by
    simpa [prefixWord, tailWord_7772697, baseEnd_7772697] using wordTrace_append hprefix tailTrace_7772697
  have hstable : (prefixWord ++ tailWord_7772697).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7772697).length < 2 ^ (prefixWord ++ tailWord_7772697).sum := by decide
  have hdescent : baseEnd_7772697 < baseStart_7772697 := by decide
  rcases family_descends (prefixWord ++ tailWord_7772697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7772701 : List Nat := [1, 4, 2, 2, 1, 2, 3, 1, 2, 3, 2]
def baseStart_7772701 : Nat := 118140960795 + 7772701 * 2 ^ 59
def prefixEnd_7772701 : Nat := 4983230072969 + 3 ^ 40 * 7772701 * 2
def baseEnd_7772701 : Nat := 3991131596682499005291505

theorem tailTrace_7772701 : CollatzResearch.WordTrace tailWord_7772701 prefixEnd_7772701 3991131596682499005291505 := by
  unfold tailWord_7772701
  simp only [CollatzResearch.WordTrace]
  refine ⟨283493695413839223490493957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188995796942559482326995971 283493695413839223490493957)
  ·
    refine ⟨53155067890094854404467617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 283493695413839223490493957 53155067890094854404467617)
    ·
      refine ⟨39866300917571140803350713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53155067890094854404467617 39866300917571140803350713)
      ·
        refine ⟨29899725688178355602513035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39866300917571140803350713 29899725688178355602513035)
        ·
          refine ⟨44849588532267533403769553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29899725688178355602513035 44849588532267533403769553)
          ·
            refine ⟨33637191399200650052827165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44849588532267533403769553 33637191399200650052827165)
            ·
              refine ⟨12613946774700243769810187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33637191399200650052827165 12613946774700243769810187)
              ·
                refine ⟨18920920162050365654715281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12613946774700243769810187 18920920162050365654715281)
                ·
                  refine ⟨14190690121537774241036461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18920920162050365654715281 14190690121537774241036461)
                  ·
                    refine ⟨5321508795576665340388673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14190690121537774241036461 5321508795576665340388673)
                    ·
                      refine ⟨3991131596682499005291505, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5321508795576665340388673 3991131596682499005291505)
                      ·
                        rfl

theorem cell23_7772701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 2, 3, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 2, 3, 1, 2, 3, 2].length) (baseStart_7772701 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7772701 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7772701 prefixEnd_7772701 := by exact prefixLift 7772701
  have htrace : WordTrace (prefixWord ++ tailWord_7772701) baseStart_7772701 baseEnd_7772701 := by
    simpa [prefixWord, tailWord_7772701, baseEnd_7772701] using wordTrace_append hprefix tailTrace_7772701
  have hstable : (prefixWord ++ tailWord_7772701).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7772701).length < 2 ^ (prefixWord ++ tailWord_7772701).sum := by decide
  have hdescent : baseEnd_7772701 < baseStart_7772701 := by decide
  rcases family_descends (prefixWord ++ tailWord_7772701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7772707 : List Nat := [1, 1, 1, 4, 4, 1, 2, 2, 1, 6]
def baseStart_7772707 : Nat := 118140960795 + 7772707 * 2 ^ 59
def prefixEnd_7772707 : Nat := 4983230072969 + 3 ^ 40 * 7772707 * 2
def baseEnd_7772707 : Nat := 1330378225855475327272159

theorem tailTrace_7772707 : CollatzResearch.WordTrace tailWord_7772707 prefixEnd_7772707 1330378225855475327272159 := by
  unfold tailWord_7772707
  simp only [CollatzResearch.WordTrace]
  refine ⟨283493914251817486515212375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188995942834544991010141583 283493914251817486515212375)
  ·
    refine ⟨425240871377726229772818563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 283493914251817486515212375 425240871377726229772818563)
    ·
      refine ⟨637861307066589344659227845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 425240871377726229772818563 637861307066589344659227845)
      ·
        refine ⟨119598995074985502123605221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 637861307066589344659227845 119598995074985502123605221)
        ·
          refine ⟨22424811576559781648175979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 119598995074985502123605221 22424811576559781648175979)
          ·
            refine ⟨33637217364839672472263969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22424811576559781648175979 33637217364839672472263969)
            ·
              refine ⟨25227913023629754354197977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33637217364839672472263969 25227913023629754354197977)
              ·
                refine ⟨18920934767722315765648483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25227913023629754354197977 18920934767722315765648483)
                ·
                  refine ⟨28381402151583473648472725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18920934767722315765648483 28381402151583473648472725)
                  ·
                    refine ⟨1330378225855475327272159, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28381402151583473648472725 1330378225855475327272159)
                    ·
                      rfl

theorem cell23_7772707_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 1, 2, 2, 1, 6].length) (baseStart_7772707 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7772707 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7772707 prefixEnd_7772707 := by exact prefixLift 7772707
  have htrace : WordTrace (prefixWord ++ tailWord_7772707) baseStart_7772707 baseEnd_7772707 := by
    simpa [prefixWord, tailWord_7772707, baseEnd_7772707] using wordTrace_append hprefix tailTrace_7772707
  have hstable : (prefixWord ++ tailWord_7772707).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7772707).length < 2 ^ (prefixWord ++ tailWord_7772707).sum := by decide
  have hdescent : baseEnd_7772707 < baseStart_7772707 := by decide
  rcases family_descends (prefixWord ++ tailWord_7772707) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7772741 : List Nat := [1, 3, 1, 1, 1, 6, 3, 1, 2, 4]
def baseStart_7772741 : Nat := 118140960795 + 7772741 * 2 ^ 59
def prefixEnd_7772741 : Nat := 4983230072969 + 3 ^ 40 * 7772741 * 2
def baseEnd_7772741 : Nat := 1330384045302892949597107

theorem tailTrace_7772741 : CollatzResearch.WordTrace tailWord_7772741 prefixEnd_7772741 1330384045302892949597107 := by
  unfold tailWord_7772741
  simp only [CollatzResearch.WordTrace]
  refine ⟨283495154333694310321950077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188996769555796206881300051 283495154333694310321950077)
  ·
    refine ⟨106310682875135366370731279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 283495154333694310321950077 106310682875135366370731279)
    ·
      refine ⟨159466024312703049556096919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106310682875135366370731279 159466024312703049556096919)
      ·
        refine ⟨239199036469054574334145379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 159466024312703049556096919 239199036469054574334145379)
        ·
          refine ⟨358798554703581861501218069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 239199036469054574334145379 358798554703581861501218069)
          ·
            refine ⟨16818682251730399757869597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 358798554703581861501218069 16818682251730399757869597)
            ·
              refine ⟨6307005844398899909201099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16818682251730399757869597 6307005844398899909201099)
              ·
                refine ⟨9460508766598349863801649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6307005844398899909201099 9460508766598349863801649)
                ·
                  refine ⟨7095381574948762397851237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9460508766598349863801649 7095381574948762397851237)
                  ·
                    refine ⟨1330384045302892949597107, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7095381574948762397851237 1330384045302892949597107)
                    ·
                      rfl

theorem cell23_7772741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 6, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 6, 3, 1, 2, 4].length) (baseStart_7772741 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7772741 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7772741 prefixEnd_7772741 := by exact prefixLift 7772741
  have htrace : WordTrace (prefixWord ++ tailWord_7772741) baseStart_7772741 baseEnd_7772741 := by
    simpa [prefixWord, tailWord_7772741, baseEnd_7772741] using wordTrace_append hprefix tailTrace_7772741
  have hstable : (prefixWord ++ tailWord_7772741).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7772741).length < 2 ^ (prefixWord ++ tailWord_7772741).sum := by decide
  have hdescent : baseEnd_7772741 < baseStart_7772741 := by decide
  rcases family_descends (prefixWord ++ tailWord_7772741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7772781 : List Nat := [1, 5, 1, 1, 3, 1, 2, 1, 4, 1, 3]
def baseStart_7772781 : Nat := 118140960795 + 7772781 * 2 ^ 59
def prefixEnd_7772781 : Nat := 4983230072969 + 3 ^ 40 * 7772781 * 2
def baseEnd_7772781 : Nat := 3991172675134858692291137

theorem tailTrace_7772781 : CollatzResearch.WordTrace tailWord_7772781 prefixEnd_7772781 3991172675134858692291137 := by
  unfold tailWord_7772781
  simp only [CollatzResearch.WordTrace]
  refine ⟨283496613253549397153406197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188997742169032931435604131 283496613253549397153406197)
  ·
    refine ⟨26577807492520255983131831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 283496613253549397153406197 26577807492520255983131831)
    ·
      refine ⟨39866711238780383974697747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26577807492520255983131831 39866711238780383974697747)
      ·
        refine ⟨59800066858170575962046621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39866711238780383974697747 59800066858170575962046621)
        ·
          refine ⟨22425025071813965985767483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 59800066858170575962046621 22425025071813965985767483)
          ·
            refine ⟨33637537607720948978651225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22425025071813965985767483 33637537607720948978651225)
            ·
              refine ⟨25228153205790711733988419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33637537607720948978651225 25228153205790711733988419)
              ·
                refine ⟨37842229808686067600982629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25228153205790711733988419 37842229808686067600982629)
                ·
                  refine ⟨7095418089128637675184243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 37842229808686067600982629 7095418089128637675184243)
                  ·
                    refine ⟨10643127133692956512776365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7095418089128637675184243 10643127133692956512776365)
                    ·
                      refine ⟨3991172675134858692291137, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10643127133692956512776365 3991172675134858692291137)
                      ·
                        rfl

theorem cell23_7772781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 1, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 1, 2, 1, 4, 1, 3].length) (baseStart_7772781 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7772781 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7772781 prefixEnd_7772781 := by exact prefixLift 7772781
  have htrace : WordTrace (prefixWord ++ tailWord_7772781) baseStart_7772781 baseEnd_7772781 := by
    simpa [prefixWord, tailWord_7772781, baseEnd_7772781] using wordTrace_append hprefix tailTrace_7772781
  have hstable : (prefixWord ++ tailWord_7772781).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7772781).length < 2 ^ (prefixWord ++ tailWord_7772781).sum := by decide
  have hdescent : baseEnd_7772781 < baseStart_7772781 := by decide
  rcases family_descends (prefixWord ++ tailWord_7772781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7772782 : List Nat := [4, 1, 2, 2, 2, 2, 3, 2, 1, 2, 2]
def baseStart_7772782 : Nat := 118140960795 + 7772782 * 2 ^ 59
def prefixEnd_7772782 : Nat := 4983230072969 + 3 ^ 40 * 7772782 * 2
def baseEnd_7772782 : Nat := 3991173188615513188378633

theorem tailTrace_7772782 : CollatzResearch.WordTrace tailWord_7772782 prefixEnd_7772782 3991173188615513188378633 := by
  unfold tailWord_7772782
  simp only [CollatzResearch.WordTrace]
  refine ⟨35437081215818221790524075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 188997766484363849549461733 35437081215818221790524075)
  ·
    refine ⟨53155621823727332685786113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35437081215818221790524075 53155621823727332685786113)
    ·
      refine ⟨39866716367795499514339585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53155621823727332685786113 39866716367795499514339585)
      ·
        refine ⟨29900037275846624635754689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39866716367795499514339585 29900037275846624635754689)
        ·
          refine ⟨22425027956884968476816017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29900037275846624635754689 22425027956884968476816017)
          ·
            refine ⟨16818770967663726357612013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22425027956884968476816017 16818770967663726357612013)
            ·
              refine ⟨6307039112873897384104505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16818770967663726357612013 6307039112873897384104505)
              ·
                refine ⟨4730279334655423038078379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6307039112873897384104505 4730279334655423038078379)
                ·
                  refine ⟨7095419001983134557117569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4730279334655423038078379 7095419001983134557117569)
                  ·
                    refine ⟨5321564251487350917838177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7095419001983134557117569 5321564251487350917838177)
                    ·
                      refine ⟨3991173188615513188378633, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5321564251487350917838177 3991173188615513188378633)
                      ·
                        rfl

theorem cell23_7772782_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 2, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 2, 3, 2, 1, 2, 2].length) (baseStart_7772782 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7772782 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7772782 prefixEnd_7772782 := by exact prefixLift 7772782
  have htrace : WordTrace (prefixWord ++ tailWord_7772782) baseStart_7772782 baseEnd_7772782 := by
    simpa [prefixWord, tailWord_7772782, baseEnd_7772782] using wordTrace_append hprefix tailTrace_7772782
  have hstable : (prefixWord ++ tailWord_7772782).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7772782).length < 2 ^ (prefixWord ++ tailWord_7772782).sum := by decide
  have hdescent : baseEnd_7772782 < baseStart_7772782 := by decide
  rcases family_descends (prefixWord ++ tailWord_7772782) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7772807 : List Nat := [1, 1, 4, 2, 1, 2, 1, 1, 4, 1, 5]
def baseStart_7772807 : Nat := 118140960795 + 7772807 * 2 ^ 59
def prefixEnd_7772807 : Nat := 4983230072969 + 3 ^ 40 * 7772807 * 2
def baseEnd_7772807 : Nat := 3991186025631875590566017

theorem tailTrace_7772807 : CollatzResearch.WordTrace tailWord_7772807 prefixEnd_7772807 3991186025631875590566017 := by
  unfold tailWord_7772807
  simp only [CollatzResearch.WordTrace]
  refine ⟨283497561551455203593852675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188998374367636802395901783 283497561551455203593852675)
  ·
    refine ⟨425246342327182805390779013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 283497561551455203593852675 425246342327182805390779013)
    ·
      refine ⟨79733689186346776010771065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 425246342327182805390779013 79733689186346776010771065)
      ·
        refine ⟨59800266889760082008078299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79733689186346776010771065 59800266889760082008078299)
        ·
          refine ⟨89700400334640123012117449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59800266889760082008078299 89700400334640123012117449)
          ·
            refine ⟨67275300250980092259088087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 89700400334640123012117449 67275300250980092259088087)
            ·
              refine ⟨100912950376470138388632131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67275300250980092259088087 100912950376470138388632131)
              ·
                refine ⟨151369425564705207582948197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 100912950376470138388632131 151369425564705207582948197)
                ·
                  refine ⟨28381767293382226421802787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 151369425564705207582948197 28381767293382226421802787)
                  ·
                    refine ⟨42572650940073339632704181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 28381767293382226421802787 42572650940073339632704181)
                    ·
                      refine ⟨3991186025631875590566017, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 42572650940073339632704181 3991186025631875590566017)
                      ·
                        rfl

theorem cell23_7772807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 1, 1, 4, 1, 5].length) (baseStart_7772807 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7772807 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7772807 prefixEnd_7772807 := by exact prefixLift 7772807
  have htrace : WordTrace (prefixWord ++ tailWord_7772807) baseStart_7772807 baseEnd_7772807 := by
    simpa [prefixWord, tailWord_7772807, baseEnd_7772807] using wordTrace_append hprefix tailTrace_7772807
  have hstable : (prefixWord ++ tailWord_7772807).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7772807).length < 2 ^ (prefixWord ++ tailWord_7772807).sum := by decide
  have hdescent : baseEnd_7772807 < baseStart_7772807 := by decide
  rcases family_descends (prefixWord ++ tailWord_7772807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7772857 : List Nat := [1, 2, 1, 4, 1, 1, 1, 4, 1, 7]
def baseStart_7772857 : Nat := 118140960795 + 7772857 * 2 ^ 59
def prefixEnd_7772857 : Nat := 4983230072969 + 3 ^ 40 * 7772857 * 2
def baseEnd_7772857 : Nat := 1330403899888200131646929

theorem tailTrace_7772857 : CollatzResearch.WordTrace tailWord_7772857 prefixEnd_7772857 1330403899888200131646929 := by
  unfold tailWord_7772857
  simp only [CollatzResearch.WordTrace]
  refine ⟨283499385201274062133172825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188999590134182708088781883 283499385201274062133172825)
  ·
    refine ⟨212624538900955546599879619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 283499385201274062133172825 212624538900955546599879619)
    ·
      refine ⟨318936808351433319899819429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 212624538900955546599879619 318936808351433319899819429)
      ·
        refine ⟨59800651565893747481216143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 318936808351433319899819429 59800651565893747481216143)
        ·
          refine ⟨89700977348840621221824215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59800651565893747481216143 89700977348840621221824215)
          ·
            refine ⟨134551466023260931832736323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89700977348840621221824215 134551466023260931832736323)
            ·
              refine ⟨201827199034891397749104485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 134551466023260931832736323 201827199034891397749104485)
              ·
                refine ⟨37842599819042137077957091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 201827199034891397749104485 37842599819042137077957091)
                ·
                  refine ⟨56763899728563205616935637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37842599819042137077957091 56763899728563205616935637)
                  ·
                    refine ⟨1330403899888200131646929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 56763899728563205616935637 1330403899888200131646929)
                    ·
                      rfl

theorem cell23_7772857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 1, 4, 1, 7].length) (baseStart_7772857 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7772857 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7772857 prefixEnd_7772857 := by exact prefixLift 7772857
  have htrace : WordTrace (prefixWord ++ tailWord_7772857) baseStart_7772857 baseEnd_7772857 := by
    simpa [prefixWord, tailWord_7772857, baseEnd_7772857] using wordTrace_append hprefix tailTrace_7772857
  have hstable : (prefixWord ++ tailWord_7772857).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7772857).length < 2 ^ (prefixWord ++ tailWord_7772857).sum := by decide
  have hdescent : baseEnd_7772857 < baseStart_7772857 := by decide
  rcases family_descends (prefixWord ++ tailWord_7772857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7772874 : List Nat := [3, 1, 2, 1, 4, 2, 1, 1, 1, 7]
def baseStart_7772874 : Nat := 118140960795 + 7772874 * 2 ^ 59
def prefixEnd_7772874 : Nat := 4983230072969 + 3 ^ 40 * 7772874 * 2
def baseEnd_7772874 : Nat := 1330406809611908942809403

theorem tailTrace_7772874 : CollatzResearch.WordTrace tailWord_7772874 prefixEnd_7772874 1330406809611908942809403 := by
  unfold tailWord_7772874
  simp only [CollatzResearch.WordTrace]
  refine ⟨70875001310553118509135419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 189000003494808316024361117 70875001310553118509135419)
  ·
    refine ⟨106312501965829677763703129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70875001310553118509135419 106312501965829677763703129)
    ·
      refine ⟨79734376474372258322777347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 106312501965829677763703129 79734376474372258322777347)
      ·
        refine ⟨119601564711558387484166021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79734376474372258322777347 119601564711558387484166021)
        ·
          refine ⟨22425293383417197653281129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 119601564711558387484166021 22425293383417197653281129)
          ·
            refine ⟨16818970037562898239960847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22425293383417197653281129 16818970037562898239960847)
            ·
              refine ⟨25228455056344347359941271, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16818970037562898239960847 25228455056344347359941271)
              ·
                refine ⟨37842682584516521039911907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25228455056344347359941271 37842682584516521039911907)
                ·
                  refine ⟨56764023876774781559867861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37842682584516521039911907 56764023876774781559867861)
                  ·
                    refine ⟨1330406809611908942809403, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 56764023876774781559867861 1330406809611908942809403)
                    ·
                      rfl

theorem cell23_7772874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 2, 1, 1, 1, 7].length) (baseStart_7772874 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7772874 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7772874 prefixEnd_7772874 := by exact prefixLift 7772874
  have htrace : WordTrace (prefixWord ++ tailWord_7772874) baseStart_7772874 baseEnd_7772874 := by
    simpa [prefixWord, tailWord_7772874, baseEnd_7772874] using wordTrace_append hprefix tailTrace_7772874
  have hstable : (prefixWord ++ tailWord_7772874).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7772874).length < 2 ^ (prefixWord ++ tailWord_7772874).sum := by decide
  have hdescent : baseEnd_7772874 < baseStart_7772874 := by decide
  rcases family_descends (prefixWord ++ tailWord_7772874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7772907 : List Nat := [1, 1, 1, 1, 2, 4, 1, 1, 4, 1, 6]
def baseStart_7772907 : Nat := 118140960795 + 7772907 * 2 ^ 59
def prefixEnd_7772907 : Nat := 4983230072969 + 3 ^ 40 * 7772907 * 2
def baseEnd_7772907 : Nat := 3991237373697325199315557

theorem tailTrace_7772907 : CollatzResearch.WordTrace tailWord_7772907 prefixEnd_7772907 3991237373697325199315557 := by
  unfold tailWord_7772907
  simp only [CollatzResearch.WordTrace]
  refine ⟨283501208851092920672492975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189000805900728613781661983 283501208851092920672492975)
  ·
    refine ⟨425251813276639381008739463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 283501208851092920672492975 425251813276639381008739463)
    ·
      refine ⟨637877719914959071513109195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 425251813276639381008739463 637877719914959071513109195)
      ·
        refine ⟨956816579872438607269663793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 637877719914959071513109195 956816579872438607269663793)
        ·
          refine ⟨717612434904328955452247845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 956816579872438607269663793 717612434904328955452247845)
          ·
            refine ⟨134552331544561679147296471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 717612434904328955452247845 134552331544561679147296471)
            ·
              refine ⟨201828497316842518720944707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 134552331544561679147296471 201828497316842518720944707)
              ·
                refine ⟨302742745975263778081417061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 201828497316842518720944707 302742745975263778081417061)
                ·
                  refine ⟨56764264870361958390265699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 302742745975263778081417061 56764264870361958390265699)
                  ·
                    refine ⟨85146397305542937585398549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 56764264870361958390265699 85146397305542937585398549)
                    ·
                      refine ⟨3991237373697325199315557, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 85146397305542937585398549 3991237373697325199315557)
                      ·
                        rfl

theorem cell23_7772907_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 1, 1, 4, 1, 6].length) (baseStart_7772907 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7772907 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7772907 prefixEnd_7772907 := by exact prefixLift 7772907
  have htrace : WordTrace (prefixWord ++ tailWord_7772907) baseStart_7772907 baseEnd_7772907 := by
    simpa [prefixWord, tailWord_7772907, baseEnd_7772907] using wordTrace_append hprefix tailTrace_7772907
  have hstable : (prefixWord ++ tailWord_7772907).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7772907).length < 2 ^ (prefixWord ++ tailWord_7772907).sum := by decide
  have hdescent : baseEnd_7772907 < baseStart_7772907 := by decide
  rcases family_descends (prefixWord ++ tailWord_7772907) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7772911 : List Nat := [1, 1, 2, 1, 5, 2, 2, 1, 2, 4, 2]
def baseStart_7772911 : Nat := 118140960795 + 7772911 * 2 ^ 59
def prefixEnd_7772911 : Nat := 4983230072969 + 3 ^ 40 * 7772911 * 2
def baseEnd_7772911 : Nat := 3991239427619943183665539

theorem tailTrace_7772911 : CollatzResearch.WordTrace tailWord_7772911 prefixEnd_7772911 3991239427619943183665539 := by
  unfold tailWord_7772911
  simp only [CollatzResearch.WordTrace]
  refine ⟨283501354743078429355638587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189000903162052286237092391 283501354743078429355638587)
  ·
    refine ⟨425252032114617644033457881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 283501354743078429355638587 425252032114617644033457881)
    ·
      refine ⟨318939024085963233025093411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 425252032114617644033457881 318939024085963233025093411)
      ·
        refine ⟨478408536128944849537640117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 318939024085963233025093411 478408536128944849537640117)
        ·
          refine ⟨44850800262088579644153761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 478408536128944849537640117 44850800262088579644153761)
          ·
            refine ⟨33638100196566434733115321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44850800262088579644153761 33638100196566434733115321)
            ·
              refine ⟨25228575147424826049836491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33638100196566434733115321 25228575147424826049836491)
              ·
                refine ⟨37842862721137239074754737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25228575147424826049836491 37842862721137239074754737)
                ·
                  refine ⟨28382147040852929306066053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37842862721137239074754737 28382147040852929306066053)
                  ·
                    refine ⟨5321652570159924244887385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28382147040852929306066053 5321652570159924244887385)
                    ·
                      refine ⟨3991239427619943183665539, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5321652570159924244887385 3991239427619943183665539)
                      ·
                        rfl

theorem cell23_7772911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 2, 2, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 2, 2, 1, 2, 4, 2].length) (baseStart_7772911 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7772911 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7772911 prefixEnd_7772911 := by exact prefixLift 7772911
  have htrace : WordTrace (prefixWord ++ tailWord_7772911) baseStart_7772911 baseEnd_7772911 := by
    simpa [prefixWord, tailWord_7772911, baseEnd_7772911] using wordTrace_append hprefix tailTrace_7772911
  have hstable : (prefixWord ++ tailWord_7772911).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7772911).length < 2 ^ (prefixWord ++ tailWord_7772911).sum := by decide
  have hdescent : baseEnd_7772911 < baseStart_7772911 := by decide
  rcases family_descends (prefixWord ++ tailWord_7772911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7772981 : List Nat := [1, 3, 3, 1, 3, 2, 1, 1, 3, 5]
def baseStart_7772981 : Nat := 118140960795 + 7772981 * 2 ^ 59
def prefixEnd_7772981 : Nat := 4983230072969 + 3 ^ 40 * 7772981 * 2
def baseEnd_7772981 : Nat := 1330425123755252636596739

theorem tailTrace_7772981 : CollatzResearch.WordTrace tailWord_7772981 prefixEnd_7772981 1330425123755252636596739 := by
  unfold tailWord_7772981
  simp only [CollatzResearch.WordTrace]
  refine ⟨283503907852824831310686797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189002605235216554207124531 283503907852824831310686797)
  ·
    refine ⟨106313965444809311741507549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 283503907852824831310686797 106313965444809311741507549)
    ·
      refine ⟨39867737041803491903065331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 106313965444809311741507549 39867737041803491903065331)
      ·
        refine ⟨59801605562705237854597997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39867737041803491903065331 59801605562705237854597997)
        ·
          refine ⟨22425602086014464195474249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 59801605562705237854597997 22425602086014464195474249)
          ·
            refine ⟨16819201564510848146605687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22425602086014464195474249 16819201564510848146605687)
            ·
              refine ⟨25228802346766272219908531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16819201564510848146605687 25228802346766272219908531)
              ·
                refine ⟨37843203520149408329862797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25228802346766272219908531 37843203520149408329862797)
                ·
                  refine ⟨14191201320056028123698549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 37843203520149408329862797 14191201320056028123698549)
                  ·
                    refine ⟨1330425123755252636596739, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14191201320056028123698549 1330425123755252636596739)
                    ·
                      rfl

theorem cell23_7772981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 2, 1, 1, 3, 5].length) (baseStart_7772981 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7772981 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7772981 prefixEnd_7772981 := by exact prefixLift 7772981
  have htrace : WordTrace (prefixWord ++ tailWord_7772981) baseStart_7772981 baseEnd_7772981 := by
    simpa [prefixWord, tailWord_7772981, baseEnd_7772981] using wordTrace_append hprefix tailTrace_7772981
  have hstable : (prefixWord ++ tailWord_7772981).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7772981).length < 2 ^ (prefixWord ++ tailWord_7772981).sum := by decide
  have hdescent : baseEnd_7772981 < baseStart_7772981 := by decide
  rcases family_descends (prefixWord ++ tailWord_7772981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7773012 : List Nat := [2, 4, 1, 1, 4, 1, 1, 4, 1, 1, 3]
def baseStart_7773012 : Nat := 118140960795 + 7773012 * 2 ^ 59
def prefixEnd_7773012 : Nat := 4983230072969 + 3 ^ 40 * 7773012 * 2
def baseEnd_7773012 : Nat := 3991291289166047288502575

theorem tailTrace_7773012 : CollatzResearch.WordTrace tailWord_7773012 prefixEnd_7773012 3991291289166047288502575 := by
  unfold tailWord_7773012
  simp only [CollatzResearch.WordTrace]
  refine ⟨141752519257856261802532645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 189003359010475015736710193 141752519257856261802532645)
  ·
    refine ⟨26578597360848049087974871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 141752519257856261802532645 26578597360848049087974871)
    ·
      refine ⟨39867896041272073631962307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26578597360848049087974871 39867896041272073631962307)
      ·
        refine ⟨59801844061908110447943461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39867896041272073631962307 59801844061908110447943461)
        ·
          refine ⟨11212845761607770708989399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 59801844061908110447943461 11212845761607770708989399)
          ·
            refine ⟨16819268642411656063484099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11212845761607770708989399 16819268642411656063484099)
            ·
              refine ⟨25228902963617484095226149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16819268642411656063484099 25228902963617484095226149)
              ·
                refine ⟨4730419305678278267854903, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25228902963617484095226149 4730419305678278267854903)
                ·
                  refine ⟨7095628958517417401782355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4730419305678278267854903 7095628958517417401782355)
                  ·
                    refine ⟨10643443437776126102673533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7095628958517417401782355 10643443437776126102673533)
                    ·
                      refine ⟨3991291289166047288502575, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10643443437776126102673533 3991291289166047288502575)
                      ·
                        rfl

theorem cell23_7773012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 4, 1, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 4, 1, 1, 4, 1, 1, 3].length) (baseStart_7773012 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7773012 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7773012 prefixEnd_7773012 := by exact prefixLift 7773012
  have htrace : WordTrace (prefixWord ++ tailWord_7773012) baseStart_7773012 baseEnd_7773012 := by
    simpa [prefixWord, tailWord_7773012, baseEnd_7773012] using wordTrace_append hprefix tailTrace_7773012
  have hstable : (prefixWord ++ tailWord_7773012).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7773012).length < 2 ^ (prefixWord ++ tailWord_7773012).sum := by decide
  have hdescent : baseEnd_7773012 < baseStart_7773012 := by decide
  rcases family_descends (prefixWord ++ tailWord_7773012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7773028 : List Nat := [2, 3, 1, 1, 4, 1, 2, 3, 2, 4]
def baseStart_7773028 : Nat := 118140960795 + 7773028 * 2 ^ 59
def prefixEnd_7773028 : Nat := 4983230072969 + 3 ^ 40 * 7773028 * 2
def baseEnd_7773028 : Nat := 1330433168285506408634167

theorem tailTrace_7773028 : CollatzResearch.WordTrace tailWord_7773028 prefixEnd_7773028 1330433168285506408634167 := by
  unfold tailWord_7773028
  simp only [CollatzResearch.WordTrace]
  refine ⟨141752811041827279168823869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 189003748055769705558431825 141752811041827279168823869)
  ·
    refine ⟨53157304140685229688308951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 141752811041827279168823869 53157304140685229688308951)
    ·
      refine ⟨79735956211027844532463427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53157304140685229688308951 79735956211027844532463427)
      ·
        refine ⟨119603934316541766798695141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79735956211027844532463427 119603934316541766798695141)
        ·
          refine ⟨22425737684351581274755339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 119603934316541766798695141 22425737684351581274755339)
          ·
            refine ⟨33638606526527371912133009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22425737684351581274755339 33638606526527371912133009)
            ·
              refine ⟨25228954894895528934099757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33638606526527371912133009 25228954894895528934099757)
              ·
                refine ⟨9460858085585823350287409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25228954894895528934099757 9460858085585823350287409)
                ·
                  refine ⟨7095643564189367512715557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9460858085585823350287409 7095643564189367512715557)
                  ·
                    refine ⟨1330433168285506408634167, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7095643564189367512715557 1330433168285506408634167)
                    ·
                      rfl

theorem cell23_7773028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 1, 2, 3, 2, 4].length) (baseStart_7773028 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7773028 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7773028 prefixEnd_7773028 := by exact prefixLift 7773028
  have htrace : WordTrace (prefixWord ++ tailWord_7773028) baseStart_7773028 baseEnd_7773028 := by
    simpa [prefixWord, tailWord_7773028, baseEnd_7773028] using wordTrace_append hprefix tailTrace_7773028
  have hstable : (prefixWord ++ tailWord_7773028).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7773028).length < 2 ^ (prefixWord ++ tailWord_7773028).sum := by decide
  have hdescent : baseEnd_7773028 < baseStart_7773028 := by decide
  rcases family_descends (prefixWord ++ tailWord_7773028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7773031 : List Nat := [1, 1, 5, 1, 2, 2, 1, 3, 1, 2, 4]
def baseStart_7773031 : Nat := 118140960795 + 7773031 * 2 ^ 59
def prefixEnd_7773031 : Nat := 4983230072969 + 3 ^ 40 * 7773031 * 2
def baseEnd_7773031 : Nat := 3991301045298482714164987

theorem tailTrace_7773031 : CollatzResearch.WordTrace tailWord_7773031 prefixEnd_7773031 3991301045298482714164987 := by
  unfold tailWord_7773031
  simp only [CollatzResearch.WordTrace]
  refine ⟨283505731502643689850006947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189003821001762459900004631 283505731502643689850006947)
  ·
    refine ⟨425258597253965534775010421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 283505731502643689850006947 425258597253965534775010421)
    ·
      refine ⟨39867993492559268885157227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 425258597253965534775010421 39867993492559268885157227)
      ·
        refine ⟨59801990238838903327735841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39867993492559268885157227 59801990238838903327735841)
        ·
          refine ⟨44851492679129177495801881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59801990238838903327735841 44851492679129177495801881)
          ·
            refine ⟨33638619509346883121851411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44851492679129177495801881 33638619509346883121851411)
            ·
              refine ⟨50457929264020324682777117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33638619509346883121851411 50457929264020324682777117)
              ·
                refine ⟨18921723474007621756041419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 50457929264020324682777117 18921723474007621756041419)
                ·
                  refine ⟨28382585211011432634062129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18921723474007621756041419 28382585211011432634062129)
                  ·
                    refine ⟨21286938908258574475546597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 28382585211011432634062129 21286938908258574475546597)
                    ·
                      refine ⟨3991301045298482714164987, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21286938908258574475546597 3991301045298482714164987)
                      ·
                        rfl

theorem cell23_7773031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 2, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 2, 1, 3, 1, 2, 4].length) (baseStart_7773031 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7773031 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7773031 prefixEnd_7773031 := by exact prefixLift 7773031
  have htrace : WordTrace (prefixWord ++ tailWord_7773031) baseStart_7773031 baseEnd_7773031 := by
    simpa [prefixWord, tailWord_7773031, baseEnd_7773031] using wordTrace_append hprefix tailTrace_7773031
  have hstable : (prefixWord ++ tailWord_7773031).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7773031).length < 2 ^ (prefixWord ++ tailWord_7773031).sum := by decide
  have hdescent : baseEnd_7773031 < baseStart_7773031 := by decide
  rcases family_descends (prefixWord ++ tailWord_7773031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7773041 : List Nat := [1, 2, 2, 2, 1, 5, 3, 7]
def baseStart_7773041 : Nat := 118140960795 + 7773041 * 2 ^ 59
def prefixEnd_7773041 : Nat := 4983230072969 + 3 ^ 40 * 7773041 * 2
def baseEnd_7773041 : Nat := 147826154818704728705183

theorem tailTrace_7773041 : CollatzResearch.WordTrace tailWord_7773041 prefixEnd_7773041 147826154818704728705183 := by
  unfold tailWord_7773041
  simp only [CollatzResearch.WordTrace]
  refine ⟨283506096232607461557870977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189004064155071641038580651 283506096232607461557870977)
  ·
    refine ⟨212629572174455596168403233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 283506096232607461557870977 212629572174455596168403233)
    ·
      refine ⟨159472179130841697126302425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 212629572174455596168403233 159472179130841697126302425)
      ·
        refine ⟨119604134348131272844726819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 159472179130841697126302425 119604134348131272844726819)
        ·
          refine ⟨179406201522196909267090229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 119604134348131272844726819 179406201522196909267090229)
          ·
            refine ⟨16819331392705960243789709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 179406201522196909267090229 16819331392705960243789709)
            ·
              refine ⟨6307249272264735091421141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16819331392705960243789709 6307249272264735091421141)
              ·
                refine ⟨147826154818704728705183, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6307249272264735091421141 147826154818704728705183)
                ·
                  rfl

theorem cell23_7773041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 5, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 5, 3, 7].length) (baseStart_7773041 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7773041 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7773041 prefixEnd_7773041 := by exact prefixLift 7773041
  have htrace : WordTrace (prefixWord ++ tailWord_7773041) baseStart_7773041 baseEnd_7773041 := by
    simpa [prefixWord, tailWord_7773041, baseEnd_7773041] using wordTrace_append hprefix tailTrace_7773041
  have hstable : (prefixWord ++ tailWord_7773041).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7773041).length < 2 ^ (prefixWord ++ tailWord_7773041).sum := by decide
  have hdescent : baseEnd_7773041 < baseStart_7773041 := by decide
  rcases family_descends (prefixWord ++ tailWord_7773041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7773051 : List Nat := [1, 1, 1, 1, 1, 5, 4, 2, 1, 3, 3]
def baseStart_7773051 : Nat := 118140960795 + 7773051 * 2 ^ 59
def prefixEnd_7773051 : Nat := 4983230072969 + 3 ^ 40 * 7773051 * 2
def baseEnd_7773051 : Nat := 3991311314911572635914895

theorem tailTrace_7773051 : CollatzResearch.WordTrace tailWord_7773051 prefixEnd_7773051 3991311314911572635914895 := by
  unfold tailWord_7773051
  simp only [CollatzResearch.WordTrace]
  refine ⟨283506460962571233265735007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189004307308380822177156671 283506460962571233265735007)
  ·
    refine ⟨425259691443856849898602511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 283506460962571233265735007 425259691443856849898602511)
    ·
      refine ⟨637889537165785274847903767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 425259691443856849898602511 637889537165785274847903767)
      ·
        refine ⟨956834305748677912271855651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 637889537165785274847903767 956834305748677912271855651)
        ·
          refine ⟨1435251458623016868407783477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 956834305748677912271855651 1435251458623016868407783477)
          ·
            refine ⟨134554824245907831413229701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 1435251458623016868407783477 134554824245907831413229701)
            ·
              refine ⟨25229029546107718389980569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 134554824245907831413229701 25229029546107718389980569)
              ·
                refine ⟨18921772159580788792485427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25229029546107718389980569 18921772159580788792485427)
                ·
                  refine ⟨28382658239371183188728141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18921772159580788792485427 28382658239371183188728141)
                  ·
                    refine ⟨10643496839764193695773053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 28382658239371183188728141 10643496839764193695773053)
                    ·
                      refine ⟨3991311314911572635914895, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10643496839764193695773053 3991311314911572635914895)
                      ·
                        rfl

theorem cell23_7773051_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 4, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 4, 2, 1, 3, 3].length) (baseStart_7773051 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7773051 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7773051 prefixEnd_7773051 := by exact prefixLift 7773051
  have htrace : WordTrace (prefixWord ++ tailWord_7773051) baseStart_7773051 baseEnd_7773051 := by
    simpa [prefixWord, tailWord_7773051, baseEnd_7773051] using wordTrace_append hprefix tailTrace_7773051
  have hstable : (prefixWord ++ tailWord_7773051).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7773051).length < 2 ^ (prefixWord ++ tailWord_7773051).sum := by decide
  have hdescent : baseEnd_7773051 < baseStart_7773051 := by decide
  rcases family_descends (prefixWord ++ tailWord_7773051) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7773131 : List Nat := [1, 1, 1, 1, 3, 5, 3, 1, 7]
def baseStart_7773131 : Nat := 118140960795 + 7773131 * 2 ^ 59
def prefixEnd_7773131 : Nat := 4983230072969 + 3 ^ 40 * 7773131 * 2
def baseEnd_7773131 : Nat := 443483599262659146990503

theorem tailTrace_7773131 : CollatzResearch.WordTrace tailWord_7773131 prefixEnd_7773131 443483599262659146990503 := by
  unfold tailWord_7773131
  simp only [CollatzResearch.WordTrace]
  refine ⟨283509378802281406928647247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189006252534854271285764831 283509378802281406928647247)
  ·
    refine ⟨425264068203422110392970871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 283509378802281406928647247 425264068203422110392970871)
    ·
      refine ⟨637896102305133165589456307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 425264068203422110392970871 637896102305133165589456307)
      ·
        refine ⟨956844153457699748384184461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 637896102305133165589456307 956844153457699748384184461)
        ·
          refine ⟨358816557546637405644069173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 956844153457699748384184461 358816557546637405644069173)
          ·
            refine ⟨33639052269997256779131485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 358816557546637405644069173 33639052269997256779131485)
            ·
              refine ⟨12614644601248971292174307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33639052269997256779131485 12614644601248971292174307)
              ·
                refine ⟨18921966901873456938261461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12614644601248971292174307 18921966901873456938261461)
                ·
                  refine ⟨443483599262659146990503, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18921966901873456938261461 443483599262659146990503)
                  ·
                    rfl

theorem cell23_7773131_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 5, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 5, 3, 1, 7].length) (baseStart_7773131 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7773131 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7773131 prefixEnd_7773131 := by exact prefixLift 7773131
  have htrace : WordTrace (prefixWord ++ tailWord_7773131) baseStart_7773131 baseEnd_7773131 := by
    simpa [prefixWord, tailWord_7773131, baseEnd_7773131] using wordTrace_append hprefix tailTrace_7773131
  have hstable : (prefixWord ++ tailWord_7773131).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7773131).length < 2 ^ (prefixWord ++ tailWord_7773131).sum := by decide
  have hdescent : baseEnd_7773131 < baseStart_7773131 := by decide
  rcases family_descends (prefixWord ++ tailWord_7773131) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7773181 : List Nat := [1, 4, 1, 1, 1, 2, 1, 2, 3, 3, 4]
def baseStart_7773181 : Nat := 118140960795 + 7773181 * 2 ^ 59
def prefixEnd_7773181 : Nat := 4983230072969 + 3 ^ 40 * 7773181 * 2
def baseEnd_7773181 : Nat := 3991378067396657127289297

theorem tailTrace_7773181 : CollatzResearch.WordTrace tailWord_7773181 prefixEnd_7773181 3991378067396657127289297 := by
  unfold tailWord_7773181
  simp only [CollatzResearch.WordTrace]
  refine ⟨283511202452100265467967397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189007468301400176978644931 283511202452100265467967397)
  ·
    refine ⟨53158350459768799775243887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 283511202452100265467967397 53158350459768799775243887)
    ·
      refine ⟨79737525689653199662865831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53158350459768799775243887 79737525689653199662865831)
      ·
        refine ⟨119606288534479799494298747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79737525689653199662865831 119606288534479799494298747)
        ·
          refine ⟨179409432801719699241448121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 119606288534479799494298747 179409432801719699241448121)
          ·
            refine ⟨134557074601289774431086091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 179409432801719699241448121 134557074601289774431086091)
            ·
              refine ⟨201835611901934661646629137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 134557074601289774431086091 201835611901934661646629137)
              ·
                refine ⟨151376708926450996234971853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 201835611901934661646629137 151376708926450996234971853)
                ·
                  refine ⟨56766265847419123588114445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 151376708926450996234971853 56766265847419123588114445)
                  ·
                    refine ⟨21287349692782171345542917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 56766265847419123588114445 21287349692782171345542917)
                    ·
                      refine ⟨3991378067396657127289297, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21287349692782171345542917 3991378067396657127289297)
                      ·
                        rfl

theorem cell23_7773181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 1, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 1, 2, 3, 3, 4].length) (baseStart_7773181 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7773181 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7773181 prefixEnd_7773181 := by exact prefixLift 7773181
  have htrace : WordTrace (prefixWord ++ tailWord_7773181) baseStart_7773181 baseEnd_7773181 := by
    simpa [prefixWord, tailWord_7773181, baseEnd_7773181] using wordTrace_append hprefix tailTrace_7773181
  have hstable : (prefixWord ++ tailWord_7773181).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7773181).length < 2 ^ (prefixWord ++ tailWord_7773181).sum := by decide
  have hdescent : baseEnd_7773181 < baseStart_7773181 := by decide
  rcases family_descends (prefixWord ++ tailWord_7773181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7773182 : List Nat := [4, 2, 2, 2, 2, 1, 1, 4, 5]
def baseStart_7773182 : Nat := 118140960795 + 7773182 * 2 ^ 59
def prefixEnd_7773182 : Nat := 4983230072969 + 3 ^ 40 * 7773182 * 2
def baseEnd_7773182 : Nat := 443486508986367958152977

theorem tailTrace_7773182 : CollatzResearch.WordTrace tailWord_7773182 prefixEnd_7773182 443486508986367958152977 := by
  unfold tailWord_7773182
  simp only [CollatzResearch.WordTrace]
  refine ⟨35438904865637080329844225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 189007492616731095092502533 35438904865637080329844225)
  ·
    refine ⟨26579178649227810247383169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35438904865637080329844225 26579178649227810247383169)
    ·
      refine ⟨19934383986920857685537377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26579178649227810247383169 19934383986920857685537377)
      ·
        refine ⟨14950787990190643264153033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19934383986920857685537377 14950787990190643264153033)
        ·
          refine ⟨11213090992642982448114775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14950787990190643264153033 11213090992642982448114775)
          ·
            refine ⟨16819636488964473672172163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11213090992642982448114775 16819636488964473672172163)
            ·
              refine ⟨25229454733446710508258245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16819636488964473672172163 25229454733446710508258245)
              ·
                refine ⟨4730522762521258220298421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25229454733446710508258245 4730522762521258220298421)
                ·
                  refine ⟨443486508986367958152977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4730522762521258220298421 443486508986367958152977)
                  ·
                    rfl

theorem cell23_7773182_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 2, 1, 1, 4, 5].length) (baseStart_7773182 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7773182 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7773182 prefixEnd_7773182 := by exact prefixLift 7773182
  have htrace : WordTrace (prefixWord ++ tailWord_7773182) baseStart_7773182 baseEnd_7773182 := by
    simpa [prefixWord, tailWord_7773182, baseEnd_7773182] using wordTrace_append hprefix tailTrace_7773182
  have hstable : (prefixWord ++ tailWord_7773182).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7773182).length < 2 ^ (prefixWord ++ tailWord_7773182).sum := by decide
  have hdescent : baseEnd_7773182 < baseStart_7773182 := by decide
  rcases family_descends (prefixWord ++ tailWord_7773182) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7773208 : List Nat := [2, 1, 2, 3, 2, 2, 1, 1, 5, 4]
def baseStart_7773208 : Nat := 118140960795 + 7773208 * 2 ^ 59
def prefixEnd_7773208 : Nat := 4983230072969 + 3 ^ 40 * 7773208 * 2
def baseEnd_7773208 : Nat := 1330463977124776173883891

theorem tailTrace_7773208 : CollatzResearch.WordTrace tailWord_7773208 prefixEnd_7773208 1330463977124776173883891 := by
  unfold tailWord_7773208
  simp only [CollatzResearch.WordTrace]
  refine ⟨141756093611501224539600139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 189008124815334966052800185 141756093611501224539600139)
  ·
    refine ⟨212634140417251836809400209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141756093611501224539600139 212634140417251836809400209)
    ·
      refine ⟨159475605312938877607050157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 212634140417251836809400209 159475605312938877607050157)
      ·
        refine ⟨59803351992352079102643809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 159475605312938877607050157 59803351992352079102643809)
        ·
          refine ⟨44852513994264059326982857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59803351992352079102643809 44852513994264059326982857)
          ·
            refine ⟨33639385495698044495237143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44852513994264059326982857 33639385495698044495237143)
            ·
              refine ⟨50459078243547066742855715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33639385495698044495237143 50459078243547066742855715)
              ·
                refine ⟨75688617365320600114283573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50459078243547066742855715 75688617365320600114283573)
                ·
                  refine ⟨7095807877998806260714085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 75688617365320600114283573 7095807877998806260714085)
                  ·
                    refine ⟨1330463977124776173883891, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7095807877998806260714085 1330463977124776173883891)
                    ·
                      rfl

theorem cell23_7773208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 2, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 2, 1, 1, 5, 4].length) (baseStart_7773208 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7773208 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7773208 prefixEnd_7773208 := by exact prefixLift 7773208
  have htrace : WordTrace (prefixWord ++ tailWord_7773208) baseStart_7773208 baseEnd_7773208 := by
    simpa [prefixWord, tailWord_7773208, baseEnd_7773208] using wordTrace_append hprefix tailTrace_7773208
  have hstable : (prefixWord ++ tailWord_7773208).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7773208).length < 2 ^ (prefixWord ++ tailWord_7773208).sum := by decide
  have hdescent : baseEnd_7773208 < baseStart_7773208 := by decide
  rcases family_descends (prefixWord ++ tailWord_7773208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7773212 : List Nat := [2, 2, 3, 1, 5, 1, 1, 1, 2, 5]
def baseStart_7773212 : Nat := 118140960795 + 7773212 * 2 ^ 59
def prefixEnd_7773212 : Nat := 4983230072969 + 3 ^ 40 * 7773212 * 2
def baseEnd_7773212 : Nat := 1330464661765648835333885

theorem tailTrace_7773212 : CollatzResearch.WordTrace tailWord_7773212 prefixEnd_7773212 1330464661765648835333885 := by
  unfold tailWord_7773212
  simp only [CollatzResearch.WordTrace]
  refine ⟨141756166557493978881172945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 189008222076658638508230593 141756166557493978881172945)
  ·
    refine ⟨106317124918120484160879709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 141756166557493978881172945 106317124918120484160879709)
    ·
      refine ⟨39868921844295181560329891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 106317124918120484160879709 39868921844295181560329891)
      ·
        refine ⟨59803382766442772340494837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39868921844295181560329891 59803382766442772340494837)
        ·
          refine ⟨5606567134354009906921391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 59803382766442772340494837 5606567134354009906921391)
          ·
            refine ⟨8409850701531014860382087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5606567134354009906921391 8409850701531014860382087)
            ·
              refine ⟨12614776052296522290573131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8409850701531014860382087 12614776052296522290573131)
              ·
                refine ⟨18922164078444783435859697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12614776052296522290573131 18922164078444783435859697)
                ·
                  refine ⟨14191623058833587576894773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18922164078444783435859697 14191623058833587576894773)
                  ·
                    refine ⟨1330464661765648835333885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14191623058833587576894773 1330464661765648835333885)
                    ·
                      rfl

theorem cell23_7773212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 5, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 5, 1, 1, 1, 2, 5].length) (baseStart_7773212 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7773212 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7773212 prefixEnd_7773212 := by exact prefixLift 7773212
  have htrace : WordTrace (prefixWord ++ tailWord_7773212) baseStart_7773212 baseEnd_7773212 := by
    simpa [prefixWord, tailWord_7773212, baseEnd_7773212] using wordTrace_append hprefix tailTrace_7773212
  have hstable : (prefixWord ++ tailWord_7773212).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7773212).length < 2 ^ (prefixWord ++ tailWord_7773212).sum := by decide
  have hdescent : baseEnd_7773212 < baseStart_7773212 := by decide
  rcases family_descends (prefixWord ++ tailWord_7773212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7773215 : List Nat := [1, 1, 2, 4, 1, 5, 1, 1, 2, 1, 4]
def baseStart_7773215 : Nat := 118140960795 + 7773215 * 2 ^ 59
def prefixEnd_7773215 : Nat := 4983230072969 + 3 ^ 40 * 7773215 * 2
def baseEnd_7773215 : Nat := 3991395525738909994264141

theorem tailTrace_7773215 : CollatzResearch.WordTrace tailWord_7773215 prefixEnd_7773215 3991395525738909994264141 := by
  unfold tailWord_7773215
  simp only [CollatzResearch.WordTrace]
  refine ⟨283512442533977089274705099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189008295022651392849803399 283512442533977089274705099)
  ·
    refine ⟨425268663800965633912057649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 283512442533977089274705099 425268663800965633912057649)
    ·
      refine ⟨318951497850724225434043237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 425268663800965633912057649 318951497850724225434043237)
      ·
        refine ⟨59803405847010792268883107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 318951497850724225434043237 59803405847010792268883107)
        ·
          refine ⟨89705108770516188403324661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59803405847010792268883107 89705108770516188403324661)
          ·
            refine ⟨8409853947235892662811687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 89705108770516188403324661 8409853947235892662811687)
            ·
              refine ⟨12614780920853838994217531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8409853947235892662811687 12614780920853838994217531)
              ·
                refine ⟨18922171381280758491326297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12614780920853838994217531 18922171381280758491326297)
                ·
                  refine ⟨14191628535960568868494723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18922171381280758491326297 14191628535960568868494723)
                  ·
                    refine ⟨21287442803940853302742085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14191628535960568868494723 21287442803940853302742085)
                    ·
                      refine ⟨3991395525738909994264141, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21287442803940853302742085 3991395525738909994264141)
                      ·
                        rfl

theorem cell23_7773215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 5, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 5, 1, 1, 2, 1, 4].length) (baseStart_7773215 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7773215 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7773215 prefixEnd_7773215 := by exact prefixLift 7773215
  have htrace : WordTrace (prefixWord ++ tailWord_7773215) baseStart_7773215 baseEnd_7773215 := by
    simpa [prefixWord, tailWord_7773215, baseEnd_7773215] using wordTrace_append hprefix tailTrace_7773215
  have hstable : (prefixWord ++ tailWord_7773215).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7773215).length < 2 ^ (prefixWord ++ tailWord_7773215).sum := by decide
  have hdescent : baseEnd_7773215 < baseStart_7773215 := by decide
  rcases family_descends (prefixWord ++ tailWord_7773215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7773221 : List Nat := [1, 3, 1, 2, 2, 2, 2, 2, 8]
def baseStart_7773221 : Nat := 118140960795 + 7773221 * 2 ^ 59
def prefixEnd_7773221 : Nat := 4983230072969 + 3 ^ 40 * 7773221 * 2
def baseEnd_7773221 : Nat := 443488734069204107865457

theorem tailTrace_7773221 : CollatzResearch.WordTrace tailWord_7773221 prefixEnd_7773221 443488734069204107865457 := by
  unfold tailWord_7773221
  simp only [CollatzResearch.WordTrace]
  refine ⟨283512661371955352299423517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189008440914636901532949011 283512661371955352299423517)
  ·
    refine ⟨106317248014483257112283819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 283512661371955352299423517 106317248014483257112283819)
    ·
      refine ⟨159475872021724885668425729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106317248014483257112283819 159475872021724885668425729)
      ·
        refine ⟨119606904016293664251319297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 159475872021724885668425729 119606904016293664251319297)
        ·
          refine ⟨89705178012220248188489473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 119606904016293664251319297 89705178012220248188489473)
          ·
            refine ⟨67278883509165186141367105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 89705178012220248188489473 67278883509165186141367105)
            ·
              refine ⟨50459162631873889606025329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 67278883509165186141367105 50459162631873889606025329)
              ·
                refine ⟨37844371973905417204518997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50459162631873889606025329 37844371973905417204518997)
                ·
                  refine ⟨443488734069204107865457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 37844371973905417204518997 443488734069204107865457)
                  ·
                    rfl

theorem cell23_7773221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 2, 2, 8].length) (baseStart_7773221 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7773221 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7773221 prefixEnd_7773221 := by exact prefixLift 7773221
  have htrace : WordTrace (prefixWord ++ tailWord_7773221) baseStart_7773221 baseEnd_7773221 := by
    simpa [prefixWord, tailWord_7773221, baseEnd_7773221] using wordTrace_append hprefix tailTrace_7773221
  have hstable : (prefixWord ++ tailWord_7773221).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7773221).length < 2 ^ (prefixWord ++ tailWord_7773221).sum := by decide
  have hdescent : baseEnd_7773221 < baseStart_7773221 := by decide
  rcases family_descends (prefixWord ++ tailWord_7773221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7773255 : List Nat := [1, 1, 4, 1, 3, 3, 3, 1, 6]
def baseStart_7773255 : Nat := 118140960795 + 7773255 * 2 ^ 59
def prefixEnd_7773255 : Nat := 4983230072969 + 3 ^ 40 * 7773255 * 2
def baseEnd_7773255 : Nat := 443490673885009981973773

theorem tailTrace_7773255 : CollatzResearch.WordTrace tailWord_7773255 prefixEnd_7773255 443490673885009981973773 := by
  unfold tailWord_7773255
  simp only [CollatzResearch.WordTrace]
  refine ⟨283513901453832176106161219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189009267635888117404107479 283513901453832176106161219)
  ·
    refine ⟨425270852180748264159241829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 283513901453832176106161219 425270852180748264159241829)
    ·
      refine ⟨79738284783890299529857843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 425270852180748264159241829 79738284783890299529857843)
      ·
        refine ⟨119607427175835449294786765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79738284783890299529857843 119607427175835449294786765)
        ·
          refine ⟨44852785190938293485545037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 119607427175835449294786765 44852785190938293485545037)
          ·
            refine ⟨16819794446601860057079389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 44852785190938293485545037 16819794446601860057079389)
            ·
              refine ⟨6307422917475697521404771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16819794446601860057079389 6307422917475697521404771)
              ·
                refine ⟨9461134376213546282107157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6307422917475697521404771 9461134376213546282107157)
                ·
                  refine ⟨443490673885009981973773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9461134376213546282107157 443490673885009981973773)
                  ·
                    rfl

theorem cell23_7773255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 3, 3, 1, 6].length) (baseStart_7773255 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7773255 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7773255 prefixEnd_7773255 := by exact prefixLift 7773255
  have htrace : WordTrace (prefixWord ++ tailWord_7773255) baseStart_7773255 baseEnd_7773255 := by
    simpa [prefixWord, tailWord_7773255, baseEnd_7773255] using wordTrace_append hprefix tailTrace_7773255
  have hstable : (prefixWord ++ tailWord_7773255).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7773255).length < 2 ^ (prefixWord ++ tailWord_7773255).sum := by decide
  have hdescent : baseEnd_7773255 < baseStart_7773255 := by decide
  rcases family_descends (prefixWord ++ tailWord_7773255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7773265 : List Nat := [1, 2, 2, 1, 3, 1, 4, 2, 3, 1, 3]
def baseStart_7773265 : Nat := 118140960795 + 7773265 * 2 ^ 59
def prefixEnd_7773265 : Nat := 4983230072969 + 3 ^ 40 * 7773265 * 2
def baseEnd_7773265 : Nat := 3991421199771634798638911

theorem tailTrace_7773265 : CollatzResearch.WordTrace tailWord_7773265 prefixEnd_7773265 3991421199771634798638911 := by
  unfold tailWord_7773265
  simp only [CollatzResearch.WordTrace]
  refine ⟨283514266183795947814025249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189009510789197298542683499 283514266183795947814025249)
  ·
    refine ⟨212635699637846960860518937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 283514266183795947814025249 212635699637846960860518937)
    ·
      refine ⟨159476774728385220645389203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 212635699637846960860518937 159476774728385220645389203)
      ·
        refine ⟨239215162092577830968083805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 159476774728385220645389203 239215162092577830968083805)
        ·
          refine ⟨89705685784716686613031427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 239215162092577830968083805 89705685784716686613031427)
          ·
            refine ⟨134558528677075029919547141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89705685784716686613031427 134558528677075029919547141)
            ·
              refine ⟨25229724126951568109915089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 134558528677075029919547141 25229724126951568109915089)
              ·
                refine ⟨18922293095213676082436317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25229724126951568109915089 18922293095213676082436317)
                ·
                  refine ⟨7095859910705128530913619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18922293095213676082436317 7095859910705128530913619)
                  ·
                    refine ⟨10643789866057692796370429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7095859910705128530913619 10643789866057692796370429)
                    ·
                      refine ⟨3991421199771634798638911, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10643789866057692796370429 3991421199771634798638911)
                      ·
                        rfl

theorem cell23_7773265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 4, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 4, 2, 3, 1, 3].length) (baseStart_7773265 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7773265 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7773265 prefixEnd_7773265 := by exact prefixLift 7773265
  have htrace : WordTrace (prefixWord ++ tailWord_7773265) baseStart_7773265 baseEnd_7773265 := by
    simpa [prefixWord, tailWord_7773265, baseEnd_7773265] using wordTrace_append hprefix tailTrace_7773265
  have hstable : (prefixWord ++ tailWord_7773265).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7773265).length < 2 ^ (prefixWord ++ tailWord_7773265).sum := by decide
  have hdescent : baseEnd_7773265 < baseStart_7773265 := by decide
  rcases family_descends (prefixWord ++ tailWord_7773265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7773268 : List Nat := [2, 4, 1, 1, 1, 1, 2, 3, 3, 5]
def baseStart_7773268 : Nat := 118140960795 + 7773268 * 2 ^ 59
def prefixEnd_7773268 : Nat := 4983230072969 + 3 ^ 40 * 7773268 * 2
def baseEnd_7773268 : Nat := 1330474246737866095633799

theorem tailTrace_7773268 : CollatzResearch.WordTrace tailWord_7773268 prefixEnd_7773268 1330474246737866095633799 := by
  unfold tailWord_7773268
  simp only [CollatzResearch.WordTrace]
  refine ⟨141757187801392539663192229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 189009583735190052884256305 141757187801392539663192229)
  ·
    refine ⟨26579472712761101186848543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 141757187801392539663192229 26579472712761101186848543)
    ·
      refine ⟨39869209069141651780272815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26579472712761101186848543 39869209069141651780272815)
      ·
        refine ⟨59803813603712477670409223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39869209069141651780272815 59803813603712477670409223)
        ·
          refine ⟨89705720405568716505613835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59803813603712477670409223 89705720405568716505613835)
          ·
            refine ⟨134558580608353074758420753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89705720405568716505613835 134558580608353074758420753)
            ·
              refine ⟨100918935456264806068815565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 134558580608353074758420753 100918935456264806068815565)
              ·
                refine ⟨37844600796099302275805837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 100918935456264806068815565 37844600796099302275805837)
                ·
                  refine ⟨14191725298537238353427189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 37844600796099302275805837 14191725298537238353427189)
                  ·
                    refine ⟨1330474246737866095633799, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14191725298537238353427189 1330474246737866095633799)
                    ·
                      rfl

theorem cell23_7773268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 2, 3, 3, 5].length) (baseStart_7773268 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7773268 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7773268 prefixEnd_7773268 := by exact prefixLift 7773268
  have htrace : WordTrace (prefixWord ++ tailWord_7773268) baseStart_7773268 baseEnd_7773268 := by
    simpa [prefixWord, tailWord_7773268, baseEnd_7773268] using wordTrace_append hprefix tailTrace_7773268
  have hstable : (prefixWord ++ tailWord_7773268).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7773268).length < 2 ^ (prefixWord ++ tailWord_7773268).sum := by decide
  have hdescent : baseEnd_7773268 < baseStart_7773268 := by decide
  rcases family_descends (prefixWord ++ tailWord_7773268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7773308 : List Nat := [2, 2, 2, 1, 1, 3, 1, 4, 1, 1, 5]
def baseStart_7773308 : Nat := 118140960795 + 7773308 * 2 ^ 59
def prefixEnd_7773308 : Nat := 4983230072969 + 3 ^ 40 * 7773308 * 2
def baseEnd_7773308 : Nat := 3991443279439778130401213

theorem tailTrace_7773308 : CollatzResearch.WordTrace tailWord_7773308 prefixEnd_7773308 3991443279439778130401213 := by
  unfold tailWord_7773308
  simp only [CollatzResearch.WordTrace]
  refine ⟨141757917261320083078920289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 189010556348426777438560385 141757917261320083078920289)
  ·
    refine ⟨106318437945990062309190217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 141757917261320083078920289 106318437945990062309190217)
    ·
      refine ⟨79738828459492546731892663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 106318437945990062309190217 79738828459492546731892663)
      ·
        refine ⟨119608242689238820097838995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79738828459492546731892663 119608242689238820097838995)
        ·
          refine ⟨179412364033858230146758493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 119608242689238820097838995 179412364033858230146758493)
          ·
            refine ⟨67279636512696836305034435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 179412364033858230146758493 67279636512696836305034435)
            ·
              refine ⟨100919454769045254457551653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67279636512696836305034435 100919454769045254457551653)
              ·
                refine ⟨18922397769195985210790935, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 100919454769045254457551653 18922397769195985210790935)
                ·
                  refine ⟨28383596653793977816186403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18922397769195985210790935 28383596653793977816186403)
                  ·
                    refine ⟨42575394980690966724279605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 28383596653793977816186403 42575394980690966724279605)
                    ·
                      refine ⟨3991443279439778130401213, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 42575394980690966724279605 3991443279439778130401213)
                      ·
                        rfl

theorem cell23_7773308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 1, 4, 1, 1, 5].length) (baseStart_7773308 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7773308 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7773308 prefixEnd_7773308 := by exact prefixLift 7773308
  have htrace : WordTrace (prefixWord ++ tailWord_7773308) baseStart_7773308 baseEnd_7773308 := by
    simpa [prefixWord, tailWord_7773308, baseEnd_7773308] using wordTrace_append hprefix tailTrace_7773308
  have hstable : (prefixWord ++ tailWord_7773308).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7773308).length < 2 ^ (prefixWord ++ tailWord_7773308).sum := by decide
  have hdescent : baseEnd_7773308 < baseStart_7773308 := by decide
  rcases family_descends (prefixWord ++ tailWord_7773308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7773315 : List Nat := [1, 1, 1, 3, 3, 2, 3, 3, 2, 4]
def baseStart_7773315 : Nat := 118140960795 + 7773315 * 2 ^ 59
def prefixEnd_7773315 : Nat := 4983230072969 + 3 ^ 40 * 7773315 * 2
def baseEnd_7773315 : Nat := 1330482291268119867671227

theorem tailTrace_7773315 : CollatzResearch.WordTrace tailWord_7773315 prefixEnd_7773315 1330482291268119867671227 := by
  unfold tailWord_7773315
  simp only [CollatzResearch.WordTrace]
  refine ⟨283516089833614806353345399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189010726555743204235563599 283516089833614806353345399)
  ·
    refine ⟨425274134750422209530018099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 283516089833614806353345399 425274134750422209530018099)
    ·
      refine ⟨637911202125633314295027149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 425274134750422209530018099 637911202125633314295027149)
      ·
        refine ⟨239216700797112492860635181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 637911202125633314295027149 239216700797112492860635181)
        ·
          refine ⟨89706262798917184822738193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 239216700797112492860635181 89706262798917184822738193)
          ·
            refine ⟨67279697099187888617053645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 89706262798917184822738193 67279697099187888617053645)
            ·
              refine ⟨25229886412195458231395117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 67279697099187888617053645 25229886412195458231395117)
              ·
                refine ⟨9461207404573296836773169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25229886412195458231395117 9461207404573296836773169)
                ·
                  refine ⟨7095905553429972627579877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9461207404573296836773169 7095905553429972627579877)
                  ·
                    refine ⟨1330482291268119867671227, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7095905553429972627579877 1330482291268119867671227)
                    ·
                      rfl

theorem cell23_7773315_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 3, 3, 2, 4].length) (baseStart_7773315 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7773315 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7773315 prefixEnd_7773315 := by exact prefixLift 7773315
  have htrace : WordTrace (prefixWord ++ tailWord_7773315) baseStart_7773315 baseEnd_7773315 := by
    simpa [prefixWord, tailWord_7773315, baseEnd_7773315] using wordTrace_append hprefix tailTrace_7773315
  have hstable : (prefixWord ++ tailWord_7773315).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7773315).length < 2 ^ (prefixWord ++ tailWord_7773315).sum := by decide
  have hdescent : baseEnd_7773315 < baseStart_7773315 := by decide
  rcases family_descends (prefixWord ++ tailWord_7773315) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7773322 : List Nat := [3, 1, 2, 3, 1, 1, 2, 1, 5, 2, 2]
def baseStart_7773322 : Nat := 118140960795 + 7773322 * 2 ^ 59
def prefixEnd_7773322 : Nat := 4983230072969 + 3 ^ 40 * 7773322 * 2
def baseEnd_7773322 : Nat := 3991450468168941075626149

theorem tailTrace_7773322 : CollatzResearch.WordTrace tailWord_7773322 prefixEnd_7773322 3991450468168941075626149 := by
  unfold tailWord_7773322
  simp only [CollatzResearch.WordTrace]
  refine ⟨70879086286147361637212555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 189010896763059631032566813 70879086286147361637212555)
  ·
    refine ⟨106318629429221042455818833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70879086286147361637212555 106318629429221042455818833)
    ·
      refine ⟨79738972071915781841864125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 106318629429221042455818833 79738972071915781841864125)
      ·
        refine ⟨29902114526968418190699047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 79738972071915781841864125 29902114526968418190699047)
        ·
          refine ⟨44853171790452627286048571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29902114526968418190699047 44853171790452627286048571)
          ·
            refine ⟨67279757685678940929072857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44853171790452627286048571 67279757685678940929072857)
            ·
              refine ⟨50459818264259205696804643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 67279757685678940929072857 50459818264259205696804643)
              ·
                refine ⟨75689727396388808545206965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50459818264259205696804643 75689727396388808545206965)
                ·
                  refine ⟨7095911943411450801113153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 75689727396388808545206965 7095911943411450801113153)
                  ·
                    refine ⟨5321933957558588100834865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7095911943411450801113153 5321933957558588100834865)
                    ·
                      refine ⟨3991450468168941075626149, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5321933957558588100834865 3991450468168941075626149)
                      ·
                        rfl

theorem cell23_7773322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 2, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 2, 1, 5, 2, 2].length) (baseStart_7773322 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7773322 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7773322 prefixEnd_7773322 := by exact prefixLift 7773322
  have htrace : WordTrace (prefixWord ++ tailWord_7773322) baseStart_7773322 baseEnd_7773322 := by
    simpa [prefixWord, tailWord_7773322, baseEnd_7773322] using wordTrace_append hprefix tailTrace_7773322
  have hstable : (prefixWord ++ tailWord_7773322).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7773322).length < 2 ^ (prefixWord ++ tailWord_7773322).sum := by decide
  have hdescent : baseEnd_7773322 < baseStart_7773322 := by decide
  rcases family_descends (prefixWord ++ tailWord_7773322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7773335 : List Nat := [1, 1, 3, 3, 3, 2, 1, 2, 1, 2, 4]
def baseStart_7773335 : Nat := 118140960795 + 7773335 * 2 ^ 59
def prefixEnd_7773335 : Nat := 4983230072969 + 3 ^ 40 * 7773335 * 2
def baseEnd_7773335 : Nat := 3991457143417449524763589

theorem tailTrace_7773335 : CollatzResearch.WordTrace tailWord_7773335 prefixEnd_7773335 3991457143417449524763589 := by
  unfold tailWord_7773335
  simp only [CollatzResearch.WordTrace]
  refine ⟨283516819293542349769073459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189011212862361566512715639 283516819293542349769073459)
  ·
    refine ⟨425275228940313524653610189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 283516819293542349769073459 425275228940313524653610189)
    ·
      refine ⟨159478210852617571745103821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 425275228940313524653610189 159478210852617571745103821)
      ·
        refine ⟨59804329069731589404413933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 159478210852617571745103821 59804329069731589404413933)
        ·
          refine ⟨22426623401149346026655225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 59804329069731589404413933 22426623401149346026655225)
          ·
            refine ⟨16819967550862009519991419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22426623401149346026655225 16819967550862009519991419)
            ·
              refine ⟨25229951326293014279987129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16819967550862009519991419 25229951326293014279987129)
              ·
                refine ⟨18922463494719760709990347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25229951326293014279987129 18922463494719760709990347)
                ·
                  refine ⟨28383695242079641064985521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18922463494719760709990347 28383695242079641064985521)
                  ·
                    refine ⟨21287771431559730798739141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 28383695242079641064985521 21287771431559730798739141)
                    ·
                      refine ⟨3991457143417449524763589, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21287771431559730798739141 3991457143417449524763589)
                      ·
                        rfl

theorem cell23_7773335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 2, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 2, 1, 2, 1, 2, 4].length) (baseStart_7773335 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7773335 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7773335 prefixEnd_7773335 := by exact prefixLift 7773335
  have htrace : WordTrace (prefixWord ++ tailWord_7773335) baseStart_7773335 baseEnd_7773335 := by
    simpa [prefixWord, tailWord_7773335, baseEnd_7773335] using wordTrace_append hprefix tailTrace_7773335
  have hstable : (prefixWord ++ tailWord_7773335).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7773335).length < 2 ^ (prefixWord ++ tailWord_7773335).sum := by decide
  have hdescent : baseEnd_7773335 < baseStart_7773335 := by decide
  rcases family_descends (prefixWord ++ tailWord_7773335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7773342 : List Nat := [4, 3, 1, 1, 2, 1, 3, 1, 1, 1, 5]
def baseStart_7773342 : Nat := 118140960795 + 7773342 * 2 ^ 59
def prefixEnd_7773342 : Nat := 4983230072969 + 3 ^ 40 * 7773342 * 2
def baseEnd_7773342 : Nat := 3991460737782030997376057

theorem tailTrace_7773342 : CollatzResearch.WordTrace tailWord_7773342 prefixEnd_7773342 3991460737782030997376057 := by
  unfold tailWord_7773342
  simp only [CollatzResearch.WordTrace]
  refine ⟨35439634325564623745572285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 189011383069677993309718853 35439634325564623745572285)
  ·
    refine ⟨13289862872086733904589607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35439634325564623745572285 13289862872086733904589607)
    ·
      refine ⟨19934794308130100856884411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13289862872086733904589607 19934794308130100856884411)
      ·
        refine ⟨29902191462195151285326617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19934794308130100856884411 29902191462195151285326617)
        ·
          refine ⟨22426643596646363463994963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29902191462195151285326617 22426643596646363463994963)
          ·
            refine ⟨33639965394969545195992445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22426643596646363463994963 33639965394969545195992445)
            ·
              refine ⟨12614987023113579448497167, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33639965394969545195992445 12614987023113579448497167)
              ·
                refine ⟨18922480534670369172745751, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12614987023113579448497167 18922480534670369172745751)
                ·
                  refine ⟨28383720802005553759118627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18922480534670369172745751 28383720802005553759118627)
                  ·
                    refine ⟨42575581203008330638677941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 28383720802005553759118627 42575581203008330638677941)
                    ·
                      refine ⟨3991460737782030997376057, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 42575581203008330638677941 3991460737782030997376057)
                      ·
                        rfl

theorem cell23_7773342_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 1, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 1, 3, 1, 1, 1, 5].length) (baseStart_7773342 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7773342 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7773342 prefixEnd_7773342 := by exact prefixLift 7773342
  have htrace : WordTrace (prefixWord ++ tailWord_7773342) baseStart_7773342 baseEnd_7773342 := by
    simpa [prefixWord, tailWord_7773342, baseEnd_7773342] using wordTrace_append hprefix tailTrace_7773342
  have hstable : (prefixWord ++ tailWord_7773342).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7773342).length < 2 ^ (prefixWord ++ tailWord_7773342).sum := by decide
  have hdescent : baseEnd_7773342 < baseStart_7773342 := by decide
  rcases family_descends (prefixWord ++ tailWord_7773342) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7773372 : List Nat := [2, 2, 2, 3, 2, 2, 2, 1, 1, 3, 3]
def baseStart_7773372 : Nat := 118140960795 + 7773372 * 2 ^ 59
def prefixEnd_7773372 : Nat := 4983230072969 + 3 ^ 40 * 7773372 * 2
def baseEnd_7773372 : Nat := 3991476142201665880000919

theorem tailTrace_7773372 : CollatzResearch.WordTrace tailWord_7773372 prefixEnd_7773372 3991476142201665880000919 := by
  unfold tailWord_7773372
  simp only [CollatzResearch.WordTrace]
  refine ⟨141759084397204152544085185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 189012112529605536725446913 141759084397204152544085185)
  ·
    refine ⟨106319313297903114408063889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 141759084397204152544085185 106319313297903114408063889)
    ·
      refine ⟨79739484973427335806047917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 106319313297903114408063889 79739484973427335806047917)
      ·
        refine ⟨29902306865035250927267969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 79739484973427335806047917 29902306865035250927267969)
        ·
          refine ⟨22426730148776438195450977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29902306865035250927267969 22426730148776438195450977)
          ·
            refine ⟨16820047611582328646588233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22426730148776438195450977 16820047611582328646588233)
            ·
              refine ⟨12615035708686746484941175, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16820047611582328646588233 12615035708686746484941175)
              ·
                refine ⟨18922553563030119727411763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12615035708686746484941175 18922553563030119727411763)
                ·
                  refine ⟨28383830344545179591117645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18922553563030119727411763 28383830344545179591117645)
                  ·
                    refine ⟨10643936379204442346669117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 28383830344545179591117645 10643936379204442346669117)
                    ·
                      refine ⟨3991476142201665880000919, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10643936379204442346669117 3991476142201665880000919)
                      ·
                        rfl

theorem cell23_7773372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 2, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 2, 2, 1, 1, 3, 3].length) (baseStart_7773372 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7773372 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7773372 prefixEnd_7773372 := by exact prefixLift 7773372
  have htrace : WordTrace (prefixWord ++ tailWord_7773372) baseStart_7773372 baseEnd_7773372 := by
    simpa [prefixWord, tailWord_7773372, baseEnd_7773372] using wordTrace_append hprefix tailTrace_7773372
  have hstable : (prefixWord ++ tailWord_7773372).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7773372).length < 2 ^ (prefixWord ++ tailWord_7773372).sum := by decide
  have hdescent : baseEnd_7773372 < baseStart_7773372 := by decide
  rcases family_descends (prefixWord ++ tailWord_7773372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7773399 : List Nat := [1, 1, 3, 2, 1, 2, 6, 1, 1, 3, 2]
def baseStart_7773399 : Nat := 118140960795 + 7773399 * 2 ^ 59
def prefixEnd_7773399 : Nat := 4983230072969 + 3 ^ 40 * 7773399 * 2
def baseEnd_7773399 : Nat := 3991490006179337274363295

theorem tailTrace_7773399 : CollatzResearch.WordTrace tailWord_7773399 prefixEnd_7773399 3991490006179337274363295 := by
  unfold tailWord_7773399
  simp only [CollatzResearch.WordTrace]
  refine ⟨283519153565310488699403251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189012769043540325799602167 283519153565310488699403251)
  ·
    refine ⟨425278730347965733049104877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 283519153565310488699403251 425278730347965733049104877)
    ·
      refine ⟨159479523880487149893414329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 425278730347965733049104877 159479523880487149893414329)
      ·
        refine ⟨119609642910365362420060747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 159479523880487149893414329 119609642910365362420060747)
        ·
          refine ⟨179414464365548043630091121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 119609642910365362420060747 179414464365548043630091121)
          ·
            refine ⟨134560848274161032722568341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 179414464365548043630091121 134560848274161032722568341)
            ·
              refine ⟨6307539762851298408870391, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 134560848274161032722568341 6307539762851298408870391)
              ·
                refine ⟨9461309644276947613305587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6307539762851298408870391 9461309644276947613305587)
                ·
                  refine ⟨14191964466415421419958381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9461309644276947613305587 14191964466415421419958381)
                  ·
                    refine ⟨5321986674905783032484393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14191964466415421419958381 5321986674905783032484393)
                    ·
                      refine ⟨3991490006179337274363295, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5321986674905783032484393 3991490006179337274363295)
                      ·
                        rfl

theorem cell23_7773399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 6, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 6, 1, 1, 3, 2].length) (baseStart_7773399 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7773399 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7773399 prefixEnd_7773399 := by exact prefixLift 7773399
  have htrace : WordTrace (prefixWord ++ tailWord_7773399) baseStart_7773399 baseEnd_7773399 := by
    simpa [prefixWord, tailWord_7773399, baseEnd_7773399] using wordTrace_append hprefix tailTrace_7773399
  have hstable : (prefixWord ++ tailWord_7773399).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7773399).length < 2 ^ (prefixWord ++ tailWord_7773399).sum := by decide
  have hdescent : baseEnd_7773399 < baseStart_7773399 := by decide
  rcases family_descends (prefixWord ++ tailWord_7773399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7773452 : List Nat := [2, 2, 1, 2, 2, 3, 3, 3, 5]
def baseStart_7773452 : Nat := 118140960795 + 7773452 * 2 ^ 59
def prefixEnd_7773452 : Nat := 4983230072969 + 3 ^ 40 * 7773452 * 2
def baseEnd_7773452 : Nat := 443501913406002840777839

theorem tailTrace_7773452 : CollatzResearch.WordTrace tailWord_7773452 prefixEnd_7773452 443501913406002840777839 := by
  unfold tailWord_7773452
  simp only [CollatzResearch.WordTrace]
  refine ⟨141760543317059239375541305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 189014057756078985834055073 141760543317059239375541305)
  ·
    refine ⟨106320407487794429531655979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 141760543317059239375541305 106320407487794429531655979)
    ·
      refine ⟨159480611231691644297483969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106320407487794429531655979 159480611231691644297483969)
      ·
        refine ⟨119610458423768733223112977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 159480611231691644297483969 119610458423768733223112977)
        ·
          refine ⟨89707843817826549917334733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 119610458423768733223112977 89707843817826549917334733)
          ·
            refine ⟨33640441431684956219000525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 89707843817826549917334733 33640441431684956219000525)
            ·
              refine ⟨12615165536881858582125197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33640441431684956219000525 12615165536881858582125197)
              ·
                refine ⟨4730687076330696968296949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12615165536881858582125197 4730687076330696968296949)
                ·
                  refine ⟨443501913406002840777839, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4730687076330696968296949 443501913406002840777839)
                  ·
                    rfl

theorem cell23_7773452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 3, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 3, 3, 3, 5].length) (baseStart_7773452 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7773452 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7773452 prefixEnd_7773452 := by exact prefixLift 7773452
  have htrace : WordTrace (prefixWord ++ tailWord_7773452) baseStart_7773452 baseEnd_7773452 := by
    simpa [prefixWord, tailWord_7773452, baseEnd_7773452] using wordTrace_append hprefix tailTrace_7773452
  have hstable : (prefixWord ++ tailWord_7773452).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7773452).length < 2 ^ (prefixWord ++ tailWord_7773452).sum := by decide
  have hdescent : baseEnd_7773452 < baseStart_7773452 := by decide
  rcases family_descends (prefixWord ++ tailWord_7773452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7773455 : List Nat := [1, 1, 2, 1, 1, 1, 3, 1, 3, 7, 2]
def baseStart_7773455 : Nat := 118140960795 + 7773455 * 2 ^ 59
def prefixEnd_7773455 : Nat := 4983230072969 + 3 ^ 40 * 7773455 * 2
def baseEnd_7773455 : Nat := 3991518761095989055263037

theorem tailTrace_7773455 : CollatzResearch.WordTrace tailWord_7773455 prefixEnd_7773455 3991518761095989055263037 := by
  unfold tailWord_7773455
  simp only [CollatzResearch.WordTrace]
  refine ⟨283521196053107610263441819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189014130702071740175627879 283521196053107610263441819)
  ·
    refine ⟨425281794079661415395162729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 283521196053107610263441819 425281794079661415395162729)
    ·
      refine ⟨318961345559746061546372047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 425281794079661415395162729 318961345559746061546372047)
      ·
        refine ⟨478442018339619092319558071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 318961345559746061546372047 478442018339619092319558071)
        ·
          refine ⟨717663027509428638479337107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 478442018339619092319558071 717663027509428638479337107)
          ·
            refine ⟨1076494541264142957719005661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 717663027509428638479337107 1076494541264142957719005661)
            ·
              refine ⟨403685452974053609144627123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1076494541264142957719005661 403685452974053609144627123)
              ·
                refine ⟨605528179461080413716940685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 403685452974053609144627123 605528179461080413716940685)
                ·
                  refine ⟨227073067297905155143852757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 605528179461080413716940685 227073067297905155143852757)
                  ·
                    refine ⟨5322025014794652073684049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 227073067297905155143852757 5322025014794652073684049)
                    ·
                      refine ⟨3991518761095989055263037, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5322025014794652073684049 3991518761095989055263037)
                      ·
                        rfl

theorem cell23_7773455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 3, 1, 3, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 3, 1, 3, 7, 2].length) (baseStart_7773455 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7773455 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7773455 prefixEnd_7773455 := by exact prefixLift 7773455
  have htrace : WordTrace (prefixWord ++ tailWord_7773455) baseStart_7773455 baseEnd_7773455 := by
    simpa [prefixWord, tailWord_7773455, baseEnd_7773455] using wordTrace_append hprefix tailTrace_7773455
  have hstable : (prefixWord ++ tailWord_7773455).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7773455).length < 2 ^ (prefixWord ++ tailWord_7773455).sum := by decide
  have hdescent : baseEnd_7773455 < baseStart_7773455 := by decide
  rcases family_descends (prefixWord ++ tailWord_7773455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7773475 : List Nat := [1, 1, 1, 4, 2, 4, 1, 1, 1, 2, 5]
def baseStart_7773475 : Nat := 118140960795 + 7773475 * 2 ^ 59
def prefixEnd_7773475 : Nat := 4983230072969 + 3 ^ 40 * 7773475 * 2
def baseEnd_7773475 : Nat := 3991529030709078977012945

theorem tailTrace_7773475 : CollatzResearch.WordTrace tailWord_7773475 prefixEnd_7773475 3991529030709078977012945 := by
  unfold tailWord_7773475
  simp only [CollatzResearch.WordTrace]
  refine ⟨283521925513035153679169879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189014617008690102452779919 283521925513035153679169879)
  ·
    refine ⟨425282888269552730518754819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 283521925513035153679169879 425282888269552730518754819)
    ·
      refine ⟨637924332404329095778132229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 425282888269552730518754819 637924332404329095778132229)
      ·
        refine ⟨119610812325811705458399793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 637924332404329095778132229 119610812325811705458399793)
        ·
          refine ⟨89708109244358779093799845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 119610812325811705458399793 89708109244358779093799845)
          ·
            refine ⟨16820270483317271080087471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 89708109244358779093799845 16820270483317271080087471)
            ·
              refine ⟨25230405724975906620131207, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16820270483317271080087471 25230405724975906620131207)
              ·
                refine ⟨37845608587463859930196811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25230405724975906620131207 37845608587463859930196811)
                ·
                  refine ⟨56768412881195789895295217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37845608587463859930196811 56768412881195789895295217)
                  ·
                    refine ⟨42576309660896842421471413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 56768412881195789895295217 42576309660896842421471413)
                    ·
                      refine ⟨3991529030709078977012945, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 42576309660896842421471413 3991529030709078977012945)
                      ·
                        rfl

theorem cell23_7773475_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 4, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 4, 1, 1, 1, 2, 5].length) (baseStart_7773475 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7773475 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7773475 prefixEnd_7773475 := by exact prefixLift 7773475
  have htrace : WordTrace (prefixWord ++ tailWord_7773475) baseStart_7773475 baseEnd_7773475 := by
    simpa [prefixWord, tailWord_7773475, baseEnd_7773475] using wordTrace_append hprefix tailTrace_7773475
  have hstable : (prefixWord ++ tailWord_7773475).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7773475).length < 2 ^ (prefixWord ++ tailWord_7773475).sum := by decide
  have hdescent : baseEnd_7773475 < baseStart_7773475 := by decide
  rcases family_descends (prefixWord ++ tailWord_7773475) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7773535 : List Nat := [1, 1, 2, 3, 1, 2, 1, 2, 2, 5, 3]
def baseStart_7773535 : Nat := 118140960795 + 7773535 * 2 ^ 59
def prefixEnd_7773535 : Nat := 4983230072969 + 3 ^ 40 * 7773535 * 2
def baseEnd_7773535 : Nat := 3991559839548348742262669

theorem tailTrace_7773535 : CollatzResearch.WordTrace tailWord_7773535 prefixEnd_7773535 3991559839548348742262669 := by
  unfold tailWord_7773535
  simp only [CollatzResearch.WordTrace]
  refine ⟨283524113892817783926354059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189016075928545189284236039 283524113892817783926354059)
  ·
    refine ⟨425286170839226675889531089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 283524113892817783926354059 425286170839226675889531089)
    ·
      refine ⟨318964628129420006917148317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 425286170839226675889531089 318964628129420006917148317)
      ·
        refine ⟨119611735548532502593930619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 318964628129420006917148317 119611735548532502593930619)
        ·
          refine ⟨179417603322798753890895929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 119611735548532502593930619 179417603322798753890895929)
          ·
            refine ⟨134563202492099065418171947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 179417603322798753890895929 134563202492099065418171947)
            ·
              refine ⟨201844803738148598127257921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 134563202492099065418171947 201844803738148598127257921)
              ·
                refine ⟨151383602803611448595443441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 201844803738148598127257921 151383602803611448595443441)
                ·
                  refine ⟨113537702102708586446582581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 151383602803611448595443441 113537702102708586446582581)
                  ·
                    refine ⟨10644159572128929979367117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 113537702102708586446582581 10644159572128929979367117)
                    ·
                      refine ⟨3991559839548348742262669, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10644159572128929979367117 3991559839548348742262669)
                      ·
                        rfl

theorem cell23_7773535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 1, 2, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 1, 2, 2, 5, 3].length) (baseStart_7773535 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7773535 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7773535 prefixEnd_7773535 := by exact prefixLift 7773535
  have htrace : WordTrace (prefixWord ++ tailWord_7773535) baseStart_7773535 baseEnd_7773535 := by
    simpa [prefixWord, tailWord_7773535, baseEnd_7773535] using wordTrace_append hprefix tailTrace_7773535
  have hstable : (prefixWord ++ tailWord_7773535).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7773535).length < 2 ^ (prefixWord ++ tailWord_7773535).sum := by decide
  have hdescent : baseEnd_7773535 < baseStart_7773535 := by decide
  rcases family_descends (prefixWord ++ tailWord_7773535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7773562 : List Nat := [3, 1, 1, 1, 1, 1, 2, 5, 1, 5, 2]
def baseStart_7773562 : Nat := 118140960795 + 7773562 * 2 ^ 59
def prefixEnd_7773562 : Nat := 4983230072969 + 3 ^ 40 * 7773562 * 2
def baseEnd_7773562 : Nat := 3991573703526020136625045

theorem tailTrace_7773562 : CollatzResearch.WordTrace tailWord_7773562 prefixEnd_7773562 3991573703526020136625045 := by
  unfold tailWord_7773562
  simp only [CollatzResearch.WordTrace]
  refine ⟨70881274665929991884396735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 189016732442479978358391293 70881274665929991884396735)
  ·
    refine ⟨106321911998894987826595103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70881274665929991884396735 106321911998894987826595103)
    ·
      refine ⟨159482867998342481739892655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106321911998894987826595103 159482867998342481739892655)
      ·
        refine ⟨239224301997513722609838983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 159482867998342481739892655 239224301997513722609838983)
        ·
          refine ⟨358836452996270583914758475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 239224301997513722609838983 358836452996270583914758475)
          ·
            refine ⟨538254679494405875872137713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 358836452996270583914758475 538254679494405875872137713)
            ·
              refine ⟨403691009620804406904103285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 538254679494405875872137713 403691009620804406904103285)
              ·
                refine ⟨37846032151950413147259683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 403691009620804406904103285 37846032151950413147259683)
                ·
                  refine ⟨56769048227925619720889525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37846032151950413147259683 56769048227925619720889525)
                  ·
                    refine ⟨5322098271368026848833393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 56769048227925619720889525 5322098271368026848833393)
                    ·
                      refine ⟨3991573703526020136625045, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5322098271368026848833393 3991573703526020136625045)
                      ·
                        rfl

theorem cell23_7773562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 2, 5, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 2, 5, 1, 5, 2].length) (baseStart_7773562 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7773562 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7773562 prefixEnd_7773562 := by exact prefixLift 7773562
  have htrace : WordTrace (prefixWord ++ tailWord_7773562) baseStart_7773562 baseEnd_7773562 := by
    simpa [prefixWord, tailWord_7773562, baseEnd_7773562] using wordTrace_append hprefix tailTrace_7773562
  have hstable : (prefixWord ++ tailWord_7773562).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7773562).length < 2 ^ (prefixWord ++ tailWord_7773562).sum := by decide
  have hdescent : baseEnd_7773562 < baseStart_7773562 := by decide
  rcases family_descends (prefixWord ++ tailWord_7773562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7773612 : List Nat := [2, 2, 1, 1, 1, 1, 4, 3, 3, 2, 3]
def baseStart_7773612 : Nat := 118140960795 + 7773612 * 2 ^ 59
def prefixEnd_7773612 : Nat := 4983230072969 + 3 ^ 40 * 7773612 * 2
def baseEnd_7773612 : Nat := 3991599377558744940999815

theorem tailTrace_7773612 : CollatzResearch.WordTrace tailWord_7773612 prefixEnd_7773612 3991599377558744940999815 := by
  unfold tailWord_7773612
  simp only [CollatzResearch.WordTrace]
  refine ⟨141763461156769413038453545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 189017948209025884051271393 141763461156769413038453545)
  ·
    refine ⟨106322595867577059778840159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 141763461156769413038453545 106322595867577059778840159)
    ·
      refine ⟨159483893801365589668260239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106322595867577059778840159 159483893801365589668260239)
      ·
        refine ⟨239225840702048384502390359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 159483893801365589668260239 239225840702048384502390359)
        ·
          refine ⟨358838761053072576753585539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 239225840702048384502390359 358838761053072576753585539)
          ·
            refine ⟨538258141579608865130378309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 358838761053072576753585539 538258141579608865130378309)
            ·
              refine ⟨100923401546176662211945933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 538258141579608865130378309 100923401546176662211945933)
              ·
                refine ⟨37846275579816248329479725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 100923401546176662211945933 37846275579816248329479725)
                ·
                  refine ⟨14192353342431093123554897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 37846275579816248329479725 14192353342431093123554897)
                  ·
                    refine ⟨10644265006823319842666173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14192353342431093123554897 10644265006823319842666173)
                    ·
                      refine ⟨3991599377558744940999815, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10644265006823319842666173 3991599377558744940999815)
                      ·
                        rfl

theorem cell23_7773612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 3, 2, 3].length) (baseStart_7773612 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7773612 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7773612 prefixEnd_7773612 := by exact prefixLift 7773612
  have htrace : WordTrace (prefixWord ++ tailWord_7773612) baseStart_7773612 baseEnd_7773612 := by
    simpa [prefixWord, tailWord_7773612, baseEnd_7773612] using wordTrace_append hprefix tailTrace_7773612
  have hstable : (prefixWord ++ tailWord_7773612).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7773612).length < 2 ^ (prefixWord ++ tailWord_7773612).sum := by decide
  have hdescent : baseEnd_7773612 < baseStart_7773612 := by decide
  rcases family_descends (prefixWord ++ tailWord_7773612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7773629 : List Nat := [1, 4, 1, 2, 2, 1, 1, 5, 1, 2, 3]
def baseStart_7773629 : Nat := 118140960795 + 7773629 * 2 ^ 59
def prefixEnd_7773629 : Nat := 4983230072969 + 3 ^ 40 * 7773629 * 2
def baseEnd_7773629 : Nat := 3991608106729871374487237

theorem tailTrace_7773629 : CollatzResearch.WordTrace tailWord_7773629 prefixEnd_7773629 3991608106729871374487237 := by
  unfold tailWord_7773629
  simp only [CollatzResearch.WordTrace]
  refine ⟨283527542354477237980275941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189018361569651491986850627 283527542354477237980275941)
  ·
    refine ⟨53161414191464482121301739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 283527542354477237980275941 53161414191464482121301739)
    ·
      refine ⟨79742121287196723181952609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53161414191464482121301739 79742121287196723181952609)
      ·
        refine ⟨59806590965397542386464457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79742121287196723181952609 59806590965397542386464457)
        ·
          refine ⟨44854943224048156789848343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59806590965397542386464457 44854943224048156789848343)
          ·
            refine ⟨67282414836072235184772515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44854943224048156789848343 67282414836072235184772515)
            ·
              refine ⟨100923622254108352777158773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67282414836072235184772515 100923622254108352777158773)
              ·
                refine ⟨9461589586322658072858635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 100923622254108352777158773 9461589586322658072858635)
                ·
                  refine ⟨14192384379483987109287953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9461589586322658072858635 14192384379483987109287953)
                  ·
                    refine ⟨10644288284612990331965965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14192384379483987109287953 10644288284612990331965965)
                    ·
                      refine ⟨3991608106729871374487237, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10644288284612990331965965 3991608106729871374487237)
                      ·
                        rfl

theorem cell23_7773629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 1, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 1, 5, 1, 2, 3].length) (baseStart_7773629 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7773629 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7773629 prefixEnd_7773629 := by exact prefixLift 7773629
  have htrace : WordTrace (prefixWord ++ tailWord_7773629) baseStart_7773629 baseEnd_7773629 := by
    simpa [prefixWord, tailWord_7773629, baseEnd_7773629] using wordTrace_append hprefix tailTrace_7773629
  have hstable : (prefixWord ++ tailWord_7773629).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7773629).length < 2 ^ (prefixWord ++ tailWord_7773629).sum := by decide
  have hdescent : baseEnd_7773629 < baseStart_7773629 := by decide
  rcases family_descends (prefixWord ++ tailWord_7773629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7773675 : List Nat := [1, 1, 1, 1, 2, 3, 2, 1, 3, 8]
def baseStart_7773675 : Nat := 118140960795 + 7773675 * 2 ^ 59
def prefixEnd_7773675 : Nat := 4983230072969 + 3 ^ 40 * 7773675 * 2
def baseEnd_7773675 : Nat := 1330543908946659398170675

theorem tailTrace_7773675 : CollatzResearch.WordTrace tailWord_7773675 prefixEnd_7773675 1330543908946659398170675 := by
  unfold tailWord_7773675
  simp only [CollatzResearch.WordTrace]
  refine ⟨283529220112310587836450479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189019480074873725224300319 283529220112310587836450479)
  ·
    refine ⟨425293830168465881754675719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 283529220112310587836450479 425293830168465881754675719)
    ·
      refine ⟨637940745252698822632013579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 425293830168465881754675719 637940745252698822632013579)
      ·
        refine ⟨956911117879048233948020369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 637940745252698822632013579 956911117879048233948020369)
        ·
          refine ⟨717683338409286175461015277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 956911117879048233948020369 717683338409286175461015277)
          ·
            refine ⟨269131251903482315797880729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 717683338409286175461015277 269131251903482315797880729)
            ·
              refine ⟨201848438927611736848410547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 269131251903482315797880729 201848438927611736848410547)
              ·
                refine ⟨302772658391417605272615821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 201848438927611736848410547 302772658391417605272615821)
                ·
                  refine ⟨113539746896781601977230933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 302772658391417605272615821 113539746896781601977230933)
                  ·
                    refine ⟨1330543908946659398170675, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 113539746896781601977230933 1330543908946659398170675)
                    ·
                      rfl

theorem cell23_7773675_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 2, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 2, 1, 3, 8].length) (baseStart_7773675 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7773675 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7773675 prefixEnd_7773675 := by exact prefixLift 7773675
  have htrace : WordTrace (prefixWord ++ tailWord_7773675) baseStart_7773675 baseEnd_7773675 := by
    simpa [prefixWord, tailWord_7773675, baseEnd_7773675] using wordTrace_append hprefix tailTrace_7773675
  have hstable : (prefixWord ++ tailWord_7773675).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7773675).length < 2 ^ (prefixWord ++ tailWord_7773675).sum := by decide
  have hdescent : baseEnd_7773675 < baseStart_7773675 := by decide
  rcases family_descends (prefixWord ++ tailWord_7773675) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7773749 : List Nat := [1, 3, 3, 1, 1, 3, 1, 2, 2, 3, 3]
def baseStart_7773749 : Nat := 118140960795 + 7773749 * 2 ^ 59
def prefixEnd_7773749 : Nat := 4983230072969 + 3 ^ 40 * 7773749 * 2
def baseEnd_7773749 : Nat := 3991669724408410904986685

theorem tailTrace_7773749 : CollatzResearch.WordTrace tailWord_7773749 prefixEnd_7773749 3991669724408410904986685 := by
  unfold tailWord_7773749
  simp only [CollatzResearch.WordTrace]
  refine ⟨283531919114042498474644301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189021279409361665649762867 283531919114042498474644301)
  ·
    refine ⟨106324469667765936927991613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 283531919114042498474644301 106324469667765936927991613)
    ·
      refine ⟨39871676125412226347996855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 106324469667765936927991613 39871676125412226347996855)
      ·
        refine ⟨59807514188118339521995283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39871676125412226347996855 59807514188118339521995283)
        ·
          refine ⟨89711271282177509282992925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59807514188118339521995283 89711271282177509282992925)
          ·
            refine ⟨33641726730816565981122347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 89711271282177509282992925 33641726730816565981122347)
            ·
              refine ⟨50462590096224848971683521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33641726730816565981122347 50462590096224848971683521)
              ·
                refine ⟨37846942572168636728762641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50462590096224848971683521 37846942572168636728762641)
                ·
                  refine ⟨28385206929126477546571981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37846942572168636728762641 28385206929126477546571981)
                  ·
                    refine ⟨10644452598422429079964493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 28385206929126477546571981 10644452598422429079964493)
                    ·
                      refine ⟨3991669724408410904986685, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10644452598422429079964493 3991669724408410904986685)
                      ·
                        rfl

theorem cell23_7773749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 3, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 3, 1, 2, 2, 3, 3].length) (baseStart_7773749 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7773749 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7773749 prefixEnd_7773749 := by exact prefixLift 7773749
  have htrace : WordTrace (prefixWord ++ tailWord_7773749) baseStart_7773749 baseEnd_7773749 := by
    simpa [prefixWord, tailWord_7773749, baseEnd_7773749] using wordTrace_append hprefix tailTrace_7773749
  have hstable : (prefixWord ++ tailWord_7773749).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7773749).length < 2 ^ (prefixWord ++ tailWord_7773749).sum := by decide
  have hdescent : baseEnd_7773749 < baseStart_7773749 := by decide
  rcases family_descends (prefixWord ++ tailWord_7773749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7773750 : List Nat := [5, 1, 2, 1, 3, 1, 1, 1, 4, 2, 2]
def baseStart_7773750 : Nat := 118140960795 + 7773750 * 2 ^ 59
def prefixEnd_7773750 : Nat := 4983230072969 + 3 ^ 40 * 7773750 * 2
def baseEnd_7773750 : Nat := 3991670237889065401074181

theorem tailTrace_7773750 : CollatzResearch.WordTrace tailWord_7773750 prefixEnd_7773750 3991670237889065401074181 := by
  unfold tailWord_7773750
  simp only [CollatzResearch.WordTrace]
  refine ⟨17720747224189929727839419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 189021303724692583763620469 17720747224189929727839419)
  ·
    refine ⟨26581120836284894591759129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17720747224189929727839419 26581120836284894591759129)
    ·
      refine ⟨19935840627213670943819347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26581120836284894591759129 19935840627213670943819347)
      ·
        refine ⟨29903760940820506415729021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19935840627213670943819347 29903760940820506415729021)
        ·
          refine ⟨11213910352807689905898383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29903760940820506415729021 11213910352807689905898383)
          ·
            refine ⟨16820865529211534858847575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11213910352807689905898383 16820865529211534858847575)
            ·
              refine ⟨25231298293817302288271363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16820865529211534858847575 25231298293817302288271363)
              ·
                refine ⟨37846947440725953432407045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25231298293817302288271363 37846947440725953432407045)
                ·
                  refine ⟨7096302645136116268576321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 37846947440725953432407045 7096302645136116268576321)
                  ·
                    refine ⟨5322226983852087201432241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7096302645136116268576321 5322226983852087201432241)
                    ·
                      refine ⟨3991670237889065401074181, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5322226983852087201432241 3991670237889065401074181)
                      ·
                        rfl

theorem cell23_7773750_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 3, 1, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 3, 1, 1, 1, 4, 2, 2].length) (baseStart_7773750 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7773750 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7773750 prefixEnd_7773750 := by exact prefixLift 7773750
  have htrace : WordTrace (prefixWord ++ tailWord_7773750) baseStart_7773750 baseEnd_7773750 := by
    simpa [prefixWord, tailWord_7773750, baseEnd_7773750] using wordTrace_append hprefix tailTrace_7773750
  have hstable : (prefixWord ++ tailWord_7773750).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7773750).length < 2 ^ (prefixWord ++ tailWord_7773750).sum := by decide
  have hdescent : baseEnd_7773750 < baseStart_7773750 := by decide
  rcases family_descends (prefixWord ++ tailWord_7773750) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7773792 : List Nat := [2, 1, 1, 3, 2, 1, 1, 2, 2, 3, 5]
def baseStart_7773792 : Nat := 118140960795 + 7773792 * 2 ^ 59
def prefixEnd_7773792 : Nat := 4983230072969 + 3 ^ 40 * 7773792 * 2
def baseEnd_7773792 : Nat := 3991691804076554236748987

theorem tailTrace_7773792 : CollatzResearch.WordTrace tailWord_7773792 prefixEnd_7773792 3991691804076554236748987 := by
  unfold tailWord_7773792
  simp only [CollatzResearch.WordTrace]
  refine ⟨141766743726443358409229815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 189022324968591144545639753 141766743726443358409229815)
  ·
    refine ⟨212650115589665037613844723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141766743726443358409229815 212650115589665037613844723)
    ·
      refine ⟨318975173384497556420767085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 212650115589665037613844723 318975173384497556420767085)
      ·
        refine ⟨119615690019186583657787657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 318975173384497556420767085 119615690019186583657787657)
        ·
          refine ⟨89711767514389937743340743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 119615690019186583657787657 89711767514389937743340743)
          ·
            refine ⟨134567651271584906615011115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89711767514389937743340743 134567651271584906615011115)
            ·
              refine ⟨201851476907377359922516673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 134567651271584906615011115 201851476907377359922516673)
              ·
                refine ⟨151388607680533019941887505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 201851476907377359922516673 151388607680533019941887505)
                ·
                  refine ⟨113541455760399764956415629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 151388607680533019941887505 113541455760399764956415629)
                  ·
                    refine ⟨42578045910149911858655861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 113541455760399764956415629 42578045910149911858655861)
                    ·
                      refine ⟨3991691804076554236748987, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 42578045910149911858655861 3991691804076554236748987)
                      ·
                        rfl

theorem cell23_7773792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 1, 2, 2, 3, 5].length) (baseStart_7773792 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7773792 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7773792 prefixEnd_7773792 := by exact prefixLift 7773792
  have htrace : WordTrace (prefixWord ++ tailWord_7773792) baseStart_7773792 baseEnd_7773792 := by
    simpa [prefixWord, tailWord_7773792, baseEnd_7773792] using wordTrace_append hprefix tailTrace_7773792
  have hstable : (prefixWord ++ tailWord_7773792).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7773792).length < 2 ^ (prefixWord ++ tailWord_7773792).sum := by decide
  have hdescent : baseEnd_7773792 < baseStart_7773792 := by decide
  rcases family_descends (prefixWord ++ tailWord_7773792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7773799 : List Nat := [1, 1, 5, 1, 1, 1, 2, 2, 5, 4]
def baseStart_7773799 : Nat := 118140960795 + 7773799 * 2 ^ 59
def prefixEnd_7773799 : Nat := 4983230072969 + 3 ^ 40 * 7773799 * 2
def baseEnd_7773799 : Nat := 1330565132813711903120485

theorem tailTrace_7773799 : CollatzResearch.WordTrace tailWord_7773799 prefixEnd_7773799 1330565132813711903120485 := by
  unfold tailWord_7773799
  simp only [CollatzResearch.WordTrace]
  refine ⟨283533742763861357013964451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189022495175907571342642967 283533742763861357013964451)
  ·
    refine ⟨425300614145792035520946677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 283533742763861357013964451 425300614145792035520946677)
    ·
      refine ⟨39871932576168003330088751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 425300614145792035520946677 39871932576168003330088751)
      ·
        refine ⟨59807898864252004995133127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39871932576168003330088751 59807898864252004995133127)
        ·
          refine ⟨89711848296378007492699691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59807898864252004995133127 89711848296378007492699691)
          ·
            refine ⟨134567772444567011239049537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89711848296378007492699691 134567772444567011239049537)
            ·
              refine ⟨100925829333425258429287153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 134567772444567011239049537 100925829333425258429287153)
              ·
                refine ⟨75694372000068943821965365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 100925829333425258429287153 75694372000068943821965365)
                ·
                  refine ⟨7096347375006463483309253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 75694372000068943821965365 7096347375006463483309253)
                  ·
                    refine ⟨1330565132813711903120485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7096347375006463483309253 1330565132813711903120485)
                    ·
                      rfl

theorem cell23_7773799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 2, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 2, 2, 5, 4].length) (baseStart_7773799 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7773799 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7773799 prefixEnd_7773799 := by exact prefixLift 7773799
  have htrace : WordTrace (prefixWord ++ tailWord_7773799) baseStart_7773799 baseEnd_7773799 := by
    simpa [prefixWord, tailWord_7773799, baseEnd_7773799] using wordTrace_append hprefix tailTrace_7773799
  have hstable : (prefixWord ++ tailWord_7773799).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7773799).length < 2 ^ (prefixWord ++ tailWord_7773799).sum := by decide
  have hdescent : baseEnd_7773799 < baseStart_7773799 := by decide
  rcases family_descends (prefixWord ++ tailWord_7773799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7773829 : List Nat := [1, 3, 1, 1, 4, 1, 3, 3, 6]
def baseStart_7773829 : Nat := 118140960795 + 7773829 * 2 ^ 59
def prefixEnd_7773829 : Nat := 4983230072969 + 3 ^ 40 * 7773829 * 2
def baseEnd_7773829 : Nat := 443523422540085621331813

theorem tailTrace_7773829 : CollatzResearch.WordTrace tailWord_7773829 prefixEnd_7773829 443523422540085621331813 := by
  unfold tailWord_7773829
  simp only [CollatzResearch.WordTrace]
  refine ⟨283534836953752672137556541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189023224635835114758371027 283534836953752672137556541)
  ·
    refine ⟨106325563857657252051583703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 283534836953752672137556541 106325563857657252051583703)
    ·
      refine ⟨159488345786485878077375555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106325563857657252051583703 159488345786485878077375555)
      ·
        refine ⟨239232518679728817116063333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 159488345786485878077375555 239232518679728817116063333)
        ·
          refine ⟨44856097252449153209261875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 239232518679728817116063333 44856097252449153209261875)
          ·
            refine ⟨67284145878673729813892813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44856097252449153209261875 67284145878673729813892813)
            ·
              refine ⟨25231554704502648680209805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 67284145878673729813892813 25231554704502648680209805)
              ·
                refine ⟨9461833014188493255078677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25231554704502648680209805 9461833014188493255078677)
                ·
                  refine ⟨443523422540085621331813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9461833014188493255078677 443523422540085621331813)
                  ·
                    rfl

theorem cell23_7773829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 3, 3, 6].length) (baseStart_7773829 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7773829 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7773829 prefixEnd_7773829 := by exact prefixLift 7773829
  have htrace : WordTrace (prefixWord ++ tailWord_7773829) baseStart_7773829 baseEnd_7773829 := by
    simpa [prefixWord, tailWord_7773829, baseEnd_7773829] using wordTrace_append hprefix tailTrace_7773829
  have hstable : (prefixWord ++ tailWord_7773829).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7773829).length < 2 ^ (prefixWord ++ tailWord_7773829).sum := by decide
  have hdescent : baseEnd_7773829 < baseStart_7773829 := by decide
  rcases family_descends (prefixWord ++ tailWord_7773829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7773896 : List Nat := [2, 1, 3, 1, 2, 2, 2, 4, 1, 1, 4]
def baseStart_7773896 : Nat := 118140960795 + 7773896 * 2 ^ 59
def prefixEnd_7773896 : Nat := 4983230072969 + 3 ^ 40 * 7773896 * 2
def baseEnd_7773896 : Nat := 3991745206064621829848509

theorem tailTrace_7773896 : CollatzResearch.WordTrace tailWord_7773896 prefixEnd_7773896 3991745206064621829848509 := by
  unfold tailWord_7773896
  simp only [CollatzResearch.WordTrace]
  refine ⟨141768640322254971290122771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 189024853763006628386830361 141768640322254971290122771)
  ·
    refine ⟨212652960483382456935184157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141768640322254971290122771 212652960483382456935184157)
    ·
      refine ⟨79744860181268421350694059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 212652960483382456935184157 79744860181268421350694059)
      ·
        refine ⟨119617290271902632026041089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79744860181268421350694059 119617290271902632026041089)
        ·
          refine ⟨89712967703926974019530817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 119617290271902632026041089 89712967703926974019530817)
          ·
            refine ⟨67284725777945230514648113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 89712967703926974019530817 67284725777945230514648113)
            ·
              refine ⟨50463544333458922885986085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 67284725777945230514648113 50463544333458922885986085)
              ·
                refine ⟨9461914562523548041122391, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 50463544333458922885986085 9461914562523548041122391)
                ·
                  refine ⟨14192871843785322061683587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9461914562523548041122391 14192871843785322061683587)
                  ·
                    refine ⟨21289307765677983092525381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14192871843785322061683587 21289307765677983092525381)
                    ·
                      refine ⟨3991745206064621829848509, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21289307765677983092525381 3991745206064621829848509)
                      ·
                        rfl

theorem cell23_7773896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 2, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 2, 4, 1, 1, 4].length) (baseStart_7773896 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7773896 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7773896 prefixEnd_7773896 := by exact prefixLift 7773896
  have htrace : WordTrace (prefixWord ++ tailWord_7773896) baseStart_7773896 baseEnd_7773896 := by
    simpa [prefixWord, tailWord_7773896, baseEnd_7773896] using wordTrace_append hprefix tailTrace_7773896
  have hstable : (prefixWord ++ tailWord_7773896).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7773896).length < 2 ^ (prefixWord ++ tailWord_7773896).sum := by decide
  have hdescent : baseEnd_7773896 < baseStart_7773896 := by decide
  rcases family_descends (prefixWord ++ tailWord_7773896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7773906 : List Nat := [3, 2, 2, 2, 2, 1, 2, 2, 1, 6]
def baseStart_7773906 : Nat := 118140960795 + 7773906 * 2 ^ 59
def prefixEnd_7773906 : Nat := 4983230072969 + 3 ^ 40 * 7773906 * 2
def baseEnd_7773906 : Nat := 1330583446957055596907821

theorem tailTrace_7773906 : CollatzResearch.WordTrace tailWord_7773906 prefixEnd_7773906 1330583446957055596907821 := by
  unfold tailWord_7773906
  simp only [CollatzResearch.WordTrace]
  refine ⟨70884411343618428572027393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 189025096916315809525406381 70884411343618428572027393)
  ·
    refine ⟨53163308507713821429020545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70884411343618428572027393 53163308507713821429020545)
    ·
      refine ⟨39872481380785366071765409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53163308507713821429020545 39872481380785366071765409)
      ·
        refine ⟨29904361035589024553824057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39872481380785366071765409 29904361035589024553824057)
        ·
          refine ⟨22428270776691768415368043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29904361035589024553824057 22428270776691768415368043)
          ·
            refine ⟨33642406165037652623052065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22428270776691768415368043 33642406165037652623052065)
            ·
              refine ⟨25231804623778239467289049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33642406165037652623052065 25231804623778239467289049)
              ·
                refine ⟨18923853467833679600466787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25231804623778239467289049 18923853467833679600466787)
                ·
                  refine ⟨28385780201750519400700181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18923853467833679600466787 28385780201750519400700181)
                  ·
                    refine ⟨1330583446957055596907821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28385780201750519400700181 1330583446957055596907821)
                    ·
                      rfl

theorem cell23_7773906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 1, 2, 2, 1, 6].length) (baseStart_7773906 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7773906 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7773906 prefixEnd_7773906 := by exact prefixLift 7773906
  have htrace : WordTrace (prefixWord ++ tailWord_7773906) baseStart_7773906 baseEnd_7773906 := by
    simpa [prefixWord, tailWord_7773906, baseEnd_7773906] using wordTrace_append hprefix tailTrace_7773906
  have hstable : (prefixWord ++ tailWord_7773906).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7773906).length < 2 ^ (prefixWord ++ tailWord_7773906).sum := by decide
  have hdescent : baseEnd_7773906 < baseStart_7773906 := by decide
  rcases family_descends (prefixWord ++ tailWord_7773906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7773913 : List Nat := [1, 2, 1, 2, 3, 3, 4, 1, 1, 1, 4]
def baseStart_7773913 : Nat := 118140960795 + 7773913 * 2 ^ 59
def prefixEnd_7773913 : Nat := 4983230072969 + 3 ^ 40 * 7773913 * 2
def baseEnd_7773913 : Nat := 3991753935235748263335931

theorem tailTrace_7773913 : CollatzResearch.WordTrace tailWord_7773913 prefixEnd_7773913 3991753935235748263335931 := by
  unfold tailWord_7773913
  simp only [CollatzResearch.WordTrace]
  refine ⟨283537900685448354483614393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189025267123632236322409595 283537900685448354483614393)
  ·
    refine ⟨212653425514086265862710795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 283537900685448354483614393 212653425514086265862710795)
    ·
      refine ⟨318980138271129398794066193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 212653425514086265862710795 318980138271129398794066193)
      ·
        refine ⟨239235103703347049095549645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 318980138271129398794066193 239235103703347049095549645)
        ·
          refine ⟨89713163888755143410831117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 239235103703347049095549645 89713163888755143410831117)
          ·
            refine ⟨33642436458283178779061669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 89713163888755143410831117 33642436458283178779061669)
            ·
              refine ⟨6307956835928096021074063, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 33642436458283178779061669 6307956835928096021074063)
              ·
                refine ⟨9461935253892144031611095, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6307956835928096021074063 9461935253892144031611095)
                ·
                  refine ⟨14192902880838216047416643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9461935253892144031611095 14192902880838216047416643)
                  ·
                    refine ⟨21289354321257324071124965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14192902880838216047416643 21289354321257324071124965)
                    ·
                      refine ⟨3991753935235748263335931, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21289354321257324071124965 3991753935235748263335931)
                      ·
                        rfl

theorem cell23_7773913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 3, 4, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 3, 4, 1, 1, 1, 4].length) (baseStart_7773913 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7773913 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7773913 prefixEnd_7773913 := by exact prefixLift 7773913
  have htrace : WordTrace (prefixWord ++ tailWord_7773913) baseStart_7773913 baseEnd_7773913 := by
    simpa [prefixWord, tailWord_7773913, baseEnd_7773913] using wordTrace_append hprefix tailTrace_7773913
  have hstable : (prefixWord ++ tailWord_7773913).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7773913).length < 2 ^ (prefixWord ++ tailWord_7773913).sum := by decide
  have hdescent : baseEnd_7773913 < baseStart_7773913 := by decide
  rcases family_descends (prefixWord ++ tailWord_7773913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7773923 : List Nat := [1, 1, 1, 7, 2, 1, 1, 1, 4, 4]
def baseStart_7773923 : Nat := 118140960795 + 7773923 * 2 ^ 59
def prefixEnd_7773923 : Nat := 4983230072969 + 3 ^ 40 * 7773923 * 2
def baseEnd_7773923 : Nat := 1330586356680764408070295

theorem tailTrace_7773923 : CollatzResearch.WordTrace tailWord_7773923 prefixEnd_7773923 1330586356680764408070295 := by
  unfold tailWord_7773923
  simp only [CollatzResearch.WordTrace]
  refine ⟨283538265415412126191478423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189025510276941417460985615 283538265415412126191478423)
  ·
    refine ⟨425307398123118189287217635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 283538265415412126191478423 425307398123118189287217635)
    ·
      refine ⟨637961097184677283930826453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 425307398123118189287217635 637961097184677283930826453)
      ·
        refine ⟨14952213215265873842128745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 637961097184677283930826453 14952213215265873842128745)
        ·
          refine ⟨11214159911449405381596559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14952213215265873842128745 11214159911449405381596559)
          ·
            refine ⟨16821239867174108072394839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11214159911449405381596559 16821239867174108072394839)
            ·
              refine ⟨25231859800761162108592259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16821239867174108072394839 25231859800761162108592259)
              ·
                refine ⟨37847789701141743162888389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25231859800761162108592259 37847789701141743162888389)
                ·
                  refine ⟨7096460568964076843041573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 37847789701141743162888389 7096460568964076843041573)
                  ·
                    refine ⟨1330586356680764408070295, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7096460568964076843041573 1330586356680764408070295)
                    ·
                      rfl

theorem cell23_7773923_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 2, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 2, 1, 1, 1, 4, 4].length) (baseStart_7773923 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7773923 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7773923 prefixEnd_7773923 := by exact prefixLift 7773923
  have htrace : WordTrace (prefixWord ++ tailWord_7773923) baseStart_7773923 baseEnd_7773923 := by
    simpa [prefixWord, tailWord_7773923, baseEnd_7773923] using wordTrace_append hprefix tailTrace_7773923
  have hstable : (prefixWord ++ tailWord_7773923).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7773923).length < 2 ^ (prefixWord ++ tailWord_7773923).sum := by decide
  have hdescent : baseEnd_7773923 < baseStart_7773923 := by decide
  rcases family_descends (prefixWord ++ tailWord_7773923) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7773940 : List Nat := [2, 6, 1, 1, 1, 1, 3, 1, 1, 6]
def baseStart_7773940 : Nat := 118140960795 + 7773940 * 2 ^ 59
def prefixEnd_7773940 : Nat := 4983230072969 + 3 ^ 40 * 7773940 * 2
def baseEnd_7773940 : Nat := 1330589266404473219232769

theorem tailTrace_7773940 : CollatzResearch.WordTrace tailWord_7773940 prefixEnd_7773940 1330589266404473219232769 := by
  unfold tailWord_7773940
  simp only [CollatzResearch.WordTrace]
  refine ⟨141769442728175269047423637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 189025923637567025396564849 141769442728175269047423637)
  ·
    refine ⟨6645442627883215736597983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 141769442728175269047423637 6645442627883215736597983)
    ·
      refine ⟨9968163941824823604896975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6645442627883215736597983 9968163941824823604896975)
      ·
        refine ⟨14952245912737235407345463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9968163941824823604896975 14952245912737235407345463)
        ·
          refine ⟨22428368869105853111018195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14952245912737235407345463 22428368869105853111018195)
          ·
            refine ⟨33642553303658779666527293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22428368869105853111018195 33642553303658779666527293)
            ·
              refine ⟨12615957488872042374947735, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33642553303658779666527293 12615957488872042374947735)
              ·
                refine ⟨18923936233308063562421603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12615957488872042374947735 18923936233308063562421603)
                ·
                  refine ⟨28385904349962095343632405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18923936233308063562421603 28385904349962095343632405)
                  ·
                    refine ⟨1330589266404473219232769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28385904349962095343632405 1330589266404473219232769)
                    ·
                      rfl

theorem cell23_7773940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 1, 3, 1, 1, 6].length) (baseStart_7773940 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7773940 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7773940 prefixEnd_7773940 := by exact prefixLift 7773940
  have htrace : WordTrace (prefixWord ++ tailWord_7773940) baseStart_7773940 baseEnd_7773940 := by
    simpa [prefixWord, tailWord_7773940, baseEnd_7773940] using wordTrace_append hprefix tailTrace_7773940
  have hstable : (prefixWord ++ tailWord_7773940).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7773940).length < 2 ^ (prefixWord ++ tailWord_7773940).sum := by decide
  have hdescent : baseEnd_7773940 < baseStart_7773940 := by decide
  rcases family_descends (prefixWord ++ tailWord_7773940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7773969 : List Nat := [1, 2, 2, 1, 1, 3, 1, 2, 1, 5, 4]
def baseStart_7773969 : Nat := 118140960795 + 7773969 * 2 ^ 59
def prefixEnd_7773969 : Nat := 4983230072969 + 3 ^ 40 * 7773969 * 2
def baseEnd_7773969 : Nat := 3991782690152400044235673

theorem tailTrace_7773969 : CollatzResearch.WordTrace tailWord_7773969 prefixEnd_7773969 3991782690152400044235673 := by
  unfold tailWord_7773969
  simp only [CollatzResearch.WordTrace]
  refine ⟨283539943173245476047652961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189026628782163650698435307 283539943173245476047652961)
  ·
    refine ⟨212654957379934107035739721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 283539943173245476047652961 212654957379934107035739721)
    ·
      refine ⟨159491218034950580276804791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 212654957379934107035739721 159491218034950580276804791)
      ·
        refine ⟨239236827052425870415207187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 159491218034950580276804791 239236827052425870415207187)
        ·
          refine ⟨358855240578638805622810781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 239236827052425870415207187 358855240578638805622810781)
          ·
            refine ⟨134570715216989552108554043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 358855240578638805622810781 134570715216989552108554043)
            ·
              refine ⟨201856072825484328162831065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 134570715216989552108554043 201856072825484328162831065)
              ·
                refine ⟨151392054619113246122123299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 201856072825484328162831065 151392054619113246122123299)
                ·
                  refine ⟨227088081928669869183184949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 151392054619113246122123299 227088081928669869183184949)
                  ·
                    refine ⟨21289507680812800235923589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 227088081928669869183184949 21289507680812800235923589)
                    ·
                      refine ⟨3991782690152400044235673, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21289507680812800235923589 3991782690152400044235673)
                      ·
                        rfl

theorem cell23_7773969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 5, 4].length) (baseStart_7773969 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7773969 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7773969 prefixEnd_7773969 := by exact prefixLift 7773969
  have htrace : WordTrace (prefixWord ++ tailWord_7773969) baseStart_7773969 baseEnd_7773969 := by
    simpa [prefixWord, tailWord_7773969, baseEnd_7773969] using wordTrace_append hprefix tailTrace_7773969
  have hstable : (prefixWord ++ tailWord_7773969).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7773969).length < 2 ^ (prefixWord ++ tailWord_7773969).sum := by decide
  have hdescent : baseEnd_7773969 < baseStart_7773969 := by decide
  rcases family_descends (prefixWord ++ tailWord_7773969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7773986 : List Nat := [3, 3, 1, 1, 2, 1, 2, 1, 2, 3, 4]
def baseStart_7773986 : Nat := 118140960795 + 7773986 * 2 ^ 59
def prefixEnd_7773986 : Nat := 4983230072969 + 3 ^ 40 * 7773986 * 2
def baseEnd_7773986 : Nat := 3991791419323526477723095

theorem tailTrace_7773986 : CollatzResearch.WordTrace tailWord_7773986 prefixEnd_7773986 3991791419323526477723095 := by
  unfold tailWord_7773986
  simp only [CollatzResearch.WordTrace]
  refine ⟨70885140803545971987755453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 189027042142789258634014541 70885140803545971987755453)
  ·
    refine ⟨26581927801329739495408295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 70885140803545971987755453 26581927801329739495408295)
    ·
      refine ⟨39872891701994609243112443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26581927801329739495408295 39872891701994609243112443)
      ·
        refine ⟨59809337552991913864668665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39872891701994609243112443 59809337552991913864668665)
        ·
          refine ⟨44857003164743935398501499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59809337552991913864668665 44857003164743935398501499)
          ·
            refine ⟨67285504747115903097752249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44857003164743935398501499 67285504747115903097752249)
            ·
              refine ⟨50464128560336927323314187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 67285504747115903097752249 50464128560336927323314187)
              ·
                refine ⟨75696192840505390984971281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50464128560336927323314187 75696192840505390984971281)
                ·
                  refine ⟨56772144630379043238728461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 75696192840505390984971281 56772144630379043238728461)
                  ·
                    refine ⟨21289554236392141214523173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 56772144630379043238728461 21289554236392141214523173)
                    ·
                      refine ⟨3991791419323526477723095, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21289554236392141214523173 3991791419323526477723095)
                      ·
                        rfl

theorem cell23_7773986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 2, 1, 2, 3, 4].length) (baseStart_7773986 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7773986 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7773986 prefixEnd_7773986 := by exact prefixLift 7773986
  have htrace : WordTrace (prefixWord ++ tailWord_7773986) baseStart_7773986 baseEnd_7773986 := by
    simpa [prefixWord, tailWord_7773986, baseEnd_7773986] using wordTrace_append hprefix tailTrace_7773986
  have hstable : (prefixWord ++ tailWord_7773986).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7773986).length < 2 ^ (prefixWord ++ tailWord_7773986).sum := by decide
  have hdescent : baseEnd_7773986 < baseStart_7773986 := by decide
  rcases family_descends (prefixWord ++ tailWord_7773986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7774037 : List Nat := [1, 3, 2, 2, 2, 3, 2, 2, 2, 2, 2]
def baseStart_7774037 : Nat := 118140960795 + 7774037 * 2 ^ 59
def prefixEnd_7774037 : Nat := 4983230072969 + 3 ^ 40 * 7774037 * 2
def baseEnd_7774037 : Nat := 3991817606836905778185361

theorem tailTrace_7774037 : CollatzResearch.WordTrace tailWord_7774037 prefixEnd_7774037 3991817606836905778185361 := by
  unfold tailWord_7774037
  simp only [CollatzResearch.WordTrace]
  refine ⟨283542423336999123661128365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189028282224666082440752243 283542423336999123661128365)
  ·
    refine ⟨106328408751374671372923137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 283542423336999123661128365 106328408751374671372923137)
    ·
      refine ⟨79746306563531003529692353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 106328408751374671372923137 79746306563531003529692353)
      ·
        refine ⟨59809729922648252647269265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79746306563531003529692353 59809729922648252647269265)
        ·
          refine ⟨44857297441986189485451949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59809729922648252647269265 44857297441986189485451949)
          ·
            refine ⟨16821486540744821057044481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 44857297441986189485451949 16821486540744821057044481)
            ·
              refine ⟨12616114905558615792783361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16821486540744821057044481 12616114905558615792783361)
              ·
                refine ⟨9462086179168961844587521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12616114905558615792783361 9462086179168961844587521)
                ·
                  refine ⟨7096564634376721383440641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9462086179168961844587521 7096564634376721383440641)
                  ·
                    refine ⟨5322423475782541037580481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7096564634376721383440641 5322423475782541037580481)
                    ·
                      refine ⟨3991817606836905778185361, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5322423475782541037580481 3991817606836905778185361)
                      ·
                        rfl

theorem cell23_7774037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 3, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 3, 2, 2, 2, 2, 2].length) (baseStart_7774037 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7774037 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7774037 prefixEnd_7774037 := by exact prefixLift 7774037
  have htrace : WordTrace (prefixWord ++ tailWord_7774037) baseStart_7774037 baseEnd_7774037 := by
    simpa [prefixWord, tailWord_7774037, baseEnd_7774037] using wordTrace_append hprefix tailTrace_7774037
  have hstable : (prefixWord ++ tailWord_7774037).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7774037).length < 2 ^ (prefixWord ++ tailWord_7774037).sum := by decide
  have hdescent : baseEnd_7774037 < baseStart_7774037 := by decide
  rcases family_descends (prefixWord ++ tailWord_7774037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7774056 : List Nat := [2, 1, 4, 2, 1, 1, 2, 2, 1, 7]
def baseStart_7774056 : Nat := 118140960795 + 7774056 * 2 ^ 59
def prefixEnd_7774056 : Nat := 4983230072969 + 3 ^ 40 * 7774056 * 2
def baseEnd_7774056 : Nat := 1330609120989780401282591

theorem tailTrace_7774056 : CollatzResearch.WordTrace tailWord_7774056 prefixEnd_7774056 1330609120989780401282591 := by
  unfold tailWord_7774056
  simp only [CollatzResearch.WordTrace]
  refine ⟨141771558161965144953035011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 189028744215953526604046681 141771558161965144953035011)
  ·
    refine ⟨212657337242947717429552517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141771558161965144953035011 212657337242947717429552517)
    ·
      refine ⟨39873250733052697018041097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 212657337242947717429552517 39873250733052697018041097)
      ·
        refine ⟨29904938049789522763530823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39873250733052697018041097 29904938049789522763530823)
        ·
          refine ⟨44857407074684284145296235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29904938049789522763530823 44857407074684284145296235)
          ·
            refine ⟨67286110612026426217944353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44857407074684284145296235 67286110612026426217944353)
            ·
              refine ⟨50464582959019819663458265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 67286110612026426217944353 50464582959019819663458265)
              ·
                refine ⟨37848437219264864747593699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50464582959019819663458265 37848437219264864747593699)
                ·
                  refine ⟨56772655828897297121390549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37848437219264864747593699 56772655828897297121390549)
                  ·
                    refine ⟨1330609120989780401282591, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 56772655828897297121390549 1330609120989780401282591)
                    ·
                      rfl

theorem cell23_7774056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 2, 2, 1, 7].length) (baseStart_7774056 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7774056 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7774056 prefixEnd_7774056 := by exact prefixLift 7774056
  have htrace : WordTrace (prefixWord ++ tailWord_7774056) baseStart_7774056 baseEnd_7774056 := by
    simpa [prefixWord, tailWord_7774056, baseEnd_7774056] using wordTrace_append hprefix tailTrace_7774056
  have hstable : (prefixWord ++ tailWord_7774056).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7774056).length < 2 ^ (prefixWord ++ tailWord_7774056).sum := by decide
  have hdescent : baseEnd_7774056 < baseStart_7774056 := by decide
  rcases family_descends (prefixWord ++ tailWord_7774056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7774096 : List Nat := [2, 1, 1, 1, 1, 1, 2, 4, 3, 4, 3]
def baseStart_7774096 : Nat := 118140960795 + 7774096 * 2 ^ 59
def prefixEnd_7774096 : Nat := 4983230072969 + 3 ^ 40 * 7774096 * 2
def baseEnd_7774096 : Nat := 3991847902195521047347589

theorem tailTrace_7774096 : CollatzResearch.WordTrace tailWord_7774096 prefixEnd_7774096 3991847902195521047347589 := by
  unfold tailWord_7774096
  simp only [CollatzResearch.WordTrace]
  refine ⟨141772287621892688368763071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 189029716829190251158350761 141772287621892688368763071)
  ·
    refine ⟨212658431432839032553144607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141772287621892688368763071 212658431432839032553144607)
    ·
      refine ⟨318987647149258548829716911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 212658431432839032553144607 318987647149258548829716911)
      ·
        refine ⟨478481470723887823244575367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 318987647149258548829716911 478481470723887823244575367)
        ·
          refine ⟨717722206085831734866863051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 478481470723887823244575367 717722206085831734866863051)
          ·
            refine ⟨1076583309128747602300294577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 717722206085831734866863051 1076583309128747602300294577)
            ·
              refine ⟨807437481846560701725220933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1076583309128747602300294577 807437481846560701725220933)
              ·
                refine ⟨151394527846230131573478925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 807437481846560701725220933 151394527846230131573478925)
                ·
                  refine ⟨56772947942336299340054597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 151394527846230131573478925 56772947942336299340054597)
                  ·
                    refine ⟨10644927739188056126260237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 56772947942336299340054597 10644927739188056126260237)
                    ·
                      refine ⟨3991847902195521047347589, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10644927739188056126260237 3991847902195521047347589)
                      ·
                        rfl

theorem cell23_7774096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 4, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 4, 3, 4, 3].length) (baseStart_7774096 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7774096 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7774096 prefixEnd_7774096 := by exact prefixLift 7774096
  have htrace : WordTrace (prefixWord ++ tailWord_7774096) baseStart_7774096 baseEnd_7774096 := by
    simpa [prefixWord, tailWord_7774096, baseEnd_7774096] using wordTrace_append hprefix tailTrace_7774096
  have hstable : (prefixWord ++ tailWord_7774096).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7774096).length < 2 ^ (prefixWord ++ tailWord_7774096).sum := by decide
  have hdescent : baseEnd_7774096 < baseStart_7774096 := by decide
  rcases family_descends (prefixWord ++ tailWord_7774096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7774103 : List Nat := [1, 1, 3, 3, 1, 3, 1, 3, 3, 4]
def baseStart_7774103 : Nat := 118140960795 + 7774103 * 2 ^ 59
def prefixEnd_7774103 : Nat := 4983230072969 + 3 ^ 40 * 7774103 * 2
def baseEnd_7774103 : Nat := 1330617165520034173320019

theorem tailTrace_7774103 : CollatzResearch.WordTrace tailWord_7774103 prefixEnd_7774103 1330617165520034173320019 := by
  unfold tailWord_7774103
  simp only [CollatzResearch.WordTrace]
  refine ⟨283544830554760016933030963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189029887036506677955353975 283544830554760016933030963)
  ·
    refine ⟨425317245832140025399546445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 283544830554760016933030963 425317245832140025399546445)
    ·
      refine ⟨159493967187052509524829917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 425317245832140025399546445 159493967187052509524829917)
      ·
        refine ⟨59810237695144691071811219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 159493967187052509524829917 59810237695144691071811219)
        ·
          refine ⟨89715356542717036607716829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59810237695144691071811219 89715356542717036607716829)
          ·
            refine ⟨33643258703518888727893811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 89715356542717036607716829 33643258703518888727893811)
            ·
              refine ⟨50464888055278333091840717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33643258703518888727893811 50464888055278333091840717)
              ·
                refine ⟨18924333020729374909440269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 50464888055278333091840717 18924333020729374909440269)
                ·
                  refine ⟨7096624882773515591040101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18924333020729374909440269 7096624882773515591040101)
                  ·
                    refine ⟨1330617165520034173320019, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7096624882773515591040101 1330617165520034173320019)
                    ·
                      rfl

theorem cell23_7774103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 3, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 3, 1, 3, 3, 4].length) (baseStart_7774103 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7774103 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7774103 prefixEnd_7774103 := by exact prefixLift 7774103
  have htrace : WordTrace (prefixWord ++ tailWord_7774103) baseStart_7774103 baseEnd_7774103 := by
    simpa [prefixWord, tailWord_7774103, baseEnd_7774103] using wordTrace_append hprefix tailTrace_7774103
  have hstable : (prefixWord ++ tailWord_7774103).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7774103).length < 2 ^ (prefixWord ++ tailWord_7774103).sum := by decide
  have hdescent : baseEnd_7774103 < baseStart_7774103 := by decide
  rcases family_descends (prefixWord ++ tailWord_7774103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7774160 : List Nat := [2, 1, 1, 1, 1, 2, 7, 1, 3, 1, 3]
def baseStart_7774160 : Nat := 118140960795 + 7774160 * 2 ^ 59
def prefixEnd_7774160 : Nat := 4983230072969 + 3 ^ 40 * 7774160 * 2
def baseEnd_7774160 : Nat := 3991880764957408796947295

theorem tailTrace_7774160 : CollatzResearch.WordTrace tailWord_7774160 prefixEnd_7774160 3991880764957408796947295 := by
  unfold tailWord_7774160
  simp only [CollatzResearch.WordTrace]
  refine ⟨141773454757776757833927967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 189031273010369010445237289 141773454757776757833927967)
  ·
    refine ⟨212660182136665136750891951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141773454757776757833927967 212660182136665136750891951)
    ·
      refine ⟨318990273204997705126337927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 212660182136665136750891951 318990273204997705126337927)
      ·
        refine ⟨478485409807496557689506891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 318990273204997705126337927 478485409807496557689506891)
        ·
          refine ⟨717728114711244836534260337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 478485409807496557689506891 717728114711244836534260337)
          ·
            refine ⟨538296086033433627400695253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 717728114711244836534260337 538296086033433627400695253)
            ·
              refine ⟨12616314516408600642203795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 538296086033433627400695253 12616314516408600642203795)
              ·
                refine ⟨18924471774612900963305693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12616314516408600642203795 18924471774612900963305693)
                ·
                  refine ⟨7096676915479837861239635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18924471774612900963305693 7096676915479837861239635)
                  ·
                    refine ⟨10645015373219756791859453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7096676915479837861239635 10645015373219756791859453)
                    ·
                      refine ⟨3991880764957408796947295, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10645015373219756791859453 3991880764957408796947295)
                      ·
                        rfl

theorem cell23_7774160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 7, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 7, 1, 3, 1, 3].length) (baseStart_7774160 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7774160 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7774160 prefixEnd_7774160 := by exact prefixLift 7774160
  have htrace : WordTrace (prefixWord ++ tailWord_7774160) baseStart_7774160 baseEnd_7774160 := by
    simpa [prefixWord, tailWord_7774160, baseEnd_7774160] using wordTrace_append hprefix tailTrace_7774160
  have hstable : (prefixWord ++ tailWord_7774160).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7774160).length < 2 ^ (prefixWord ++ tailWord_7774160).sum := by decide
  have hdescent : baseEnd_7774160 < baseStart_7774160 := by decide
  rcases family_descends (prefixWord ++ tailWord_7774160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7774176 : List Nat := [2, 1, 1, 3, 1, 1, 1, 2, 5, 6]
def baseStart_7774176 : Nat := 118140960795 + 7774176 * 2 ^ 59
def prefixEnd_7774176 : Nat := 4983230072969 + 3 ^ 40 * 7774176 * 2
def baseEnd_7774176 : Nat := 1330629660215960244782407

theorem tailTrace_7774176 : CollatzResearch.WordTrace tailWord_7774176 prefixEnd_7774176 1330629660215960244782407 := by
  unfold tailWord_7774176
  simp only [CollatzResearch.WordTrace]
  refine ⟨141773746541747775200219191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 189031662055663700266958921 141773746541747775200219191)
  ·
    refine ⟨212660619812621662800328787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141773746541747775200219191 212660619812621662800328787)
    ·
      refine ⟨318990929718932494200493181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 212660619812621662800328787 318990929718932494200493181)
      ·
        refine ⟨119621598644599685325184943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 318990929718932494200493181 119621598644599685325184943)
        ·
          refine ⟨179432397966899527987777415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 119621598644599685325184943 179432397966899527987777415)
          ·
            refine ⟨269148596950349291981666123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 179432397966899527987777415 269148596950349291981666123)
            ·
              refine ⟨403722895425523937972499185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 269148596950349291981666123 403722895425523937972499185)
              ·
                refine ⟨302792171569142953479374389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 403722895425523937972499185 302792171569142953479374389)
                ·
                  refine ⟨28386766084607151888691349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 302792171569142953479374389 28386766084607151888691349)
                  ·
                    refine ⟨1330629660215960244782407, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28386766084607151888691349 1330629660215960244782407)
                    ·
                      rfl

theorem cell23_7774176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 1, 2, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 1, 2, 5, 6].length) (baseStart_7774176 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7774176 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7774176 prefixEnd_7774176 := by exact prefixLift 7774176
  have htrace : WordTrace (prefixWord ++ tailWord_7774176) baseStart_7774176 baseEnd_7774176 := by
    simpa [prefixWord, tailWord_7774176, baseEnd_7774176] using wordTrace_append hprefix tailTrace_7774176
  have hstable : (prefixWord ++ tailWord_7774176).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7774176).length < 2 ^ (prefixWord ++ tailWord_7774176).sum := by decide
  have hdescent : baseEnd_7774176 < baseStart_7774176 := by decide
  rcases family_descends (prefixWord ++ tailWord_7774176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7774203 : List Nat := [1, 1, 1, 1, 1, 3, 7, 1, 1, 1, 5]
def baseStart_7774203 : Nat := 118140960795 + 7774203 * 2 ^ 59
def prefixEnd_7774203 : Nat := 4983230072969 + 3 ^ 40 * 7774203 * 2
def baseEnd_7774203 : Nat := 3991902844625552128709597

theorem tailTrace_7774203 : CollatzResearch.WordTrace tailWord_7774203 prefixEnd_7774203 3991902844625552128709597 := by
  unfold tailWord_7774203
  simp only [CollatzResearch.WordTrace]
  refine ⟨283548477854397734011671263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189032318569598489341114175 283548477854397734011671263)
  ·
    refine ⟨425322716781596601017506895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 283548477854397734011671263 425322716781596601017506895)
    ·
      refine ⟨637984075172394901526260343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 425322716781596601017506895 637984075172394901526260343)
      ·
        refine ⟨956976112758592352289390515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 637984075172394901526260343 956976112758592352289390515)
        ·
          refine ⟨1435464169137888528434085773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 956976112758592352289390515 1435464169137888528434085773)
          ·
            refine ⟨538299063426708198162782165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1435464169137888528434085773 538299063426708198162782165)
            ·
              refine ⟨12616384299063473394440207, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 538299063426708198162782165 12616384299063473394440207)
              ·
                refine ⟨18924576448595210091660311, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12616384299063473394440207 18924576448595210091660311)
                ·
                  refine ⟨28386864672892815137490467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18924576448595210091660311 28386864672892815137490467)
                  ·
                    refine ⟨42580297009339222706235701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 28386864672892815137490467 42580297009339222706235701)
                    ·
                      refine ⟨3991902844625552128709597, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 42580297009339222706235701 3991902844625552128709597)
                      ·
                        rfl

theorem cell23_7774203_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 7, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 7, 1, 1, 1, 5].length) (baseStart_7774203 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7774203 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7774203 prefixEnd_7774203 := by exact prefixLift 7774203
  have htrace : WordTrace (prefixWord ++ tailWord_7774203) baseStart_7774203 baseEnd_7774203 := by
    simpa [prefixWord, tailWord_7774203, baseEnd_7774203] using wordTrace_append hprefix tailTrace_7774203
  have hstable : (prefixWord ++ tailWord_7774203).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7774203).length < 2 ^ (prefixWord ++ tailWord_7774203).sum := by decide
  have hdescent : baseEnd_7774203 < baseStart_7774203 := by decide
  rcases family_descends (prefixWord ++ tailWord_7774203) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7774254 : List Nat := [4, 1, 3, 1, 1, 2, 4, 1, 1, 2, 3]
def baseStart_7774254 : Nat := 118140960795 + 7774254 * 2 ^ 59
def prefixEnd_7774254 : Nat := 4983230072969 + 3 ^ 40 * 7774254 * 2
def baseEnd_7774254 : Nat := 3991929032138931429171863

theorem tailTrace_7774254 : CollatzResearch.WordTrace tailWord_7774254 prefixEnd_7774254 3991929032138931429171863 := by
  unfold tailWord_7774254
  simp only [CollatzResearch.WordTrace]
  refine ⟨35443792247151621215222227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 189033558651475313147851877 35443792247151621215222227)
  ·
    refine ⟨53165688370727431822833341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35443792247151621215222227 53165688370727431822833341)
    ·
      refine ⟨19937133139022786933562503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 53165688370727431822833341 19937133139022786933562503)
      ·
        refine ⟨29905699708534180400343755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19937133139022786933562503 29905699708534180400343755)
        ·
          refine ⟨44858549562801270600515633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29905699708534180400343755 44858549562801270600515633)
          ·
            refine ⟨33643912172100952950386725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44858549562801270600515633 33643912172100952950386725)
            ·
              refine ⟨6308233532268928678197511, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 33643912172100952950386725 6308233532268928678197511)
              ·
                refine ⟨9462350298403393017296267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6308233532268928678197511 9462350298403393017296267)
                ·
                  refine ⟨14193525447605089525944401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9462350298403393017296267 14193525447605089525944401)
                  ·
                    refine ⟨10645144085703817144458301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14193525447605089525944401 10645144085703817144458301)
                    ·
                      refine ⟨3991929032138931429171863, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10645144085703817144458301 3991929032138931429171863)
                      ·
                        rfl

theorem cell23_7774254_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 2, 4, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 2, 4, 1, 1, 2, 3].length) (baseStart_7774254 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7774254 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7774254 prefixEnd_7774254 := by exact prefixLift 7774254
  have htrace : WordTrace (prefixWord ++ tailWord_7774254) baseStart_7774254 baseEnd_7774254 := by
    simpa [prefixWord, tailWord_7774254, baseEnd_7774254] using wordTrace_append hprefix tailTrace_7774254
  have hstable : (prefixWord ++ tailWord_7774254).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7774254).length < 2 ^ (prefixWord ++ tailWord_7774254).sum := by decide
  have hdescent : baseEnd_7774254 < baseStart_7774254 := by decide
  rcases family_descends (prefixWord ++ tailWord_7774254) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7774302 : List Nat := [4, 4, 1, 1, 2, 2, 1, 3, 1, 2, 2]
def baseStart_7774302 : Nat := 118140960795 + 7774302 * 2 ^ 59
def prefixEnd_7774302 : Nat := 4983230072969 + 3 ^ 40 * 7774302 * 2
def baseEnd_7774302 : Nat := 3991953679210347241371643

theorem tailTrace_7774302 : CollatzResearch.WordTrace tailWord_7774302 prefixEnd_7774302 3991953679210347241371643 := by
  unfold tailWord_7774302
  simp only [CollatzResearch.WordTrace]
  refine ⟨35444011085129884239940645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 189034725787359382613016773 35444011085129884239940645)
  ·
    refine ⟨6645752078461853294988871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 35444011085129884239940645 6645752078461853294988871)
    ·
      refine ⟨9968628117692779942483307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6645752078461853294988871 9968628117692779942483307)
      ·
        refine ⟨14952942176539169913724961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9968628117692779942483307 14952942176539169913724961)
        ·
          refine ⟨11214706632404377435293721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14952942176539169913724961 11214706632404377435293721)
          ·
            refine ⟨8411029974303283076470291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11214706632404377435293721 8411029974303283076470291)
            ·
              refine ⟨12616544961454924614705437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8411029974303283076470291 12616544961454924614705437)
              ·
                refine ⟨4731204360545596730514539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12616544961454924614705437 4731204360545596730514539)
                ·
                  refine ⟨7096806540818395095771809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4731204360545596730514539 7096806540818395095771809)
                  ·
                    refine ⟨5322604905613796321828857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7096806540818395095771809 5322604905613796321828857)
                    ·
                      refine ⟨3991953679210347241371643, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5322604905613796321828857 3991953679210347241371643)
                      ·
                        rfl

theorem cell23_7774302_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 2, 2, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 2, 2, 1, 3, 1, 2, 2].length) (baseStart_7774302 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7774302 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7774302 prefixEnd_7774302 := by exact prefixLift 7774302
  have htrace : WordTrace (prefixWord ++ tailWord_7774302) baseStart_7774302 baseEnd_7774302 := by
    simpa [prefixWord, tailWord_7774302, baseEnd_7774302] using wordTrace_append hprefix tailTrace_7774302
  have hstable : (prefixWord ++ tailWord_7774302).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7774302).length < 2 ^ (prefixWord ++ tailWord_7774302).sum := by decide
  have hdescent : baseEnd_7774302 < baseStart_7774302 := by decide
  rcases family_descends (prefixWord ++ tailWord_7774302) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7774303 : List Nat := [1, 1, 2, 3, 1, 1, 2, 2, 4, 2, 4]
def baseStart_7774303 : Nat := 118140960795 + 7774303 * 2 ^ 59
def prefixEnd_7774303 : Nat := 4983230072969 + 3 ^ 40 * 7774303 * 2
def baseEnd_7774303 : Nat := 3991954192691001737459137

theorem tailTrace_7774303 : CollatzResearch.WordTrace tailWord_7774303 prefixEnd_7774303 3991954192691001737459137 := by
  unfold tailWord_7774303
  simp only [CollatzResearch.WordTrace]
  refine ⟨283552125154035451090311563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189034750102690300726874375 283552125154035451090311563)
  ·
    refine ⟨425328187731053176635467345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 283552125154035451090311563 425328187731053176635467345)
    ·
      refine ⟨318996140798289882476600509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 425328187731053176635467345 318996140798289882476600509)
      ·
        refine ⟨119623552799358705928725191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 318996140798289882476600509 119623552799358705928725191)
        ·
          refine ⟨179435329199038058893087787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 119623552799358705928725191 179435329199038058893087787)
          ·
            refine ⟨269152993798557088339631681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 179435329199038058893087787 269152993798557088339631681)
            ·
              refine ⟨201864745348917816254723761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 269152993798557088339631681 201864745348917816254723761)
              ·
                refine ⟨151398559011688362191042821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 201864745348917816254723761 151398559011688362191042821)
                ·
                  refine ⟨28387229814691567910820529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 151398559011688362191042821 28387229814691567910820529)
                  ·
                    refine ⟨21290422361018675933115397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 28387229814691567910820529 21290422361018675933115397)
                    ·
                      refine ⟨3991954192691001737459137, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21290422361018675933115397 3991954192691001737459137)
                      ·
                        rfl

theorem cell23_7774303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 2, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 2, 2, 4, 2, 4].length) (baseStart_7774303 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7774303 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7774303 prefixEnd_7774303 := by exact prefixLift 7774303
  have htrace : WordTrace (prefixWord ++ tailWord_7774303) baseStart_7774303 baseEnd_7774303 := by
    simpa [prefixWord, tailWord_7774303, baseEnd_7774303] using wordTrace_append hprefix tailTrace_7774303
  have hstable : (prefixWord ++ tailWord_7774303).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7774303).length < 2 ^ (prefixWord ++ tailWord_7774303).sum := by decide
  have hdescent : baseEnd_7774303 < baseStart_7774303 := by decide
  rcases family_descends (prefixWord ++ tailWord_7774303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7774307 : List Nat := [1, 1, 1, 5, 1, 1, 3, 2, 4, 2, 2]
def baseStart_7774307 : Nat := 118140960795 + 7774307 * 2 ^ 59
def prefixEnd_7774307 : Nat := 4983230072969 + 3 ^ 40 * 7774307 * 2
def baseEnd_7774307 : Nat := 3991956246613619721809119

theorem tailTrace_7774307 : CollatzResearch.WordTrace tailWord_7774307 prefixEnd_7774307 3991956246613619721809119 := by
  unfold tailWord_7774307
  simp only [CollatzResearch.WordTrace]
  refine ⟨283552271046020959773457175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189034847364013973182304783 283552271046020959773457175)
  ·
    refine ⟨425328406569031439660185763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 283552271046020959773457175 425328406569031439660185763)
    ·
      refine ⟨637992609853547159490278645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 425328406569031439660185763 637992609853547159490278645)
      ·
        refine ⟨59811807173770046202213623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 637992609853547159490278645 59811807173770046202213623)
        ·
          refine ⟨89717710760655069303320435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59811807173770046202213623 89717710760655069303320435)
          ·
            refine ⟨134576566140982603954980653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89717710760655069303320435 134576566140982603954980653)
            ·
              refine ⟨50466212302868476483117745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 134576566140982603954980653 50466212302868476483117745)
              ·
                refine ⟨37849659227151357362338309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50466212302868476483117745 37849659227151357362338309)
                ·
                  refine ⟨7096811105090879505438433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 37849659227151357362338309 7096811105090879505438433)
                  ·
                    refine ⟨5322608328818159629078825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7096811105090879505438433 5322608328818159629078825)
                    ·
                      refine ⟨3991956246613619721809119, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5322608328818159629078825 3991956246613619721809119)
                      ·
                        rfl

theorem cell23_7774307_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 3, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 3, 2, 4, 2, 2].length) (baseStart_7774307 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7774307 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7774307 prefixEnd_7774307 := by exact prefixLift 7774307
  have htrace : WordTrace (prefixWord ++ tailWord_7774307) baseStart_7774307 baseEnd_7774307 := by
    simpa [prefixWord, tailWord_7774307, baseEnd_7774307] using wordTrace_append hprefix tailTrace_7774307
  have hstable : (prefixWord ++ tailWord_7774307).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7774307).length < 2 ^ (prefixWord ++ tailWord_7774307).sum := by decide
  have hdescent : baseEnd_7774307 < baseStart_7774307 := by decide
  rcases family_descends (prefixWord ++ tailWord_7774307) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7774340 : List Nat := [2, 3, 2, 1, 2, 1, 2, 1, 1, 5, 3]
def baseStart_7774340 : Nat := 118140960795 + 7774340 * 2 ^ 59
def prefixEnd_7774340 : Nat := 4983230072969 + 3 ^ 40 * 7774340 * 2
def baseEnd_7774340 : Nat := 3991973191475218092696467

theorem tailTrace_7774340 : CollatzResearch.WordTrace tailWord_7774340 prefixEnd_7774340 3991973191475218092696467 := by
  unfold tailWord_7774340
  simp only [CollatzResearch.WordTrace]
  refine ⟨141776737327450703204704237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 189035649769934270939605649 141776737327450703204704237)
  ·
    refine ⟨53166276497794013701764089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 141776737327450703204704237 53166276497794013701764089)
    ·
      refine ⟨39874707373345510276323067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53166276497794013701764089 39874707373345510276323067)
      ·
        refine ⟨59812061060018265414484601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39874707373345510276323067 59812061060018265414484601)
        ·
          refine ⟨44859045795013699060863451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59812061060018265414484601 44859045795013699060863451)
          ·
            refine ⟨67288568692520548591295177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44859045795013699060863451 67288568692520548591295177)
            ·
              refine ⟨50466426519390411443471383, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 67288568692520548591295177 50466426519390411443471383)
              ·
                refine ⟨75699639779085617165207075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50466426519390411443471383 75699639779085617165207075)
                ·
                  refine ⟨113549459668628425747810613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 75699639779085617165207075 113549459668628425747810613)
                  ·
                    refine ⟨10645261843933914913857245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 113549459668628425747810613 10645261843933914913857245)
                    ·
                      refine ⟨3991973191475218092696467, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10645261843933914913857245 3991973191475218092696467)
                      ·
                        rfl

theorem cell23_7774340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 2, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 2, 1, 1, 5, 3].length) (baseStart_7774340 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7774340 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7774340 prefixEnd_7774340 := by exact prefixLift 7774340
  have htrace : WordTrace (prefixWord ++ tailWord_7774340) baseStart_7774340 baseEnd_7774340 := by
    simpa [prefixWord, tailWord_7774340, baseEnd_7774340] using wordTrace_append hprefix tailTrace_7774340
  have hstable : (prefixWord ++ tailWord_7774340).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7774340).length < 2 ^ (prefixWord ++ tailWord_7774340).sum := by decide
  have hdescent : baseEnd_7774340 < baseStart_7774340 := by decide
  rcases family_descends (prefixWord ++ tailWord_7774340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7774341 : List Nat := [1, 3, 1, 1, 5, 1, 4, 1, 2, 2, 2]
def baseStart_7774341 : Nat := 118140960795 + 7774341 * 2 ^ 59
def prefixEnd_7774341 : Nat := 4983230072969 + 3 ^ 40 * 7774341 * 2
def baseEnd_7774341 : Nat := 3991973704955872588783963

theorem tailTrace_7774341 : CollatzResearch.WordTrace tailWord_7774341 prefixEnd_7774341 3991973704955872588783963 := by
  unfold tailWord_7774341
  simp only [CollatzResearch.WordTrace]
  refine ⟨283553511127897783580194877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189035674085265189053463251 283553511127897783580194877)
  ·
    refine ⟨106332566672961668842573079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 283553511127897783580194877 106332566672961668842573079)
    ·
      refine ⟨159498850009442503263859619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106332566672961668842573079 159498850009442503263859619)
      ·
        refine ⟨239248275014163754895789429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 159498850009442503263859619 239248275014163754895789429)
        ·
          refine ⟨22429525782577852021480259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 239248275014163754895789429 22429525782577852021480259)
          ·
            refine ⟨33644288673866778032220389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22429525782577852021480259 33644288673866778032220389)
            ·
              refine ⟨6308304126350020881041323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 33644288673866778032220389 6308304126350020881041323)
              ·
                refine ⟨9462456189525031321561985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6308304126350020881041323 9462456189525031321561985)
                ·
                  refine ⟨7096842142143773491171489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9462456189525031321561985 7096842142143773491171489)
                  ·
                    refine ⟨5322631606607830118378617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7096842142143773491171489 5322631606607830118378617)
                    ·
                      refine ⟨3991973704955872588783963, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5322631606607830118378617 3991973704955872588783963)
                      ·
                        rfl

theorem cell23_7774341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 1, 4, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 1, 4, 1, 2, 2, 2].length) (baseStart_7774341 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7774341 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7774341 prefixEnd_7774341 := by exact prefixLift 7774341
  have htrace : WordTrace (prefixWord ++ tailWord_7774341) baseStart_7774341 baseEnd_7774341 := by
    simpa [prefixWord, tailWord_7774341, baseEnd_7774341] using wordTrace_append hprefix tailTrace_7774341
  have hstable : (prefixWord ++ tailWord_7774341).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7774341).length < 2 ^ (prefixWord ++ tailWord_7774341).sum := by decide
  have hdescent : baseEnd_7774341 < baseStart_7774341 := by decide
  rcases family_descends (prefixWord ++ tailWord_7774341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7774343 : List Nat := [1, 1, 4, 2, 1, 1, 2, 1, 3, 7]
def baseStart_7774343 : Nat := 118140960795 + 7774343 * 2 ^ 59
def prefixEnd_7774343 : Nat := 4983230072969 + 3 ^ 40 * 7774343 * 2
def baseEnd_7774343 : Nat := 1330658243972393860319651

theorem tailTrace_7774343 : CollatzResearch.WordTrace tailWord_7774343 prefixEnd_7774343 1330658243972393860319651 := by
  unfold tailWord_7774343
  simp only [CollatzResearch.WordTrace]
  refine ⟨283553584073890537921767683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189035722715927025281178455 283553584073890537921767683)
  ·
    refine ⟨425330376110835806882651525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 283553584073890537921767683 425330376110835806882651525)
    ·
      refine ⟨79749445520781713790497161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 425330376110835806882651525 79749445520781713790497161)
      ·
        refine ⟨59812084140586285342872871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79749445520781713790497161 59812084140586285342872871)
        ·
          refine ⟨89718126210879428014309307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59812084140586285342872871 89718126210879428014309307)
          ·
            refine ⟨134577189316319142021463961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89718126210879428014309307 134577189316319142021463961)
            ·
              refine ⟨100932891987239356516097971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 134577189316319142021463961 100932891987239356516097971)
              ·
                refine ⟨151399337980859034774146957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 100932891987239356516097971 151399337980859034774146957)
                ·
                  refine ⟨56774751742822138040305109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 151399337980859034774146957 56774751742822138040305109)
                  ·
                    refine ⟨1330658243972393860319651, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 56774751742822138040305109 1330658243972393860319651)
                    ·
                      rfl

theorem cell23_7774343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 2, 1, 3, 7].length) (baseStart_7774343 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7774343 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7774343 prefixEnd_7774343 := by exact prefixLift 7774343
  have htrace : WordTrace (prefixWord ++ tailWord_7774343) baseStart_7774343 baseEnd_7774343 := by
    simpa [prefixWord, tailWord_7774343, baseEnd_7774343] using wordTrace_append hprefix tailTrace_7774343
  have hstable : (prefixWord ++ tailWord_7774343).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7774343).length < 2 ^ (prefixWord ++ tailWord_7774343).sum := by decide
  have hdescent : baseEnd_7774343 < baseStart_7774343 := by decide
  rcases family_descends (prefixWord ++ tailWord_7774343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7774381 : List Nat := [1, 5, 2, 1, 2, 3, 2, 2, 5]
def baseStart_7774381 : Nat := 118140960795 + 7774381 * 2 ^ 59
def prefixEnd_7774381 : Nat := 4983230072969 + 3 ^ 40 * 7774381 * 2
def baseEnd_7774381 : Nat := 443554916020228048031531

theorem tailTrace_7774381 : CollatzResearch.WordTrace tailWord_7774381 prefixEnd_7774381 443554916020228048031531 := by
  unfold tailWord_7774381
  simp only [CollatzResearch.WordTrace]
  refine ⟨283554970047752870411650997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189036646698501913607767331 283554970047752870411650997)
  ·
    refine ⟨26583278441976831601092281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 283554970047752870411650997 26583278441976831601092281)
    ·
      refine ⟨19937458831482623700819211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26583278441976831601092281 19937458831482623700819211)
      ·
        refine ⟨29906188247223935551228817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19937458831482623700819211 29906188247223935551228817)
        ·
          refine ⟨22429641185417951663421613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29906188247223935551228817 22429641185417951663421613)
          ·
            refine ⟨8411115444531731873783105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22429641185417951663421613 8411115444531731873783105)
            ·
              refine ⟨6308336583398798905337329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8411115444531731873783105 6308336583398798905337329)
              ·
                refine ⟨4731252437549099179002997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6308336583398798905337329 4731252437549099179002997)
                ·
                  refine ⟨443554916020228048031531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4731252437549099179002997 443554916020228048031531)
                  ·
                    rfl

theorem cell23_7774381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 3, 2, 2, 5].length) (baseStart_7774381 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7774381 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7774381 prefixEnd_7774381 := by exact prefixLift 7774381
  have htrace : WordTrace (prefixWord ++ tailWord_7774381) baseStart_7774381 baseEnd_7774381 := by
    simpa [prefixWord, tailWord_7774381, baseEnd_7774381] using wordTrace_append hprefix tailTrace_7774381
  have hstable : (prefixWord ++ tailWord_7774381).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7774381).length < 2 ^ (prefixWord ++ tailWord_7774381).sum := by decide
  have hdescent : baseEnd_7774381 < baseStart_7774381 := by decide
  rcases family_descends (prefixWord ++ tailWord_7774381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7774383 : List Nat := [1, 1, 2, 1, 2, 3, 1, 1, 1, 5, 5]
def baseStart_7774383 : Nat := 118140960795 + 7774383 * 2 ^ 59
def prefixEnd_7774383 : Nat := 4983230072969 + 3 ^ 40 * 7774383 * 2
def baseEnd_7774383 : Nat := 3991995271143361424458769

theorem tailTrace_7774383 : CollatzResearch.WordTrace tailWord_7774383 prefixEnd_7774383 3991995271143361424458769 := by
  unfold tailWord_7774383
  simp only [CollatzResearch.WordTrace]
  refine ⟨283555042993745624753223803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189036695329163749835482535 283555042993745624753223803)
  ·
    refine ⟨425332564490618437129835705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 283555042993745624753223803 425332564490618437129835705)
    ·
      refine ⟨318999423367963827847376779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 425332564490618437129835705 318999423367963827847376779)
      ·
        refine ⟨478499135051945741771065169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 318999423367963827847376779 478499135051945741771065169)
        ·
          refine ⟨358874351288959306328298877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 478499135051945741771065169 358874351288959306328298877)
          ·
            refine ⟨134577881733359739873112079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 358874351288959306328298877 134577881733359739873112079)
            ·
              refine ⟨201866822600039609809668119, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 134577881733359739873112079 201866822600039609809668119)
              ·
                refine ⟨302800233900059414714502179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 201866822600039609809668119 302800233900059414714502179)
                ·
                  refine ⟨454200350850089122071753269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 302800233900059414714502179 454200350850089122071753269)
                  ·
                    refine ⟨42581282892195855194226869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 454200350850089122071753269 42581282892195855194226869)
                    ·
                      refine ⟨3991995271143361424458769, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 42581282892195855194226869 3991995271143361424458769)
                      ·
                        rfl

theorem cell23_7774383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 1, 1, 1, 5, 5].length) (baseStart_7774383 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7774383 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7774383 prefixEnd_7774383 := by exact prefixLift 7774383
  have htrace : WordTrace (prefixWord ++ tailWord_7774383) baseStart_7774383 baseEnd_7774383 := by
    simpa [prefixWord, tailWord_7774383, baseEnd_7774383] using wordTrace_append hprefix tailTrace_7774383
  have hstable : (prefixWord ++ tailWord_7774383).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7774383).length < 2 ^ (prefixWord ++ tailWord_7774383).sum := by decide
  have hdescent : baseEnd_7774383 < baseStart_7774383 := by decide
  rcases family_descends (prefixWord ++ tailWord_7774383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7774414 : List Nat := [4, 1, 1, 1, 4, 3, 1, 1, 2, 1, 4]
def baseStart_7774414 : Nat := 118140960795 + 7774414 * 2 ^ 59
def prefixEnd_7774414 : Nat := 4983230072969 + 3 ^ 40 * 7774414 * 2
def baseEnd_7774414 : Nat := 3992011189043650803171127

theorem tailTrace_7774414 : CollatzResearch.WordTrace tailWord_7774414 prefixEnd_7774414 3992011189043650803171127 := by
  unfold tailWord_7774414
  simp only [CollatzResearch.WordTrace]
  refine ⟨35444521707079164630950287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 189037449104422211365068197 35444521707079164630950287)
  ·
    refine ⟨53166782560618746946425431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35444521707079164630950287 53166782560618746946425431)
    ·
      refine ⟨79750173840928120419638147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53166782560618746946425431 79750173840928120419638147)
      ·
        refine ⟨119625260761392180629457221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79750173840928120419638147 119625260761392180629457221)
        ·
          refine ⟨22429736392761033868023229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 119625260761392180629457221 22429736392761033868023229)
          ·
            refine ⟨8411151147285387700508711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22429736392761033868023229 8411151147285387700508711)
            ·
              refine ⟨12616726720928081550763067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8411151147285387700508711 12616726720928081550763067)
              ·
                refine ⟨18925090081392122326144601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12616726720928081550763067 18925090081392122326144601)
                ·
                  refine ⟨14193817561044091744608451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18925090081392122326144601 14193817561044091744608451)
                  ·
                    refine ⟨21290726341566137616912677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14193817561044091744608451 21290726341566137616912677)
                    ·
                      refine ⟨3992011189043650803171127, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21290726341566137616912677 3992011189043650803171127)
                      ·
                        rfl

theorem cell23_7774414_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 3, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 3, 1, 1, 2, 1, 4].length) (baseStart_7774414 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7774414 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7774414 prefixEnd_7774414 := by exact prefixLift 7774414
  have htrace : WordTrace (prefixWord ++ tailWord_7774414) baseStart_7774414 baseEnd_7774414 := by
    simpa [prefixWord, tailWord_7774414, baseEnd_7774414] using wordTrace_append hprefix tailTrace_7774414
  have hstable : (prefixWord ++ tailWord_7774414).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7774414).length < 2 ^ (prefixWord ++ tailWord_7774414).sum := by decide
  have hdescent : baseEnd_7774414 < baseStart_7774414 := by decide
  rcases family_descends (prefixWord ++ tailWord_7774414) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7774417 : List Nat := [1, 2, 2, 1, 2, 2, 5, 1, 2, 2, 3]
def baseStart_7774417 : Nat := 118140960795 + 7774417 * 2 ^ 59
def prefixEnd_7774417 : Nat := 4983230072969 + 3 ^ 40 * 7774417 * 2
def baseEnd_7774417 : Nat := 3992012729485614291433613

theorem tailTrace_7774417 : CollatzResearch.WordTrace tailWord_7774417 prefixEnd_7774417 3992012729485614291433613 := by
  unfold tailWord_7774417
  simp only [CollatzResearch.WordTrace]
  refine ⟨283556283075622448559961505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189037522050414965706641003 283556283075622448559961505)
  ·
    refine ⟨212667212306716836419971129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 283556283075622448559961505 212667212306716836419971129)
    ·
      refine ⟨159500409230037627314978347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 212667212306716836419971129 159500409230037627314978347)
      ·
        refine ⟨239250613845056440972467521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 159500409230037627314978347 239250613845056440972467521)
        ·
          refine ⟨179437960383792330729350641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 239250613845056440972467521 179437960383792330729350641)
          ·
            refine ⟨134578470287844248047012981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 179437960383792330729350641 134578470287844248047012981)
            ·
              refine ⟨12616731589485398254407467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 134578470287844248047012981 12616731589485398254407467)
              ·
                refine ⟨18925097384228097381611201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12616731589485398254407467 18925097384228097381611201)
                ·
                  refine ⟨14193823038171073036208401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18925097384228097381611201 14193823038171073036208401)
                  ·
                    refine ⟨10645367278628304777156301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14193823038171073036208401 10645367278628304777156301)
                    ·
                      refine ⟨3992012729485614291433613, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10645367278628304777156301 3992012729485614291433613)
                      ·
                        rfl

theorem cell23_7774417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 5, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 5, 1, 2, 2, 3].length) (baseStart_7774417 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7774417 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7774417 prefixEnd_7774417 := by exact prefixLift 7774417
  have htrace : WordTrace (prefixWord ++ tailWord_7774417) baseStart_7774417 baseEnd_7774417 := by
    simpa [prefixWord, tailWord_7774417, baseEnd_7774417] using wordTrace_append hprefix tailTrace_7774417
  have hstable : (prefixWord ++ tailWord_7774417).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7774417).length < 2 ^ (prefixWord ++ tailWord_7774417).sum := by decide
  have hdescent : baseEnd_7774417 < baseStart_7774417 := by decide
  rcases family_descends (prefixWord ++ tailWord_7774417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7774424 : List Nat := [2, 1, 2, 2, 4, 1, 1, 5, 1, 4]
def baseStart_7774424 : Nat := 118140960795 + 7774424 * 2 ^ 59
def prefixEnd_7774424 : Nat := 4983230072969 + 3 ^ 40 * 7774424 * 2
def baseEnd_7774424 : Nat := 1330672107950065254682027

theorem tailTrace_7774424 : CollatzResearch.WordTrace tailWord_7774424 prefixEnd_7774424 1330672107950065254682027 := by
  unfold tailWord_7774424
  simp only [CollatzResearch.WordTrace]
  refine ⟨141778269193298544377733163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 189037692257731392503644217 141778269193298544377733163)
  ·
    refine ⟨212667403789947816566599745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141778269193298544377733163 212667403789947816566599745)
    ·
      refine ⟨159500552842460862424949809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 212667403789947816566599745 159500552842460862424949809)
      ·
        refine ⟨119625414631845646818712357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 159500552842460862424949809 119625414631845646818712357)
        ·
          refine ⟨22429765243471058778508567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 119625414631845646818712357 22429765243471058778508567)
          ·
            refine ⟨33644647865206588167762851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22429765243471058778508567 33644647865206588167762851)
            ·
              refine ⟨50466971797809882251644277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33644647865206588167762851 50466971797809882251644277)
              ·
                refine ⟨4731278606044676461091651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 50466971797809882251644277 4731278606044676461091651)
                ·
                  refine ⟨7096917909067014691637477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4731278606044676461091651 7096917909067014691637477)
                  ·
                    refine ⟨1330672107950065254682027, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7096917909067014691637477 1330672107950065254682027)
                    ·
                      rfl

theorem cell23_7774424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 1, 1, 5, 1, 4].length) (baseStart_7774424 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7774424 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7774424 prefixEnd_7774424 := by exact prefixLift 7774424
  have htrace : WordTrace (prefixWord ++ tailWord_7774424) baseStart_7774424 baseEnd_7774424 := by
    simpa [prefixWord, tailWord_7774424, baseEnd_7774424] using wordTrace_append hprefix tailTrace_7774424
  have hstable : (prefixWord ++ tailWord_7774424).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7774424).length < 2 ^ (prefixWord ++ tailWord_7774424).sum := by decide
  have hdescent : baseEnd_7774424 < baseStart_7774424 := by decide
  rcases family_descends (prefixWord ++ tailWord_7774424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7774437 : List Nat := [1, 3, 1, 4, 2, 1, 3, 2, 6]
def baseStart_7774437 : Nat := 118140960795 + 7774437 * 2 ^ 59
def prefixEnd_7774437 : Nat := 4983230072969 + 3 ^ 40 * 7774437 * 2
def baseEnd_7774437 : Nat := 443558111010967134798169

theorem tailTrace_7774437 : CollatzResearch.WordTrace tailWord_7774437 prefixEnd_7774437 443558111010967134798169 := by
  unfold tailWord_7774437
  simp only [CollatzResearch.WordTrace]
  refine ⟨283557012535549991975689565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189038008357033327983793043 283557012535549991975689565)
  ·
    refine ⟨106333879700831246990883587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 283557012535549991975689565 106333879700831246990883587)
    ·
      refine ⟨159500819551246870486325381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106333879700831246990883587 159500819551246870486325381)
      ·
        refine ⟨29906403665858788216186009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 159500819551246870486325381 29906403665858788216186009)
        ·
          refine ⟨22429802749394091162139507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29906403665858788216186009 22429802749394091162139507)
          ·
            refine ⟨33644704124091136743209261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22429802749394091162139507 33644704124091136743209261)
            ·
              refine ⟨12616764046534176278703473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33644704124091136743209261 12616764046534176278703473)
              ·
                refine ⟨9462573034900632209027605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12616764046534176278703473 9462573034900632209027605)
                ·
                  refine ⟨443558111010967134798169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9462573034900632209027605 443558111010967134798169)
                  ·
                    rfl

theorem cell23_7774437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 1, 3, 2, 6].length) (baseStart_7774437 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7774437 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7774437 prefixEnd_7774437 := by exact prefixLift 7774437
  have htrace : WordTrace (prefixWord ++ tailWord_7774437) baseStart_7774437 baseEnd_7774437 := by
    simpa [prefixWord, tailWord_7774437, baseEnd_7774437] using wordTrace_append hprefix tailTrace_7774437
  have hstable : (prefixWord ++ tailWord_7774437).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7774437).length < 2 ^ (prefixWord ++ tailWord_7774437).sum := by decide
  have hdescent : baseEnd_7774437 < baseStart_7774437 := by decide
  rcases family_descends (prefixWord ++ tailWord_7774437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7774440 : List Nat := [2, 1, 4, 1, 2, 2, 1, 1, 1, 2, 6]
def baseStart_7774440 : Nat := 118140960795 + 7774440 * 2 ^ 59
def prefixEnd_7774440 : Nat := 4983230072969 + 3 ^ 40 * 7774440 * 2
def baseEnd_7774440 : Nat := 3992024539540667701446007

theorem tailTrace_7774440 : CollatzResearch.WordTrace tailWord_7774440 prefixEnd_7774440 3992024539540667701446007 := by
  unfold tailWord_7774440
  simp only [CollatzResearch.WordTrace]
  refine ⟨141778560977269561744024387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 189038081303026082325365849 141778560977269561744024387)
  ·
    refine ⟨212667841465904342616036581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141778560977269561744024387 212667841465904342616036581)
    ·
      refine ⟨39875220274857064240506859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 212667841465904342616036581 39875220274857064240506859)
      ·
        refine ⟨59812830412285596360760289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39875220274857064240506859 59812830412285596360760289)
        ·
          refine ⟨44859622809214197270570217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59812830412285596360760289 44859622809214197270570217)
          ·
            refine ⟨33644717106910647952927663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44859622809214197270570217 33644717106910647952927663)
            ·
              refine ⟨50467075660365971929391495, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33644717106910647952927663 50467075660365971929391495)
              ·
                refine ⟨75700613490548957894087243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50467075660365971929391495 75700613490548957894087243)
                ·
                  refine ⟨113550920235823436841130865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 75700613490548957894087243 113550920235823436841130865)
                  ·
                    refine ⟨85163190176867577630848149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 113550920235823436841130865 85163190176867577630848149)
                    ·
                      refine ⟨3992024539540667701446007, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 85163190176867577630848149 3992024539540667701446007)
                      ·
                        rfl

theorem cell23_7774440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 2, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 2, 1, 1, 1, 2, 6].length) (baseStart_7774440 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7774440 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7774440 prefixEnd_7774440 := by exact prefixLift 7774440
  have htrace : WordTrace (prefixWord ++ tailWord_7774440) baseStart_7774440 baseEnd_7774440 := by
    simpa [prefixWord, tailWord_7774440, baseEnd_7774440] using wordTrace_append hprefix tailTrace_7774440
  have hstable : (prefixWord ++ tailWord_7774440).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7774440).length < 2 ^ (prefixWord ++ tailWord_7774440).sum := by decide
  have hdescent : baseEnd_7774440 < baseStart_7774440 := by decide
  rcases family_descends (prefixWord ++ tailWord_7774440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7774457 : List Nat := [1, 2, 1, 3, 1, 1, 2, 1, 6, 3, 2]
def baseStart_7774457 : Nat := 118140960795 + 7774457 * 2 ^ 59
def prefixEnd_7774457 : Nat := 4983230072969 + 3 ^ 40 * 7774457 * 2
def baseEnd_7774457 : Nat := 3992033268711794134933429

theorem tailTrace_7774457 : CollatzResearch.WordTrace tailWord_7774457 prefixEnd_7774457 3992033268711794134933429 := by
  unfold tailWord_7774457
  simp only [CollatzResearch.WordTrace]
  refine ⟨283557741995477535391417625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189038494663651690260945083 283557741995477535391417625)
  ·
    refine ⟨212668306496608151543563219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 283557741995477535391417625 212668306496608151543563219)
    ·
      refine ⟨319002459744912227315344829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 212668306496608151543563219 319002459744912227315344829)
      ·
        refine ⟨119625922404342085243254311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 319002459744912227315344829 119625922404342085243254311)
        ·
          refine ⟨179438883606513127864881467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 119625922404342085243254311 179438883606513127864881467)
          ·
            refine ⟨269158325409769691797322201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 179438883606513127864881467 269158325409769691797322201)
            ·
              refine ⟨201868744057327268847991651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 269158325409769691797322201 201868744057327268847991651)
              ·
                refine ⟨302803116085990903271987477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 201868744057327268847991651 302803116085990903271987477)
                ·
                  refine ⟨14193896066530823590874413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 302803116085990903271987477 14193896066530823590874413)
                  ·
                    refine ⟨5322711024949058846577905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14193896066530823590874413 5322711024949058846577905)
                    ·
                      refine ⟨3992033268711794134933429, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5322711024949058846577905 3992033268711794134933429)
                      ·
                        rfl

theorem cell23_7774457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 2, 1, 6, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 2, 1, 6, 3, 2].length) (baseStart_7774457 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7774457 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7774457 prefixEnd_7774457 := by exact prefixLift 7774457
  have htrace : WordTrace (prefixWord ++ tailWord_7774457) baseStart_7774457 baseEnd_7774457 := by
    simpa [prefixWord, tailWord_7774457, baseEnd_7774457] using wordTrace_append hprefix tailTrace_7774457
  have hstable : (prefixWord ++ tailWord_7774457).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7774457).length < 2 ^ (prefixWord ++ tailWord_7774457).sum := by decide
  have hdescent : baseEnd_7774457 < baseStart_7774457 := by decide
  rcases family_descends (prefixWord ++ tailWord_7774457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7774467 : List Nat := [1, 1, 1, 3, 2, 3, 4, 2, 1, 5]
def baseStart_7774467 : Nat := 118140960795 + 7774467 * 2 ^ 59
def prefixEnd_7774467 : Nat := 4983230072969 + 3 ^ 40 * 7774467 * 2
def baseEnd_7774467 : Nat := 1330679467839446365269461

theorem tailTrace_7774467 : CollatzResearch.WordTrace tailWord_7774467 prefixEnd_7774467 1330679467839446365269461 := by
  unfold tailWord_7774467
  simp only [CollatzResearch.WordTrace]
  refine ⟨283558106725441307099281655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189038737816960871399521103 283558106725441307099281655)
  ·
    refine ⟨425337160088161960648922483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 283558106725441307099281655 425337160088161960648922483)
    ·
      refine ⟨638005740132242940973383725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 425337160088161960648922483 638005740132242940973383725)
      ·
        refine ⟨239252152549591102865018897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 638005740132242940973383725 239252152549591102865018897)
        ·
          refine ⟨179439114412193327148764173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 239252152549591102865018897 179439114412193327148764173)
          ·
            refine ⟨67289667904572497680786565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 179439114412193327148764173 67289667904572497680786565)
            ·
              refine ⟨12616812732107343315147481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 67289667904572497680786565 12616812732107343315147481)
              ·
                refine ⟨9462609549080507486360611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12616812732107343315147481 9462609549080507486360611)
                ·
                  refine ⟨14193914323620761229540917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9462609549080507486360611 14193914323620761229540917)
                  ·
                    refine ⟨1330679467839446365269461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14193914323620761229540917 1330679467839446365269461)
                    ·
                      rfl

theorem cell23_7774467_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 4, 2, 1, 5].length) (baseStart_7774467 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7774467 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7774467 prefixEnd_7774467 := by exact prefixLift 7774467
  have htrace : WordTrace (prefixWord ++ tailWord_7774467) baseStart_7774467 baseEnd_7774467 := by
    simpa [prefixWord, tailWord_7774467, baseEnd_7774467] using wordTrace_append hprefix tailTrace_7774467
  have hstable : (prefixWord ++ tailWord_7774467).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7774467).length < 2 ^ (prefixWord ++ tailWord_7774467).sum := by decide
  have hdescent : baseEnd_7774467 < baseStart_7774467 := by decide
  rcases family_descends (prefixWord ++ tailWord_7774467) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7774481 : List Nat := [1, 2, 2, 1, 1, 5, 3, 3, 1, 1, 3]
def baseStart_7774481 : Nat := 118140960795 + 7774481 * 2 ^ 59
def prefixEnd_7774481 : Nat := 4983230072969 + 3 ^ 40 * 7774481 * 2
def baseEnd_7774481 : Nat := 3992045592247502041033319

theorem tailTrace_7774481 : CollatzResearch.WordTrace tailWord_7774481 prefixEnd_7774481 3992045592247502041033319 := by
  unfold tailWord_7774481
  simp only [CollatzResearch.WordTrace]
  refine ⟨283558617347390587490291297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189039078231593724993527531 283558617347390587490291297)
  ·
    refine ⟨212668963010542940617718473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 283558617347390587490291297 212668963010542940617718473)
    ·
      refine ⟨159501722257907205463288855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 212668963010542940617718473 159501722257907205463288855)
      ·
        refine ⟨239252583386860808194933283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 159501722257907205463288855 239252583386860808194933283)
        ·
          refine ⟨358878875080291212292399925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 239252583386860808194933283 358878875080291212292399925)
          ·
            refine ⟨33644894538777301152412493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 358878875080291212292399925 33644894538777301152412493)
            ·
              refine ⟨12616835452041487932154685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33644894538777301152412493 12616835452041487932154685)
              ·
                refine ⟨4731313294515557974558007, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12616835452041487932154685 4731313294515557974558007)
                ·
                  refine ⟨7096969941773336961837011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4731313294515557974558007 7096969941773336961837011)
                  ·
                    refine ⟨10645454912660005442755517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7096969941773336961837011 10645454912660005442755517)
                    ·
                      refine ⟨3992045592247502041033319, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10645454912660005442755517 3992045592247502041033319)
                      ·
                        rfl

theorem cell23_7774481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 5, 3, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 5, 3, 3, 1, 1, 3].length) (baseStart_7774481 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7774481 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7774481 prefixEnd_7774481 := by exact prefixLift 7774481
  have htrace : WordTrace (prefixWord ++ tailWord_7774481) baseStart_7774481 baseEnd_7774481 := by
    simpa [prefixWord, tailWord_7774481, baseEnd_7774481] using wordTrace_append hprefix tailTrace_7774481
  have hstable : (prefixWord ++ tailWord_7774481).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7774481).length < 2 ^ (prefixWord ++ tailWord_7774481).sum := by decide
  have hdescent : baseEnd_7774481 < baseStart_7774481 := by decide
  rcases family_descends (prefixWord ++ tailWord_7774481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7774497 : List Nat := [1, 2, 3, 2, 1, 1, 4, 1, 4, 4]
def baseStart_7774497 : Nat := 118140960795 + 7774497 * 2 ^ 59
def prefixEnd_7774497 : Nat := 4983230072969 + 3 ^ 40 * 7774497 * 2
def baseEnd_7774497 : Nat := 1330684602645991326144415

theorem tailTrace_7774497 : CollatzResearch.WordTrace tailWord_7774497 prefixEnd_7774497 1330684602645991326144415 := by
  unfold tailWord_7774497
  simp only [CollatzResearch.WordTrace]
  refine ⟨283559200915332622222873745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189039467276888414815249163 283559200915332622222873745)
  ·
    refine ⟨212669400686499466667155309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 283559200915332622222873745 212669400686499466667155309)
    ·
      refine ⟨79751025257437300000183241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 212669400686499466667155309 79751025257437300000183241)
      ·
        refine ⟨59813268943077975000137431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79751025257437300000183241 59813268943077975000137431)
        ·
          refine ⟨89719903414616962500206147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59813268943077975000137431 89719903414616962500206147)
          ·
            refine ⟨134579855121925443750309221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89719903414616962500206147 134579855121925443750309221)
            ·
              refine ⟨25233722835361020703182979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 134579855121925443750309221 25233722835361020703182979)
              ·
                refine ⟨37850584253041531054774469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25233722835361020703182979 37850584253041531054774469)
                ·
                  refine ⟨7096984547445287072770213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 37850584253041531054774469 7096984547445287072770213)
                  ·
                    refine ⟨1330684602645991326144415, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7096984547445287072770213 1330684602645991326144415)
                    ·
                      rfl

theorem cell23_7774497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 4, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 4, 1, 4, 4].length) (baseStart_7774497 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7774497 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7774497 prefixEnd_7774497 := by exact prefixLift 7774497
  have htrace : WordTrace (prefixWord ++ tailWord_7774497) baseStart_7774497 baseEnd_7774497 := by
    simpa [prefixWord, tailWord_7774497, baseEnd_7774497] using wordTrace_append hprefix tailTrace_7774497
  have hstable : (prefixWord ++ tailWord_7774497).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7774497).length < 2 ^ (prefixWord ++ tailWord_7774497).sum := by decide
  have hdescent : baseEnd_7774497 < baseStart_7774497 := by decide
  rcases family_descends (prefixWord ++ tailWord_7774497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7774517 : List Nat := [1, 3, 3, 1, 2, 1, 2, 3, 1, 2, 4]
def baseStart_7774517 : Nat := 118140960795 + 7774517 * 2 ^ 59
def prefixEnd_7774517 : Nat := 4983230072969 + 3 ^ 40 * 7774517 * 2
def baseEnd_7774517 : Nat := 3992064077551063900183153

theorem tailTrace_7774517 : CollatzResearch.WordTrace tailWord_7774517 prefixEnd_7774517 3992064077551063900183153 := by
  unfold tailWord_7774517
  simp only [CollatzResearch.WordTrace]
  refine ⟨283559930375260165638601805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189039953583506777092401203 283559930375260165638601805)
  ·
    refine ⟨106334973890722562114475677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 283559930375260165638601805 106334973890722562114475677)
    ·
      refine ⟨39875615209020960792928379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 106334973890722562114475677 39875615209020960792928379)
      ·
        refine ⟨59813422813531441189392569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39875615209020960792928379 59813422813531441189392569)
        ·
          refine ⟨44860067110148580892044427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59813422813531441189392569 44860067110148580892044427)
          ·
            refine ⟨67290100665222871338066641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44860067110148580892044427 67290100665222871338066641)
            ·
              refine ⟨50467575498917153503549981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 67290100665222871338066641 50467575498917153503549981)
              ·
                refine ⟨18925340812093932563831243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 50467575498917153503549981 18925340812093932563831243)
                ·
                  refine ⟨28388011218140898845746865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18925340812093932563831243 28388011218140898845746865)
                  ·
                    refine ⟨21291008413605674134310149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 28388011218140898845746865 21291008413605674134310149)
                    ·
                      refine ⟨3992064077551063900183153, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21291008413605674134310149 3992064077551063900183153)
                      ·
                        rfl

theorem cell23_7774517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 2, 3, 1, 2, 4].length) (baseStart_7774517 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7774517 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7774517 prefixEnd_7774517 := by exact prefixLift 7774517
  have htrace : WordTrace (prefixWord ++ tailWord_7774517) baseStart_7774517 baseEnd_7774517 := by
    simpa [prefixWord, tailWord_7774517, baseEnd_7774517] using wordTrace_append hprefix tailTrace_7774517
  have hstable : (prefixWord ++ tailWord_7774517).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7774517).length < 2 ^ (prefixWord ++ tailWord_7774517).sum := by decide
  have hdescent : baseEnd_7774517 < baseStart_7774517 := by decide
  rcases family_descends (prefixWord ++ tailWord_7774517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7774521 : List Nat := [1, 2, 1, 6, 1, 3, 1, 2, 1, 1, 4]
def baseStart_7774521 : Nat := 118140960795 + 7774521 * 2 ^ 59
def prefixEnd_7774521 : Nat := 4983230072969 + 3 ^ 40 * 7774521 * 2
def baseEnd_7774521 : Nat := 3992066131473681884533135

theorem tailTrace_7774521 : CollatzResearch.WordTrace tailWord_7774521 prefixEnd_7774521 3992066131473681884533135 := by
  unfold tailWord_7774521
  simp only [CollatzResearch.WordTrace]
  refine ⟨283560076267245674321747417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189040050844830449547831611 283560076267245674321747417)
  ·
    refine ⟨212670057200434255741310563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 283560076267245674321747417 212670057200434255741310563)
    ·
      refine ⟨319005085800651383611965845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 212670057200434255741310563 319005085800651383611965845)
      ·
        refine ⟨14953363396905533606810899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 319005085800651383611965845 14953363396905533606810899)
        ·
          refine ⟨22430045095358300410216349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14953363396905533606810899 22430045095358300410216349)
          ·
            refine ⟨8411266910759362653831131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22430045095358300410216349 8411266910759362653831131)
            ·
              refine ⟨12616900366139043980746697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8411266910759362653831131 12616900366139043980746697)
              ·
                refine ⟨9462675274604282985560023, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12616900366139043980746697 9462675274604282985560023)
                ·
                  refine ⟨14194012911906424478340035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9462675274604282985560023 14194012911906424478340035)
                  ·
                    refine ⟨21291019367859636717510053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14194012911906424478340035 21291019367859636717510053)
                    ·
                      refine ⟨3992066131473681884533135, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21291019367859636717510053 3992066131473681884533135)
                      ·
                        rfl

theorem cell23_7774521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 3, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 3, 1, 2, 1, 1, 4].length) (baseStart_7774521 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7774521 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7774521 prefixEnd_7774521 := by exact prefixLift 7774521
  have htrace : WordTrace (prefixWord ++ tailWord_7774521) baseStart_7774521 baseEnd_7774521 := by
    simpa [prefixWord, tailWord_7774521, baseEnd_7774521] using wordTrace_append hprefix tailTrace_7774521
  have hstable : (prefixWord ++ tailWord_7774521).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7774521).length < 2 ^ (prefixWord ++ tailWord_7774521).sum := by decide
  have hdescent : baseEnd_7774521 < baseStart_7774521 := by decide
  rcases family_descends (prefixWord ++ tailWord_7774521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7774564 : List Nat := [2, 3, 1, 1, 3, 1, 1, 1, 5, 3, 2]
def baseStart_7774564 : Nat := 118140960795 + 7774564 * 2 ^ 59
def prefixEnd_7774564 : Nat := 4983230072969 + 3 ^ 40 * 7774564 * 2
def baseEnd_7774564 : Nat := 3992088211141825216295437

theorem tailTrace_7774564 : CollatzResearch.WordTrace tailWord_7774564 prefixEnd_7774564 3992088211141825216295437 := by
  unfold tailWord_7774564
  simp only [CollatzResearch.WordTrace]
  refine ⟨141780822303044946332781373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 189041096404059928443708497 141780822303044946332781373)
  ·
    refine ⟨53167808363641854874793015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 141780822303044946332781373 53167808363641854874793015)
    ·
      refine ⟨79751712545462782312189523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53167808363641854874793015 79751712545462782312189523)
      ·
        refine ⟨119627568818194173468284285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79751712545462782312189523 119627568818194173468284285)
        ·
          refine ⟨44860338306822815050606607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 119627568818194173468284285 44860338306822815050606607)
          ·
            refine ⟨67290507460234222575909911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44860338306822815050606607 67290507460234222575909911)
            ·
              refine ⟨100935761190351333863864867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67290507460234222575909911 100935761190351333863864867)
              ·
                refine ⟨151403641785527000795797301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 100935761190351333863864867 151403641785527000795797301)
                ·
                  refine ⟨14194091417393156324605997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 151403641785527000795797301 14194091417393156324605997)
                  ·
                    refine ⟨5322784281522433621727249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14194091417393156324605997 5322784281522433621727249)
                    ·
                      refine ⟨3992088211141825216295437, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5322784281522433621727249 3992088211141825216295437)
                      ·
                        rfl

theorem cell23_7774564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 1, 1, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 1, 1, 5, 3, 2].length) (baseStart_7774564 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7774564 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7774564 prefixEnd_7774564 := by exact prefixLift 7774564
  have htrace : WordTrace (prefixWord ++ tailWord_7774564) baseStart_7774564 baseEnd_7774564 := by
    simpa [prefixWord, tailWord_7774564, baseEnd_7774564] using wordTrace_append hprefix tailTrace_7774564
  have hstable : (prefixWord ++ tailWord_7774564).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7774564).length < 2 ^ (prefixWord ++ tailWord_7774564).sum := by decide
  have hdescent : baseEnd_7774564 < baseStart_7774564 := by decide
  rcases family_descends (prefixWord ++ tailWord_7774564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7774581 : List Nat := [1, 3, 4, 1, 2, 1, 2, 1, 3, 3, 2]
def baseStart_7774581 : Nat := 118140960795 + 7774581 * 2 ^ 59
def prefixEnd_7774581 : Nat := 4983230072969 + 3 ^ 40 * 7774581 * 2
def baseEnd_7774581 : Nat := 3992096940312951649782859

theorem tailTrace_7774581 : CollatzResearch.WordTrace tailWord_7774581 prefixEnd_7774581 3992096940312951649782859 := by
  unfold tailWord_7774581
  simp only [CollatzResearch.WordTrace]
  refine ⟨283562264647028304568931597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189041509764685536379287731 283562264647028304568931597)
  ·
    refine ⟨106335849242635614213349349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 283562264647028304568931597 106335849242635614213349349)
    ·
      refine ⟨19937971732994177665003003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 106335849242635614213349349 19937971732994177665003003)
      ·
        refine ⟨29906957599491266497504505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19937971732994177665003003 29906957599491266497504505)
        ·
          refine ⟨22430218199618449873128379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29906957599491266497504505 22430218199618449873128379)
          ·
            refine ⟨33645327299427674809692569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22430218199618449873128379 33645327299427674809692569)
            ·
              refine ⟨25233995474570756107269427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33645327299427674809692569 25233995474570756107269427)
              ·
                refine ⟨37850993211856134160904141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25233995474570756107269427 37850993211856134160904141)
                ·
                  refine ⟨14194122454446050310339053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 37850993211856134160904141 14194122454446050310339053)
                  ·
                    refine ⟨5322795920417268866377145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14194122454446050310339053 5322795920417268866377145)
                    ·
                      refine ⟨3992096940312951649782859, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5322795920417268866377145 3992096940312951649782859)
                      ·
                        rfl

theorem cell23_7774581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 1, 2, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 1, 2, 1, 3, 3, 2].length) (baseStart_7774581 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7774581 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7774581 prefixEnd_7774581 := by exact prefixLift 7774581
  have htrace : WordTrace (prefixWord ++ tailWord_7774581) baseStart_7774581 baseEnd_7774581 := by
    simpa [prefixWord, tailWord_7774581, baseEnd_7774581] using wordTrace_append hprefix tailTrace_7774581
  have hstable : (prefixWord ++ tailWord_7774581).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7774581).length < 2 ^ (prefixWord ++ tailWord_7774581).sum := by decide
  have hdescent : baseEnd_7774581 < baseStart_7774581 := by decide
  rcases family_descends (prefixWord ++ tailWord_7774581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7774617 : List Nat := [1, 2, 1, 2, 1, 4, 4, 1, 7]
def baseStart_7774617 : Nat := 118140960795 + 7774617 * 2 ^ 59
def prefixEnd_7774617 : Nat := 4983230072969 + 3 ^ 40 * 7774617 * 2
def baseEnd_7774617 : Nat := 443568380624057056548077

theorem tailTrace_7774617 : CollatzResearch.WordTrace tailWord_7774617 prefixEnd_7774617 443568380624057056548077 := by
  unfold tailWord_7774617
  simp only [CollatzResearch.WordTrace]
  refine ⟨283563577674897882717242105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189042385116598588478161403 283563577674897882717242105)
  ·
    refine ⟨212672683256173412037931579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 283563577674897882717242105 212672683256173412037931579)
    ·
      refine ⟨319009024884260118056897369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 212672683256173412037931579 319009024884260118056897369)
      ·
        refine ⟨239256768663195088542673027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 319009024884260118056897369 239256768663195088542673027)
        ·
          refine ⟨358885152994792632814009541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 239256768663195088542673027 358885152994792632814009541)
          ·
            refine ⟨67290966186523618652626789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 358885152994792632814009541 67290966186523618652626789)
            ·
              refine ⟨12617056159973178497367523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 67290966186523618652626789 12617056159973178497367523)
              ·
                refine ⟨18925584239959767746051285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12617056159973178497367523 18925584239959767746051285)
                ·
                  refine ⟨443568380624057056548077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18925584239959767746051285 443568380624057056548077)
                  ·
                    rfl

theorem cell23_7774617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 4, 1, 7].length) (baseStart_7774617 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7774617 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7774617 prefixEnd_7774617 := by exact prefixLift 7774617
  have htrace : WordTrace (prefixWord ++ tailWord_7774617) baseStart_7774617 baseEnd_7774617 := by
    simpa [prefixWord, tailWord_7774617, baseEnd_7774617] using wordTrace_append hprefix tailTrace_7774617
  have hstable : (prefixWord ++ tailWord_7774617).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7774617).length < 2 ^ (prefixWord ++ tailWord_7774617).sum := by decide
  have hdescent : baseEnd_7774617 < baseStart_7774617 := by decide
  rcases family_descends (prefixWord ++ tailWord_7774617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7774647 : List Nat := [1, 1, 3, 1, 3, 3, 2, 1, 1, 7]
def baseStart_7774647 : Nat := 118140960795 + 7774647 * 2 ^ 59
def prefixEnd_7774647 : Nat := 4983230072969 + 3 ^ 40 * 7774647 * 2
def baseEnd_7774647 : Nat := 1330710276678716130519185

theorem tailTrace_7774647 : CollatzResearch.WordTrace tailWord_7774647 prefixEnd_7774647 1330710276678716130519185 := by
  unfold tailWord_7774647
  simp only [CollatzResearch.WordTrace]
  refine ⟨283564671864789197840834195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189043114576526131893889463 283564671864789197840834195)
  ·
    refine ⟨425347007797183796761251293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 283564671864789197840834195 425347007797183796761251293)
    ·
      refine ⟨159505127923943923785469235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 425347007797183796761251293 159505127923943923785469235)
      ·
        refine ⟨239257691885915885678203853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 159505127923943923785469235 239257691885915885678203853)
        ·
          refine ⟨89721634457218457129326445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 239257691885915885678203853 89721634457218457129326445)
          ·
            refine ⟨33645612921456921423497417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 89721634457218457129326445 33645612921456921423497417)
            ·
              refine ⟨25234209691092691067623063, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33645612921456921423497417 25234209691092691067623063)
              ·
                refine ⟨37851314536639036601434595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25234209691092691067623063 37851314536639036601434595)
                ·
                  refine ⟨56776971804958554902151893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37851314536639036601434595 56776971804958554902151893)
                  ·
                    refine ⟨1330710276678716130519185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 56776971804958554902151893 1330710276678716130519185)
                    ·
                      rfl

theorem cell23_7774647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 3, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 3, 2, 1, 1, 7].length) (baseStart_7774647 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7774647 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7774647 prefixEnd_7774647 := by exact prefixLift 7774647
  have htrace : WordTrace (prefixWord ++ tailWord_7774647) baseStart_7774647 baseEnd_7774647 := by
    simpa [prefixWord, tailWord_7774647, baseEnd_7774647] using wordTrace_append hprefix tailTrace_7774647
  have hstable : (prefixWord ++ tailWord_7774647).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7774647).length < 2 ^ (prefixWord ++ tailWord_7774647).sum := by decide
  have hdescent : baseEnd_7774647 < baseStart_7774647 := by decide
  rcases family_descends (prefixWord ++ tailWord_7774647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7774664 : List Nat := [2, 1, 3, 1, 3, 3, 1, 2, 2, 5]
def baseStart_7774664 : Nat := 118140960795 + 7774664 * 2 ^ 59
def prefixEnd_7774664 : Nat := 4983230072969 + 3 ^ 40 * 7774664 * 2
def baseEnd_7774664 : Nat := 1330713186402424941681659

theorem tailTrace_7774664 : CollatzResearch.WordTrace tailWord_7774664 prefixEnd_7774664 1330713186402424941681659 := by
  unfold tailWord_7774664
  simp only [CollatzResearch.WordTrace]
  refine ⟨141782645952863804872101523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 189043527937151739829468697 141782645952863804872101523)
  ·
    refine ⟨212673968929295707308152285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141782645952863804872101523 212673968929295707308152285)
    ·
      refine ⟨79752738348485890240557107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 212673968929295707308152285 79752738348485890240557107)
      ·
        refine ⟨119629107522728835360835661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79752738348485890240557107 119629107522728835360835661)
        ·
          refine ⟨44860915321023313260313373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 119629107522728835360835661 44860915321023313260313373)
          ·
            refine ⟨16822843245383742472617515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 44860915321023313260313373 16822843245383742472617515)
            ·
              refine ⟨25234264868075613708926273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16822843245383742472617515 25234264868075613708926273)
              ·
                refine ⟨18925698651056710281694705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25234264868075613708926273 18925698651056710281694705)
                ·
                  refine ⟨14194273988292532711271029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18925698651056710281694705 14194273988292532711271029)
                  ·
                    refine ⟨1330713186402424941681659, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14194273988292532711271029 1330713186402424941681659)
                    ·
                      rfl

theorem cell23_7774664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 3, 1, 2, 2, 5].length) (baseStart_7774664 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7774664 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7774664 prefixEnd_7774664 := by exact prefixLift 7774664
  have htrace : WordTrace (prefixWord ++ tailWord_7774664) baseStart_7774664 baseEnd_7774664 := by
    simpa [prefixWord, tailWord_7774664, baseEnd_7774664] using wordTrace_append hprefix tailTrace_7774664
  have hstable : (prefixWord ++ tailWord_7774664).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7774664).length < 2 ^ (prefixWord ++ tailWord_7774664).sum := by decide
  have hdescent : baseEnd_7774664 < baseStart_7774664 := by decide
  rcases family_descends (prefixWord ++ tailWord_7774664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7774668 : List Nat := [2, 2, 1, 4, 3, 1, 3, 2, 5]
def baseStart_7774668 : Nat := 118140960795 + 7774668 * 2 ^ 59
def prefixEnd_7774668 : Nat := 4983230072969 + 3 ^ 40 * 7774668 * 2
def baseEnd_7774668 : Nat := 443571290347765867710551

theorem tailTrace_7774668 : CollatzResearch.WordTrace tailWord_7774668 prefixEnd_7774668 443571290347765867710551 := by
  unfold tailWord_7774668
  simp only [CollatzResearch.WordTrace]
  refine ⟨141782718898856559213674329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 189043625198475412284899105 141782718898856559213674329)
  ·
    refine ⟨106337039174142419410255747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 141782718898856559213674329 106337039174142419410255747)
    ·
      refine ⟨159505558761213629115383621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106337039174142419410255747 159505558761213629115383621)
      ·
        refine ⟨29907292267727555459134429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 159505558761213629115383621 29907292267727555459134429)
        ·
          refine ⟨11215234600397833297175411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29907292267727555459134429 11215234600397833297175411)
          ·
            refine ⟨16822851900596749945763117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11215234600397833297175411 16822851900596749945763117)
            ·
              refine ⟨6308569462723781229661169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16822851900596749945763117 6308569462723781229661169)
              ·
                refine ⟨4731427097042835922245877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6308569462723781229661169 4731427097042835922245877)
                ·
                  refine ⟨443571290347765867710551, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4731427097042835922245877 443571290347765867710551)
                  ·
                    rfl

theorem cell23_7774668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 3, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 3, 1, 3, 2, 5].length) (baseStart_7774668 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7774668 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7774668 prefixEnd_7774668 := by exact prefixLift 7774668
  have htrace : WordTrace (prefixWord ++ tailWord_7774668) baseStart_7774668 baseEnd_7774668 := by
    simpa [prefixWord, tailWord_7774668, baseEnd_7774668] using wordTrace_append hprefix tailTrace_7774668
  have hstable : (prefixWord ++ tailWord_7774668).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7774668).length < 2 ^ (prefixWord ++ tailWord_7774668).sum := by decide
  have hdescent : baseEnd_7774668 < baseStart_7774668 := by decide
  rcases family_descends (prefixWord ++ tailWord_7774668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7774701 : List Nat := [1, 5, 1, 3, 1, 1, 1, 3, 2, 1, 4]
def baseStart_7774701 : Nat := 118140960795 + 7774701 * 2 ^ 59
def prefixEnd_7774701 : Nat := 4983230072969 + 3 ^ 40 * 7774701 * 2
def baseEnd_7774701 : Nat := 3992158557991491180282307

theorem tailTrace_7774701 : CollatzResearch.WordTrace tailWord_7774701 prefixEnd_7774701 3992158557991491180282307 := by
  unfold tailWord_7774701
  simp only [CollatzResearch.WordTrace]
  refine ⟨283566641406593565063299957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189044427604395710042199971 283566641406593565063299957)
  ·
    refine ⟨26584372631868146724684371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 283566641406593565063299957 26584372631868146724684371)
    ·
      refine ⟨39876558947802220087026557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26584372631868146724684371 39876558947802220087026557)
      ·
        refine ⟨14953709605425832532634959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39876558947802220087026557 14953709605425832532634959)
        ·
          refine ⟨22430564408138748798952439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14953709605425832532634959 22430564408138748798952439)
          ·
            refine ⟨33645846612208123198428659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22430564408138748798952439 33645846612208123198428659)
            ·
              refine ⟨50468769918312184797642989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33645846612208123198428659 50468769918312184797642989)
              ·
                refine ⟨18925788719367069299116121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 50468769918312184797642989 18925788719367069299116121)
                ·
                  refine ⟨14194341539525301974337091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18925788719367069299116121 14194341539525301974337091)
                  ·
                    refine ⟨21291512309287952961505637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14194341539525301974337091 21291512309287952961505637)
                    ·
                      refine ⟨3992158557991491180282307, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21291512309287952961505637 3992158557991491180282307)
                      ·
                        rfl

theorem cell23_7774701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 1, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 1, 1, 3, 2, 1, 4].length) (baseStart_7774701 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7774701 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7774701 prefixEnd_7774701 := by exact prefixLift 7774701
  have htrace : WordTrace (prefixWord ++ tailWord_7774701) baseStart_7774701 baseEnd_7774701 := by
    simpa [prefixWord, tailWord_7774701, baseEnd_7774701] using wordTrace_append hprefix tailTrace_7774701
  have hstable : (prefixWord ++ tailWord_7774701).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7774701).length < 2 ^ (prefixWord ++ tailWord_7774701).sum := by decide
  have hdescent : baseEnd_7774701 < baseStart_7774701 := by decide
  rcases family_descends (prefixWord ++ tailWord_7774701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7774721 : List Nat := [1, 2, 4, 1, 3, 1, 2, 2, 2, 2, 3]
def baseStart_7774721 : Nat := 118140960795 + 7774721 * 2 ^ 59
def prefixEnd_7774721 : Nat := 4983230072969 + 3 ^ 40 * 7774721 * 2
def baseEnd_7774721 : Nat := 3992168827604581102032215

theorem tailTrace_7774721 : CollatzResearch.WordTrace tailWord_7774721 prefixEnd_7774721 3992168827604581102032215 := by
  unfold tailWord_7774721
  simp only [CollatzResearch.WordTrace]
  refine ⟨283567370866521108479028017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189044913911014072319352011 283567370866521108479028017)
  ·
    refine ⟨212675528149890831359271013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 283567370866521108479028017 212675528149890831359271013)
    ·
      refine ⟨39876661528104530879863315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 212675528149890831359271013 39876661528104530879863315)
      ·
        refine ⟨59814992292156796319794973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39876661528104530879863315 59814992292156796319794973)
        ·
          refine ⟨22430622109558798619923115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 59814992292156796319794973 22430622109558798619923115)
          ·
            refine ⟨33645933164338197929884673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22430622109558798619923115 33645933164338197929884673)
            ·
              refine ⟨25234449873253648447413505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33645933164338197929884673 25234449873253648447413505)
              ·
                refine ⟨18925837404940236335560129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25234449873253648447413505 18925837404940236335560129)
                ·
                  refine ⟨14194378053705177251670097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18925837404940236335560129 14194378053705177251670097)
                  ·
                    refine ⟨10645783540278882938752573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14194378053705177251670097 10645783540278882938752573)
                    ·
                      refine ⟨3992168827604581102032215, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10645783540278882938752573 3992168827604581102032215)
                      ·
                        rfl

theorem cell23_7774721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 1, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 1, 2, 2, 2, 2, 3].length) (baseStart_7774721 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7774721 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7774721 prefixEnd_7774721 := by exact prefixLift 7774721
  have htrace : WordTrace (prefixWord ++ tailWord_7774721) baseStart_7774721 baseEnd_7774721 := by
    simpa [prefixWord, tailWord_7774721, baseEnd_7774721] using wordTrace_append hprefix tailTrace_7774721
  have hstable : (prefixWord ++ tailWord_7774721).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7774721).length < 2 ^ (prefixWord ++ tailWord_7774721).sum := by decide
  have hdescent : baseEnd_7774721 < baseStart_7774721 := by decide
  rcases family_descends (prefixWord ++ tailWord_7774721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7774768 : List Nat := [2, 1, 1, 1, 2, 3, 3, 5, 1, 1, 3]
def baseStart_7774768 : Nat := 118140960795 + 7774768 * 2 ^ 59
def prefixEnd_7774768 : Nat := 4983230072969 + 3 ^ 40 * 7774768 * 2
def baseEnd_7774768 : Nat := 3992192961195342418144499

theorem tailTrace_7774768 : CollatzResearch.WordTrace tailWord_7774768 prefixEnd_7774768 3992192961195342418144499 := by
  unfold tailWord_7774768
  simp only [CollatzResearch.WordTrace]
  refine ⟨141784542548675417752994479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 189046056731567223670659305 141784542548675417752994479)
  ·
    refine ⟨212676813823013126629491719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141784542548675417752994479 212676813823013126629491719)
    ·
      refine ⟨319015220734519689944237579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 212676813823013126629491719 319015220734519689944237579)
      ·
        refine ⟨478522831101779534916356369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 319015220734519689944237579 478522831101779534916356369)
        ·
          refine ⟨358892123326334651187267277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 478522831101779534916356369 358892123326334651187267277)
          ·
            refine ⟨134584546247375494195225229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 358892123326334651187267277 134584546247375494195225229)
            ·
              refine ⟨50469204842765810323209461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 134584546247375494195225229 50469204842765810323209461)
              ·
                refine ⟨4731487954009294717800887, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 50469204842765810323209461 4731487954009294717800887)
                ·
                  refine ⟨7097231931013942076701331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4731487954009294717800887 7097231931013942076701331)
                  ·
                    refine ⟨10645847896520913115051997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7097231931013942076701331 10645847896520913115051997)
                    ·
                      refine ⟨3992192961195342418144499, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10645847896520913115051997 3992192961195342418144499)
                      ·
                        rfl

theorem cell23_7774768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 3, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 3, 5, 1, 1, 3].length) (baseStart_7774768 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7774768 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7774768 prefixEnd_7774768 := by exact prefixLift 7774768
  have htrace : WordTrace (prefixWord ++ tailWord_7774768) baseStart_7774768 baseEnd_7774768 := by
    simpa [prefixWord, tailWord_7774768, baseEnd_7774768] using wordTrace_append hprefix tailTrace_7774768
  have hstable : (prefixWord ++ tailWord_7774768).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7774768).length < 2 ^ (prefixWord ++ tailWord_7774768).sum := by decide
  have hdescent : baseEnd_7774768 < baseStart_7774768 := by decide
  rcases family_descends (prefixWord ++ tailWord_7774768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7774785 : List Nat := [1, 2, 5, 1, 1, 2, 2, 4, 1, 1, 3]
def baseStart_7774785 : Nat := 118140960795 + 7774785 * 2 ^ 59
def prefixEnd_7774785 : Nat := 4983230072969 + 3 ^ 40 * 7774785 * 2
def baseEnd_7774785 : Nat := 3992201690366468851631921

theorem tailTrace_7774785 : CollatzResearch.WordTrace tailWord_7774785 prefixEnd_7774785 3992201690366468851631921 := by
  unfold tailWord_7774785
  simp only [CollatzResearch.WordTrace]
  refine ⟨283569705138289247409357809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189046470092192831606238539 283569705138289247409357809)
  ·
    refine ⟨212677278853716935557018357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 283569705138289247409357809 212677278853716935557018357)
    ·
      refine ⟨19938494892535962708470471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 212677278853716935557018357 19938494892535962708470471)
      ·
        refine ⟨29907742338803944062705707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19938494892535962708470471 29907742338803944062705707)
        ·
          refine ⟨44861613508205916094058561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29907742338803944062705707 44861613508205916094058561)
          ·
            refine ⟨33646210131154437070543921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44861613508205916094058561 33646210131154437070543921)
            ·
              refine ⟨25234657598365827802907941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33646210131154437070543921 25234657598365827802907941)
              ·
                refine ⟨4731498299693592713045239, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25234657598365827802907941 4731498299693592713045239)
                ·
                  refine ⟨7097247449540389069567859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4731498299693592713045239 7097247449540389069567859)
                  ·
                    refine ⟨10645871174310583604351789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7097247449540389069567859 10645871174310583604351789)
                    ·
                      refine ⟨3992201690366468851631921, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10645871174310583604351789 3992201690366468851631921)
                      ·
                        rfl

theorem cell23_7774785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 2, 2, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 2, 2, 4, 1, 1, 3].length) (baseStart_7774785 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7774785 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7774785 prefixEnd_7774785 := by exact prefixLift 7774785
  have htrace : WordTrace (prefixWord ++ tailWord_7774785) baseStart_7774785 baseEnd_7774785 := by
    simpa [prefixWord, tailWord_7774785, baseEnd_7774785] using wordTrace_append hprefix tailTrace_7774785
  have hstable : (prefixWord ++ tailWord_7774785).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7774785).length < 2 ^ (prefixWord ++ tailWord_7774785).sum := by decide
  have hdescent : baseEnd_7774785 < baseStart_7774785 := by decide
  rcases family_descends (prefixWord ++ tailWord_7774785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7774794 : List Nat := [3, 1, 2, 1, 1, 4, 1, 1, 3, 1, 5]
def baseStart_7774794 : Nat := 118140960795 + 7774794 * 2 ^ 59
def prefixEnd_7774794 : Nat := 4983230072969 + 3 ^ 40 * 7774794 * 2
def baseEnd_7774794 : Nat := 3992206311692359316419379

theorem tailTrace_7774794 : CollatzResearch.WordTrace tailWord_7774794 prefixEnd_7774794 3992206311692359316419379 := by
  unfold tailWord_7774794
  simp only [CollatzResearch.WordTrace]
  refine ⟨70892508348814160486608859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 189046688930171094630956957 70892508348814160486608859)
  ·
    refine ⟨106338762523221240729913289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70892508348814160486608859 106338762523221240729913289)
    ·
      refine ⟨79754071892415930547434967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 106338762523221240729913289 79754071892415930547434967)
      ·
        refine ⟨119631107838623895821152451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79754071892415930547434967 119631107838623895821152451)
        ·
          refine ⟨179446661757935843731728677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 119631107838623895821152451 179446661757935843731728677)
          ·
            refine ⟨33646249079612970699699127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 179446661757935843731728677 33646249079612970699699127)
            ·
              refine ⟨50469373619419456049548691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33646249079612970699699127 50469373619419456049548691)
              ·
                refine ⟨75704060429129184074323037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50469373619419456049548691 75704060429129184074323037)
                ·
                  refine ⟨28389022660923444027871139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 75704060429129184074323037 28389022660923444027871139)
                  ·
                    refine ⟨42583533991385166041806709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 28389022660923444027871139 42583533991385166041806709)
                    ·
                      refine ⟨3992206311692359316419379, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 42583533991385166041806709 3992206311692359316419379)
                      ·
                        rfl

theorem cell23_7774794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 4, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 4, 1, 1, 3, 1, 5].length) (baseStart_7774794 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7774794 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7774794 prefixEnd_7774794 := by exact prefixLift 7774794
  have htrace : WordTrace (prefixWord ++ tailWord_7774794) baseStart_7774794 baseEnd_7774794 := by
    simpa [prefixWord, tailWord_7774794, baseEnd_7774794] using wordTrace_append hprefix tailTrace_7774794
  have hstable : (prefixWord ++ tailWord_7774794).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7774794).length < 2 ^ (prefixWord ++ tailWord_7774794).sum := by decide
  have hdescent : baseEnd_7774794 < baseStart_7774794 := by decide
  rcases family_descends (prefixWord ++ tailWord_7774794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7774801 : List Nat := [1, 2, 2, 1, 3, 5, 1, 1, 1, 6]
def baseStart_7774801 : Nat := 118140960795 + 7774801 * 2 ^ 59
def prefixEnd_7774801 : Nat := 4983230072969 + 3 ^ 40 * 7774801 * 2
def baseEnd_7774801 : Nat := 1330736635352313596343949

theorem tailTrace_7774801 : CollatzResearch.WordTrace tailWord_7774801 prefixEnd_7774801 1330736635352313596343949 := by
  unfold tailWord_7774801
  simp only [CollatzResearch.WordTrace]
  refine ⟨283570288706231282141940257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189046859137487521427960171 283570288706231282141940257)
  ·
    refine ⟨212677716529673461606455193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 283570288706231282141940257 212677716529673461606455193)
    ·
      refine ⟨159508287397255096204841395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 212677716529673461606455193 159508287397255096204841395)
      ·
        refine ⟨239262431095882644307262093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 159508287397255096204841395 239262431095882644307262093)
        ·
          refine ⟨89723411660955991615223285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 239262431095882644307262093 89723411660955991615223285)
          ·
            refine ⟨8411569843214624213927183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 89723411660955991615223285 8411569843214624213927183)
            ·
              refine ⟨12617354764821936320890775, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8411569843214624213927183 12617354764821936320890775)
              ·
                refine ⟨18926032147232904481336163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12617354764821936320890775 18926032147232904481336163)
                ·
                  refine ⟨28389048220849356722004245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18926032147232904481336163 28389048220849356722004245)
                  ·
                    refine ⟨1330736635352313596343949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28389048220849356722004245 1330736635352313596343949)
                    ·
                      rfl

theorem cell23_7774801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 5, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 5, 1, 1, 1, 6].length) (baseStart_7774801 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7774801 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7774801 prefixEnd_7774801 := by exact prefixLift 7774801
  have htrace : WordTrace (prefixWord ++ tailWord_7774801) baseStart_7774801 baseEnd_7774801 := by
    simpa [prefixWord, tailWord_7774801, baseEnd_7774801] using wordTrace_append hprefix tailTrace_7774801
  have hstable : (prefixWord ++ tailWord_7774801).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7774801).length < 2 ^ (prefixWord ++ tailWord_7774801).sum := by decide
  have hdescent : baseEnd_7774801 < baseStart_7774801 := by decide
  rcases family_descends (prefixWord ++ tailWord_7774801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7774808 : List Nat := [2, 1, 2, 2, 1, 2, 4, 2, 3, 2, 2]
def baseStart_7774808 : Nat := 118140960795 + 7774808 * 2 ^ 59
def prefixEnd_7774808 : Nat := 4983230072969 + 3 ^ 40 * 7774808 * 2
def baseEnd_7774808 : Nat := 3992213500421522261644315

theorem tailTrace_7774808 : CollatzResearch.WordTrace tailWord_7774808 prefixEnd_7774808 3992213500421522261644315 := by
  unfold tailWord_7774808
  simp only [CollatzResearch.WordTrace]
  refine ⟨141785272008602961168722539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 189047029344803948224963385 141785272008602961168722539)
  ·
    refine ⟨212677908012904441753083809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141785272008602961168722539 212677908012904441753083809)
    ·
      refine ⟨159508431009678331314812857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 212677908012904441753083809 159508431009678331314812857)
      ·
        refine ⟨119631323257258748486109643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 159508431009678331314812857 119631323257258748486109643)
        ·
          refine ⟨179446984885888122729164465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 119631323257258748486109643 179446984885888122729164465)
          ·
            refine ⟨134585238664416092046873349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 179446984885888122729164465 134585238664416092046873349)
            ·
              refine ⟨25234732249578017258788753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 134585238664416092046873349 25234732249578017258788753)
              ·
                refine ⟨18926049187183512944091565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25234732249578017258788753 18926049187183512944091565)
                ·
                  refine ⟨7097268445193817354034337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18926049187183512944091565 7097268445193817354034337)
                  ·
                    refine ⟨5322951333895363015525753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7097268445193817354034337 5322951333895363015525753)
                    ·
                      refine ⟨3992213500421522261644315, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5322951333895363015525753 3992213500421522261644315)
                      ·
                        rfl

theorem cell23_7774808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 4, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 4, 2, 3, 2, 2].length) (baseStart_7774808 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7774808 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7774808 prefixEnd_7774808 := by exact prefixLift 7774808
  have htrace : WordTrace (prefixWord ++ tailWord_7774808) baseStart_7774808 baseEnd_7774808 := by
    simpa [prefixWord, tailWord_7774808, baseEnd_7774808] using wordTrace_append hprefix tailTrace_7774808
  have hstable : (prefixWord ++ tailWord_7774808).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7774808).length < 2 ^ (prefixWord ++ tailWord_7774808).sum := by decide
  have hdescent : baseEnd_7774808 < baseStart_7774808 := by decide
  rcases family_descends (prefixWord ++ tailWord_7774808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7774911 : List Nat := [1, 1, 2, 2, 2, 5, 1, 1, 2, 2, 4]
def baseStart_7774911 : Nat := 118140960795 + 7774911 * 2 ^ 59
def prefixEnd_7774911 : Nat := 4983230072969 + 3 ^ 40 * 7774911 * 2
def baseEnd_7774911 : Nat := 3992266388928935358656341

theorem tailTrace_7774911 : CollatzResearch.WordTrace tailWord_7774911 prefixEnd_7774911 3992266388928935358656341 := by
  unfold tailWord_7774911
  simp only [CollatzResearch.WordTrace]
  refine ⟨283574300735832770928444587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189049533823888513952296391 283574300735832770928444587)
  ·
    refine ⟨425361451103749156392666881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 283574300735832770928444587 425361451103749156392666881)
    ·
      refine ⟨319021088327811867294500161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 425361451103749156392666881 319021088327811867294500161)
      ·
        refine ⟨239265816245858900470875121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 319021088327811867294500161 239265816245858900470875121)
        ·
          refine ⟨179449362184394175353156341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 239265816245858900470875121 179449362184394175353156341)
          ·
            refine ⟨16823377704786953939358407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 179449362184394175353156341 16823377704786953939358407)
            ·
              refine ⟨25235066557180430909037611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16823377704786953939358407 25235066557180430909037611)
              ·
                refine ⟨37852599835770646363556417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25235066557180430909037611 37852599835770646363556417)
                ·
                  refine ⟨28389449876827984772667313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37852599835770646363556417 28389449876827984772667313)
                  ·
                    refine ⟨21292087407620988579500485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 28389449876827984772667313 21292087407620988579500485)
                    ·
                      refine ⟨3992266388928935358656341, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21292087407620988579500485 3992266388928935358656341)
                      ·
                        rfl

theorem cell23_7774911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 5, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 5, 1, 1, 2, 2, 4].length) (baseStart_7774911 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7774911 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7774911 prefixEnd_7774911 := by exact prefixLift 7774911
  have htrace : WordTrace (prefixWord ++ tailWord_7774911) baseStart_7774911 baseEnd_7774911 := by
    simpa [prefixWord, tailWord_7774911, baseEnd_7774911] using wordTrace_append hprefix tailTrace_7774911
  have hstable : (prefixWord ++ tailWord_7774911).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7774911).length < 2 ^ (prefixWord ++ tailWord_7774911).sum := by decide
  have hdescent : baseEnd_7774911 < baseStart_7774911 := by decide
  rcases family_descends (prefixWord ++ tailWord_7774911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7774938 : List Nat := [3, 1, 1, 2, 2, 2, 4, 3, 5]
def baseStart_7774938 : Nat := 118140960795 + 7774938 * 2 ^ 59
def prefixEnd_7774938 : Nat := 4983230072969 + 3 ^ 40 * 7774938 * 2
def baseEnd_7774938 : Nat := 443586694767400750335413

theorem tailTrace_7774938 : CollatzResearch.WordTrace tailWord_7774938 prefixEnd_7774938 443586694767400750335413 := by
  unfold tailWord_7774938
  simp only [CollatzResearch.WordTrace]
  refine ⟨70893821376683738634919367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 189050190337823303026451645 70893821376683738634919367)
  ·
    refine ⟨106340732065025607952379051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70893821376683738634919367 106340732065025607952379051)
    ·
      refine ⟨159511098097538411928568577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106340732065025607952379051 159511098097538411928568577)
      ·
        refine ⟨119633323573153808946426433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 159511098097538411928568577 119633323573153808946426433)
        ·
          refine ⟨89724992679865356709819825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 119633323573153808946426433 89724992679865356709819825)
          ·
            refine ⟨67293744509899017532364869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 89724992679865356709819825 67293744509899017532364869)
            ·
              refine ⟨12617577095606065787318413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 67293744509899017532364869 12617577095606065787318413)
              ·
                refine ⟨4731591410852274670244405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12617577095606065787318413 4731591410852274670244405)
                ·
                  refine ⟨443586694767400750335413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4731591410852274670244405 443586694767400750335413)
                  ·
                    rfl

theorem cell23_7774938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 4, 3, 5].length) (baseStart_7774938 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7774938 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7774938 prefixEnd_7774938 := by exact prefixLift 7774938
  have htrace : WordTrace (prefixWord ++ tailWord_7774938) baseStart_7774938 baseEnd_7774938 := by
    simpa [prefixWord, tailWord_7774938, baseEnd_7774938] using wordTrace_append hprefix tailTrace_7774938
  have hstable : (prefixWord ++ tailWord_7774938).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7774938).length < 2 ^ (prefixWord ++ tailWord_7774938).sum := by decide
  have hdescent : baseEnd_7774938 < baseStart_7774938 := by decide
  rcases family_descends (prefixWord ++ tailWord_7774938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7774991 : List Nat := [1, 1, 2, 1, 1, 1, 5, 3, 1, 4, 3]
def baseStart_7774991 : Nat := 118140960795 + 7774991 * 2 ^ 59
def prefixEnd_7774991 : Nat := 4983230072969 + 3 ^ 40 * 7774991 * 2
def baseEnd_7774991 : Nat := 3992307467381295045655973

theorem tailTrace_7774991 : CollatzResearch.WordTrace tailWord_7774991 prefixEnd_7774991 3992307467381295045655973 := by
  unfold tailWord_7774991
  simp only [CollatzResearch.WordTrace]
  refine ⟨283577218575542944591356827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189051479050361963060904551 283577218575542944591356827)
  ·
    refine ⟨425365827863314416887035241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 283577218575542944591356827 425365827863314416887035241)
    ·
      refine ⟨319024370897485812665276431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 425365827863314416887035241 319024370897485812665276431)
      ·
        refine ⟨478536556346228718997914647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 319024370897485812665276431 478536556346228718997914647)
        ·
          refine ⟨717804834519343078496871971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 478536556346228718997914647 717804834519343078496871971)
          ·
            refine ⟨1076707251779014617745307957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 717804834519343078496871971 1076707251779014617745307957)
            ·
              refine ⟨100941304854282620413622621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1076707251779014617745307957 100941304854282620413622621)
              ·
                refine ⟨37852989320355982655108483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 100941304854282620413622621 37852989320355982655108483)
                ·
                  refine ⟨56779483980533973982662725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37852989320355982655108483 56779483980533973982662725)
                  ·
                    refine ⟨10646153246350120121749261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 56779483980533973982662725 10646153246350120121749261)
                    ·
                      refine ⟨3992307467381295045655973, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10646153246350120121749261 3992307467381295045655973)
                      ·
                        rfl

theorem cell23_7774991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 5, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 5, 3, 1, 4, 3].length) (baseStart_7774991 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7774991 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7774991 prefixEnd_7774991 := by exact prefixLift 7774991
  have htrace : WordTrace (prefixWord ++ tailWord_7774991) baseStart_7774991 baseEnd_7774991 := by
    simpa [prefixWord, tailWord_7774991, baseEnd_7774991] using wordTrace_append hprefix tailTrace_7774991
  have hstable : (prefixWord ++ tailWord_7774991).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7774991).length < 2 ^ (prefixWord ++ tailWord_7774991).sum := by decide
  have hdescent : baseEnd_7774991 < baseStart_7774991 := by decide
  rcases family_descends (prefixWord ++ tailWord_7774991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7775008 : List Nat := [2, 1, 1, 5, 1, 2, 1, 1, 4, 2, 3]
def baseStart_7775008 : Nat := 118140960795 + 7775008 * 2 ^ 59
def prefixEnd_7775008 : Nat := 4983230072969 + 3 ^ 40 * 7775008 * 2
def baseEnd_7775008 : Nat := 3992316196552421479143395

theorem tailTrace_7775008 : CollatzResearch.WordTrace tailWord_7775008 prefixEnd_7775008 3992316196552421479143395 := by
  unfold tailWord_7775008
  simp only [CollatzResearch.WordTrace]
  refine ⟨141788919308240678247362839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 189051892410987570996483785 141788919308240678247362839)
  ·
    refine ⟨212683378962361017371044259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141788919308240678247362839 212683378962361017371044259)
    ·
      refine ⟨319025068443541526056566389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 212683378962361017371044259 319025068443541526056566389)
      ·
        refine ⟨29908600166582018067803099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 319025068443541526056566389 29908600166582018067803099)
        ·
          refine ⟨44862900249873027101704649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29908600166582018067803099 44862900249873027101704649)
          ·
            refine ⟨33647175187404770326278487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44862900249873027101704649 33647175187404770326278487)
            ·
              refine ⟨50470762781107155489417731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33647175187404770326278487 50470762781107155489417731)
              ·
                refine ⟨75706144171660733234126597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50470762781107155489417731 75706144171660733234126597)
                ·
                  refine ⟨14194902032186387481398737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 75706144171660733234126597 14194902032186387481398737)
                  ·
                    refine ⟨10646176524139790611049053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14194902032186387481398737 10646176524139790611049053)
                    ·
                      refine ⟨3992316196552421479143395, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10646176524139790611049053 3992316196552421479143395)
                      ·
                        rfl

theorem cell23_7775008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 2, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 2, 1, 1, 4, 2, 3].length) (baseStart_7775008 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7775008 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7775008 prefixEnd_7775008 := by exact prefixLift 7775008
  have htrace : WordTrace (prefixWord ++ tailWord_7775008) baseStart_7775008 baseEnd_7775008 := by
    simpa [prefixWord, tailWord_7775008, baseEnd_7775008] using wordTrace_append hprefix tailTrace_7775008
  have hstable : (prefixWord ++ tailWord_7775008).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7775008).length < 2 ^ (prefixWord ++ tailWord_7775008).sum := by decide
  have hdescent : baseEnd_7775008 < baseStart_7775008 := by decide
  rcases family_descends (prefixWord ++ tailWord_7775008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7775011 : List Nat := [1, 1, 1, 4, 2, 1, 1, 6, 6]
def baseStart_7775011 : Nat := 118140960795 + 7775011 * 2 ^ 59
def prefixEnd_7775011 : Nat := 4983230072969 + 3 ^ 40 * 7775011 * 2
def baseEnd_7775011 : Nat := 443590859666042774156209

theorem tailTrace_7775011 : CollatzResearch.WordTrace tailWord_7775011 prefixEnd_7775011 443590859666042774156209 := by
  unfold tailWord_7775011
  simp only [CollatzResearch.WordTrace]
  refine ⟨283577948035470488007084887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189051965356980325338056591 283577948035470488007084887)
  ·
    refine ⟨425366922053205732010627331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 283577948035470488007084887 425366922053205732010627331)
    ·
      refine ⟨638050383079808598015940997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 425366922053205732010627331 638050383079808598015940997)
      ·
        refine ⟨119634446827464112127988937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 638050383079808598015940997 119634446827464112127988937)
        ·
          refine ⟨89725835120598084095991703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 119634446827464112127988937 89725835120598084095991703)
          ·
            refine ⟨134588752680897126143987555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89725835120598084095991703 134588752680897126143987555)
            ·
              refine ⟨201883129021345689215981333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 134588752680897126143987555 201883129021345689215981333)
              ·
                refine ⟨9463271672875579181999125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 201883129021345689215981333 9463271672875579181999125)
                ·
                  refine ⟨443590859666042774156209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9463271672875579181999125 443590859666042774156209)
                  ·
                    rfl

theorem cell23_7775011_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 1, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 1, 6, 6].length) (baseStart_7775011 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7775011 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7775011 prefixEnd_7775011 := by exact prefixLift 7775011
  have htrace : WordTrace (prefixWord ++ tailWord_7775011) baseStart_7775011 baseEnd_7775011 := by
    simpa [prefixWord, tailWord_7775011, baseEnd_7775011] using wordTrace_append hprefix tailTrace_7775011
  have hstable : (prefixWord ++ tailWord_7775011).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7775011).length < 2 ^ (prefixWord ++ tailWord_7775011).sum := by decide
  have hdescent : baseEnd_7775011 < baseStart_7775011 := by decide
  rcases family_descends (prefixWord ++ tailWord_7775011) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7775065 : List Nat := [1, 2, 1, 2, 2, 4, 2, 2, 2, 3, 2]
def baseStart_7775065 : Nat := 118140960795 + 7775065 * 2 ^ 59
def prefixEnd_7775065 : Nat := 4983230072969 + 3 ^ 40 * 7775065 * 2
def baseEnd_7775065 : Nat := 3992345464949727756130633

theorem tailTrace_7775065 : CollatzResearch.WordTrace tailWord_7775065 prefixEnd_7775065 3992345464949727756130633 := by
  unfold tailWord_7775065
  simp only [CollatzResearch.WordTrace]
  refine ⟨283579917577274855229550649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189053278384849903486367099 283579917577274855229550649)
  ·
    refine ⟨212684938182956141422162987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 283579917577274855229550649 212684938182956141422162987)
    ·
      refine ⟨319027407274434212133244481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 212684938182956141422162987 319027407274434212133244481)
      ·
        refine ⟨239270555455825659099933361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 319027407274434212133244481 239270555455825659099933361)
        ·
          refine ⟨179452916591869244324950021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 239270555455825659099933361 179452916591869244324950021)
          ·
            refine ⟨33647421860975483310928129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 179452916591869244324950021 33647421860975483310928129)
            ·
              refine ⟨25235566395731612483196097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33647421860975483310928129 25235566395731612483196097)
              ·
                refine ⟨18926674796798709362397073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25235566395731612483196097 18926674796798709362397073)
                ·
                  refine ⟨14195006097599032021797805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18926674796798709362397073 14195006097599032021797805)
                  ·
                    refine ⟨5323127286599637008174177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14195006097599032021797805 5323127286599637008174177)
                    ·
                      refine ⟨3992345464949727756130633, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5323127286599637008174177 3992345464949727756130633)
                      ·
                        rfl

theorem cell23_7775065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 4, 2, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 4, 2, 2, 2, 3, 2].length) (baseStart_7775065 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7775065 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7775065 prefixEnd_7775065 := by exact prefixLift 7775065
  have htrace : WordTrace (prefixWord ++ tailWord_7775065) baseStart_7775065 baseEnd_7775065 := by
    simpa [prefixWord, tailWord_7775065, baseEnd_7775065] using wordTrace_append hprefix tailTrace_7775065
  have hstable : (prefixWord ++ tailWord_7775065).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7775065).length < 2 ^ (prefixWord ++ tailWord_7775065).sum := by decide
  have hdescent : baseEnd_7775065 < baseStart_7775065 := by decide
  rcases family_descends (prefixWord ++ tailWord_7775065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7775071 : List Nat := [1, 1, 2, 3, 1, 3, 1, 2, 3, 6]
def baseStart_7775071 : Nat := 118140960795 + 7775071 * 2 ^ 59
def prefixEnd_7775071 : Nat := 4983230072969 + 3 ^ 40 * 7775071 * 2
def baseEnd_7775071 : Nat := 1330782848611218244218535

theorem tailTrace_7775071 : CollatzResearch.WordTrace tailWord_7775071 prefixEnd_7775071 1330782848611218244218535 := by
  unfold tailWord_7775071
  simp only [CollatzResearch.WordTrace]
  refine ⟨283580136415253118254269067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189053424276835412169512711 283580136415253118254269067)
  ·
    refine ⟨425370204622879677381403601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 283580136415253118254269067 425370204622879677381403601)
    ·
      refine ⟨319027653467159758036052701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 425370204622879677381403601 319027653467159758036052701)
      ·
        refine ⟨119635370050184909263519763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 319027653467159758036052701 119635370050184909263519763)
        ·
          refine ⟨179453055075277363895279645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 119635370050184909263519763 179453055075277363895279645)
          ·
            refine ⟨67294895653229011460729867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 179453055075277363895279645 67294895653229011460729867)
            ·
              refine ⟨100942343479843517191094801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67294895653229011460729867 100942343479843517191094801)
              ·
                refine ⟨75706757609882637893321101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 100942343479843517191094801 75706757609882637893321101)
                ·
                  refine ⟨28390034103705989209995413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 75706757609882637893321101 28390034103705989209995413)
                  ·
                    refine ⟨1330782848611218244218535, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28390034103705989209995413 1330782848611218244218535)
                    ·
                      rfl

theorem cell23_7775071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 1, 2, 3, 6].length) (baseStart_7775071 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7775071 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7775071 prefixEnd_7775071 := by exact prefixLift 7775071
  have htrace : WordTrace (prefixWord ++ tailWord_7775071) baseStart_7775071 baseEnd_7775071 := by
    simpa [prefixWord, tailWord_7775071, baseEnd_7775071] using wordTrace_append hprefix tailTrace_7775071
  have hstable : (prefixWord ++ tailWord_7775071).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7775071).length < 2 ^ (prefixWord ++ tailWord_7775071).sum := by decide
  have hdescent : baseEnd_7775071 < baseStart_7775071 := by decide
  rcases family_descends (prefixWord ++ tailWord_7775071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7775072 : List Nat := [2, 1, 1, 3, 3, 1, 3, 4, 1, 1, 3]
def baseStart_7775072 : Nat := 118140960795 + 7775072 * 2 ^ 59
def prefixEnd_7775072 : Nat := 4983230072969 + 3 ^ 40 * 7775072 * 2
def baseEnd_7775072 : Nat := 3992349059314309228743101

theorem tailTrace_7775072 : CollatzResearch.WordTrace tailWord_7775072 prefixEnd_7775072 3992349059314309228743101 := by
  unfold tailWord_7775072
  simp only [CollatzResearch.WordTrace]
  refine ⟨141790086444124747712527735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 189053448592166330283370313 141790086444124747712527735)
  ·
    refine ⟨212685129666187121568791603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141790086444124747712527735 212685129666187121568791603)
    ·
      refine ⟨319027694499280682353187405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 212685129666187121568791603 319027694499280682353187405)
      ·
        refine ⟨119635385437230255882445277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 319027694499280682353187405 119635385437230255882445277)
        ·
          refine ⟨44863269538961345955916979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 119635385437230255882445277 44863269538961345955916979)
          ·
            refine ⟨67294904308442018933875469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44863269538961345955916979 67294904308442018933875469)
            ·
              refine ⟨25235589115665757100203301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 67294904308442018933875469 25235589115665757100203301)
              ·
                refine ⟨4731672959187329456288119, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25235589115665757100203301 4731672959187329456288119)
                ·
                  refine ⟨7097509438780994184432179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4731672959187329456288119 7097509438780994184432179)
                  ·
                    refine ⟨10646264158171491276648269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7097509438780994184432179 10646264158171491276648269)
                    ·
                      refine ⟨3992349059314309228743101, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10646264158171491276648269 3992349059314309228743101)
                      ·
                        rfl

theorem cell23_7775072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 3, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 3, 4, 1, 1, 3].length) (baseStart_7775072 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7775072 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7775072 prefixEnd_7775072 := by exact prefixLift 7775072
  have htrace : WordTrace (prefixWord ++ tailWord_7775072) baseStart_7775072 baseEnd_7775072 := by
    simpa [prefixWord, tailWord_7775072, baseEnd_7775072] using wordTrace_append hprefix tailTrace_7775072
  have hstable : (prefixWord ++ tailWord_7775072).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7775072).length < 2 ^ (prefixWord ++ tailWord_7775072).sum := by decide
  have hdescent : baseEnd_7775072 < baseStart_7775072 := by decide
  rcases family_descends (prefixWord ++ tailWord_7775072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7775091 : List Nat := [1, 1, 1, 2, 2, 1, 4, 3, 1, 1, 6]
def baseStart_7775091 : Nat := 118140960795 + 7775091 * 2 ^ 59
def prefixEnd_7775091 : Nat := 4983230072969 + 3 ^ 40 * 7775091 * 2
def baseEnd_7775091 : Nat := 3992358815446744654405513

theorem tailTrace_7775091 : CollatzResearch.WordTrace tailWord_7775091 prefixEnd_7775091 3992358815446744654405513 := by
  unfold tailWord_7775091
  simp only [CollatzResearch.WordTrace]
  refine ⟨283580865875180661669997127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189053910583453774446664751 283580865875180661669997127)
  ·
    refine ⟨425371298812770992504995691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 283580865875180661669997127 425371298812770992504995691)
    ·
      refine ⟨638056948219156488757493537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 425371298812770992504995691 638056948219156488757493537)
      ·
        refine ⟨478542711164367366568120153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 638056948219156488757493537 478542711164367366568120153)
        ·
          refine ⟨358907033373275524926090115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 478542711164367366568120153 358907033373275524926090115)
          ·
            refine ⟨538360550059913287389135173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 358907033373275524926090115 538360550059913287389135173)
            ·
              refine ⟨100942603136233741385462845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 538360550059913287389135173 100942603136233741385462845)
              ·
                refine ⟨37853476176087653019548567, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 100942603136233741385462845 37853476176087653019548567)
                ·
                  refine ⟨56780214264131479529322851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37853476176087653019548567 56780214264131479529322851)
                  ·
                    refine ⟨85170321396197219293984277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 56780214264131479529322851 85170321396197219293984277)
                    ·
                      refine ⟨3992358815446744654405513, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 85170321396197219293984277 3992358815446744654405513)
                      ·
                        rfl

theorem cell23_7775091_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 4, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 4, 3, 1, 1, 6].length) (baseStart_7775091 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7775091 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7775091 prefixEnd_7775091 := by exact prefixLift 7775091
  have htrace : WordTrace (prefixWord ++ tailWord_7775091) baseStart_7775091 baseEnd_7775091 := by
    simpa [prefixWord, tailWord_7775091, baseEnd_7775091] using wordTrace_append hprefix tailTrace_7775091
  have hstable : (prefixWord ++ tailWord_7775091).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7775091).length < 2 ^ (prefixWord ++ tailWord_7775091).sum := by decide
  have hdescent : baseEnd_7775091 < baseStart_7775091 := by decide
  rcases family_descends (prefixWord ++ tailWord_7775091) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7775101 : List Nat := [1, 4, 1, 1, 2, 1, 2, 11]
def baseStart_7775101 : Nat := 118140960795 + 7775101 * 2 ^ 59
def prefixEnd_7775101 : Nat := 4983230072969 + 3 ^ 40 * 7775101 * 2
def baseEnd_7775101 : Nat := 147865331490862578343721

theorem tailTrace_7775101 : CollatzResearch.WordTrace tailWord_7775101 prefixEnd_7775101 147865331490862578343721 := by
  unfold tailWord_7775101
  simp only [CollatzResearch.WordTrace]
  refine ⟨283581230605144433377861157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189054153736762955585240771 283581230605144433377861157)
  ·
    refine ⟨53171480738464581258348967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 283581230605144433377861157 53171480738464581258348967)
    ·
      refine ⟨79757221107696871887523451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53171480738464581258348967 79757221107696871887523451)
      ·
        refine ⟨119635831661545307831285177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79757221107696871887523451 119635831661545307831285177)
        ·
          refine ⟨89726873746158980873463883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 119635831661545307831285177 89726873746158980873463883)
          ·
            refine ⟨134590310619238471310195825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89726873746158980873463883 134590310619238471310195825)
            ·
              refine ⟨100942732964428853482646869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 134590310619238471310195825 100942732964428853482646869)
              ·
                refine ⟨147865331490862578343721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 100942732964428853482646869 147865331490862578343721)
                ·
                  rfl

theorem cell23_7775101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 2, 11].length) (baseStart_7775101 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7775101 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7775101 prefixEnd_7775101 := by exact prefixLift 7775101
  have htrace : WordTrace (prefixWord ++ tailWord_7775101) baseStart_7775101 baseEnd_7775101 := by
    simpa [prefixWord, tailWord_7775101, baseEnd_7775101] using wordTrace_append hprefix tailTrace_7775101
  have hstable : (prefixWord ++ tailWord_7775101).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7775101).length < 2 ^ (prefixWord ++ tailWord_7775101).sum := by decide
  have hdescent : baseEnd_7775101 < baseStart_7775101 := by decide
  rcases family_descends (prefixWord ++ tailWord_7775101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7775112 : List Nat := [2, 1, 3, 3, 2, 1, 4, 1, 1, 1, 4]
def baseStart_7775112 : Nat := 118140960795 + 7775112 * 2 ^ 59
def prefixEnd_7775112 : Nat := 4983230072969 + 3 ^ 40 * 7775112 * 2
def baseEnd_7775112 : Nat := 3992369598540489072242917

theorem tailTrace_7775112 : CollatzResearch.WordTrace tailWord_7775112 prefixEnd_7775112 3992369598540489072242917 := by
  unfold tailWord_7775112
  simp only [CollatzResearch.WordTrace]
  refine ⟨141790815904052291128255795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 189054421205403054837674393 141790815904052291128255795)
  ·
    refine ⟨212686223856078436692383693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141790815904052291128255795 212686223856078436692383693)
    ·
      refine ⟨79757333946029413759643885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 212686223856078436692383693 79757333946029413759643885)
      ·
        refine ⟨29909000229761030159866457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 79757333946029413759643885 29909000229761030159866457)
        ·
          refine ⟨22431750172320772619899843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29909000229761030159866457 22431750172320772619899843)
          ·
            refine ⟨33647625258481158929849765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22431750172320772619899843 33647625258481158929849765)
            ·
              refine ⟨6308929735965217299346831, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 33647625258481158929849765 6308929735965217299346831)
              ·
                refine ⟨9463394603947825949020247, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6308929735965217299346831 9463394603947825949020247)
                ·
                  refine ⟨14195091905921738923530371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9463394603947825949020247 14195091905921738923530371)
                  ·
                    refine ⟨21292637858882608385295557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14195091905921738923530371 21292637858882608385295557)
                    ·
                      refine ⟨3992369598540489072242917, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21292637858882608385295557 3992369598540489072242917)
                      ·
                        rfl

theorem cell23_7775112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 1, 4, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 1, 4, 1, 1, 1, 4].length) (baseStart_7775112 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7775112 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7775112 prefixEnd_7775112 := by exact prefixLift 7775112
  have htrace : WordTrace (prefixWord ++ tailWord_7775112) baseStart_7775112 baseEnd_7775112 := by
    simpa [prefixWord, tailWord_7775112, baseEnd_7775112] using wordTrace_append hprefix tailTrace_7775112
  have hstable : (prefixWord ++ tailWord_7775112).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7775112).length < 2 ^ (prefixWord ++ tailWord_7775112).sum := by decide
  have hdescent : baseEnd_7775112 < baseStart_7775112 := by decide
  rcases family_descends (prefixWord ++ tailWord_7775112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7775121 : List Nat := [1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 6]
def baseStart_7775121 : Nat := 118140960795 + 7775121 * 2 ^ 59
def prefixEnd_7775121 : Nat := 4983230072969 + 3 ^ 40 * 7775121 * 2
def baseEnd_7775121 : Nat := 3992374219866379537030375

theorem tailTrace_7775121 : CollatzResearch.WordTrace tailWord_7775121 prefixEnd_7775121 3992374219866379537030375 := by
  unfold tailWord_7775121
  simp only [CollatzResearch.WordTrace]
  refine ⟨283581960065071976793589217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189054640043381317862392811 283581960065071976793589217)
  ·
    refine ⟨212686470048803982595191913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 283581960065071976793589217 212686470048803982595191913)
    ·
      refine ⟨159514852536602986946393935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 212686470048803982595191913 159514852536602986946393935)
      ·
        refine ⟨239272278804904480419590903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 159514852536602986946393935 239272278804904480419590903)
        ·
          refine ⟨358908418207356720629386355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 239272278804904480419590903 358908418207356720629386355)
          ·
            refine ⟨538362627311035080944079533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 358908418207356720629386355 538362627311035080944079533)
            ·
              refine ⟨201885985241638155354029825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 538362627311035080944079533 201885985241638155354029825)
              ·
                refine ⟨151414488931228616515522369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 201885985241638155354029825 151414488931228616515522369)
                ·
                  refine ⟨113560866698421462386641777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 151414488931228616515522369 113560866698421462386641777)
                  ·
                    refine ⟨85170650023816096789981333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 113560866698421462386641777 85170650023816096789981333)
                    ·
                      refine ⟨3992374219866379537030375, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 85170650023816096789981333 3992374219866379537030375)
                      ·
                        rfl

theorem cell23_7775121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 6].length) (baseStart_7775121 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7775121 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7775121 prefixEnd_7775121 := by exact prefixLift 7775121
  have htrace : WordTrace (prefixWord ++ tailWord_7775121) baseStart_7775121 baseEnd_7775121 := by
    simpa [prefixWord, tailWord_7775121, baseEnd_7775121] using wordTrace_append hprefix tailTrace_7775121
  have hstable : (prefixWord ++ tailWord_7775121).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7775121).length < 2 ^ (prefixWord ++ tailWord_7775121).sum := by decide
  have hdescent : baseEnd_7775121 < baseStart_7775121 := by decide
  rcases family_descends (prefixWord ++ tailWord_7775121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7775122 : List Nat := [3, 2, 3, 2, 2, 1, 1, 1, 4, 4]
def baseStart_7775122 : Nat := 118140960795 + 7775122 * 2 ^ 59
def prefixEnd_7775122 : Nat := 4983230072969 + 3 ^ 40 * 7775122 * 2
def baseEnd_7775122 : Nat := 1330791577782344677705957

theorem tailTrace_7775122 : CollatzResearch.WordTrace tailWord_7775122 prefixEnd_7775122 1330791577782344677705957 := by
  unfold tailWord_7775122
  simp only [CollatzResearch.WordTrace]
  refine ⟨70895499134517088491093905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 189054664358712235976250413 70895499134517088491093905)
  ·
    refine ⟨53171624350887816368320429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70895499134517088491093905 53171624350887816368320429)
    ·
      refine ⟨19939359131582931138120161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 53171624350887816368320429 19939359131582931138120161)
      ·
        refine ⟨14954519348687198353590121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19939359131582931138120161 14954519348687198353590121)
        ·
          refine ⟨11215889511515398765192591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14954519348687198353590121 11215889511515398765192591)
          ·
            refine ⟨16823834267273098147788887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11215889511515398765192591 16823834267273098147788887)
            ·
              refine ⟨25235751400909647221683331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16823834267273098147788887 25235751400909647221683331)
              ·
                refine ⟨37853627101364470832524997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25235751400909647221683331 37853627101364470832524997)
                ·
                  refine ⟨7097555081505838281098437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 37853627101364470832524997 7097555081505838281098437)
                  ·
                    refine ⟨1330791577782344677705957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7097555081505838281098437 1330791577782344677705957)
                    ·
                      rfl

theorem cell23_7775122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 2, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 2, 1, 1, 1, 4, 4].length) (baseStart_7775122 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7775122 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7775122 prefixEnd_7775122 := by exact prefixLift 7775122
  have htrace : WordTrace (prefixWord ++ tailWord_7775122) baseStart_7775122 baseEnd_7775122 := by
    simpa [prefixWord, tailWord_7775122, baseEnd_7775122] using wordTrace_append hprefix tailTrace_7775122
  have hstable : (prefixWord ++ tailWord_7775122).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7775122).length < 2 ^ (prefixWord ++ tailWord_7775122).sum := by decide
  have hdescent : baseEnd_7775122 < baseStart_7775122 := by decide
  rcases family_descends (prefixWord ++ tailWord_7775122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7775151 : List Nat := [1, 1, 2, 1, 2, 2, 2, 1, 1, 2, 8]
def baseStart_7775151 : Nat := 118140960795 + 7775151 * 2 ^ 59
def prefixEnd_7775151 : Nat := 4983230072969 + 3 ^ 40 * 7775151 * 2
def baseEnd_7775151 : Nat := 3992389624286014419655237

theorem tailTrace_7775151 : CollatzResearch.WordTrace tailWord_7775151 prefixEnd_7775151 3992389624286014419655237 := by
  unfold tailWord_7775151
  simp only [CollatzResearch.WordTrace]
  refine ⟨283583054254963291917181307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189055369503308861278120871 283583054254963291917181307)
  ·
    refine ⟨425374581382444937875771961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 283583054254963291917181307 425374581382444937875771961)
    ·
      refine ⟨319030936036833703406828971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 425374581382444937875771961 319030936036833703406828971)
      ·
        refine ⟨478546404055250555110243457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 319030936036833703406828971 478546404055250555110243457)
        ·
          refine ⟨358909803041437916332682593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 478546404055250555110243457 358909803041437916332682593)
          ·
            refine ⟨269182352281078437249511945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 358909803041437916332682593 269182352281078437249511945)
            ·
              refine ⟨201886764210808827937133959, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 269182352281078437249511945 201886764210808827937133959)
              ·
                refine ⟨302830146316213241905700939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 201886764210808827937133959 302830146316213241905700939)
                ·
                  refine ⟨454245219474319862858551409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 302830146316213241905700939 454245219474319862858551409)
                  ·
                    refine ⟨340683914605739897143913557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 454245219474319862858551409 340683914605739897143913557)
                    ·
                      refine ⟨3992389624286014419655237, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 340683914605739897143913557 3992389624286014419655237)
                      ·
                        rfl

theorem cell23_7775151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 2, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 2, 1, 1, 2, 8].length) (baseStart_7775151 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7775151 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7775151 prefixEnd_7775151 := by exact prefixLift 7775151
  have htrace : WordTrace (prefixWord ++ tailWord_7775151) baseStart_7775151 baseEnd_7775151 := by
    simpa [prefixWord, tailWord_7775151, baseEnd_7775151] using wordTrace_append hprefix tailTrace_7775151
  have hstable : (prefixWord ++ tailWord_7775151).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7775151).length < 2 ^ (prefixWord ++ tailWord_7775151).sum := by decide
  have hdescent : baseEnd_7775151 < baseStart_7775151 := by decide
  rcases family_descends (prefixWord ++ tailWord_7775151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7775208 : List Nat := [2, 1, 4, 1, 1, 1, 2, 4, 7]
def baseStart_7775208 : Nat := 118140960795 + 7775208 * 2 ^ 59
def prefixEnd_7775208 : Nat := 4983230072969 + 3 ^ 40 * 7775208 * 2
def baseEnd_7775208 : Nat := 443602099187035632960275

theorem tailTrace_7775208 : CollatzResearch.WordTrace tailWord_7775208 prefixEnd_7775208 443602099187035632960275 := by
  unfold tailWord_7775208
  simp only [CollatzResearch.WordTrace]
  refine ⟨141792566607878395326003139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 189056755477171193768004185 141792566607878395326003139)
  ·
    refine ⟨212688849911817592989004709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141792566607878395326003139 212688849911817592989004709)
    ·
      refine ⟨39879159358465798685438383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 212688849911817592989004709 39879159358465798685438383)
      ·
        refine ⟨59818739037698698028157575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39879159358465798685438383 59818739037698698028157575)
        ·
          refine ⟨89728108556548047042236363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59818739037698698028157575 89728108556548047042236363)
          ·
            refine ⟨134592162834822070563354545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89728108556548047042236363 134592162834822070563354545)
            ·
              refine ⟨100944122126116552922515909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 134592162834822070563354545 100944122126116552922515909)
              ·
                refine ⟨18927022898646853672971733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 100944122126116552922515909 18927022898646853672971733)
                ·
                  refine ⟨443602099187035632960275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18927022898646853672971733 443602099187035632960275)
                  ·
                    rfl

theorem cell23_7775208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 2, 4, 7].length) (baseStart_7775208 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7775208 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7775208 prefixEnd_7775208 := by exact prefixLift 7775208
  have htrace : WordTrace (prefixWord ++ tailWord_7775208) baseStart_7775208 baseEnd_7775208 := by
    simpa [prefixWord, tailWord_7775208, baseEnd_7775208] using wordTrace_append hprefix tailTrace_7775208
  have hstable : (prefixWord ++ tailWord_7775208).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7775208).length < 2 ^ (prefixWord ++ tailWord_7775208).sum := by decide
  have hdescent : baseEnd_7775208 < baseStart_7775208 := by decide
  rcases family_descends (prefixWord ++ tailWord_7775208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7775225 : List Nat := [1, 2, 1, 3, 1, 3, 2, 5, 5]
def baseStart_7775225 : Nat := 118140960795 + 7775225 * 2 ^ 59
def prefixEnd_7775225 : Nat := 4983230072969 + 3 ^ 40 * 7775225 * 2
def baseEnd_7775225 : Nat := 443603069094938570014433

theorem tailTrace_7775225 : CollatzResearch.WordTrace tailWord_7775225 prefixEnd_7775225 443603069094938570014433 := by
  unfold tailWord_7775225
  simp only [CollatzResearch.WordTrace]
  refine ⟨283585753256695202555375129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189057168837796801703583419 283585753256695202555375129)
  ·
    refine ⟨212689314942521401916531347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 283585753256695202555375129 212689314942521401916531347)
    ·
      refine ⟨319033972413782102874797021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 212689314942521401916531347 319033972413782102874797021)
      ·
        refine ⟨119637739655168288578048883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 319033972413782102874797021 119637739655168288578048883)
        ·
          refine ⟨179456609482752432867073325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 119637739655168288578048883 179456609482752432867073325)
          ·
            refine ⟨67296228556032162325152497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 179456609482752432867073325 67296228556032162325152497)
            ·
              refine ⟨50472171417024121743864373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 67296228556032162325152497 50472171417024121743864373)
              ·
                refine ⟨4731766070346011413487285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 50472171417024121743864373 4731766070346011413487285)
                ·
                  refine ⟨443603069094938570014433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4731766070346011413487285 443603069094938570014433)
                  ·
                    rfl

theorem cell23_7775225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 2, 5, 5].length) (baseStart_7775225 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7775225 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7775225 prefixEnd_7775225 := by exact prefixLift 7775225
  have htrace : WordTrace (prefixWord ++ tailWord_7775225) baseStart_7775225 baseEnd_7775225 := by
    simpa [prefixWord, tailWord_7775225, baseEnd_7775225] using wordTrace_append hprefix tailTrace_7775225
  have hstable : (prefixWord ++ tailWord_7775225).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7775225).length < 2 ^ (prefixWord ++ tailWord_7775225).sum := by decide
  have hdescent : baseEnd_7775225 < baseStart_7775225 := by decide
  rcases family_descends (prefixWord ++ tailWord_7775225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7775242 : List Nat := [3, 1, 2, 2, 3, 2, 1, 4, 5]
def baseStart_7775242 : Nat := 118140960795 + 7775242 * 2 ^ 59
def prefixEnd_7775242 : Nat := 4983230072969 + 3 ^ 40 * 7775242 * 2
def baseEnd_7775242 : Nat := 443604039002841507068591

theorem tailTrace_7775242 : CollatzResearch.WordTrace tailWord_7775242 prefixEnd_7775242 443604039002841507068591 := by
  unfold tailWord_7775242
  simp only [CollatzResearch.WordTrace]
  refine ⟨70896593324408403614685995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 189057582198422409639162653 70896593324408403614685995)
  ·
    refine ⟨106344889986612605422028993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70896593324408403614685995 106344889986612605422028993)
    ·
      refine ⟨79758667489959454066521745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 106344889986612605422028993 79758667489959454066521745)
      ·
        refine ⟨59819000617469590549891309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79758667489959454066521745 59819000617469590549891309)
        ·
          refine ⟨22432125231551096456209241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 59819000617469590549891309 22432125231551096456209241)
          ·
            refine ⟨16824093923663322342156931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22432125231551096456209241 16824093923663322342156931)
            ·
              refine ⟨25236140885494983513235397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16824093923663322342156931 25236140885494983513235397)
              ·
                refine ⟨4731776416030309408731637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25236140885494983513235397 4731776416030309408731637)
                ·
                  refine ⟨443604039002841507068591, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4731776416030309408731637 443604039002841507068591)
                  ·
                    rfl

theorem cell23_7775242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 2, 1, 4, 5].length) (baseStart_7775242 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7775242 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7775242 prefixEnd_7775242 := by exact prefixLift 7775242
  have htrace : WordTrace (prefixWord ++ tailWord_7775242) baseStart_7775242 baseEnd_7775242 := by
    simpa [prefixWord, tailWord_7775242, baseEnd_7775242] using wordTrace_append hprefix tailTrace_7775242
  have hstable : (prefixWord ++ tailWord_7775242).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7775242).length < 2 ^ (prefixWord ++ tailWord_7775242).sum := by decide
  have hdescent : baseEnd_7775242 < baseStart_7775242 := by decide
  rcases family_descends (prefixWord ++ tailWord_7775242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7775275 : List Nat := [1, 1, 1, 1, 2, 1, 5, 2, 1, 6, 2]
def baseStart_7775275 : Nat := 118140960795 + 7775275 * 2 ^ 59
def prefixEnd_7775275 : Nat := 4983230072969 + 3 ^ 40 * 7775275 * 2
def baseEnd_7775275 : Nat := 3992453295887171934504667

theorem tailTrace_7775275 : CollatzResearch.WordTrace tailWord_7775275 prefixEnd_7775275 3992453295887171934504667 := by
  unfold tailWord_7775275
  simp only [CollatzResearch.WordTrace]
  refine ⟨283587576906514061094695279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189058384604342707396463519 283587576906514061094695279)
  ·
    refine ⟨425381365359771091642042919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 283587576906514061094695279 425381365359771091642042919)
    ·
      refine ⟨638072048039656637463064379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 425381365359771091642042919 638072048039656637463064379)
      ·
        refine ⟨957108072059484956194596569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 638072048039656637463064379 957108072059484956194596569)
        ·
          refine ⟨717831054044613717145947427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 957108072059484956194596569 717831054044613717145947427)
          ·
            refine ⟨1076746581066920575718921141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 717831054044613717145947427 1076746581066920575718921141)
            ·
              refine ⟨100944991975023803973648857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1076746581066920575718921141 100944991975023803973648857)
              ·
                refine ⟨75708743981267852980236643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 100944991975023803973648857 75708743981267852980236643)
                ·
                  refine ⟨113563115971901779470354965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 75708743981267852980236643 113563115971901779470354965)
                  ·
                    refine ⟨5323271061182895912672889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 113563115971901779470354965 5323271061182895912672889)
                    ·
                      refine ⟨3992453295887171934504667, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5323271061182895912672889 3992453295887171934504667)
                      ·
                        rfl

theorem cell23_7775275_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 5, 2, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 5, 2, 1, 6, 2].length) (baseStart_7775275 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7775275 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7775275 prefixEnd_7775275 := by exact prefixLift 7775275
  have htrace : WordTrace (prefixWord ++ tailWord_7775275) baseStart_7775275 baseEnd_7775275 := by
    simpa [prefixWord, tailWord_7775275, baseEnd_7775275] using wordTrace_append hprefix tailTrace_7775275
  have hstable : (prefixWord ++ tailWord_7775275).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7775275).length < 2 ^ (prefixWord ++ tailWord_7775275).sum := by decide
  have hdescent : baseEnd_7775275 < baseStart_7775275 := by decide
  rcases family_descends (prefixWord ++ tailWord_7775275) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7775285 : List Nat := [1, 3, 3, 1, 1, 1, 1, 1, 7, 4]
def baseStart_7775285 : Nat := 118140960795 + 7775285 * 2 ^ 59
def prefixEnd_7775285 : Nat := 4983230072969 + 3 ^ 40 * 7775285 * 2
def baseEnd_7775285 : Nat := 1330819476897905631793207

theorem tailTrace_7775285 : CollatzResearch.WordTrace tailWord_7775285 prefixEnd_7775285 1330819476897905631793207 := by
  unfold tailWord_7775285
  simp only [CollatzResearch.WordTrace]
  refine ⟨283587941636477832802559309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189058627757651888535039539 283587941636477832802559309)
  ·
    refine ⟨106345478113679187300959741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 283587941636477832802559309 106345478113679187300959741)
    ·
      refine ⟨39879554292629695237859903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 106345478113679187300959741 39879554292629695237859903)
      ·
        refine ⟨59819331438944542856789855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39879554292629695237859903 59819331438944542856789855)
        ·
          refine ⟨89728997158416814285184783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59819331438944542856789855 89728997158416814285184783)
          ·
            refine ⟨134593495737625221427777175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89728997158416814285184783 134593495737625221427777175)
            ·
              refine ⟨201890243606437832141665763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 134593495737625221427777175 201890243606437832141665763)
              ·
                refine ⟨302835365409656748212498645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 201890243606437832141665763 302835365409656748212498645)
                ·
                  refine ⟨7097703876788830036230437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 302835365409656748212498645 7097703876788830036230437)
                  ·
                    refine ⟨1330819476897905631793207, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7097703876788830036230437 1330819476897905631793207)
                    ·
                      rfl

theorem cell23_7775285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 1, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 1, 1, 7, 4].length) (baseStart_7775285 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7775285 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7775285 prefixEnd_7775285 := by exact prefixLift 7775285
  have htrace : WordTrace (prefixWord ++ tailWord_7775285) baseStart_7775285 baseEnd_7775285 := by
    simpa [prefixWord, tailWord_7775285, baseEnd_7775285] using wordTrace_append hprefix tailTrace_7775285
  have hstable : (prefixWord ++ tailWord_7775285).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7775285).length < 2 ^ (prefixWord ++ tailWord_7775285).sum := by decide
  have hdescent : baseEnd_7775285 < baseStart_7775285 := by decide
  rcases family_descends (prefixWord ++ tailWord_7775285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7775292 : List Nat := [2, 2, 2, 2, 2, 2, 1, 2, 2, 4, 2]
def baseStart_7775292 : Nat := 118140960795 + 7775292 * 2 ^ 59
def prefixEnd_7775292 : Nat := 4983230072969 + 3 ^ 40 * 7775292 * 2
def baseEnd_7775292 : Nat := 3992462025058298367992089

theorem tailTrace_7775292 : CollatzResearch.WordTrace tailWord_7775292 prefixEnd_7775292 3992462025058298367992089 := by
  unfold tailWord_7775292
  simp only [CollatzResearch.WordTrace]
  refine ⟨141794098473726236499032065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 189058797964968315332042753 141794098473726236499032065)
  ·
    refine ⟨106345573855294677374274049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 141794098473726236499032065 106345573855294677374274049)
    ·
      refine ⟨79759180391471008030705537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 106345573855294677374274049 79759180391471008030705537)
      ·
        refine ⟨59819385293603256023029153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79759180391471008030705537 59819385293603256023029153)
        ·
          refine ⟨44864538970202442017271865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59819385293603256023029153 44864538970202442017271865)
          ·
            refine ⟨33648404227651831512953899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44864538970202442017271865 33648404227651831512953899)
            ·
              refine ⟨50472606341477747269430849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33648404227651831512953899 50472606341477747269430849)
              ·
                refine ⟨37854454756108310452073137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50472606341477747269430849 37854454756108310452073137)
                ·
                  refine ⟨28390841067081232839054853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37854454756108310452073137 28390841067081232839054853)
                  ·
                    refine ⟨5323282700077731157322785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28390841067081232839054853 5323282700077731157322785)
                    ·
                      refine ⟨3992462025058298367992089, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5323282700077731157322785 3992462025058298367992089)
                      ·
                        rfl

theorem cell23_7775292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 2, 1, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 2, 1, 2, 2, 4, 2].length) (baseStart_7775292 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7775292 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7775292 prefixEnd_7775292 := by exact prefixLift 7775292
  have htrace : WordTrace (prefixWord ++ tailWord_7775292) baseStart_7775292 baseEnd_7775292 := by
    simpa [prefixWord, tailWord_7775292, baseEnd_7775292] using wordTrace_append hprefix tailTrace_7775292
  have hstable : (prefixWord ++ tailWord_7775292).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7775292).length < 2 ^ (prefixWord ++ tailWord_7775292).sum := by decide
  have hdescent : baseEnd_7775292 < baseStart_7775292 := by decide
  rcases family_descends (prefixWord ++ tailWord_7775292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7775295 : List Nat := [1, 1, 2, 2, 3, 1, 1, 3, 4, 2, 3]
def baseStart_7775295 : Nat := 118140960795 + 7775295 * 2 ^ 59
def prefixEnd_7775295 : Nat := 4983230072969 + 3 ^ 40 * 7775295 * 2
def baseEnd_7775295 : Nat := 3992463565500261856254575

theorem tailTrace_7775295 : CollatzResearch.WordTrace tailWord_7775295 prefixEnd_7775295 3992463565500261856254575 := by
  unfold tailWord_7775295
  simp only [CollatzResearch.WordTrace]
  refine ⟨283588306366441604510423339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189058870910961069673615559 283588306366441604510423339)
  ·
    refine ⟨425382459549662406765635009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 283588306366441604510423339 425382459549662406765635009)
    ·
      refine ⟨319036844662246805074226257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 425382459549662406765635009 319036844662246805074226257)
      ·
        refine ⟨239277633496685103805669693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 319036844662246805074226257 239277633496685103805669693)
        ·
          refine ⟨89729112561256913927126135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 239277633496685103805669693 89729112561256913927126135)
          ·
            refine ⟨134593668841885370890689203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89729112561256913927126135 134593668841885370890689203)
            ·
              refine ⟨201890503262828056336033805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 134593668841885370890689203 201890503262828056336033805)
              ·
                refine ⟨75708938723560521126012677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 201890503262828056336033805 75708938723560521126012677)
                ·
                  refine ⟨14195426010667597711127377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 75708938723560521126012677 14195426010667597711127377)
                  ·
                    refine ⟨10646569508000698283345533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14195426010667597711127377 10646569508000698283345533)
                    ·
                      refine ⟨3992463565500261856254575, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10646569508000698283345533 3992463565500261856254575)
                      ·
                        rfl

theorem cell23_7775295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 1, 3, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 1, 3, 4, 2, 3].length) (baseStart_7775295 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7775295 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7775295 prefixEnd_7775295 := by exact prefixLift 7775295
  have htrace : WordTrace (prefixWord ++ tailWord_7775295) baseStart_7775295 baseEnd_7775295 := by
    simpa [prefixWord, tailWord_7775295, baseEnd_7775295] using wordTrace_append hprefix tailTrace_7775295
  have hstable : (prefixWord ++ tailWord_7775295).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7775295).length < 2 ^ (prefixWord ++ tailWord_7775295).sum := by decide
  have hdescent : baseEnd_7775295 < baseStart_7775295 := by decide
  rcases family_descends (prefixWord ++ tailWord_7775295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7775309 : List Nat := [1, 6, 1, 1, 1, 2, 2, 1, 2, 4, 2]
def baseStart_7775309 : Nat := 118140960795 + 7775309 * 2 ^ 59
def prefixEnd_7775309 : Nat := 4983230072969 + 3 ^ 40 * 7775309 * 2
def baseEnd_7775309 : Nat := 3992470754229424801479511

theorem tailTrace_7775309 : CollatzResearch.WordTrace tailWord_7775309 prefixEnd_7775309 3992470754229424801479511 := by
  unfold tailWord_7775309
  simp only [CollatzResearch.WordTrace]
  refine ⟨283588816988390884901432981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189059211325593923267621987 283588816988390884901432981)
  ·
    refine ⟨13293225796330822729754671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 283588816988390884901432981 13293225796330822729754671)
    ·
      refine ⟨19939838694496234094632007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13293225796330822729754671 19939838694496234094632007)
      ·
        refine ⟨29909758041744351141948011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19939838694496234094632007 29909758041744351141948011)
        ·
          refine ⟨44864637062616526712922017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29909758041744351141948011 44864637062616526712922017)
          ·
            refine ⟨33648477796962395034691513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44864637062616526712922017 33648477796962395034691513)
            ·
              refine ⟨25236358347721796276018635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33648477796962395034691513 25236358347721796276018635)
              ·
                refine ⟨37854537521582694414027953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25236358347721796276018635 37854537521582694414027953)
                ·
                  refine ⟨28390903141187020810520965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37854537521582694414027953 28390903141187020810520965)
                  ·
                    refine ⟨5323294338972566401972681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28390903141187020810520965 5323294338972566401972681)
                    ·
                      refine ⟨3992470754229424801479511, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5323294338972566401972681 3992470754229424801479511)
                      ·
                        rfl

theorem cell23_7775309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 2, 2, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 2, 2, 1, 2, 4, 2].length) (baseStart_7775309 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7775309 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7775309 prefixEnd_7775309 := by exact prefixLift 7775309
  have htrace : WordTrace (prefixWord ++ tailWord_7775309) baseStart_7775309 baseEnd_7775309 := by
    simpa [prefixWord, tailWord_7775309, baseEnd_7775309] using wordTrace_append hprefix tailTrace_7775309
  have hstable : (prefixWord ++ tailWord_7775309).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7775309).length < 2 ^ (prefixWord ++ tailWord_7775309).sum := by decide
  have hdescent : baseEnd_7775309 < baseStart_7775309 := by decide
  rcases family_descends (prefixWord ++ tailWord_7775309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7775352 : List Nat := [2, 1, 2, 1, 1, 1, 5, 1, 4, 3, 2]
def baseStart_7775352 : Nat := 118140960795 + 7775352 * 2 ^ 59
def prefixEnd_7775352 : Nat := 4983230072969 + 3 ^ 40 * 7775352 * 2
def baseEnd_7775352 : Nat := 3992492833897568133241813

theorem tailTrace_7775352 : CollatzResearch.WordTrace tailWord_7775352 prefixEnd_7775352 3992492833897568133241813 := by
  unfold tailWord_7775352
  simp only [CollatzResearch.WordTrace]
  refine ⟨141795192663617551622624155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 189060256884823402163498873 141795192663617551622624155)
  ·
    refine ⟨212692788995426327433936233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141795192663617551622624155 212692788995426327433936233)
    ·
      refine ⟨159519591746569745575452175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 212692788995426327433936233 159519591746569745575452175)
      ·
        refine ⟨239279387619854618363178263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 159519591746569745575452175 239279387619854618363178263)
        ·
          refine ⟨358919081429781927544767395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 239279387619854618363178263 358919081429781927544767395)
          ·
            refine ⟨538378622144672891317151093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 358919081429781927544767395 538378622144672891317151093)
            ·
              refine ⟨50472995826063083560982915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 538378622144672891317151093 50472995826063083560982915)
              ·
                refine ⟨75709493739094625341474373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50472995826063083560982915 75709493739094625341474373)
                ·
                  refine ⟨14195530076080242251526445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 75709493739094625341474373 14195530076080242251526445)
                  ·
                    refine ⟨5323323778530090844322417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14195530076080242251526445 5323323778530090844322417)
                    ·
                      refine ⟨3992492833897568133241813, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5323323778530090844322417 3992492833897568133241813)
                      ·
                        rfl

theorem cell23_7775352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 5, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 5, 1, 4, 3, 2].length) (baseStart_7775352 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7775352 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7775352 prefixEnd_7775352 := by exact prefixLift 7775352
  have htrace : WordTrace (prefixWord ++ tailWord_7775352) baseStart_7775352 baseEnd_7775352 := by
    simpa [prefixWord, tailWord_7775352, baseEnd_7775352] using wordTrace_append hprefix tailTrace_7775352
  have hstable : (prefixWord ++ tailWord_7775352).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7775352).length < 2 ^ (prefixWord ++ tailWord_7775352).sum := by decide
  have hdescent : baseEnd_7775352 < baseStart_7775352 := by decide
  rcases family_descends (prefixWord ++ tailWord_7775352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7775386 : List Nat := [3, 1, 1, 5, 1, 2, 2, 1, 2, 3, 2]
def baseStart_7775386 : Nat := 118140960795 + 7775386 * 2 ^ 59
def prefixEnd_7775386 : Nat := 4983230072969 + 3 ^ 40 * 7775386 * 2
def baseEnd_7775386 : Nat := 3992510292239821000216657

theorem tailTrace_7775386 : CollatzResearch.WordTrace tailWord_7775386 prefixEnd_7775386 3992510292239821000216657 := by
  unfold tailWord_7775386
  simp only [CollatzResearch.WordTrace]
  refine ⟨70897906352277981762996503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 189061083606074618034657341 70897906352277981762996503)
  ·
    refine ⟨106346859528416972644494755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70897906352277981762996503 106346859528416972644494755)
    ·
      refine ⟨159520289292625458966742133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106346859528416972644494755 159520289292625458966742133)
      ·
        refine ⟨14955027121183636778132075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 159520289292625458966742133 14955027121183636778132075)
        ·
          refine ⟨22432540681775455167198113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14955027121183636778132075 22432540681775455167198113)
          ·
            refine ⟨16824405511331591375398585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22432540681775455167198113 16824405511331591375398585)
            ·
              refine ⟨12618304133498693531548939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16824405511331591375398585 12618304133498693531548939)
              ·
                refine ⟨18927456200248040297323409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12618304133498693531548939 18927456200248040297323409)
                ·
                  refine ⟨14195592150186030222992557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18927456200248040297323409 14195592150186030222992557)
                  ·
                    refine ⟨5323347056319761333622209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14195592150186030222992557 5323347056319761333622209)
                    ·
                      refine ⟨3992510292239821000216657, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5323347056319761333622209 3992510292239821000216657)
                      ·
                        rfl

theorem cell23_7775386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 2, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 2, 2, 1, 2, 3, 2].length) (baseStart_7775386 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7775386 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7775386 prefixEnd_7775386 := by exact prefixLift 7775386
  have htrace : WordTrace (prefixWord ++ tailWord_7775386) baseStart_7775386 baseEnd_7775386 := by
    simpa [prefixWord, tailWord_7775386, baseEnd_7775386] using wordTrace_append hprefix tailTrace_7775386
  have hstable : (prefixWord ++ tailWord_7775386).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7775386).length < 2 ^ (prefixWord ++ tailWord_7775386).sum := by decide
  have hdescent : baseEnd_7775386 < baseStart_7775386 := by decide
  rcases family_descends (prefixWord ++ tailWord_7775386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7775405 : List Nat := [1, 5, 2, 1, 14]
def baseStart_7775405 : Nat := 118140960795 + 7775405 * 2 ^ 59
def prefixEnd_7775405 : Nat := 4983230072969 + 3 ^ 40 * 7775405 * 2
def baseEnd_7775405 : Nat := 5476707885284302367461

theorem tailTrace_7775405 : CollatzResearch.WordTrace tailWord_7775405 prefixEnd_7775405 5476707885284302367461 := by
  unfold tailWord_7775405
  simp only [CollatzResearch.WordTrace]
  refine ⟨283592318396043093296927669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189061545597362062197951779 283592318396043093296927669)
  ·
    refine ⟨26586779849629039996586969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 283592318396043093296927669 26586779849629039996586969)
    ·
      refine ⟨19940084887221779997440227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26586779849629039996586969 19940084887221779997440227)
      ·
        refine ⟨29910127330832669996160341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19940084887221779997440227 29910127330832669996160341)
        ·
          refine ⟨5476707885284302367461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 14 29910127330832669996160341 5476707885284302367461)
          ·
            rfl

theorem cell23_7775405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 14].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 14].length) (baseStart_7775405 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7775405 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7775405 prefixEnd_7775405 := by exact prefixLift 7775405
  have htrace : WordTrace (prefixWord ++ tailWord_7775405) baseStart_7775405 baseEnd_7775405 := by
    simpa [prefixWord, tailWord_7775405, baseEnd_7775405] using wordTrace_append hprefix tailTrace_7775405
  have hstable : (prefixWord ++ tailWord_7775405).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7775405).length < 2 ^ (prefixWord ++ tailWord_7775405).sum := by decide
  have hdescent : baseEnd_7775405 < baseStart_7775405 := by decide
  rcases family_descends (prefixWord ++ tailWord_7775405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7775409 : List Nat := [1, 2, 2, 5, 1, 1, 1, 4, 2, 4]
def baseStart_7775409 : Nat := 118140960795 + 7775409 * 2 ^ 59
def prefixEnd_7775409 : Nat := 4983230072969 + 3 ^ 40 * 7775409 * 2
def baseEnd_7775409 : Nat := 1330840700764958136743017

theorem tailTrace_7775409 : CollatzResearch.WordTrace tailWord_7775409 prefixEnd_7775409 1330840700764958136743017 := by
  unfold tailWord_7775409
  simp only [CollatzResearch.WordTrace]
  refine ⟨283592464288028601980073281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189061642858685734653382187 283592464288028601980073281)
  ·
    refine ⟨212694348216021451485054961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 283592464288028601980073281 212694348216021451485054961)
    ·
      refine ⟨159520761162016088613791221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 212694348216021451485054961 159520761162016088613791221)
      ·
        refine ⟨14955071358939008307542927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 159520761162016088613791221 14955071358939008307542927)
        ·
          refine ⟨22432607038408512461314391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14955071358939008307542927 22432607038408512461314391)
          ·
            refine ⟨33648910557612768691971587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22432607038408512461314391 33648910557612768691971587)
            ·
              refine ⟨50473365836419153037957381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33648910557612768691971587 50473365836419153037957381)
              ·
                refine ⟨9463756094328591194617009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 50473365836419153037957381 9463756094328591194617009)
                ·
                  refine ⟨7097817070746443395962757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9463756094328591194617009 7097817070746443395962757)
                  ·
                    refine ⟨1330840700764958136743017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7097817070746443395962757 1330840700764958136743017)
                    ·
                      rfl

theorem cell23_7775409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 1, 1, 4, 2, 4].length) (baseStart_7775409 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7775409 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7775409 prefixEnd_7775409 := by exact prefixLift 7775409
  have htrace : WordTrace (prefixWord ++ tailWord_7775409) baseStart_7775409 baseEnd_7775409 := by
    simpa [prefixWord, tailWord_7775409, baseEnd_7775409] using wordTrace_append hprefix tailTrace_7775409
  have hstable : (prefixWord ++ tailWord_7775409).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7775409).length < 2 ^ (prefixWord ++ tailWord_7775409).sum := by decide
  have hdescent : baseEnd_7775409 < baseStart_7775409 := by decide
  rcases family_descends (prefixWord ++ tailWord_7775409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7775422 : List Nat := [4, 2, 1, 1, 3, 1, 3, 8]
def baseStart_7775422 : Nat := 118140960795 + 7775422 * 2 ^ 59
def prefixEnd_7775422 : Nat := 4983230072969 + 3 ^ 40 * 7775422 * 2
def baseEnd_7775422 : Nat := 147871436205310476272833

theorem tailTrace_7775422 : CollatzResearch.WordTrace tailWord_7775422 prefixEnd_7775422 147871436205310476272833 := by
  unfold tailWord_7775422
  simp only [CollatzResearch.WordTrace]
  refine ⟨35449117304622688150037065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 189061958957987670133531013 35449117304622688150037065)
  ·
    refine ⟨26586837978467016112527799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35449117304622688150037065 26586837978467016112527799)
    ·
      refine ⟨39880256967700524168791699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26586837978467016112527799 39880256967700524168791699)
      ·
        refine ⟨59820385451550786253187549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39880256967700524168791699 59820385451550786253187549)
        ·
          refine ⟨22432644544331544844945331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 59820385451550786253187549 22432644544331544844945331)
          ·
            refine ⟨33648966816497317267417997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22432644544331544844945331 33648966816497317267417997)
            ·
              refine ⟨12618362556186493975281749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33648966816497317267417997 12618362556186493975281749)
              ·
                refine ⟨147871436205310476272833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 12618362556186493975281749 147871436205310476272833)
                ·
                  rfl

theorem cell23_7775422_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 1, 3, 8].length) (baseStart_7775422 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7775422 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7775422 prefixEnd_7775422 := by exact prefixLift 7775422
  have htrace : WordTrace (prefixWord ++ tailWord_7775422) baseStart_7775422 baseEnd_7775422 := by
    simpa [prefixWord, tailWord_7775422, baseEnd_7775422] using wordTrace_append hprefix tailTrace_7775422
  have hstable : (prefixWord ++ tailWord_7775422).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7775422).length < 2 ^ (prefixWord ++ tailWord_7775422).sum := by decide
  have hdescent : baseEnd_7775422 < baseStart_7775422 := by decide
  rcases family_descends (prefixWord ++ tailWord_7775422) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7775432 : List Nat := [2, 1, 3, 1, 2, 1, 3, 3, 1, 3, 3]
def baseStart_7775432 : Nat := 118140960795 + 7775432 * 2 ^ 59
def prefixEnd_7775432 : Nat := 4983230072969 + 3 ^ 40 * 7775432 * 2
def baseEnd_7775432 : Nat := 3992533912349927820241445

theorem tailTrace_7775432 : CollatzResearch.WordTrace tailWord_7775432 prefixEnd_7775432 3992533912349927820241445 := by
  unfold tailWord_7775432
  simp only [CollatzResearch.WordTrace]
  refine ⟨141796651583472638454080275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 189062202111296851272107033 141796651583472638454080275)
  ·
    refine ⟨212694977375208957681120413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141796651583472638454080275 212694977375208957681120413)
    ·
      refine ⟨79760616515703359130420155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 212694977375208957681120413 79760616515703359130420155)
      ·
        refine ⟨119640924773555038695630233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79760616515703359130420155 119640924773555038695630233)
        ·
          refine ⟨89730693580166279021722675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 119640924773555038695630233 89730693580166279021722675)
          ·
            refine ⟨134596040370249418532584013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89730693580166279021722675 134596040370249418532584013)
            ·
              refine ⟨50473515138843531949719005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 134596040370249418532584013 50473515138843531949719005)
              ·
                refine ⟨18927568177066324481144627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 50473515138843531949719005 18927568177066324481144627)
                ·
                  refine ⟨28391352265599486721716941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18927568177066324481144627 28391352265599486721716941)
                  ·
                    refine ⟨10646757099599807520643853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 28391352265599486721716941 10646757099599807520643853)
                    ·
                      refine ⟨3992533912349927820241445, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10646757099599807520643853 3992533912349927820241445)
                      ·
                        rfl

theorem cell23_7775432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 3, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 3, 3, 1, 3, 3].length) (baseStart_7775432 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7775432 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7775432 prefixEnd_7775432 := by exact prefixLift 7775432
  have htrace : WordTrace (prefixWord ++ tailWord_7775432) baseStart_7775432 baseEnd_7775432 := by
    simpa [prefixWord, tailWord_7775432, baseEnd_7775432] using wordTrace_append hprefix tailTrace_7775432
  have hstable : (prefixWord ++ tailWord_7775432).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7775432).length < 2 ^ (prefixWord ++ tailWord_7775432).sum := by decide
  have hdescent : baseEnd_7775432 < baseStart_7775432 := by decide
  rcases family_descends (prefixWord ++ tailWord_7775432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7775437 : List Nat := [1, 6, 2, 2, 2, 1, 1, 1, 2, 3, 2]
def baseStart_7775437 : Nat := 118140960795 + 7775437 * 2 ^ 59
def prefixEnd_7775437 : Nat := 4983230072969 + 3 ^ 40 * 7775437 * 2
def baseEnd_7775437 : Nat := 3992536479753200300678923

theorem tailTrace_7775437 : CollatzResearch.WordTrace tailWord_7775437 prefixEnd_7775437 3992536479753200300678923 := by
  unfold tailWord_7775437
  simp only [CollatzResearch.WordTrace]
  refine ⟨283593485531927162762092565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189062323687951441841395043 283593485531927162762092565)
  ·
    refine ⟨13293444634309085754473089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 283593485531927162762092565 13293444634309085754473089)
    ·
      refine ⟨9970083475731814315854817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13293444634309085754473089 9970083475731814315854817)
      ·
        refine ⟨7477562606798860736891113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9970083475731814315854817 7477562606798860736891113)
        ·
          refine ⟨5608171955099145552668335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7477562606798860736891113 5608171955099145552668335)
          ·
            refine ⟨8412257932648718329002503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5608171955099145552668335 8412257932648718329002503)
            ·
              refine ⟨12618386898973077493503755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8412257932648718329002503 12618386898973077493503755)
              ·
                refine ⟨18927580348459616240255633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12618386898973077493503755 18927580348459616240255633)
                ·
                  refine ⟨14195685261344712180191725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18927580348459616240255633 14195685261344712180191725)
                  ·
                    refine ⟨5323381973004267067571897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14195685261344712180191725 5323381973004267067571897)
                    ·
                      refine ⟨3992536479753200300678923, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5323381973004267067571897 3992536479753200300678923)
                      ·
                        rfl

theorem cell23_7775437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 2, 1, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 2, 1, 1, 1, 2, 3, 2].length) (baseStart_7775437 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7775437 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7775437 prefixEnd_7775437 := by exact prefixLift 7775437
  have htrace : WordTrace (prefixWord ++ tailWord_7775437) baseStart_7775437 baseEnd_7775437 := by
    simpa [prefixWord, tailWord_7775437, baseEnd_7775437] using wordTrace_append hprefix tailTrace_7775437
  have hstable : (prefixWord ++ tailWord_7775437).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7775437).length < 2 ^ (prefixWord ++ tailWord_7775437).sum := by decide
  have hdescent : baseEnd_7775437 < baseStart_7775437 := by decide
  rcases family_descends (prefixWord ++ tailWord_7775437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7775466 : List Nat := [3, 1, 3, 1, 1, 3, 3, 2, 2, 1, 3]
def baseStart_7775466 : Nat := 118140960795 + 7775466 * 2 ^ 59
def prefixEnd_7775466 : Nat := 4983230072969 + 3 ^ 40 * 7775466 * 2
def baseEnd_7775466 : Nat := 3992551370692180687216289

theorem tailTrace_7775466 : CollatzResearch.WordTrace tailWord_7775466 prefixEnd_7775466 3992551370692180687216289 := by
  unfold tailWord_7775466
  simp only [CollatzResearch.WordTrace]
  refine ⟨70898635812205525178724563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 189063028832548067143265501 70898635812205525178724563)
  ·
    refine ⟨106347953718308287768086845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70898635812205525178724563 106347953718308287768086845)
    ·
      refine ⟨39880482644365607913032567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 106347953718308287768086845 39880482644365607913032567)
      ·
        refine ⟨59820723966548411869548851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39880482644365607913032567 59820723966548411869548851)
        ·
          refine ⟨89731085949822617804323277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59820723966548411869548851 89731085949822617804323277)
          ·
            refine ⟨33649157231183481676621229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 89731085949822617804323277 33649157231183481676621229)
            ·
              refine ⟨12618433961693805628732961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33649157231183481676621229 12618433961693805628732961)
              ·
                refine ⟨9463825471270354221549721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12618433961693805628732961 9463825471270354221549721)
                ·
                  refine ⟨7097869103452765666162291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9463825471270354221549721 7097869103452765666162291)
                  ·
                    refine ⟨10646803655179148499243437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7097869103452765666162291 10646803655179148499243437)
                    ·
                      refine ⟨3992551370692180687216289, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10646803655179148499243437 3992551370692180687216289)
                      ·
                        rfl

theorem cell23_7775466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 3, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 3, 3, 2, 2, 1, 3].length) (baseStart_7775466 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7775466 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7775466 prefixEnd_7775466 := by exact prefixLift 7775466
  have htrace : WordTrace (prefixWord ++ tailWord_7775466) baseStart_7775466 baseEnd_7775466 := by
    simpa [prefixWord, tailWord_7775466, baseEnd_7775466] using wordTrace_append hprefix tailTrace_7775466
  have hstable : (prefixWord ++ tailWord_7775466).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7775466).length < 2 ^ (prefixWord ++ tailWord_7775466).sum := by decide
  have hdescent : baseEnd_7775466 < baseStart_7775466 := by decide
  rcases family_descends (prefixWord ++ tailWord_7775466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7775472 : List Nat := [2, 1, 1, 1, 3, 1, 1, 1, 2, 8, 2]
def baseStart_7775472 : Nat := 118140960795 + 7775472 * 2 ^ 59
def prefixEnd_7775472 : Nat := 4983230072969 + 3 ^ 40 * 7775472 * 2
def baseEnd_7775472 : Nat := 3992554451576107663741261

theorem tailTrace_7775472 : CollatzResearch.WordTrace tailWord_7775472 prefixEnd_7775472 3992554451576107663741261 := by
  unfold tailWord_7775472
  simp only [CollatzResearch.WordTrace]
  refine ⟨141797381043400181869808335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 189063174724533575826411113 141797381043400181869808335)
  ·
    refine ⟨212696071565100272804712503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141797381043400181869808335 212696071565100272804712503)
    ·
      refine ⟨319044107347650409207068755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 212696071565100272804712503 319044107347650409207068755)
      ·
        refine ⟨478566161021475613810603133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 319044107347650409207068755 478566161021475613810603133)
        ·
          refine ⟨179462310383053355178976175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 478566161021475613810603133 179462310383053355178976175)
          ·
            refine ⟨269193465574580032768464263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 179462310383053355178976175 269193465574580032768464263)
            ·
              refine ⟨403790198361870049152696395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 269193465574580032768464263 403790198361870049152696395)
              ·
                refine ⟨605685297542805073729044593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 403790198361870049152696395 605685297542805073729044593)
                ·
                  refine ⟨454263973157103805296783445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 605685297542805073729044593 454263973157103805296783445)
                  ·
                    refine ⟨5323405935434810218321681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 454263973157103805296783445 5323405935434810218321681)
                    ·
                      refine ⟨3992554451576107663741261, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5323405935434810218321681 3992554451576107663741261)
                      ·
                        rfl

theorem cell23_7775472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 1, 1, 2, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 1, 1, 2, 8, 2].length) (baseStart_7775472 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7775472 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7775472 prefixEnd_7775472 := by exact prefixLift 7775472
  have htrace : WordTrace (prefixWord ++ tailWord_7775472) baseStart_7775472 baseEnd_7775472 := by
    simpa [prefixWord, tailWord_7775472, baseEnd_7775472] using wordTrace_append hprefix tailTrace_7775472
  have hstable : (prefixWord ++ tailWord_7775472).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7775472).length < 2 ^ (prefixWord ++ tailWord_7775472).sum := by decide
  have hdescent : baseEnd_7775472 < baseStart_7775472 := by decide
  rcases family_descends (prefixWord ++ tailWord_7775472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7775559 : List Nat := [1, 1, 4, 1, 2, 4, 2, 1, 2, 5]
def baseStart_7775559 : Nat := 118140960795 + 7775559 * 2 ^ 59
def prefixEnd_7775559 : Nat := 4983230072969 + 3 ^ 40 * 7775559 * 2
def baseEnd_7775559 : Nat := 1330866374797682941117787

theorem tailTrace_7775559 : CollatzResearch.WordTrace tailWord_7775559 prefixEnd_7775559 1330866374797682941117787 := by
  unfold tailWord_7775559
  simp only [CollatzResearch.WordTrace]
  refine ⟨283597935237485177598033731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189065290158323451732022487 283597935237485177598033731)
  ·
    refine ⟨425396902856227766397050597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 283597935237485177598033731 425396902856227766397050597)
    ·
      refine ⟨79761919285542706199446987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 425396902856227766397050597 79761919285542706199446987)
      ·
        refine ⟨119642878928314059299170481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79761919285542706199446987 119642878928314059299170481)
        ·
          refine ⟨89732159196235544474377861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 119642878928314059299170481 89732159196235544474377861)
          ·
            refine ⟨16824779849294164588945849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 89732159196235544474377861 16824779849294164588945849)
            ·
              refine ⟨12618584886970623441709387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16824779849294164588945849 12618584886970623441709387)
              ·
                refine ⟨18927877330455935162564081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12618584886970623441709387 18927877330455935162564081)
                ·
                  refine ⟨14195907997841951371923061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18927877330455935162564081 14195907997841951371923061)
                  ·
                    refine ⟨1330866374797682941117787, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14195907997841951371923061 1330866374797682941117787)
                    ·
                      rfl

theorem cell23_7775559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 4, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 4, 2, 1, 2, 5].length) (baseStart_7775559 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7775559 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7775559 prefixEnd_7775559 := by exact prefixLift 7775559
  have htrace : WordTrace (prefixWord ++ tailWord_7775559) baseStart_7775559 baseEnd_7775559 := by
    simpa [prefixWord, tailWord_7775559, baseEnd_7775559] using wordTrace_append hprefix tailTrace_7775559
  have hstable : (prefixWord ++ tailWord_7775559).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7775559).length < 2 ^ (prefixWord ++ tailWord_7775559).sum := by decide
  have hdescent : baseEnd_7775559 < baseStart_7775559 := by decide
  rcases family_descends (prefixWord ++ tailWord_7775559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7775562 : List Nat := [3, 1, 2, 1, 1, 1, 1, 5, 1, 3, 4]
def baseStart_7775562 : Nat := 118140960795 + 7775562 * 2 ^ 59
def prefixEnd_7775562 : Nat := 4983230072969 + 3 ^ 40 * 7775562 * 2
def baseEnd_7775562 : Nat := 3992600664835012311615847

theorem tailTrace_7775562 : CollatzResearch.WordTrace tailWord_7775562 prefixEnd_7775562 3992600664835012311615847 := by
  unfold tailWord_7775562
  simp only [CollatzResearch.WordTrace]
  refine ⟨70899511164118577277598235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 189065363104316206073595293 70899511164118577277598235)
  ·
    refine ⟨106349266746177865916397353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70899511164118577277598235 106349266746177865916397353)
    ·
      refine ⟨79761950059633399437298015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 106349266746177865916397353 79761950059633399437298015)
      ·
        refine ⟨119642925089450099155947023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79761950059633399437298015 119642925089450099155947023)
        ·
          refine ⟨179464387634175148733920535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 119642925089450099155947023 179464387634175148733920535)
          ·
            refine ⟨269196581451262723100880803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 179464387634175148733920535 269196581451262723100880803)
            ·
              refine ⟨403794872176894084651321205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 269196581451262723100880803 403794872176894084651321205)
              ·
                refine ⟨37855769266583820436061363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 403794872176894084651321205 37855769266583820436061363)
                ·
                  refine ⟨56783653899875730654092045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37855769266583820436061363 56783653899875730654092045)
                  ·
                    refine ⟨21293870212453398995284517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 56783653899875730654092045 21293870212453398995284517)
                    ·
                      refine ⟨3992600664835012311615847, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21293870212453398995284517 3992600664835012311615847)
                      ·
                        rfl

theorem cell23_7775562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 1, 5, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 1, 5, 1, 3, 4].length) (baseStart_7775562 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7775562 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7775562 prefixEnd_7775562 := by exact prefixLift 7775562
  have htrace : WordTrace (prefixWord ++ tailWord_7775562) baseStart_7775562 baseEnd_7775562 := by
    simpa [prefixWord, tailWord_7775562, baseEnd_7775562] using wordTrace_append hprefix tailTrace_7775562
  have hstable : (prefixWord ++ tailWord_7775562).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7775562).length < 2 ^ (prefixWord ++ tailWord_7775562).sum := by decide
  have hdescent : baseEnd_7775562 < baseStart_7775562 := by decide
  rcases family_descends (prefixWord ++ tailWord_7775562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7775589 : List Nat := [1, 3, 1, 3, 1, 2, 2, 3, 3, 4]
def baseStart_7775589 : Nat := 118140960795 + 7775589 * 2 ^ 59
def prefixEnd_7775589 : Nat := 4983230072969 + 3 ^ 40 * 7775589 * 2
def baseEnd_7775589 : Nat := 1330871509604227901992741

theorem tailTrace_7775589 : CollatzResearch.WordTrace tailWord_7775589 prefixEnd_7775589 1330871509604227901992741 := by
  unfold tailWord_7775589
  simp only [CollatzResearch.WordTrace]
  refine ⟨283599029427376492721625821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189066019618250995147750547 283599029427376492721625821)
  ·
    refine ⟨106349636035266184770609683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 283599029427376492721625821 106349636035266184770609683)
    ·
      refine ⟨159524454052899277155914525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106349636035266184770609683 159524454052899277155914525)
      ·
        refine ⟨59821670269837228933467947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 159524454052899277155914525 59821670269837228933467947)
        ·
          refine ⟨89732505404755843400201921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59821670269837228933467947 89732505404755843400201921)
          ·
            refine ⟨67299379053566882550151441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 89732505404755843400201921 67299379053566882550151441)
            ·
              refine ⟨50474534290175161912613581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 67299379053566882550151441 50474534290175161912613581)
              ·
                refine ⟨18927950358815685717230093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 50474534290175161912613581 18927950358815685717230093)
                ·
                  refine ⟨7097981384555882143961285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18927950358815685717230093 7097981384555882143961285)
                  ·
                    refine ⟨1330871509604227901992741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7097981384555882143961285 1330871509604227901992741)
                    ·
                      rfl

theorem cell23_7775589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 2, 3, 3, 4].length) (baseStart_7775589 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7775589 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7775589 prefixEnd_7775589 := by exact prefixLift 7775589
  have htrace : WordTrace (prefixWord ++ tailWord_7775589) baseStart_7775589 baseEnd_7775589 := by
    simpa [prefixWord, tailWord_7775589, baseEnd_7775589] using wordTrace_append hprefix tailTrace_7775589
  have hstable : (prefixWord ++ tailWord_7775589).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7775589).length < 2 ^ (prefixWord ++ tailWord_7775589).sum := by decide
  have hdescent : baseEnd_7775589 < baseStart_7775589 := by decide
  rcases family_descends (prefixWord ++ tailWord_7775589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7775596 : List Nat := [2, 2, 1, 1, 5, 2, 1, 1, 2, 4, 2]
def baseStart_7775596 : Nat := 118140960795 + 7775596 * 2 ^ 59
def prefixEnd_7775596 : Nat := 4983230072969 + 3 ^ 40 * 7775596 * 2
def baseEnd_7775596 : Nat := 3992618123177265178590691

theorem tailTrace_7775596 : CollatzResearch.WordTrace tailWord_7775596 prefixEnd_7775596 3992618123177265178590691 := by
  unfold tailWord_7775596
  simp only [CollatzResearch.WordTrace]
  refine ⟨141799642369175566458565321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 189066189825567421944753761 141799642369175566458565321)
  ·
    refine ⟨106349731776881674843923991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 141799642369175566458565321 106349731776881674843923991)
    ·
      refine ⟨159524597665322512265885987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106349731776881674843923991 159524597665322512265885987)
      ·
        refine ⟨239286896497983768398828981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 159524597665322512265885987 239286896497983768398828981)
        ·
          refine ⟨22433146546685978287390217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 239286896497983768398828981 22433146546685978287390217)
          ·
            refine ⟨16824859910014483715542663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22433146546685978287390217 16824859910014483715542663)
            ·
              refine ⟨25237289865021725573313995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16824859910014483715542663 25237289865021725573313995)
              ·
                refine ⟨37855934797532588359970993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25237289865021725573313995 37855934797532588359970993)
                ·
                  refine ⟨28391951098149441269978245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37855934797532588359970993 28391951098149441269978245)
                  ·
                    refine ⟨5323490830903020238120921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28391951098149441269978245 5323490830903020238120921)
                    ·
                      refine ⟨3992618123177265178590691, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5323490830903020238120921 3992618123177265178590691)
                      ·
                        rfl

theorem cell23_7775596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 4, 2].length) (baseStart_7775596 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7775596 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7775596 prefixEnd_7775596 := by exact prefixLift 7775596
  have htrace : WordTrace (prefixWord ++ tailWord_7775596) baseStart_7775596 baseEnd_7775596 := by
    simpa [prefixWord, tailWord_7775596, baseEnd_7775596] using wordTrace_append hprefix tailTrace_7775596
  have hstable : (prefixWord ++ tailWord_7775596).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7775596).length < 2 ^ (prefixWord ++ tailWord_7775596).sum := by decide
  have hdescent : baseEnd_7775596 < baseStart_7775596 := by decide
  rcases family_descends (prefixWord ++ tailWord_7775596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7775623 : List Nat := [1, 1, 4, 2, 2, 3, 2, 3, 1, 4]
def baseStart_7775623 : Nat := 118140960795 + 7775623 * 2 ^ 59
def prefixEnd_7775623 : Nat := 4983230072969 + 3 ^ 40 * 7775623 * 2
def baseEnd_7775623 : Nat := 1330877329051645524317689

theorem tailTrace_7775623 : CollatzResearch.WordTrace tailWord_7775623 prefixEnd_7775623 1330877329051645524317689 := by
  unfold tailWord_7775623
  simp only [CollatzResearch.WordTrace]
  refine ⟨283600269509253316528363523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189066846339502211018909015 283600269509253316528363523)
  ·
    refine ⟨425400404263879974792545285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 283600269509253316528363523 425400404263879974792545285)
    ·
      refine ⟨79762575799477495273602241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 425400404263879974792545285 79762575799477495273602241)
      ·
        refine ⟨59821931849608121455201681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79762575799477495273602241 59821931849608121455201681)
        ·
          refine ⟨44866448887206091091401261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59821931849608121455201681 44866448887206091091401261)
          ·
            refine ⟨16824918332702284159275473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 44866448887206091091401261 16824918332702284159275473)
            ·
              refine ⟨12618688749526713119456605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16824918332702284159275473 12618688749526713119456605)
              ·
                refine ⟨4732008281072517419796227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12618688749526713119456605 4732008281072517419796227)
                ·
                  refine ⟨7098012421608776129694341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4732008281072517419796227 7098012421608776129694341)
                  ·
                    refine ⟨1330877329051645524317689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7098012421608776129694341 1330877329051645524317689)
                    ·
                      rfl

theorem cell23_7775623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 3, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 3, 2, 3, 1, 4].length) (baseStart_7775623 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7775623 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7775623 prefixEnd_7775623 := by exact prefixLift 7775623
  have htrace : WordTrace (prefixWord ++ tailWord_7775623) baseStart_7775623 baseEnd_7775623 := by
    simpa [prefixWord, tailWord_7775623, baseEnd_7775623] using wordTrace_append hprefix tailTrace_7775623
  have hstable : (prefixWord ++ tailWord_7775623).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7775623).length < 2 ^ (prefixWord ++ tailWord_7775623).sum := by decide
  have hdescent : baseEnd_7775623 < baseStart_7775623 := by decide
  rcases family_descends (prefixWord ++ tailWord_7775623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7775636 : List Nat := [2, 4, 2, 1, 2, 1, 3, 2, 6]
def baseStart_7775636 : Nat := 118140960795 + 7775636 * 2 ^ 59
def prefixEnd_7775636 : Nat := 4983230072969 + 3 ^ 40 * 7775636 * 2
def baseEnd_7775636 : Nat := 443626518044827224676723

theorem tailTrace_7775636 : CollatzResearch.WordTrace tailWord_7775636 prefixEnd_7775636 443626518044827224676723 := by
  unfold tailWord_7775636
  simp only [CollatzResearch.WordTrace]
  refine ⟨141800371829103109874293381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 189067162438804146499057841 141800371829103109874293381)
  ·
    refine ⟨26587569717956833101430009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 141800371829103109874293381 26587569717956833101430009)
    ·
      refine ⟨19940677288467624826072507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26587569717956833101430009 19940677288467624826072507)
      ·
        refine ⟨29911015932701437239108761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19940677288467624826072507 29911015932701437239108761)
        ·
          refine ⟨22433261949526077929331571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29911015932701437239108761 22433261949526077929331571)
          ·
            refine ⟨33649892924289116893997357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22433261949526077929331571 33649892924289116893997357)
            ·
              refine ⟨12618709846608418835249009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33649892924289116893997357 12618709846608418835249009)
              ·
                refine ⟨9464032384956314126436757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12618709846608418835249009 9464032384956314126436757)
                ·
                  refine ⟨443626518044827224676723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9464032384956314126436757 443626518044827224676723)
                  ·
                    rfl

theorem cell23_7775636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 1, 3, 2, 6].length) (baseStart_7775636 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7775636 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7775636 prefixEnd_7775636 := by exact prefixLift 7775636
  have htrace : WordTrace (prefixWord ++ tailWord_7775636) baseStart_7775636 baseEnd_7775636 := by
    simpa [prefixWord, tailWord_7775636, baseEnd_7775636] using wordTrace_append hprefix tailTrace_7775636
  have hstable : (prefixWord ++ tailWord_7775636).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7775636).length < 2 ^ (prefixWord ++ tailWord_7775636).sum := by decide
  have hdescent : baseEnd_7775636 < baseStart_7775636 := by decide
  rcases family_descends (prefixWord ++ tailWord_7775636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7775689 : List Nat := [1, 2, 1, 1, 2, 1, 3, 2, 5, 2, 3]
def baseStart_7775689 : Nat := 118140960795 + 7775689 * 2 ^ 59
def prefixEnd_7775689 : Nat := 4983230072969 + 3 ^ 40 * 7775689 * 2
def baseEnd_7775689 : Nat := 3992665876878133314727763

theorem tailTrace_7775689 : CollatzResearch.WordTrace tailWord_7775689 prefixEnd_7775689 3992665876878133314727763 := by
  unfold tailWord_7775689
  simp only [CollatzResearch.WordTrace]
  refine ⟨283602676727014209800266121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189068451151342806533510747 283602676727014209800266121)
  ·
    refine ⟨212702007545260657350199591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 283602676727014209800266121 212702007545260657350199591)
    ·
      refine ⟨319053011317890986025299387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 212702007545260657350199591 319053011317890986025299387)
      ·
        refine ⟨478579516976836479037949081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 319053011317890986025299387 478579516976836479037949081)
        ·
          refine ⟨358934637732627359278461811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 478579516976836479037949081 358934637732627359278461811)
          ·
            refine ⟨538401956598941038917692717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 358934637732627359278461811 538401956598941038917692717)
            ·
              refine ⟨201900733724602889594134769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 538401956598941038917692717 201900733724602889594134769)
              ·
                refine ⟨151425550293452167195601077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 201900733724602889594134769 151425550293452167195601077)
                ·
                  refine ⟨14196145340011140674587601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 151425550293452167195601077 14196145340011140674587601)
                  ·
                    refine ⟨10647109005008355505940701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14196145340011140674587601 10647109005008355505940701)
                    ·
                      refine ⟨3992665876878133314727763, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10647109005008355505940701 3992665876878133314727763)
                      ·
                        rfl

theorem cell23_7775689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 3, 2, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 3, 2, 5, 2, 3].length) (baseStart_7775689 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7775689 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7775689 prefixEnd_7775689 := by exact prefixLift 7775689
  have htrace : WordTrace (prefixWord ++ tailWord_7775689) baseStart_7775689 baseEnd_7775689 := by
    simpa [prefixWord, tailWord_7775689, baseEnd_7775689] using wordTrace_append hprefix tailTrace_7775689
  have hstable : (prefixWord ++ tailWord_7775689).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7775689).length < 2 ^ (prefixWord ++ tailWord_7775689).sum := by decide
  have hdescent : baseEnd_7775689 < baseStart_7775689 := by decide
  rcases family_descends (prefixWord ++ tailWord_7775689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7775709 : List Nat := [1, 4, 3, 1, 1, 2, 1, 10]
def baseStart_7775709 : Nat := 118140960795 + 7775709 * 2 ^ 59
def prefixEnd_7775709 : Nat := 4983230072969 + 3 ^ 40 * 7775709 * 2
def baseEnd_7775709 : Nat := 147876894314489749499173

theorem tailTrace_7775709 : CollatzResearch.WordTrace tailWord_7775709 prefixEnd_7775709 147876894314489749499173 := by
  unfold tailWord_7775709
  simp only [CollatzResearch.WordTrace]
  refine ⟨283603406186941753215994181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189068937457961168810662787 283603406186941753215994181)
  ·
    refine ⟨53175638660051578727998909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 283603406186941753215994181 53175638660051578727998909)
    ·
      refine ⟨19940864497519342022999591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 53175638660051578727998909 19940864497519342022999591)
      ·
        refine ⟨29911296746279013034499387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19940864497519342022999591 29911296746279013034499387)
        ·
          refine ⟨44866945119418519551749081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29911296746279013034499387 44866945119418519551749081)
          ·
            refine ⟨33650208839563889663811811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44866945119418519551749081 33650208839563889663811811)
            ·
              refine ⟨50475313259345834495717717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33650208839563889663811811 50475313259345834495717717)
              ·
                refine ⟨147876894314489749499173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 50475313259345834495717717 147876894314489749499173)
                ·
                  rfl

theorem cell23_7775709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 2, 1, 10].length) (baseStart_7775709 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7775709 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7775709 prefixEnd_7775709 := by exact prefixLift 7775709
  have htrace : WordTrace (prefixWord ++ tailWord_7775709) baseStart_7775709 baseEnd_7775709 := by
    simpa [prefixWord, tailWord_7775709, baseEnd_7775709] using wordTrace_append hprefix tailTrace_7775709
  have hstable : (prefixWord ++ tailWord_7775709).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7775709).length < 2 ^ (prefixWord ++ tailWord_7775709).sum := by decide
  have hdescent : baseEnd_7775709 < baseStart_7775709 := by decide
  rcases family_descends (prefixWord ++ tailWord_7775709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7775713 : List Nat := [1, 2, 3, 1, 2, 3, 4, 1, 2, 4]
def baseStart_7775713 : Nat := 118140960795 + 7775713 * 2 ^ 59
def prefixEnd_7775713 : Nat := 4983230072969 + 3 ^ 40 * 7775713 * 2
def baseEnd_7775713 : Nat := 1330892733471280406942551

theorem tailTrace_7775713 : CollatzResearch.WordTrace tailWord_7775713 prefixEnd_7775713 1330892733471280406942551 := by
  unfold tailWord_7775713
  simp only [CollatzResearch.WordTrace]
  refine ⟨283603552078927261899139793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189069034719284841266093195 283603552078927261899139793)
  ·
    refine ⟨212702664059195446424354845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 283603552078927261899139793 212702664059195446424354845)
    ·
      refine ⟨79763499022198292409133067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 212702664059195446424354845 79763499022198292409133067)
      ·
        refine ⟨119645248533297438613699601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79763499022198292409133067 119645248533297438613699601)
        ·
          refine ⟨89733936399973078960274701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 119645248533297438613699601 89733936399973078960274701)
          ·
            refine ⟨33650226149989904610103013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 89733936399973078960274701 33650226149989904610103013)
            ·
              refine ⟨6309417403123107114394315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 33650226149989904610103013 6309417403123107114394315)
              ·
                refine ⟨9464126104684660671591473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6309417403123107114394315 9464126104684660671591473)
                ·
                  refine ⟨7098094578513495503693605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9464126104684660671591473 7098094578513495503693605)
                  ·
                    refine ⟨1330892733471280406942551, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7098094578513495503693605 1330892733471280406942551)
                    ·
                      rfl

theorem cell23_7775713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 3, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 3, 4, 1, 2, 4].length) (baseStart_7775713 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7775713 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7775713 prefixEnd_7775713 := by exact prefixLift 7775713
  have htrace : WordTrace (prefixWord ++ tailWord_7775713) baseStart_7775713 baseEnd_7775713 := by
    simpa [prefixWord, tailWord_7775713, baseEnd_7775713] using wordTrace_append hprefix tailTrace_7775713
  have hstable : (prefixWord ++ tailWord_7775713).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7775713).length < 2 ^ (prefixWord ++ tailWord_7775713).sum := by decide
  have hdescent : baseEnd_7775713 < baseStart_7775713 := by decide
  rcases family_descends (prefixWord ++ tailWord_7775713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7775733 : List Nat := [1, 3, 5, 1, 1, 2, 1, 2, 1, 2, 4]
def baseStart_7775733 : Nat := 118140960795 + 7775733 * 2 ^ 59
def prefixEnd_7775733 : Nat := 4983230072969 + 3 ^ 40 * 7775733 * 2
def baseEnd_7775733 : Nat := 3992688470026931142577561

theorem tailTrace_7775733 : CollatzResearch.WordTrace tailWord_7775733 prefixEnd_7775733 3992688470026931142577561 := by
  unfold tailWord_7775733
  simp only [CollatzResearch.WordTrace]
  refine ⟨283604281538854805314867853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189069521025903203543245235 283604281538854805314867853)
  ·
    refine ⟨106351605577070551993075445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 283604281538854805314867853 106351605577070551993075445)
    ·
      refine ⟨9970463022850364249350823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 106351605577070551993075445 9970463022850364249350823)
      ·
        refine ⟨14955694534275546374026235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9970463022850364249350823 14955694534275546374026235)
        ·
          refine ⟨22433541801413319561039353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14955694534275546374026235 22433541801413319561039353)
          ·
            refine ⟨16825156351059989670779515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22433541801413319561039353 16825156351059989670779515)
            ·
              refine ⟨25237734526589984506169273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16825156351059989670779515 25237734526589984506169273)
              ·
                refine ⟨18928300894942488379626955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25237734526589984506169273 18928300894942488379626955)
                ·
                  refine ⟨28392451342413732569440433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18928300894942488379626955 28392451342413732569440433)
                  ·
                    refine ⟨21294338506810299427080325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 28392451342413732569440433 21294338506810299427080325)
                    ·
                      refine ⟨3992688470026931142577561, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21294338506810299427080325 3992688470026931142577561)
                      ·
                        rfl

theorem cell23_7775733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 2, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 2, 1, 2, 1, 2, 4].length) (baseStart_7775733 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7775733 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7775733 prefixEnd_7775733 := by exact prefixLift 7775733
  have htrace : WordTrace (prefixWord ++ tailWord_7775733) baseStart_7775733 baseEnd_7775733 := by
    simpa [prefixWord, tailWord_7775733, baseEnd_7775733] using wordTrace_append hprefix tailTrace_7775733
  have hstable : (prefixWord ++ tailWord_7775733).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7775733).length < 2 ^ (prefixWord ++ tailWord_7775733).sum := by decide
  have hdescent : baseEnd_7775733 < baseStart_7775733 := by decide
  rcases family_descends (prefixWord ++ tailWord_7775733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7775736 : List Nat := [2, 1, 2, 1, 1, 6, 1, 2, 1, 3, 3]
def baseStart_7775736 : Nat := 118140960795 + 7775736 * 2 ^ 59
def prefixEnd_7775736 : Nat := 4983230072969 + 3 ^ 40 * 7775736 * 2
def baseEnd_7775736 : Nat := 3992690010468894630840047

theorem tailTrace_7775736 : CollatzResearch.WordTrace tailWord_7775736 prefixEnd_7775736 3992690010468894630840047 := by
  unfold tailWord_7775736
  simp only [CollatzResearch.WordTrace]
  refine ⟨141802195478921968413613531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 189069593971895957884818041 141802195478921968413613531)
  ·
    refine ⟨212703293218382952620420297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141802195478921968413613531 212703293218382952620420297)
    ·
      refine ⟨159527469913787214465315223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 212703293218382952620420297 159527469913787214465315223)
      ·
        refine ⟨239291204870680821697972835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 159527469913787214465315223 239291204870680821697972835)
        ·
          refine ⟨358936807306021232546959253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 239291204870680821697972835 358936807306021232546959253)
          ·
            refine ⟨16825162842469745275638715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 358936807306021232546959253 16825162842469745275638715)
            ·
              refine ⟨25237744263704617913458073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16825162842469745275638715 25237744263704617913458073)
              ·
                refine ⟨18928308197778463435093555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25237744263704617913458073 18928308197778463435093555)
                ·
                  refine ⟨28392462296667695152640333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18928308197778463435093555 28392462296667695152640333)
                  ·
                    refine ⟨10647173361250385682240125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 28392462296667695152640333 10647173361250385682240125)
                    ·
                      refine ⟨3992690010468894630840047, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10647173361250385682240125 3992690010468894630840047)
                      ·
                        rfl

theorem cell23_7775736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 6, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 6, 1, 2, 1, 3, 3].length) (baseStart_7775736 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7775736 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7775736 prefixEnd_7775736 := by exact prefixLift 7775736
  have htrace : WordTrace (prefixWord ++ tailWord_7775736) baseStart_7775736 baseEnd_7775736 := by
    simpa [prefixWord, tailWord_7775736, baseEnd_7775736] using wordTrace_append hprefix tailTrace_7775736
  have hstable : (prefixWord ++ tailWord_7775736).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7775736).length < 2 ^ (prefixWord ++ tailWord_7775736).sum := by decide
  have hdescent : baseEnd_7775736 < baseStart_7775736 := by decide
  rcases family_descends (prefixWord ++ tailWord_7775736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7775753 : List Nat := [1, 2, 1, 1, 3, 1, 6, 2, 2, 1, 3]
def baseStart_7775753 : Nat := 118140960795 + 7775753 * 2 ^ 59
def prefixEnd_7775753 : Nat := 4983230072969 + 3 ^ 40 * 7775753 * 2
def baseEnd_7775753 : Nat := 3992698739640021064327469

theorem tailTrace_7775753 : CollatzResearch.WordTrace tailWord_7775753 prefixEnd_7775753 3992698739640021064327469 := by
  unfold tailWord_7775753
  simp only [CollatzResearch.WordTrace]
  refine ⟨283605010998782348730595913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189070007332521565820397275 283605010998782348730595913)
  ·
    refine ⟨212703758249086761547946935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 283605010998782348730595913 212703758249086761547946935)
    ·
      refine ⟨319055637373630142321920403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 212703758249086761547946935 319055637373630142321920403)
      ·
        refine ⟨478583456060445213482880605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 319055637373630142321920403 478583456060445213482880605)
        ·
          refine ⟨179468796022666955056080227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 478583456060445213482880605 179468796022666955056080227)
          ·
            refine ⟨269203194034000432584120341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 179468796022666955056080227 269203194034000432584120341)
            ·
              refine ⟨12618899720343770277380641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 269203194034000432584120341 12618899720343770277380641)
              ·
                refine ⟨9464174790257827708035481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12618899720343770277380641 9464174790257827708035481)
                ·
                  refine ⟨7098131092693370781026611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9464174790257827708035481 7098131092693370781026611)
                  ·
                    refine ⟨10647196639040056171539917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7098131092693370781026611 10647196639040056171539917)
                    ·
                      refine ⟨3992698739640021064327469, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10647196639040056171539917 3992698739640021064327469)
                      ·
                        rfl

theorem cell23_7775753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 6, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 6, 2, 2, 1, 3].length) (baseStart_7775753 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7775753 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7775753 prefixEnd_7775753 := by exact prefixLift 7775753
  have htrace : WordTrace (prefixWord ++ tailWord_7775753) baseStart_7775753 baseEnd_7775753 := by
    simpa [prefixWord, tailWord_7775753, baseEnd_7775753] using wordTrace_append hprefix tailTrace_7775753
  have hstable : (prefixWord ++ tailWord_7775753).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7775753).length < 2 ^ (prefixWord ++ tailWord_7775753).sum := by decide
  have hdescent : baseEnd_7775753 < baseStart_7775753 := by decide
  rcases family_descends (prefixWord ++ tailWord_7775753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7775754 : List Nat := [3, 1, 2, 2, 2, 4, 2, 2, 1, 2, 2]
def baseStart_7775754 : Nat := 118140960795 + 7775754 * 2 ^ 59
def prefixEnd_7775754 : Nat := 4983230072969 + 3 ^ 40 * 7775754 * 2
def baseEnd_7775754 : Nat := 3992699253120675560414965

theorem tailTrace_7775754 : CollatzResearch.WordTrace tailWord_7775754 prefixEnd_7775754 3992699253120675560414965 := by
  unfold tailWord_7775754
  simp only [CollatzResearch.WordTrace]
  refine ⟨70901261867944681475345579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 189070031647852483934254877 70901261867944681475345579)
  ·
    refine ⟨106351892801917022213018369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70901261867944681475345579 106351892801917022213018369)
    ·
      refine ⟨79763919601437766659763777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 106351892801917022213018369 79763919601437766659763777)
      ·
        refine ⟨59822939701078324994822833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79763919601437766659763777 59822939701078324994822833)
        ·
          refine ⟨44867204775808743746117125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59822939701078324994822833 44867204775808743746117125)
          ·
            refine ⟨8412600895464139452396961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 44867204775808743746117125 8412600895464139452396961)
            ·
              refine ⟨6309450671598104589297721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8412600895464139452396961 6309450671598104589297721)
              ·
                refine ⟨4732088003698578441973291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6309450671598104589297721 4732088003698578441973291)
                ·
                  refine ⟨7098132005547867662959937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4732088003698578441973291 7098132005547867662959937)
                  ·
                    refine ⟨5323599004160900747219953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7098132005547867662959937 5323599004160900747219953)
                    ·
                      refine ⟨3992699253120675560414965, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5323599004160900747219953 3992699253120675560414965)
                      ·
                        rfl

theorem cell23_7775754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 4, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 4, 2, 2, 1, 2, 2].length) (baseStart_7775754 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7775754 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7775754 prefixEnd_7775754 := by exact prefixLift 7775754
  have htrace : WordTrace (prefixWord ++ tailWord_7775754) baseStart_7775754 baseEnd_7775754 := by
    simpa [prefixWord, tailWord_7775754, baseEnd_7775754] using wordTrace_append hprefix tailTrace_7775754
  have hstable : (prefixWord ++ tailWord_7775754).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7775754).length < 2 ^ (prefixWord ++ tailWord_7775754).sum := by decide
  have hdescent : baseEnd_7775754 < baseStart_7775754 := by decide
  rcases family_descends (prefixWord ++ tailWord_7775754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7775793 : List Nat := [1, 2, 2, 3, 1, 1, 1, 4, 4, 2, 2]
def baseStart_7775793 : Nat := 118140960795 + 7775793 * 2 ^ 59
def prefixEnd_7775793 : Nat := 4983230072969 + 3 ^ 40 * 7775793 * 2
def baseEnd_7775793 : Nat := 3992719278866200907827285

theorem tailTrace_7775793 : CollatzResearch.WordTrace tailWord_7775793 prefixEnd_7775793 3992719278866200907827285 := by
  unfold tailWord_7775793
  simp only [CollatzResearch.WordTrace]
  refine ⟨283606469918637435562052033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189070979945758290374701355 283606469918637435562052033)
  ·
    refine ⟨212704852438978076671539025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 283606469918637435562052033 212704852438978076671539025)
    ·
      refine ⟨159528639329233557503654269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 212704852438978076671539025 159528639329233557503654269)
      ·
        refine ⟨59823239748462584063870351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 159528639329233557503654269 59823239748462584063870351)
        ·
          refine ⟨89734859622693876095805527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59823239748462584063870351 89734859622693876095805527)
          ·
            refine ⟨134602289434040814143708291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89734859622693876095805527 134602289434040814143708291)
            ·
              refine ⟨201903434151061221215562437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 134602289434040814143708291 201903434151061221215562437)
              ·
                refine ⟨37856893903323978977917957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 201903434151061221215562437 37856893903323978977917957)
                ·
                  refine ⟨7098167606873246058359617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 37856893903323978977917957 7098167606873246058359617)
                  ·
                    refine ⟨5323625705154934543769713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7098167606873246058359617 5323625705154934543769713)
                    ·
                      refine ⟨3992719278866200907827285, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5323625705154934543769713 3992719278866200907827285)
                      ·
                        rfl

theorem cell23_7775793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 1, 4, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 1, 4, 4, 2, 2].length) (baseStart_7775793 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7775793 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7775793 prefixEnd_7775793 := by exact prefixLift 7775793
  have htrace : WordTrace (prefixWord ++ tailWord_7775793) baseStart_7775793 baseEnd_7775793 := by
    simpa [prefixWord, tailWord_7775793, baseEnd_7775793] using wordTrace_append hprefix tailTrace_7775793
  have hstable : (prefixWord ++ tailWord_7775793).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7775793).length < 2 ^ (prefixWord ++ tailWord_7775793).sum := by decide
  have hdescent : baseEnd_7775793 < baseStart_7775793 := by decide
  rcases family_descends (prefixWord ++ tailWord_7775793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7775797 : List Nat := [1, 3, 3, 1, 1, 5, 2, 1, 1, 3, 2]
def baseStart_7775797 : Nat := 118140960795 + 7775797 * 2 ^ 59
def prefixEnd_7775797 : Nat := 4983230072969 + 3 ^ 40 * 7775797 * 2
def baseEnd_7775797 : Nat := 3992721332788818892177267

theorem tailTrace_7775797 : CollatzResearch.WordTrace tailWord_7775797 prefixEnd_7775797 3992721332788818892177267 := by
  unfold tailWord_7775797
  simp only [CollatzResearch.WordTrace]
  refine ⟨283606615810622944245197645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189071077207081962830131763 283606615810622944245197645)
  ·
    refine ⟨106352480928983604091949117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 283606615810622944245197645 106352480928983604091949117)
    ·
      refine ⟨39882180348368851534480919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 106352480928983604091949117 39882180348368851534480919)
      ·
        refine ⟨59823270522553277301721379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39882180348368851534480919 59823270522553277301721379)
        ·
          refine ⟨89734905783829915952582069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59823270522553277301721379 89734905783829915952582069)
          ·
            refine ⟨8412647417234054620554569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 89734905783829915952582069 8412647417234054620554569)
            ·
              refine ⟨6309485562925540965415927, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8412647417234054620554569 6309485562925540965415927)
              ·
                refine ⟨9464228344388311448123891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6309485562925540965415927 9464228344388311448123891)
                ·
                  refine ⟨14196342516582467172185837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9464228344388311448123891 14196342516582467172185837)
                  ·
                    refine ⟨5323628443718425189569689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14196342516582467172185837 5323628443718425189569689)
                    ·
                      refine ⟨3992721332788818892177267, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5323628443718425189569689 3992721332788818892177267)
                      ·
                        rfl

theorem cell23_7775797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 5, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 5, 2, 1, 1, 3, 2].length) (baseStart_7775797 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7775797 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7775797 prefixEnd_7775797 := by exact prefixLift 7775797
  have htrace : WordTrace (prefixWord ++ tailWord_7775797) baseStart_7775797 baseEnd_7775797 := by
    simpa [prefixWord, tailWord_7775797, baseEnd_7775797] using wordTrace_append hprefix tailTrace_7775797
  have hstable : (prefixWord ++ tailWord_7775797).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7775797).length < 2 ^ (prefixWord ++ tailWord_7775797).sum := by decide
  have hdescent : baseEnd_7775797 < baseStart_7775797 := by decide
  rcases family_descends (prefixWord ++ tailWord_7775797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7775839 : List Nat := [1, 1, 2, 3, 1, 1, 1, 1, 5, 2, 5]
def baseStart_7775839 : Nat := 118140960795 + 7775839 * 2 ^ 59
def prefixEnd_7775839 : Nat := 4983230072969 + 3 ^ 40 * 7775839 * 2
def baseEnd_7775839 : Nat := 3992742898976307727852073

theorem tailTrace_7775839 : CollatzResearch.WordTrace tailWord_7775839 prefixEnd_7775839 3992742898976307727852073 := by
  unfold tailWord_7775839
  simp only [CollatzResearch.WordTrace]
  refine ⟨283608147676470785418226571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189072098450980523612151047 283608147676470785418226571)
  ·
    refine ⟨425412221514706178127339857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 283608147676470785418226571 425412221514706178127339857)
    ·
      refine ⟨319059166136029633595504893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 425412221514706178127339857 319059166136029633595504893)
      ·
        refine ⟨119647187301011112598314335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 319059166136029633595504893 119647187301011112598314335)
        ·
          refine ⟨179470780951516668897471503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 119647187301011112598314335 179470780951516668897471503)
          ·
            refine ⟨269206171427275003346207255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 179470780951516668897471503 269206171427275003346207255)
            ·
              refine ⟨403809257140912505019310883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 269206171427275003346207255 403809257140912505019310883)
              ·
                refine ⟨605713885711368757528966325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 403809257140912505019310883 605713885711368757528966325)
                ·
                  refine ⟨56785676785440821018340593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 605713885711368757528966325 56785676785440821018340593)
                  ·
                    refine ⟨42589257589080615763755445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 56785676785440821018340593 42589257589080615763755445)
                    ·
                      refine ⟨3992742898976307727852073, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 42589257589080615763755445 3992742898976307727852073)
                      ·
                        rfl

theorem cell23_7775839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 1, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 1, 1, 5, 2, 5].length) (baseStart_7775839 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7775839 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7775839 prefixEnd_7775839 := by exact prefixLift 7775839
  have htrace : WordTrace (prefixWord ++ tailWord_7775839) baseStart_7775839 baseEnd_7775839 := by
    simpa [prefixWord, tailWord_7775839, baseEnd_7775839] using wordTrace_append hprefix tailTrace_7775839
  have hstable : (prefixWord ++ tailWord_7775839).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7775839).length < 2 ^ (prefixWord ++ tailWord_7775839).sum := by decide
  have hdescent : baseEnd_7775839 < baseStart_7775839 := by decide
  rcases family_descends (prefixWord ++ tailWord_7775839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7775850 : List Nat := [3, 1, 3, 2, 1, 4, 1, 3, 5]
def baseStart_7775850 : Nat := 118140960795 + 7775850 * 2 ^ 59
def prefixEnd_7775850 : Nat := 4983230072969 + 3 ^ 40 * 7775850 * 2
def baseEnd_7775850 : Nat := 443638727473723020534947

theorem tailTrace_7775850 : CollatzResearch.WordTrace tailWord_7775850 prefixEnd_7775850 443638727473723020534947 := by
  unfold tailWord_7775850
  simp only [CollatzResearch.WordTrace]
  refine ⟨70902137219857733574219251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 189072365919620622864584669 70902137219857733574219251)
  ·
    refine ⟨106353205829786600361328877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70902137219857733574219251 106353205829786600361328877)
    ·
      refine ⟨39882452186169975135498329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 106353205829786600361328877 39882452186169975135498329)
      ·
        refine ⟨29911839139627481351623747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39882452186169975135498329 29911839139627481351623747)
        ·
          refine ⟨44867758709441222027435621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29911839139627481351623747 44867758709441222027435621)
          ·
            refine ⟨8412704758020229130144179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 44867758709441222027435621 8412704758020229130144179)
            ·
              refine ⟨12619057137030343695216269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8412704758020229130144179 12619057137030343695216269)
              ·
                refine ⟨4732146426386378885706101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12619057137030343695216269 4732146426386378885706101)
                ·
                  refine ⟨443638727473723020534947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4732146426386378885706101 443638727473723020534947)
                  ·
                    rfl

theorem cell23_7775850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 4, 1, 3, 5].length) (baseStart_7775850 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7775850 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7775850 prefixEnd_7775850 := by exact prefixLift 7775850
  have htrace : WordTrace (prefixWord ++ tailWord_7775850) baseStart_7775850 baseEnd_7775850 := by
    simpa [prefixWord, tailWord_7775850, baseEnd_7775850] using wordTrace_append hprefix tailTrace_7775850
  have hstable : (prefixWord ++ tailWord_7775850).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7775850).length < 2 ^ (prefixWord ++ tailWord_7775850).sum := by decide
  have hdescent : baseEnd_7775850 < baseStart_7775850 := by decide
  rcases family_descends (prefixWord ++ tailWord_7775850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7775889 : List Nat := [1, 2, 2, 1, 1, 1, 1, 4, 10]
def baseStart_7775889 : Nat := 118140960795 + 7775889 * 2 ^ 59
def prefixEnd_7775889 : Nat := 4983230072969 + 3 ^ 40 * 7775889 * 2
def baseEnd_7775889 : Nat := 443640952556559170247427

theorem tailTrace_7775889 : CollatzResearch.WordTrace tailWord_7775889 prefixEnd_7775889 443640952556559170247427 := by
  unfold tailWord_7775889
  simp only [CollatzResearch.WordTrace]
  refine ⟨283609971326289643957546721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189073314217526429305031147 283609971326289643957546721)
  ·
    refine ⟨212707478494717232968160041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 283609971326289643957546721 212707478494717232968160041)
    ·
      refine ⟨159530608871037924726120031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 212707478494717232968160041 159530608871037924726120031)
      ·
        refine ⟨239295913306556887089180047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 159530608871037924726120031 239295913306556887089180047)
        ·
          refine ⟨358943869959835330633770071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 239295913306556887089180047 358943869959835330633770071)
          ·
            refine ⟨538415804939752995950655107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 358943869959835330633770071 538415804939752995950655107)
            ·
              refine ⟨807623707409629493925982661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 538415804939752995950655107 807623707409629493925982661)
              ·
                refine ⟨151429445139305530111121749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 807623707409629493925982661 151429445139305530111121749)
                ·
                  refine ⟨443640952556559170247427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 151429445139305530111121749 443640952556559170247427)
                  ·
                    rfl

theorem cell23_7775889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 4, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 4, 10].length) (baseStart_7775889 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7775889 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7775889 prefixEnd_7775889 := by exact prefixLift 7775889
  have htrace : WordTrace (prefixWord ++ tailWord_7775889) baseStart_7775889 baseEnd_7775889 := by
    simpa [prefixWord, tailWord_7775889, baseEnd_7775889] using wordTrace_append hprefix tailTrace_7775889
  have hstable : (prefixWord ++ tailWord_7775889).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7775889).length < 2 ^ (prefixWord ++ tailWord_7775889).sum := by decide
  have hdescent : baseEnd_7775889 < baseStart_7775889 := by decide
  rcases family_descends (prefixWord ++ tailWord_7775889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
