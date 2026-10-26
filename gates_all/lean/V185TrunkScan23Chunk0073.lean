import V185TrunkScan23Chunk0072

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_434246 : List Nat := [6, 1, 1, 1, 1, 1, 2, 10]
def baseStart_434246 : Nat := 118140960795 + 434246 * 2 ^ 59
def prefixEnd_434246 : Nat := 4983230072969 + 3 ^ 40 * 434246 * 2
def baseEnd_434246 : Nat := 8258404455274564601035

theorem tailTrace_434246 : CollatzResearch.WordTrace tailWord_434246 prefixEnd_434246 8258404455274564601035 := by
  unfold tailWord_434246
  simp only [CollatzResearch.WordTrace]
  refine ⟨494945399525261879920831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 10558835189872253438311061 494945399525261879920831)
  ·
    refine ⟨742418099287892819881247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 494945399525261879920831 742418099287892819881247)
    ·
      refine ⟨1113627148931839229821871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 742418099287892819881247 1113627148931839229821871)
      ·
        refine ⟨1670440723397758844732807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1113627148931839229821871 1670440723397758844732807)
        ·
          refine ⟨2505661085096638267099211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1670440723397758844732807 2505661085096638267099211)
          ·
            refine ⟨3758491627644957400648817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2505661085096638267099211 3758491627644957400648817)
            ·
              refine ⟨2818868720733718050486613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3758491627644957400648817 2818868720733718050486613)
              ·
                refine ⟨8258404455274564601035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 2818868720733718050486613 8258404455274564601035)
                ·
                  rfl

theorem cell23_434246_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 2, 10].length) (baseStart_434246 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_434246 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_434246 prefixEnd_434246 := by exact prefixLift 434246
  have htrace : WordTrace (prefixWord ++ tailWord_434246) baseStart_434246 baseEnd_434246 := by
    simpa [prefixWord, tailWord_434246, baseEnd_434246] using wordTrace_append hprefix tailTrace_434246
  have hstable : (prefixWord ++ tailWord_434246).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_434246).length < 2 ^ (prefixWord ++ tailWord_434246).sum := by decide
  have hdescent : baseEnd_434246 < baseStart_434246 := by decide
  rcases family_descends (prefixWord ++ tailWord_434246) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_434330 : List Nat := [3, 1, 1, 5, 2, 1, 1, 2, 1, 4, 2]
def baseStart_434330 : Nat := 118140960795 + 434330 * 2 ^ 59
def prefixEnd_434330 : Nat := 4983230072969 + 3 ^ 40 * 434330 * 2
def baseEnd_434330 : Nat := 223020052667390915577559

theorem tailTrace_434330 : CollatzResearch.WordTrace tailWord_434330 prefixEnd_434330 223020052667390915577559 := by
  unfold tailWord_434330
  simp only [CollatzResearch.WordTrace]
  refine ⟨3960329129126015625881111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10560877677669375002349629 3960329129126015625881111)
  ·
    refine ⟨5940493693689023438821667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3960329129126015625881111 5940493693689023438821667)
    ·
      refine ⟨8910740540533535158232501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5940493693689023438821667 8910740540533535158232501)
      ·
        refine ⟨835381925675018921084297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 8910740540533535158232501 835381925675018921084297)
        ·
          refine ⟨626536444256264190813223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 835381925675018921084297 626536444256264190813223)
          ·
            refine ⟨939804666384396286219835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 626536444256264190813223 939804666384396286219835)
            ·
              refine ⟨1409706999576594429329753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 939804666384396286219835 1409706999576594429329753)
              ·
                refine ⟨1057280249682445821997315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1409706999576594429329753 1057280249682445821997315)
                ·
                  refine ⟨1585920374523668732995973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1057280249682445821997315 1585920374523668732995973)
                  ·
                    refine ⟨297360070223187887436745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1585920374523668732995973 297360070223187887436745)
                    ·
                      refine ⟨223020052667390915577559, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 297360070223187887436745 223020052667390915577559)
                      ·
                        rfl

theorem cell23_434330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 2, 1, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 2, 1, 1, 2, 1, 4, 2].length) (baseStart_434330 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_434330 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_434330 prefixEnd_434330 := by exact prefixLift 434330
  have htrace : WordTrace (prefixWord ++ tailWord_434330) baseStart_434330 baseEnd_434330 := by
    simpa [prefixWord, tailWord_434330, baseEnd_434330] using wordTrace_append hprefix tailTrace_434330
  have hstable : (prefixWord ++ tailWord_434330).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_434330).length < 2 ^ (prefixWord ++ tailWord_434330).sum := by decide
  have hdescent : baseEnd_434330 < baseStart_434330 := by decide
  rcases family_descends (prefixWord ++ tailWord_434330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_434334 : List Nat := [4, 3, 1, 1, 3, 1, 3, 1, 1, 3, 2]
def baseStart_434334 : Nat := 118140960795 + 434334 * 2 ^ 59
def prefixEnd_434334 : Nat := 4983230072969 + 3 ^ 40 * 434334 * 2
def baseEnd_434334 : Nat := 223022106590008899927541

theorem tailTrace_434334 : CollatzResearch.WordTrace tailWord_434334 prefixEnd_434334 223022106590008899927541 := by
  unfold tailWord_434334
  simp only [CollatzResearch.WordTrace]
  refine ⟨1980182801061196398333757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 10560974938993047457780037 1980182801061196398333757)
  ·
    refine ⟨742568550397948649375159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1980182801061196398333757 742568550397948649375159)
    ·
      refine ⟨1113852825596922974062739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 742568550397948649375159 1113852825596922974062739)
      ·
        refine ⟨1670779238395384461094109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1113852825596922974062739 1670779238395384461094109)
        ·
          refine ⟨626542214398269172910291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1670779238395384461094109 626542214398269172910291)
          ·
            refine ⟨939813321597403759365437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 626542214398269172910291 939813321597403759365437)
            ·
              refine ⟨352429995599026409762039, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 939813321597403759365437 352429995599026409762039)
              ·
                refine ⟨528644993398539614643059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 352429995599026409762039 528644993398539614643059)
                ·
                  refine ⟨792967490097809421964589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 528644993398539614643059 792967490097809421964589)
                  ·
                    refine ⟨297362808786678533236721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 792967490097809421964589 297362808786678533236721)
                    ·
                      refine ⟨223022106590008899927541, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 297362808786678533236721 223022106590008899927541)
                      ·
                        rfl

theorem cell23_434334_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 3, 1, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 3, 1, 3, 1, 1, 3, 2].length) (baseStart_434334 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_434334 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_434334 prefixEnd_434334 := by exact prefixLift 434334
  have htrace : WordTrace (prefixWord ++ tailWord_434334) baseStart_434334 baseEnd_434334 := by
    simpa [prefixWord, tailWord_434334, baseEnd_434334] using wordTrace_append hprefix tailTrace_434334
  have hstable : (prefixWord ++ tailWord_434334).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_434334).length < 2 ^ (prefixWord ++ tailWord_434334).sum := by decide
  have hdescent : baseEnd_434334 < baseStart_434334 := by decide
  rcases family_descends (prefixWord ++ tailWord_434334) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_434370 : List Nat := [3, 5, 1, 1, 1, 2, 1, 2, 7]
def baseStart_434370 : Nat := 118140960795 + 434370 * 2 ^ 59
def prefixEnd_434370 : Nat := 4983230072969 + 3 ^ 40 * 434370 * 2
def baseEnd_434370 : Nat := 24782287988174528786375

theorem tailTrace_434370 : CollatzResearch.WordTrace tailWord_434370 prefixEnd_434370 24782287988174528786375 := by
  unfold tailWord_434370
  simp only [CollatzResearch.WordTrace]
  refine ⟨3960693859089787333745141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10561850290906099556653709 3960693859089787333745141)
  ·
    refine ⟨371315049289667562538607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 3960693859089787333745141 371315049289667562538607)
    ·
      refine ⟨556972573934501343807911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 371315049289667562538607 556972573934501343807911)
      ·
        refine ⟨835458860901752015711867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 556972573934501343807911 835458860901752015711867)
        ·
          refine ⟨1253188291352628023567801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 835458860901752015711867 1253188291352628023567801)
          ·
            refine ⟨939891218514471017675851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1253188291352628023567801 939891218514471017675851)
            ·
              refine ⟨1409836827771706526513777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 939891218514471017675851 1409836827771706526513777)
              ·
                refine ⟨1057377620828779894885333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1409836827771706526513777 1057377620828779894885333)
                ·
                  refine ⟨24782287988174528786375, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1057377620828779894885333 24782287988174528786375)
                  ·
                    rfl

theorem cell23_434370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 2, 1, 2, 7].length) (baseStart_434370 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_434370 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_434370 prefixEnd_434370 := by exact prefixLift 434370
  have htrace : WordTrace (prefixWord ++ tailWord_434370) baseStart_434370 baseEnd_434370 := by
    simpa [prefixWord, tailWord_434370, baseEnd_434370] using wordTrace_append hprefix tailTrace_434370
  have hstable : (prefixWord ++ tailWord_434370).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_434370).length < 2 ^ (prefixWord ++ tailWord_434370).sum := by decide
  have hdescent : baseEnd_434370 < baseStart_434370 := by decide
  rcases family_descends (prefixWord ++ tailWord_434370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_434409 : List Nat := [1, 2, 1, 1, 1, 2, 2, 5, 8]
def baseStart_434409 : Nat := 118140960795 + 434409 * 2 ^ 59
def prefixEnd_434409 : Nat := 4983230072969 + 3 ^ 40 * 434409 * 2
def baseEnd_434409 : Nat := 24784513071010678498855

theorem tailTrace_434409 : CollatzResearch.WordTrace tailWord_434409 prefixEnd_434409 24784513071010678498855 := by
  unfold tailWord_434409
  simp only [CollatzResearch.WordTrace]
  refine ⟨15844197883217858995650281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10562798588811905997100187 15844197883217858995650281)
  ·
    refine ⟨11883148412413394246737711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15844197883217858995650281 11883148412413394246737711)
    ·
      refine ⟨17824722618620091370106567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11883148412413394246737711 17824722618620091370106567)
      ·
        refine ⟨26737083927930137055159851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17824722618620091370106567 26737083927930137055159851)
        ·
          refine ⟨40105625891895205582739777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26737083927930137055159851 40105625891895205582739777)
          ·
            refine ⟨30079219418921404187054833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40105625891895205582739777 30079219418921404187054833)
            ·
              refine ⟨22559414564191053140291125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30079219418921404187054833 22559414564191053140291125)
              ·
                refine ⟨2114945115392911231902293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 22559414564191053140291125 2114945115392911231902293)
                ·
                  refine ⟨24784513071010678498855, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 2114945115392911231902293 24784513071010678498855)
                  ·
                    rfl

theorem cell23_434409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 2, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 2, 5, 8].length) (baseStart_434409 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_434409 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_434409 prefixEnd_434409 := by exact prefixLift 434409
  have htrace : WordTrace (prefixWord ++ tailWord_434409) baseStart_434409 baseEnd_434409 := by
    simpa [prefixWord, tailWord_434409, baseEnd_434409] using wordTrace_append hprefix tailTrace_434409
  have hstable : (prefixWord ++ tailWord_434409).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_434409).length < 2 ^ (prefixWord ++ tailWord_434409).sum := by decide
  have hdescent : baseEnd_434409 < baseStart_434409 := by decide
  rcases family_descends (prefixWord ++ tailWord_434409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_434453 : List Nat := [1, 3, 2, 1, 2, 1, 2, 2, 5, 1, 3]
def baseStart_434453 : Nat := 118140960795 + 434453 * 2 ^ 59
def prefixEnd_434453 : Nat := 4983230072969 + 3 ^ 40 * 434453 * 2
def baseEnd_434453 : Nat := 223083210787893934339493

theorem tailTrace_434453 : CollatzResearch.WordTrace tailWord_434453 prefixEnd_434453 223083210787893934339493 := by
  unfold tailWord_434453
  simp only [CollatzResearch.WordTrace]
  refine ⟨15845802695058454510252013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10563868463372303006834675 15845802695058454510252013)
  ·
    refine ⟨5942176010646920441344505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15845802695058454510252013 5942176010646920441344505)
    ·
      refine ⟨4456632007985190331008379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5942176010646920441344505 4456632007985190331008379)
      ·
        refine ⟨6684948011977785496512569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4456632007985190331008379 6684948011977785496512569)
        ·
          refine ⟨5013711008983339122384427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6684948011977785496512569 5013711008983339122384427)
          ·
            refine ⟨7520566513475008683576641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5013711008983339122384427 7520566513475008683576641)
            ·
              refine ⟨5640424885106256512682481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7520566513475008683576641 5640424885106256512682481)
              ·
                refine ⟨4230318663829692384511861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5640424885106256512682481 4230318663829692384511861)
                ·
                  refine ⟨396592374734033661047987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4230318663829692384511861 396592374734033661047987)
                  ·
                    refine ⟨594888562101050491571981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 396592374734033661047987 594888562101050491571981)
                    ·
                      refine ⟨223083210787893934339493, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 594888562101050491571981 223083210787893934339493)
                      ·
                        rfl

theorem cell23_434453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 2, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 2, 2, 5, 1, 3].length) (baseStart_434453 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_434453 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_434453 prefixEnd_434453 := by exact prefixLift 434453
  have htrace : WordTrace (prefixWord ++ tailWord_434453) baseStart_434453 baseEnd_434453 := by
    simpa [prefixWord, tailWord_434453, baseEnd_434453] using wordTrace_append hprefix tailTrace_434453
  have hstable : (prefixWord ++ tailWord_434453).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_434453).length < 2 ^ (prefixWord ++ tailWord_434453).sum := by decide
  have hdescent : baseEnd_434453 < baseStart_434453 := by decide
  rcases family_descends (prefixWord ++ tailWord_434453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_434490 : List Nat := [3, 1, 1, 1, 4, 4, 1, 2, 1, 5]
def baseStart_434490 : Nat := 118140960795 + 434490 * 2 ^ 59
def prefixEnd_434490 : Nat := 4983230072969 + 3 ^ 40 * 434490 * 2
def baseEnd_434490 : Nat := 74367403190703429858941

theorem tailTrace_434490 : CollatzResearch.WordTrace tailWord_434490 prefixEnd_434490 74367403190703429858941 := by
  unfold tailWord_434490
  simp only [CollatzResearch.WordTrace]
  refine ⟨3961788048981102457337231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10564768130616273219565949 3961788048981102457337231)
  ·
    refine ⟨5942682073471653686005847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3961788048981102457337231 5942682073471653686005847)
    ·
      refine ⟨8914023110207480529008771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5942682073471653686005847 8914023110207480529008771)
      ·
        refine ⟨13371034665311220793513157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8914023110207480529008771 13371034665311220793513157)
        ·
          refine ⟨2507068999745853898783717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13371034665311220793513157 2507068999745853898783717)
          ·
            refine ⟨470075437452347606021947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2507068999745853898783717 470075437452347606021947)
            ·
              refine ⟨705113156178521409032921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 470075437452347606021947 705113156178521409032921)
              ·
                refine ⟨528834867133891056774691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 705113156178521409032921 528834867133891056774691)
                ·
                  refine ⟨793252300700836585162037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 528834867133891056774691 793252300700836585162037)
                  ·
                    refine ⟨74367403190703429858941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 793252300700836585162037 74367403190703429858941)
                    ·
                      rfl

theorem cell23_434490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 4, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 4, 1, 2, 1, 5].length) (baseStart_434490 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_434490 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_434490 prefixEnd_434490 := by exact prefixLift 434490
  have htrace : WordTrace (prefixWord ++ tailWord_434490) baseStart_434490 baseEnd_434490 := by
    simpa [prefixWord, tailWord_434490, baseEnd_434490] using wordTrace_append hprefix tailTrace_434490
  have hstable : (prefixWord ++ tailWord_434490).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_434490).length < 2 ^ (prefixWord ++ tailWord_434490).sum := by decide
  have hdescent : baseEnd_434490 < baseStart_434490 := by decide
  rcases family_descends (prefixWord ++ tailWord_434490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_434510 : List Nat := [4, 1, 1, 1, 1, 1, 2, 1, 7, 2, 2]
def baseStart_434510 : Nat := 118140960795 + 434510 * 2 ^ 59
def prefixEnd_434510 : Nat := 4983230072969 + 3 ^ 40 * 434510 * 2
def baseEnd_434510 : Nat := 223112479185200211326731

theorem tailTrace_434510 : CollatzResearch.WordTrace tailWord_434510 prefixEnd_434510 223112479185200211326731 := by
  unfold tailWord_434510
  simp only [CollatzResearch.WordTrace]
  refine ⟨1980985206981494155634623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 10565254437234635496717989 1980985206981494155634623)
  ·
    refine ⟨2971477810472241233451935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1980985206981494155634623 2971477810472241233451935)
    ·
      refine ⟨4457216715708361850177903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2971477810472241233451935 4457216715708361850177903)
      ·
        refine ⟨6685825073562542775266855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4457216715708361850177903 6685825073562542775266855)
        ·
          refine ⟨10028737610343814162900283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6685825073562542775266855 10028737610343814162900283)
          ·
            refine ⟨15043106415515721244350425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10028737610343814162900283 15043106415515721244350425)
            ·
              refine ⟨11282329811636790933262819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15043106415515721244350425 11282329811636790933262819)
              ·
                refine ⟨16923494717455186399894229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11282329811636790933262819 16923494717455186399894229)
                ·
                  refine ⟨396644407440355931247521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16923494717455186399894229 396644407440355931247521)
                  ·
                    refine ⟨297483305580266948435641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 396644407440355931247521 297483305580266948435641)
                    ·
                      refine ⟨223112479185200211326731, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 297483305580266948435641 223112479185200211326731)
                      ·
                        rfl

theorem cell23_434510_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 2, 1, 7, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 2, 1, 7, 2, 2].length) (baseStart_434510 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_434510 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_434510 prefixEnd_434510 := by exact prefixLift 434510
  have htrace : WordTrace (prefixWord ++ tailWord_434510) baseStart_434510 baseEnd_434510 := by
    simpa [prefixWord, tailWord_434510, baseEnd_434510] using wordTrace_append hprefix tailTrace_434510
  have hstable : (prefixWord ++ tailWord_434510).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_434510).length < 2 ^ (prefixWord ++ tailWord_434510).sum := by decide
  have hdescent : baseEnd_434510 < baseStart_434510 := by decide
  rcases family_descends (prefixWord ++ tailWord_434510) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_434513 : List Nat := [1, 2, 2, 1, 4, 2, 3, 1, 1, 1, 5]
def baseStart_434513 : Nat := 118140960795 + 434513 * 2 ^ 59
def prefixEnd_434513 : Nat := 4983230072969 + 3 ^ 40 * 434513 * 2
def baseEnd_434513 : Nat := 223114019627163699589217

theorem tailTrace_434513 : CollatzResearch.WordTrace tailWord_434513 prefixEnd_434513 223114019627163699589217 := by
  unfold tailWord_434513
  simp only [CollatzResearch.WordTrace]
  refine ⟨15847991074841084757436193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10565327383227389838290795 15847991074841084757436193)
  ·
    refine ⟨11885993306130813568077145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15847991074841084757436193 11885993306130813568077145)
    ·
      refine ⟨8914494979598110176057859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11885993306130813568077145 8914494979598110176057859)
      ·
        refine ⟨13371742469397165264086789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8914494979598110176057859 13371742469397165264086789)
        ·
          refine ⟨2507201713011968487016273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13371742469397165264086789 2507201713011968487016273)
          ·
            refine ⟨1880401284758976365262205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2507201713011968487016273 1880401284758976365262205)
            ·
              refine ⟨705150481784616136973327, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1880401284758976365262205 705150481784616136973327)
              ·
                refine ⟨1057725722676924205459991, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 705150481784616136973327 1057725722676924205459991)
                ·
                  refine ⟨1586588584015386308189987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1057725722676924205459991 1586588584015386308189987)
                  ·
                    refine ⟨2379882876023079462284981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1586588584015386308189987 2379882876023079462284981)
                    ·
                      refine ⟨223114019627163699589217, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 2379882876023079462284981 223114019627163699589217)
                      ·
                        rfl

theorem cell23_434513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 2, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 2, 3, 1, 1, 1, 5].length) (baseStart_434513 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_434513 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_434513 prefixEnd_434513 := by exact prefixLift 434513
  have htrace : WordTrace (prefixWord ++ tailWord_434513) baseStart_434513 baseEnd_434513 := by
    simpa [prefixWord, tailWord_434513, baseEnd_434513] using wordTrace_append hprefix tailTrace_434513
  have hstable : (prefixWord ++ tailWord_434513).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_434513).length < 2 ^ (prefixWord ++ tailWord_434513).sum := by decide
  have hdescent : baseEnd_434513 < baseStart_434513 := by decide
  rcases family_descends (prefixWord ++ tailWord_434513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_434516 : List Nat := [2, 4, 1, 1, 2, 13]
def baseStart_434516 : Nat := 118140960795 + 434516 * 2 ^ 59
def prefixEnd_434516 : Nat := 4983230072969 + 3 ^ 40 * 434516 * 2
def baseEnd_434516 : Nat := 918171029091058386221

theorem tailTrace_434516 : CollatzResearch.WordTrace tailWord_434516 prefixEnd_434516 918171029091058386221 := by
  unfold tailWord_434516
  simp only [CollatzResearch.WordTrace]
  refine ⟨7924050246915108134897701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10565400329220144179863601 7924050246915108134897701)
  ·
    refine ⟨1485759421296582775293319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 7924050246915108134897701 1485759421296582775293319)
    ·
      refine ⟨2228639131944874162939979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1485759421296582775293319 2228639131944874162939979)
      ·
        refine ⟨3342958697917311244409969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2228639131944874162939979 3342958697917311244409969)
        ·
          refine ⟨2507219023437983433307477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3342958697917311244409969 2507219023437983433307477)
          ·
            refine ⟨918171029091058386221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 13 2507219023437983433307477 918171029091058386221)
            ·
              rfl

theorem cell23_434516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 13].length) (baseStart_434516 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_434516 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_434516 prefixEnd_434516 := by exact prefixLift 434516
  have htrace : WordTrace (prefixWord ++ tailWord_434516) baseStart_434516 baseEnd_434516 := by
    simpa [prefixWord, tailWord_434516, baseEnd_434516] using wordTrace_append hprefix tailTrace_434516
  have hstable : (prefixWord ++ tailWord_434516).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_434516).length < 2 ^ (prefixWord ++ tailWord_434516).sum := by decide
  have hdescent : baseEnd_434516 < baseStart_434516 := by decide
  rcases family_descends (prefixWord ++ tailWord_434516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_434530 : List Nat := [3, 3, 2, 1, 1, 2, 1, 2, 3, 2, 3]
def baseStart_434530 : Nat := 118140960795 + 434530 * 2 ^ 59
def prefixEnd_434530 : Nat := 4983230072969 + 3 ^ 40 * 434530 * 2
def baseEnd_434530 : Nat := 223122748798290133076639

theorem tailTrace_434530 : CollatzResearch.WordTrace tailWord_434530 prefixEnd_434530 223122748798290133076639 := by
  unfold tailWord_434530
  simp only [CollatzResearch.WordTrace]
  refine ⟨3962152778944874165201261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10565740743852997773870029 3962152778944874165201261)
  ·
    refine ⟨1485807292104327811950473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3962152778944874165201261 1485807292104327811950473)
    ·
      refine ⟨1114355469078245858962855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1485807292104327811950473 1114355469078245858962855)
      ·
        refine ⟨1671533203617368788444283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1114355469078245858962855 1671533203617368788444283)
        ·
          refine ⟨2507299805426053182666425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1671533203617368788444283 2507299805426053182666425)
          ·
            refine ⟨1880474854069539886999819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2507299805426053182666425 1880474854069539886999819)
            ·
              refine ⟨2820712281104309830499729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1880474854069539886999819 2820712281104309830499729)
              ·
                refine ⟨2115534210828232372874797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2820712281104309830499729 2115534210828232372874797)
                ·
                  refine ⟨793325329060587139828049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2115534210828232372874797 793325329060587139828049)
                  ·
                    refine ⟨594993996795440354871037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 793325329060587139828049 594993996795440354871037)
                    ·
                      refine ⟨223122748798290133076639, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 594993996795440354871037 223122748798290133076639)
                      ·
                        rfl

theorem cell23_434530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 2, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 2, 1, 2, 3, 2, 3].length) (baseStart_434530 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_434530 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_434530 prefixEnd_434530 := by exact prefixLift 434530
  have htrace : WordTrace (prefixWord ++ tailWord_434530) baseStart_434530 baseEnd_434530 := by
    simpa [prefixWord, tailWord_434530, baseEnd_434530] using wordTrace_append hprefix tailTrace_434530
  have hstable : (prefixWord ++ tailWord_434530).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_434530).length < 2 ^ (prefixWord ++ tailWord_434530).sum := by decide
  have hdescent : baseEnd_434530 < baseStart_434530 := by decide
  rcases family_descends (prefixWord ++ tailWord_434530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_434533 : List Nat := [1, 3, 1, 3, 1, 5, 1, 8]
def baseStart_434533 : Nat := 118140960795 + 434533 * 2 ^ 59
def prefixEnd_434533 : Nat := 4983230072969 + 3 ^ 40 * 434533 * 2
def baseEnd_434533 : Nat := 8263862564453837827375

theorem tailTrace_434533 : CollatzResearch.WordTrace tailWord_434533 prefixEnd_434533 8263862564453837827375 := by
  unfold tailWord_434533
  simp only [CollatzResearch.WordTrace]
  refine ⟨15848720534768628173164253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10565813689845752115442835 15848720534768628173164253)
  ·
    refine ⟨5943270200538235564936595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15848720534768628173164253 5943270200538235564936595)
    ·
      refine ⟨8914905300807353347404893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5943270200538235564936595 8914905300807353347404893)
      ·
        refine ⟨3343089487802757505276835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8914905300807353347404893 3343089487802757505276835)
        ·
          refine ⟨5014634231704136257915253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3343089487802757505276835 5014634231704136257915253)
          ·
            refine ⟨470121959222262774179555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 5014634231704136257915253 470121959222262774179555)
            ·
              refine ⟨705182938833394161269333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 470121959222262774179555 705182938833394161269333)
              ·
                refine ⟨8263862564453837827375, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 705182938833394161269333 8263862564453837827375)
                ·
                  rfl

theorem cell23_434533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 5, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 5, 1, 8].length) (baseStart_434533 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_434533 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_434533 prefixEnd_434533 := by exact prefixLift 434533
  have htrace : WordTrace (prefixWord ++ tailWord_434533) baseStart_434533 baseEnd_434533 := by
    simpa [prefixWord, tailWord_434533, baseEnd_434533] using wordTrace_append hprefix tailTrace_434533
  have hstable : (prefixWord ++ tailWord_434533).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_434533).length < 2 ^ (prefixWord ++ tailWord_434533).sum := by decide
  have hdescent : baseEnd_434533 < baseStart_434533 := by decide
  rcases family_descends (prefixWord ++ tailWord_434533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_434540 : List Nat := [2, 2, 1, 1, 6, 1, 2, 1, 1, 2, 4]
def baseStart_434540 : Nat := 118140960795 + 434540 * 2 ^ 59
def prefixEnd_434540 : Nat := 4983230072969 + 3 ^ 40 * 434540 * 2
def baseEnd_434540 : Nat := 223127883604835093951593

theorem tailTrace_434540 : CollatzResearch.WordTrace tailWord_434540 prefixEnd_434540 223127883604835093951593 := by
  unfold tailWord_434540
  simp only [CollatzResearch.WordTrace]
  refine ⟨7924487922871634184334537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10565983897162178912446049 7924487922871634184334537)
  ·
    refine ⟨5943365942153725638250903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7924487922871634184334537 5943365942153725638250903)
    ·
      refine ⟨8915048913230588457376355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5943365942153725638250903 8915048913230588457376355)
      ·
        refine ⟨13372573369845882686064533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8915048913230588457376355 13372573369845882686064533)
        ·
          refine ⟨626839376711525750909275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 13372573369845882686064533 626839376711525750909275)
          ·
            refine ⟨940259065067288626363913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 626839376711525750909275 940259065067288626363913)
            ·
              refine ⟨705194298800466469772935, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 940259065067288626363913 705194298800466469772935)
              ·
                refine ⟨1057791448200699704659403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 705194298800466469772935 1057791448200699704659403)
                ·
                  refine ⟨1586687172301049556989105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1057791448200699704659403 1586687172301049556989105)
                  ·
                    refine ⟨1190015379225787167741829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1586687172301049556989105 1190015379225787167741829)
                    ·
                      refine ⟨223127883604835093951593, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1190015379225787167741829 223127883604835093951593)
                      ·
                        rfl

theorem cell23_434540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 2, 4].length) (baseStart_434540 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_434540 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_434540 prefixEnd_434540 := by exact prefixLift 434540
  have htrace : WordTrace (prefixWord ++ tailWord_434540) baseStart_434540 baseEnd_434540 := by
    simpa [prefixWord, tailWord_434540, baseEnd_434540] using wordTrace_append hprefix tailTrace_434540
  have hstable : (prefixWord ++ tailWord_434540).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_434540).length < 2 ^ (prefixWord ++ tailWord_434540).sum := by decide
  have hdescent : baseEnd_434540 < baseStart_434540 := by decide
  rcases family_descends (prefixWord ++ tailWord_434540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_434561 : List Nat := [1, 2, 4, 3, 1, 2, 2, 3, 1, 2, 2]
def baseStart_434561 : Nat := 118140960795 + 434561 * 2 ^ 59
def prefixEnd_434561 : Nat := 4983230072969 + 3 ^ 40 * 434561 * 2
def baseEnd_434561 : Nat := 223138666698579511788997

theorem tailTrace_434561 : CollatzResearch.WordTrace tailWord_434561 prefixEnd_434561 223138666698579511788997 := by
  unfold tailWord_434561
  simp only [CollatzResearch.WordTrace]
  refine ⟨15849741778667188955183537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10566494519111459303455691 15849741778667188955183537)
  ·
    refine ⟨11887306334000391716387653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15849741778667188955183537 11887306334000391716387653)
    ·
      refine ⟨2228869937625073446822685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 11887306334000391716387653 2228869937625073446822685)
      ·
        refine ⟨835826226609402542558507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2228869937625073446822685 835826226609402542558507)
        ·
          refine ⟨1253739339914103813837761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 835826226609402542558507 1253739339914103813837761)
          ·
            refine ⟨940304504935577860378321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1253739339914103813837761 940304504935577860378321)
            ·
              refine ⟨705228378701683395283741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 940304504935577860378321 705228378701683395283741)
              ·
                refine ⟨264460642013131273231403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 705228378701683395283741 264460642013131273231403)
                ·
                  refine ⟨396690963019696909847105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 264460642013131273231403 396690963019696909847105)
                  ·
                    refine ⟨297518222264772682385329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 396690963019696909847105 297518222264772682385329)
                    ·
                      refine ⟨223138666698579511788997, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 297518222264772682385329 223138666698579511788997)
                      ·
                        rfl

theorem cell23_434561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 2, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 2, 2, 3, 1, 2, 2].length) (baseStart_434561 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_434561 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_434561 prefixEnd_434561 := by exact prefixLift 434561
  have htrace : WordTrace (prefixWord ++ tailWord_434561) baseStart_434561 baseEnd_434561 := by
    simpa [prefixWord, tailWord_434561, baseEnd_434561] using wordTrace_append hprefix tailTrace_434561
  have hstable : (prefixWord ++ tailWord_434561).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_434561).length < 2 ^ (prefixWord ++ tailWord_434561).sum := by decide
  have hdescent : baseEnd_434561 < baseStart_434561 := by decide
  rcases family_descends (prefixWord ++ tailWord_434561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_434594 : List Nat := [3, 3, 1, 2, 1, 1, 5, 1, 2, 1, 3]
def baseStart_434594 : Nat := 118140960795 + 434594 * 2 ^ 59
def prefixEnd_434594 : Nat := 4983230072969 + 3 ^ 40 * 434594 * 2
def baseEnd_434594 : Nat := 223155611560177882676345

theorem tailTrace_434594 : CollatzResearch.WordTrace tailWord_434594 prefixEnd_434594 223155611560177882676345 := by
  unfold tailWord_434594
  simp only [CollatzResearch.WordTrace]
  refine ⟨3962736346886908897783709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10567296925031757060756557 3962736346886908897783709)
  ·
    refine ⟨1486026130082590836668891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3962736346886908897783709 1486026130082590836668891)
    ·
      refine ⟨2229039195123886255003337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1486026130082590836668891 2229039195123886255003337)
      ·
        refine ⟨1671779396342914691252503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2229039195123886255003337 1671779396342914691252503)
        ·
          refine ⟨2507669094514372036878755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1671779396342914691252503 2507669094514372036878755)
          ·
            refine ⟨3761503641771558055318133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2507669094514372036878755 3761503641771558055318133)
            ·
              refine ⟨352640966416083567686075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 3761503641771558055318133 352640966416083567686075)
              ·
                refine ⟨528961449624125351529113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 352640966416083567686075 528961449624125351529113)
                ·
                  refine ⟨396721087218094013646835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 528961449624125351529113 396721087218094013646835)
                  ·
                    refine ⟨595081630827141020470253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 396721087218094013646835 595081630827141020470253)
                    ·
                      refine ⟨223155611560177882676345, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 595081630827141020470253 223155611560177882676345)
                      ·
                        rfl

theorem cell23_434594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 5, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 5, 1, 2, 1, 3].length) (baseStart_434594 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_434594 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_434594 prefixEnd_434594 := by exact prefixLift 434594
  have htrace : WordTrace (prefixWord ++ tailWord_434594) baseStart_434594 baseEnd_434594 := by
    simpa [prefixWord, tailWord_434594, baseEnd_434594] using wordTrace_append hprefix tailTrace_434594
  have hstable : (prefixWord ++ tailWord_434594).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_434594).length < 2 ^ (prefixWord ++ tailWord_434594).sum := by decide
  have hdescent : baseEnd_434594 < baseStart_434594 := by decide
  rcases family_descends (prefixWord ++ tailWord_434594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_434612 : List Nat := [2, 5, 2, 2, 2, 1, 1, 3, 1, 2, 2]
def baseStart_434612 : Nat := 118140960795 + 434612 * 2 ^ 59
def prefixEnd_434612 : Nat := 4983230072969 + 3 ^ 40 * 434612 * 2
def baseEnd_434612 : Nat := 223164854211958812251263

theorem tailTrace_434612 : CollatzResearch.WordTrace tailWord_434612 prefixEnd_434612 223164854211958812251263 := by
  unfold tailWord_434612
  simp only [CollatzResearch.WordTrace]
  refine ⟨7925800950741212332645045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10567734600988283110193393 7925800950741212332645045)
  ·
    refine ⟨743043839131988656185473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 7925800950741212332645045 743043839131988656185473)
    ·
      refine ⟨557282879348991492139105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 743043839131988656185473 557282879348991492139105)
      ·
        refine ⟨417962159511743619104329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 557282879348991492139105 417962159511743619104329)
        ·
          refine ⟨313471619633807714328247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 417962159511743619104329 313471619633807714328247)
          ·
            refine ⟨470207429450711571492371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 313471619633807714328247 470207429450711571492371)
            ·
              refine ⟨705311144176067357238557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 470207429450711571492371 705311144176067357238557)
              ·
                refine ⟨264491679066025258964459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 705311144176067357238557 264491679066025258964459)
                ·
                  refine ⟨396737518599037888446689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 264491679066025258964459 396737518599037888446689)
                  ·
                    refine ⟨297553138949278416335017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 396737518599037888446689 297553138949278416335017)
                    ·
                      refine ⟨223164854211958812251263, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 297553138949278416335017 223164854211958812251263)
                      ·
                        rfl

theorem cell23_434612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 2, 1, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 2, 1, 1, 3, 1, 2, 2].length) (baseStart_434612 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_434612 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_434612 prefixEnd_434612 := by exact prefixLift 434612
  have htrace : WordTrace (prefixWord ++ tailWord_434612) baseStart_434612 baseEnd_434612 := by
    simpa [prefixWord, tailWord_434612, baseEnd_434612] using wordTrace_append hprefix tailTrace_434612
  have hstable : (prefixWord ++ tailWord_434612).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_434612).length < 2 ^ (prefixWord ++ tailWord_434612).sum := by decide
  have hdescent : baseEnd_434612 < baseStart_434612 := by decide
  rcases family_descends (prefixWord ++ tailWord_434612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_434617 : List Nat := [1, 2, 1, 4, 3, 1, 1, 2, 4, 2, 2]
def baseStart_434617 : Nat := 118140960795 + 434617 * 2 ^ 59
def prefixEnd_434617 : Nat := 4983230072969 + 3 ^ 40 * 434617 * 2
def baseEnd_434617 : Nat := 223167421615231292688739

theorem tailTrace_434617 : CollatzResearch.WordTrace tailWord_434617 prefixEnd_434617 223167421615231292688739 := by
  unfold tailWord_434617
  simp only [CollatzResearch.WordTrace]
  refine ⟨15851784266464310519222105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10567856177642873679481403 15851784266464310519222105)
  ·
    refine ⟨11888838199848232889416579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15851784266464310519222105 11888838199848232889416579)
    ·
      refine ⟨17833257299772349334124869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11888838199848232889416579 17833257299772349334124869)
      ·
        refine ⟨3343735743707315500148413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 17833257299772349334124869 3343735743707315500148413)
        ·
          refine ⟨1253900903890243312555655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3343735743707315500148413 1253900903890243312555655)
          ·
            refine ⟨1880851355835364968833483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1253900903890243312555655 1880851355835364968833483)
            ·
              refine ⟨2821277033753047453250225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1880851355835364968833483 2821277033753047453250225)
              ·
                refine ⟨2115957775314785589937669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2821277033753047453250225 2115957775314785589937669)
                ·
                  refine ⟨396742082871522298113313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2115957775314785589937669 396742082871522298113313)
                  ·
                    refine ⟨297556562153641723584985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 396742082871522298113313 297556562153641723584985)
                    ·
                      refine ⟨223167421615231292688739, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 297556562153641723584985 223167421615231292688739)
                      ·
                        rfl

theorem cell23_434617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 1, 1, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 1, 1, 2, 4, 2, 2].length) (baseStart_434617 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_434617 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_434617 prefixEnd_434617 := by exact prefixLift 434617
  have htrace : WordTrace (prefixWord ++ tailWord_434617) baseStart_434617 baseEnd_434617 := by
    simpa [prefixWord, tailWord_434617, baseEnd_434617] using wordTrace_append hprefix tailTrace_434617
  have hstable : (prefixWord ++ tailWord_434617).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_434617).length < 2 ^ (prefixWord ++ tailWord_434617).sum := by decide
  have hdescent : baseEnd_434617 < baseStart_434617 := by decide
  rcases family_descends (prefixWord ++ tailWord_434617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_434620 : List Nat := [2, 2, 2, 4, 1, 2, 1, 1, 2, 1, 5]
def baseStart_434620 : Nat := 118140960795 + 434620 * 2 ^ 59
def prefixEnd_434620 : Nat := 4983230072969 + 3 ^ 40 * 434620 * 2
def baseEnd_434620 : Nat := 223168962057194780951225

theorem tailTrace_434620 : CollatzResearch.WordTrace tailWord_434620 prefixEnd_434620 223168962057194780951225 := by
  unfold tailWord_434620
  simp only [CollatzResearch.WordTrace]
  refine ⟨7925946842726721015790657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10567929123635628021054209 7925946842726721015790657)
  ·
    refine ⟨5944460132045040761842993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7925946842726721015790657 5944460132045040761842993)
    ·
      refine ⟨4458345099033780571382245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5944460132045040761842993 4458345099033780571382245)
      ·
        refine ⟨835939706068833857134171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4458345099033780571382245 835939706068833857134171)
        ·
          refine ⟨1253909559103250785701257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 835939706068833857134171 1253909559103250785701257)
          ·
            refine ⟨940432169327438089275943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1253909559103250785701257 940432169327438089275943)
            ·
              refine ⟨1410648253991157133913915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 940432169327438089275943 1410648253991157133913915)
              ·
                refine ⟨2115972380986735700870873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1410648253991157133913915 2115972380986735700870873)
                ·
                  refine ⟨1586979285740051775653155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2115972380986735700870873 1586979285740051775653155)
                  ·
                    refine ⟨2380468928610077663479733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1586979285740051775653155 2380468928610077663479733)
                    ·
                      refine ⟨223168962057194780951225, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 2380468928610077663479733 223168962057194780951225)
                      ·
                        rfl

theorem cell23_434620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 2, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 2, 1, 1, 2, 1, 5].length) (baseStart_434620 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_434620 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_434620 prefixEnd_434620 := by exact prefixLift 434620
  have htrace : WordTrace (prefixWord ++ tailWord_434620) baseStart_434620 baseEnd_434620 := by
    simpa [prefixWord, tailWord_434620, baseEnd_434620] using wordTrace_append hprefix tailTrace_434620
  have hstable : (prefixWord ++ tailWord_434620).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_434620).length < 2 ^ (prefixWord ++ tailWord_434620).sum := by decide
  have hdescent : baseEnd_434620 < baseStart_434620 := by decide
  rcases family_descends (prefixWord ++ tailWord_434620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_434633 : List Nat := [1, 2, 1, 1, 2, 1, 4, 1, 4, 3, 3]
def baseStart_434633 : Nat := 118140960795 + 434633 * 2 ^ 59
def prefixEnd_434633 : Nat := 4983230072969 + 3 ^ 40 * 434633 * 2
def baseEnd_434633 : Nat := 223175637305703230088665

theorem tailTrace_434633 : CollatzResearch.WordTrace tailWord_434633 prefixEnd_434633 223175637305703230088665 := by
  unfold tailWord_434633
  simp only [CollatzResearch.WordTrace]
  refine ⟨15852367834406345251804553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10568245222937563501203035 15852367834406345251804553)
  ·
    refine ⟨11889275875804758938853415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15852367834406345251804553 11889275875804758938853415)
    ·
      refine ⟨17833913813707138408280123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11889275875804758938853415 17833913813707138408280123)
      ·
        refine ⟨26750870720560707612420185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17833913813707138408280123 26750870720560707612420185)
        ·
          refine ⟨20063153040420530709315139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26750870720560707612420185 20063153040420530709315139)
          ·
            refine ⟨30094729560630796063972709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20063153040420530709315139 30094729560630796063972709)
            ·
              refine ⟨5642761792618274261994883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 30094729560630796063972709 5642761792618274261994883)
              ·
                refine ⟨8464142688927411392992325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5642761792618274261994883 8464142688927411392992325)
                ·
                  refine ⟨1587026754173889636186061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8464142688927411392992325 1587026754173889636186061)
                  ·
                    refine ⟨595135032815208613569773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1587026754173889636186061 595135032815208613569773)
                    ·
                      refine ⟨223175637305703230088665, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 595135032815208613569773 223175637305703230088665)
                      ·
                        rfl

theorem cell23_434633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 4, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 4, 1, 4, 3, 3].length) (baseStart_434633 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_434633 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_434633 prefixEnd_434633 := by exact prefixLift 434633
  have htrace : WordTrace (prefixWord ++ tailWord_434633) baseStart_434633 baseEnd_434633 := by
    simpa [prefixWord, tailWord_434633, baseEnd_434633] using wordTrace_append hprefix tailTrace_434633
  have hstable : (prefixWord ++ tailWord_434633).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_434633).length < 2 ^ (prefixWord ++ tailWord_434633).sum := by decide
  have hdescent : baseEnd_434633 < baseStart_434633 := by decide
  rcases family_descends (prefixWord ++ tailWord_434633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_434663 : List Nat := [1, 1, 5, 2, 1, 1, 1, 2, 1, 1, 7]
def baseStart_434663 : Nat := 118140960795 + 434663 * 2 ^ 59
def prefixEnd_434663 : Nat := 4983230072969 + 3 ^ 40 * 434663 * 2
def baseEnd_434663 : Nat := 223191041725338112713527

theorem tailTrace_434663 : CollatzResearch.WordTrace tailWord_434663 prefixEnd_434663 223191041725338112713527 := by
  unfold tailWord_434663
  simp only [CollatzResearch.WordTrace]
  refine ⟨15853462024297660375396643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10568974682865106916931095 15853462024297660375396643)
  ·
    refine ⟨23780193036446490563094965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15853462024297660375396643 23780193036446490563094965)
    ·
      refine ⟨2229393097166858490290153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 23780193036446490563094965 2229393097166858490290153)
      ·
        refine ⟨1672044822875143867717615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2229393097166858490290153 1672044822875143867717615)
        ·
          refine ⟨2508067234312715801576423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1672044822875143867717615 2508067234312715801576423)
          ·
            refine ⟨3762100851469073702364635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2508067234312715801576423 3762100851469073702364635)
            ·
              refine ⟨5643151277203610553546953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3762100851469073702364635 5643151277203610553546953)
              ·
                refine ⟨4232363457902707915160215, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5643151277203610553546953 4232363457902707915160215)
                ·
                  refine ⟨6348545186854061872740323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4232363457902707915160215 6348545186854061872740323)
                  ·
                    refine ⟨9522817780281092809110485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6348545186854061872740323 9522817780281092809110485)
                    ·
                      refine ⟨223191041725338112713527, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 9522817780281092809110485 223191041725338112713527)
                      ·
                        rfl

theorem cell23_434663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 1, 2, 1, 1, 7].length) (baseStart_434663 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_434663 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_434663 prefixEnd_434663 := by exact prefixLift 434663
  have htrace : WordTrace (prefixWord ++ tailWord_434663) baseStart_434663 baseEnd_434663 := by
    simpa [prefixWord, tailWord_434663, baseEnd_434663] using wordTrace_append hprefix tailTrace_434663
  have hstable : (prefixWord ++ tailWord_434663).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_434663).length < 2 ^ (prefixWord ++ tailWord_434663).sum := by decide
  have hdescent : baseEnd_434663 < baseStart_434663 := by decide
  rcases family_descends (prefixWord ++ tailWord_434663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_434670 : List Nat := [4, 1, 2, 1, 2, 2, 1, 3, 2, 5]
def baseStart_434670 : Nat := 118140960795 + 434670 * 2 ^ 59
def prefixEnd_434670 : Nat := 4983230072969 + 3 ^ 40 * 434670 * 2
def baseEnd_434670 : Nat := 74398212029973195108665

theorem tailTrace_434670 : CollatzResearch.WordTrace tailWord_434670 prefixEnd_434670 74398212029973195108665 := by
  unfold tailWord_434670
  simp only [CollatzResearch.WordTrace]
  refine ⟨1981714666909037571362683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 10569144890181533713934309 1981714666909037571362683)
  ·
    refine ⟨2972572000363556357044025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1981714666909037571362683 2972572000363556357044025)
    ·
      refine ⟨2229429000272667267783019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2972572000363556357044025 2229429000272667267783019)
      ·
        refine ⟨3344143500409000901674529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2229429000272667267783019 3344143500409000901674529)
        ·
          refine ⟨2508107625306750676255897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3344143500409000901674529 2508107625306750676255897)
          ·
            refine ⟨1881080718980063007191923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2508107625306750676255897 1881080718980063007191923)
            ·
              refine ⟨2821621078470094510787885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1881080718980063007191923 2821621078470094510787885)
              ·
                refine ⟨1058107904426285441545457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2821621078470094510787885 1058107904426285441545457)
                ·
                  refine ⟨793580928319714081159093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1058107904426285441545457 793580928319714081159093)
                  ·
                    refine ⟨74398212029973195108665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 793580928319714081159093 74398212029973195108665)
                    ·
                      rfl

theorem cell23_434670_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 2, 1, 3, 2, 5].length) (baseStart_434670 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_434670 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_434670 prefixEnd_434670 := by exact prefixLift 434670
  have htrace : WordTrace (prefixWord ++ tailWord_434670) baseStart_434670 baseEnd_434670 := by
    simpa [prefixWord, tailWord_434670, baseEnd_434670] using wordTrace_append hprefix tailTrace_434670
  have hstable : (prefixWord ++ tailWord_434670).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_434670).length < 2 ^ (prefixWord ++ tailWord_434670).sum := by decide
  have hdescent : baseEnd_434670 < baseStart_434670 := by decide
  rcases family_descends (prefixWord ++ tailWord_434670) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_434717 : List Nat := [1, 4, 2, 2, 1, 3, 1, 2, 3, 4]
def baseStart_434717 : Nat := 118140960795 + 434717 * 2 ^ 59
def prefixEnd_434717 : Nat := 4983230072969 + 3 ^ 40 * 434717 * 2
def baseEnd_434717 : Nat := 74406256560226967146093

theorem tailTrace_434717 : CollatzResearch.WordTrace tailWord_434717 prefixEnd_434717 74406256560226967146093 := by
  unfold tailWord_434717
  simp only [CollatzResearch.WordTrace]
  refine ⟨15855431566102027597862405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10570287710734685065241603 15855431566102027597862405)
  ·
    refine ⟨2972893418644130174599201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 15855431566102027597862405 2972893418644130174599201)
    ·
      refine ⟨2229670063983097630949401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2972893418644130174599201 2229670063983097630949401)
      ·
        refine ⟨1672252547987323223212051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2229670063983097630949401 1672252547987323223212051)
        ·
          refine ⟨2508378821980984834818077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1672252547987323223212051 2508378821980984834818077)
          ·
            refine ⟨940642058242869313056779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2508378821980984834818077 940642058242869313056779)
            ·
              refine ⟨1410963087364303969585169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 940642058242869313056779 1410963087364303969585169)
              ·
                refine ⟨1058222315523227977188877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1410963087364303969585169 1058222315523227977188877)
                ·
                  refine ⟨396833368321210491445829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1058222315523227977188877 396833368321210491445829)
                  ·
                    refine ⟨74406256560226967146093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 396833368321210491445829 74406256560226967146093)
                    ·
                      rfl

theorem cell23_434717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 3, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 3, 1, 2, 3, 4].length) (baseStart_434717 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_434717 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_434717 prefixEnd_434717 := by exact prefixLift 434717
  have htrace : WordTrace (prefixWord ++ tailWord_434717) baseStart_434717 baseEnd_434717 := by
    simpa [prefixWord, tailWord_434717, baseEnd_434717] using wordTrace_append hprefix tailTrace_434717
  have hstable : (prefixWord ++ tailWord_434717).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_434717).length < 2 ^ (prefixWord ++ tailWord_434717).sum := by decide
  have hdescent : baseEnd_434717 < baseStart_434717 := by decide
  rcases family_descends (prefixWord ++ tailWord_434717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_434757 : List Nat := [1, 3, 1, 1, 1, 5, 1, 3, 3, 1, 3]
def baseStart_434757 : Nat := 118140960795 + 434757 * 2 ^ 59
def prefixEnd_434757 : Nat := 4983230072969 + 3 ^ 40 * 434757 * 2
def baseEnd_434757 : Nat := 223239308906860744938095

theorem tailTrace_434757 : CollatzResearch.WordTrace tailWord_434757 prefixEnd_434757 223239308906860744938095 := by
  unfold tailWord_434757
  simp only [CollatzResearch.WordTrace]
  refine ⟨15856890485957114429318525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10571260323971409619545683 15856890485957114429318525)
  ·
    refine ⟨5946333932233917910994447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15856890485957114429318525 5946333932233917910994447)
    ·
      refine ⟨8919500898350876866491671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5946333932233917910994447 8919500898350876866491671)
      ·
        refine ⟨13379251347526315299737507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8919500898350876866491671 13379251347526315299737507)
        ·
          refine ⟨20068877021289472949606261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13379251347526315299737507 20068877021289472949606261)
          ·
            refine ⟨1881457220745888089025587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 20068877021289472949606261 1881457220745888089025587)
            ·
              refine ⟨2822185831118832133538381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1881457220745888089025587 2822185831118832133538381)
              ·
                refine ⟨1058319686669562050076893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2822185831118832133538381 1058319686669562050076893)
                ·
                  refine ⟨396869882501085768778835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1058319686669562050076893 396869882501085768778835)
                  ·
                    refine ⟨595304823751628653168253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 396869882501085768778835 595304823751628653168253)
                    ·
                      refine ⟨223239308906860744938095, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 595304823751628653168253 223239308906860744938095)
                      ·
                        rfl

theorem cell23_434757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 5, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 5, 1, 3, 3, 1, 3].length) (baseStart_434757 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_434757 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_434757 prefixEnd_434757 := by exact prefixLift 434757
  have htrace : WordTrace (prefixWord ++ tailWord_434757) baseStart_434757 baseEnd_434757 := by
    simpa [prefixWord, tailWord_434757, baseEnd_434757] using wordTrace_append hprefix tailTrace_434757
  have hstable : (prefixWord ++ tailWord_434757).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_434757).length < 2 ^ (prefixWord ++ tailWord_434757).sum := by decide
  have hdescent : baseEnd_434757 < baseStart_434757 := by decide
  rcases family_descends (prefixWord ++ tailWord_434757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_434817 : List Nat := [1, 2, 4, 2, 1, 1, 2, 2, 3, 2, 3]
def baseStart_434817 : Nat := 118140960795 + 434817 * 2 ^ 59
def prefixEnd_434817 : Nat := 4983230072969 + 3 ^ 40 * 434817 * 2
def baseEnd_434817 : Nat := 223270117746130510187819

theorem tailTrace_434817 : CollatzResearch.WordTrace tailWord_434817 prefixEnd_434817 223270117746130510187819 := by
  unfold tailWord_434817
  simp only [CollatzResearch.WordTrace]
  refine ⟨15859078865739744676502705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10572719243826496451001803 15859078865739744676502705)
  ·
    refine ⟨11894309149304808507377029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15859078865739744676502705 11894309149304808507377029)
    ·
      refine ⟨2230182965494651595133193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 11894309149304808507377029 2230182965494651595133193)
      ·
        refine ⟨1672637224120988696349895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2230182965494651595133193 1672637224120988696349895)
        ·
          refine ⟨2508955836181483044524843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1672637224120988696349895 2508955836181483044524843)
          ·
            refine ⟨3763433754272224566787265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2508955836181483044524843 3763433754272224566787265)
            ·
              refine ⟨2822575315704168425090449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3763433754272224566787265 2822575315704168425090449)
              ·
                refine ⟨2116931486778126318817837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2822575315704168425090449 2116931486778126318817837)
                ·
                  refine ⟨793849307541797369556689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2116931486778126318817837 793849307541797369556689)
                  ·
                    refine ⟨595386980656348027167517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 793849307541797369556689 595386980656348027167517)
                    ·
                      refine ⟨223270117746130510187819, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 595386980656348027167517 223270117746130510187819)
                      ·
                        rfl

theorem cell23_434817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 2, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 2, 2, 3, 2, 3].length) (baseStart_434817 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_434817 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_434817 prefixEnd_434817 := by exact prefixLift 434817
  have htrace : WordTrace (prefixWord ++ tailWord_434817) baseStart_434817 baseEnd_434817 := by
    simpa [prefixWord, tailWord_434817, baseEnd_434817] using wordTrace_append hprefix tailTrace_434817
  have hstable : (prefixWord ++ tailWord_434817).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_434817).length < 2 ^ (prefixWord ++ tailWord_434817).sum := by decide
  have hdescent : baseEnd_434817 < baseStart_434817 := by decide
  rcases family_descends (prefixWord ++ tailWord_434817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_434820 : List Nat := [2, 3, 2, 1, 3, 1, 1, 10]
def baseStart_434820 : Nat := 118140960795 + 434820 * 2 ^ 59
def prefixEnd_434820 : Nat := 4983230072969 + 3 ^ 40 * 434820 * 2
def baseEnd_434820 : Nat := 8269320673633111053715

theorem tailTrace_434820 : CollatzResearch.WordTrace tailWord_434820 prefixEnd_434820 8269320673633111053715 := by
  unfold tailWord_434820
  simp only [CollatzResearch.WordTrace]
  refine ⟨7929594142364438094430957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10572792189819250792574609 7929594142364438094430957)
  ·
    refine ⟨2973597803386664285411609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7929594142364438094430957 2973597803386664285411609)
    ·
      refine ⟨2230198352539998214058707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2973597803386664285411609 2230198352539998214058707)
      ·
        refine ⟨3345297528809997321088061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2230198352539998214058707 3345297528809997321088061)
        ·
          refine ⟨1254486573303748995408023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3345297528809997321088061 1254486573303748995408023)
          ·
            refine ⟨1881729859955623493112035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1254486573303748995408023 1881729859955623493112035)
            ·
              refine ⟨2822594789933435239668053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1881729859955623493112035 2822594789933435239668053)
              ·
                refine ⟨8269320673633111053715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 2822594789933435239668053 8269320673633111053715)
                ·
                  rfl

theorem cell23_434820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 1, 1, 10].length) (baseStart_434820 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_434820 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_434820 prefixEnd_434820 := by exact prefixLift 434820
  have htrace : WordTrace (prefixWord ++ tailWord_434820) baseStart_434820 baseEnd_434820 := by
    simpa [prefixWord, tailWord_434820, baseEnd_434820] using wordTrace_append hprefix tailTrace_434820
  have hstable : (prefixWord ++ tailWord_434820).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_434820).length < 2 ^ (prefixWord ++ tailWord_434820).sum := by decide
  have hdescent : baseEnd_434820 < baseStart_434820 := by decide
  rcases family_descends (prefixWord ++ tailWord_434820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_434834 : List Nat := [3, 2, 3, 1, 2, 2, 1, 1, 3, 2, 3]
def baseStart_434834 : Nat := 118140960795 + 434834 * 2 ^ 59
def prefixEnd_434834 : Nat := 4983230072969 + 3 ^ 40 * 434834 * 2
def baseEnd_434834 : Nat := 223278846917256943675241

theorem tailTrace_434834 : CollatzResearch.WordTrace tailWord_434834 prefixEnd_434834 223278846917256943675241 := by
  unfold tailWord_434834
  simp only [CollatzResearch.WordTrace]
  refine ⟨3964924726669539144967889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10573132604452104386581037 3964924726669539144967889)
  ·
    refine ⟨2973693545002154358725917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3964924726669539144967889 2973693545002154358725917)
    ·
      refine ⟨1115135079375807884522219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2973693545002154358725917 1115135079375807884522219)
      ·
        refine ⟨1672702619063711826783329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1115135079375807884522219 1672702619063711826783329)
        ·
          refine ⟨1254526964297783870087497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1672702619063711826783329 1254526964297783870087497)
          ·
            refine ⟨940895223223337902565623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1254526964297783870087497 940895223223337902565623)
            ·
              refine ⟨1411342834835006853848435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 940895223223337902565623 1411342834835006853848435)
              ·
                refine ⟨2117014252252510280772653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1411342834835006853848435 2117014252252510280772653)
                ·
                  refine ⟨793880344594691355289745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2117014252252510280772653 793880344594691355289745)
                  ·
                    refine ⟨595410258446018516467309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 793880344594691355289745 595410258446018516467309)
                    ·
                      refine ⟨223278846917256943675241, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 595410258446018516467309 223278846917256943675241)
                      ·
                        rfl

theorem cell23_434834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 2, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 2, 1, 1, 3, 2, 3].length) (baseStart_434834 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_434834 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_434834 prefixEnd_434834 := by exact prefixLift 434834
  have htrace : WordTrace (prefixWord ++ tailWord_434834) baseStart_434834 baseEnd_434834 := by
    simpa [prefixWord, tailWord_434834, baseEnd_434834] using wordTrace_append hprefix tailTrace_434834
  have hstable : (prefixWord ++ tailWord_434834).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_434834).length < 2 ^ (prefixWord ++ tailWord_434834).sum := by decide
  have hdescent : baseEnd_434834 < baseStart_434834 := by decide
  rcases family_descends (prefixWord ++ tailWord_434834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_434857 : List Nat := [1, 2, 1, 1, 1, 1, 2, 4, 5, 3, 2]
def baseStart_434857 : Nat := 118140960795 + 434857 * 2 ^ 59
def prefixEnd_434857 : Nat := 4983230072969 + 3 ^ 40 * 434857 * 2
def baseEnd_434857 : Nat := 223290656972310353687635

theorem tailTrace_434857 : CollatzResearch.WordTrace tailWord_434857 prefixEnd_434857 223290656972310353687635 := by
  unfold tailWord_434857
  simp only [CollatzResearch.WordTrace]
  refine ⟨15860537785594831507958825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10573691857063221005305883 15860537785594831507958825)
  ·
    refine ⟨11895403339196123630969119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15860537785594831507958825 11895403339196123630969119)
    ·
      refine ⟨17843105008794185446453679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11895403339196123630969119 17843105008794185446453679)
      ·
        refine ⟨26764657513191278169680519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17843105008794185446453679 26764657513191278169680519)
        ·
          refine ⟨40146986269786917254520779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26764657513191278169680519 40146986269786917254520779)
          ·
            refine ⟨60220479404680375881781169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40146986269786917254520779 60220479404680375881781169)
            ·
              refine ⟨45165359553510281911335877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 60220479404680375881781169 45165359553510281911335877)
              ·
                refine ⟨8468504916283177858375477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 45165359553510281911335877 8468504916283177858375477)
                ·
                  refine ⟨793922335901547924222701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 8468504916283177858375477 793922335901547924222701)
                  ·
                    refine ⟨297720875963080471583513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 793922335901547924222701 297720875963080471583513)
                    ·
                      refine ⟨223290656972310353687635, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 297720875963080471583513 223290656972310353687635)
                      ·
                        rfl

theorem cell23_434857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 4, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 4, 5, 3, 2].length) (baseStart_434857 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_434857 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_434857 prefixEnd_434857 := by exact prefixLift 434857
  have htrace : WordTrace (prefixWord ++ tailWord_434857) baseStart_434857 baseEnd_434857 := by
    simpa [prefixWord, tailWord_434857, baseEnd_434857] using wordTrace_append hprefix tailTrace_434857
  have hstable : (prefixWord ++ tailWord_434857).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_434857).length < 2 ^ (prefixWord ++ tailWord_434857).sum := by decide
  have hdescent : baseEnd_434857 < baseStart_434857 := by decide
  rcases family_descends (prefixWord ++ tailWord_434857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_434858 : List Nat := [3, 1, 5, 2, 1, 1, 2, 2, 2, 4]
def baseStart_434858 : Nat := 118140960795 + 434858 * 2 ^ 59
def prefixEnd_434858 : Nat := 4983230072969 + 3 ^ 40 * 434858 * 2
def baseEnd_434858 : Nat := 74430390150988283258377

theorem tailTrace_434858 : CollatzResearch.WordTrace tailWord_434858 prefixEnd_434858 74430390150988283258377 := by
  unfold tailWord_434858
  simp only [CollatzResearch.WordTrace]
  refine ⟨3965143564647802169686307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10573716172394139119163485 3965143564647802169686307)
  ·
    refine ⟨5947715346971703254529461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3965143564647802169686307 5947715346971703254529461)
    ·
      refine ⟨557598313778597180112137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 5947715346971703254529461 557598313778597180112137)
      ·
        refine ⟨418198735333947885084103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 557598313778597180112137 418198735333947885084103)
        ·
          refine ⟨627298103000921827626155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 418198735333947885084103 627298103000921827626155)
          ·
            refine ⟨940947154501382741439233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 627298103000921827626155 940947154501382741439233)
            ·
              refine ⟨705710365876037056079425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 940947154501382741439233 705710365876037056079425)
              ·
                refine ⟨529282774407027792059569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 705710365876037056079425 529282774407027792059569)
                ·
                  refine ⟨396962080805270844044677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 529282774407027792059569 396962080805270844044677)
                  ·
                    refine ⟨74430390150988283258377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 396962080805270844044677 74430390150988283258377)
                    ·
                      rfl

theorem cell23_434858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 1, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 1, 1, 2, 2, 2, 4].length) (baseStart_434858 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_434858 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_434858 prefixEnd_434858 := by exact prefixLift 434858
  have htrace : WordTrace (prefixWord ++ tailWord_434858) baseStart_434858 baseEnd_434858 := by
    simpa [prefixWord, tailWord_434858, baseEnd_434858] using wordTrace_append hprefix tailTrace_434858
  have hstable : (prefixWord ++ tailWord_434858).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_434858).length < 2 ^ (prefixWord ++ tailWord_434858).sum := by decide
  have hdescent : baseEnd_434858 < baseStart_434858 := by decide
  rcases family_descends (prefixWord ++ tailWord_434858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_434865 : List Nat := [1, 2, 2, 6, 1, 1, 1, 4, 1, 2, 2]
def baseStart_434865 : Nat := 118140960795 + 434865 * 2 ^ 59
def prefixEnd_434865 : Nat := 4983230072969 + 3 ^ 40 * 434865 * 2
def baseEnd_434865 : Nat := 223294764817546322387599

theorem tailTrace_434865 : CollatzResearch.WordTrace tailWord_434865 prefixEnd_434865 223294764817546322387599 := by
  unfold tailWord_434865
  simp only [CollatzResearch.WordTrace]
  refine ⟨15860829569565848874250049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10573886379710565916166699 15860829569565848874250049)
  ·
    refine ⟨11895622177174386655687537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15860829569565848874250049 11895622177174386655687537)
    ·
      refine ⟨8921716632880789991765653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11895622177174386655687537 8921716632880789991765653)
      ·
        refine ⟨418205467166287030864015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 8921716632880789991765653 418205467166287030864015)
        ·
          refine ⟨627308200749430546296023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 418205467166287030864015 627308200749430546296023)
          ·
            refine ⟨940962301124145819444035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 627308200749430546296023 940962301124145819444035)
            ·
              refine ⟨1411443451686218729166053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 940962301124145819444035 1411443451686218729166053)
              ·
                refine ⟨264645647191166011718635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1411443451686218729166053 264645647191166011718635)
                ·
                  refine ⟨396968470786749017577953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 264645647191166011718635 396968470786749017577953)
                  ·
                    refine ⟨297726353090061763183465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 396968470786749017577953 297726353090061763183465)
                    ·
                      refine ⟨223294764817546322387599, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 297726353090061763183465 223294764817546322387599)
                      ·
                        rfl

theorem cell23_434865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 1, 1, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 1, 1, 1, 4, 1, 2, 2].length) (baseStart_434865 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_434865 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_434865 prefixEnd_434865 := by exact prefixLift 434865
  have htrace : WordTrace (prefixWord ++ tailWord_434865) baseStart_434865 baseEnd_434865 := by
    simpa [prefixWord, tailWord_434865, baseEnd_434865] using wordTrace_append hprefix tailTrace_434865
  have hstable : (prefixWord ++ tailWord_434865).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_434865).length < 2 ^ (prefixWord ++ tailWord_434865).sum := by decide
  have hdescent : baseEnd_434865 < baseStart_434865 := by decide
  rcases family_descends (prefixWord ++ tailWord_434865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_434880 : List Nat := [2, 1, 1, 2, 4, 2, 1, 1, 1, 8]
def baseStart_434880 : Nat := 118140960795 + 434880 * 2 ^ 59
def prefixEnd_434880 : Nat := 4983230072969 + 3 ^ 40 * 434880 * 2
def baseEnd_434880 : Nat := 74434155675787921233343

theorem tailTrace_434880 : CollatzResearch.WordTrace tailWord_434880 prefixEnd_434880 74434155675787921233343 := by
  unfold tailWord_434880
  simp only [CollatzResearch.WordTrace]
  refine ⟨7930688332255753218023047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10574251109674337624030729 7930688332255753218023047)
  ·
    refine ⟨11896032498383629827034571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7930688332255753218023047 11896032498383629827034571)
    ·
      refine ⟨17844048747575444740551857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11896032498383629827034571 17844048747575444740551857)
      ·
        refine ⟨13383036560681583555413893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17844048747575444740551857 13383036560681583555413893)
        ·
          refine ⟨2509319355127796916640105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13383036560681583555413893 2509319355127796916640105)
          ·
            refine ⟨1881989516345847687480079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2509319355127796916640105 1881989516345847687480079)
            ·
              refine ⟨2822984274518771531220119, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1881989516345847687480079 2822984274518771531220119)
              ·
                refine ⟨4234476411778157296830179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2822984274518771531220119 4234476411778157296830179)
                ·
                  refine ⟨6351714617667235945245269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4234476411778157296830179 6351714617667235945245269)
                  ·
                    refine ⟨74434155675787921233343, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 6351714617667235945245269 74434155675787921233343)
                    ·
                      rfl

theorem cell23_434880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 2, 1, 1, 1, 8].length) (baseStart_434880 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_434880 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_434880 prefixEnd_434880 := by exact prefixLift 434880
  have htrace : WordTrace (prefixWord ++ tailWord_434880) baseStart_434880 baseEnd_434880 := by
    simpa [prefixWord, tailWord_434880, baseEnd_434880] using wordTrace_append hprefix tailTrace_434880
  have hstable : (prefixWord ++ tailWord_434880).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_434880).length < 2 ^ (prefixWord ++ tailWord_434880).sum := by decide
  have hdescent : baseEnd_434880 < baseStart_434880 := by decide
  rcases family_descends (prefixWord ++ tailWord_434880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_434904 : List Nat := [2, 1, 2, 2, 3, 2, 2, 2, 1, 4, 2]
def baseStart_434904 : Nat := 118140960795 + 434904 * 2 ^ 59
def prefixEnd_434904 : Nat := 4983230072969 + 3 ^ 40 * 434904 * 2
def baseEnd_434904 : Nat := 223314790563071669799919

theorem tailTrace_434904 : CollatzResearch.WordTrace tailWord_434904 prefixEnd_434904 223314790563071669799919 := by
  unfold tailWord_434904
  simp only [CollatzResearch.WordTrace]
  refine ⟨7931126008212279267459883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10574834677616372356613177 7931126008212279267459883)
  ·
    refine ⟨11896689012318418901189825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7931126008212279267459883 11896689012318418901189825)
    ·
      refine ⟨8922516759238814175892369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11896689012318418901189825 8922516759238814175892369)
      ·
        refine ⟨6691887569429110631919277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8922516759238814175892369 6691887569429110631919277)
        ·
          refine ⟨2509457838535916486969729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6691887569429110631919277 2509457838535916486969729)
          ·
            refine ⟨1882093378901937365227297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2509457838535916486969729 1882093378901937365227297)
            ·
              refine ⟨1411570034176453023920473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1882093378901937365227297 1411570034176453023920473)
              ·
                refine ⟨1058677525632339767940355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1411570034176453023920473 1058677525632339767940355)
                ·
                  refine ⟨1588016288448509651910533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1058677525632339767940355 1588016288448509651910533)
                  ·
                    refine ⟨297753054084095559733225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1588016288448509651910533 297753054084095559733225)
                    ·
                      refine ⟨223314790563071669799919, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 297753054084095559733225 223314790563071669799919)
                      ·
                        rfl

theorem cell23_434904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 2, 2, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 2, 2, 2, 1, 4, 2].length) (baseStart_434904 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_434904 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_434904 prefixEnd_434904 := by exact prefixLift 434904
  have htrace : WordTrace (prefixWord ++ tailWord_434904) baseStart_434904 baseEnd_434904 := by
    simpa [prefixWord, tailWord_434904, baseEnd_434904] using wordTrace_append hprefix tailTrace_434904
  have hstable : (prefixWord ++ tailWord_434904).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_434904).length < 2 ^ (prefixWord ++ tailWord_434904).sum := by decide
  have hdescent : baseEnd_434904 < baseStart_434904 := by decide
  rcases family_descends (prefixWord ++ tailWord_434904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_434908 : List Nat := [2, 2, 5, 1, 1, 2, 1, 3, 1, 3, 2]
def baseStart_434908 : Nat := 118140960795 + 434908 * 2 ^ 59
def prefixEnd_434908 : Nat := 4983230072969 + 3 ^ 40 * 434908 * 2
def baseEnd_434908 : Nat := 223316844485689654149901

theorem tailTrace_434908 : CollatzResearch.WordTrace tailWord_434908 prefixEnd_434908 223316844485689654149901 := by
  unfold tailWord_434908
  simp only [CollatzResearch.WordTrace]
  refine ⟨7931198954205033609032689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10574931938940044812043585 7931198954205033609032689)
  ·
    refine ⟨5948399215653775206774517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7931198954205033609032689 5948399215653775206774517)
    ·
      refine ⟨557662426467541425635111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 5948399215653775206774517 557662426467541425635111)
      ·
        refine ⟨836493639701312138452667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 557662426467541425635111 836493639701312138452667)
        ·
          refine ⟨1254740459551968207679001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 836493639701312138452667 1254740459551968207679001)
          ·
            refine ⟨941055344663976155759251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1254740459551968207679001 941055344663976155759251)
            ·
              refine ⟨1411583016995964233638877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 941055344663976155759251 1411583016995964233638877)
              ·
                refine ⟨529343631373486587614579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1411583016995964233638877 529343631373486587614579)
                ·
                  refine ⟨794015447060229881421869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 529343631373486587614579 794015447060229881421869)
                  ·
                    refine ⟨297755792647586205533201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 794015447060229881421869 297755792647586205533201)
                    ·
                      refine ⟨223316844485689654149901, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 297755792647586205533201 223316844485689654149901)
                      ·
                        rfl

theorem cell23_434908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 2, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 2, 1, 3, 1, 3, 2].length) (baseStart_434908 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_434908 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_434908 prefixEnd_434908 := by exact prefixLift 434908
  have htrace : WordTrace (prefixWord ++ tailWord_434908) baseStart_434908 baseEnd_434908 := by
    simpa [prefixWord, tailWord_434908, baseEnd_434908] using wordTrace_append hprefix tailTrace_434908
  have hstable : (prefixWord ++ tailWord_434908).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_434908).length < 2 ^ (prefixWord ++ tailWord_434908).sum := by decide
  have hdescent : baseEnd_434908 < baseStart_434908 := by decide
  rcases family_descends (prefixWord ++ tailWord_434908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_434917 : List Nat := [1, 3, 1, 4, 1, 2, 1, 2, 2, 2, 4]
def baseStart_434917 : Nat := 118140960795 + 434917 * 2 ^ 59
def prefixEnd_434917 : Nat := 4983230072969 + 3 ^ 40 * 434917 * 2
def baseEnd_434917 : Nat := 223321465811580118937359

theorem tailTrace_434917 : CollatzResearch.WordTrace tailWord_434917 prefixEnd_434917 223321465811580118937359 := by
  unfold tailWord_434917
  simp only [CollatzResearch.WordTrace]
  refine ⟨15862726165377461755143005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10575150776918307836762003 15862726165377461755143005)
  ·
    refine ⟨5948522312016548158178627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15862726165377461755143005 5948522312016548158178627)
    ·
      refine ⟨8922783468024822237267941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5948522312016548158178627 8922783468024822237267941)
      ·
        refine ⟨1673021900254654169487739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8922783468024822237267941 1673021900254654169487739)
        ·
          refine ⟨2509532850381981254231609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1673021900254654169487739 2509532850381981254231609)
          ·
            refine ⟨1882149637786485940673707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2509532850381981254231609 1882149637786485940673707)
            ·
              refine ⟨2823224456679728911010561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1882149637786485940673707 2823224456679728911010561)
              ·
                refine ⟨2117418342509796683257921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2823224456679728911010561 2117418342509796683257921)
                ·
                  refine ⟨1588063756882347512443441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2117418342509796683257921 1588063756882347512443441)
                  ·
                    refine ⟨1191047817661760634332581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1588063756882347512443441 1191047817661760634332581)
                    ·
                      refine ⟨223321465811580118937359, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1191047817661760634332581 223321465811580118937359)
                      ·
                        rfl

theorem cell23_434917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 2, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 2, 1, 2, 2, 2, 4].length) (baseStart_434917 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_434917 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_434917 prefixEnd_434917 := by exact prefixLift 434917
  have htrace : WordTrace (prefixWord ++ tailWord_434917) baseStart_434917 baseEnd_434917 := by
    simpa [prefixWord, tailWord_434917, baseEnd_434917] using wordTrace_append hprefix tailTrace_434917
  have hstable : (prefixWord ++ tailWord_434917).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_434917).length < 2 ^ (prefixWord ++ tailWord_434917).sum := by decide
  have hdescent : baseEnd_434917 < baseStart_434917 := by decide
  rcases family_descends (prefixWord ++ tailWord_434917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_434921 : List Nat := [1, 2, 1, 1, 1, 2, 7, 2, 2, 2, 2]
def baseStart_434921 : Nat := 118140960795 + 434921 * 2 ^ 59
def prefixEnd_434921 : Nat := 4983230072969 + 3 ^ 40 * 434921 * 2
def baseEnd_434921 : Nat := 223323519734198103287341

theorem tailTrace_434921 : CollatzResearch.WordTrace tailWord_434921 prefixEnd_434921 223323519734198103287341 := by
  unfold tailWord_434921
  simp only [CollatzResearch.WordTrace]
  refine ⟨15862872057362970438288617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10575248038241980292192411 15862872057362970438288617)
  ·
    refine ⟨11897154043022227828716463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15862872057362970438288617 11897154043022227828716463)
    ·
      refine ⟨17845731064533341743074695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11897154043022227828716463 17845731064533341743074695)
      ·
        refine ⟨26768596596800012614612043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17845731064533341743074695 26768596596800012614612043)
        ·
          refine ⟨40152894895200018921918065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26768596596800012614612043 40152894895200018921918065)
          ·
            refine ⟨30114671171400014191438549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40152894895200018921918065 30114671171400014191438549)
            ·
              refine ⟨705812605579687832611841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 30114671171400014191438549 705812605579687832611841)
              ·
                refine ⟨529359454184765874458881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 705812605579687832611841 529359454184765874458881)
                ·
                  refine ⟨397019590638574405844161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 529359454184765874458881 397019590638574405844161)
                  ·
                    refine ⟨297764692978930804383121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 397019590638574405844161 297764692978930804383121)
                    ·
                      refine ⟨223323519734198103287341, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 297764692978930804383121 223323519734198103287341)
                      ·
                        rfl

theorem cell23_434921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 7, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 7, 2, 2, 2, 2].length) (baseStart_434921 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_434921 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_434921 prefixEnd_434921 := by exact prefixLift 434921
  have htrace : WordTrace (prefixWord ++ tailWord_434921) baseStart_434921 baseEnd_434921 := by
    simpa [prefixWord, tailWord_434921, baseEnd_434921] using wordTrace_append hprefix tailTrace_434921
  have hstable : (prefixWord ++ tailWord_434921).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_434921).length < 2 ^ (prefixWord ++ tailWord_434921).sum := by decide
  have hdescent : baseEnd_434921 < baseStart_434921 := by decide
  rcases family_descends (prefixWord ++ tailWord_434921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_434927 : List Nat := [1, 1, 2, 1, 5, 3, 2, 1, 7]
def baseStart_434927 : Nat := 118140960795 + 434927 * 2 ^ 59
def prefixEnd_434927 : Nat := 4983230072969 + 3 ^ 40 * 434927 * 2
def baseEnd_434927 : Nat := 24814066735347231090257

theorem tailTrace_434927 : CollatzResearch.WordTrace tailWord_434927 prefixEnd_434927 24814066735347231090257 := by
  unfold tailWord_434927
  simp only [CollatzResearch.WordTrace]
  refine ⟨15863090895341233463007035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10575393930227488975338023 15863090895341233463007035)
  ·
    refine ⟨23794636343011850194510553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15863090895341233463007035 23794636343011850194510553)
    ·
      refine ⟨17845977257258887645882915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23794636343011850194510553 17845977257258887645882915)
      ·
        refine ⟨26768965885888331468824373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17845977257258887645882915 26768965885888331468824373)
        ·
          refine ⟨2509590551802031075202285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 26768965885888331468824373 2509590551802031075202285)
          ·
            refine ⟨941096456925761653200857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2509590551802031075202285 941096456925761653200857)
            ·
              refine ⟨705822342694321239900643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 941096456925761653200857 705822342694321239900643)
              ·
                refine ⟨1058733514041481859850965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 705822342694321239900643 1058733514041481859850965)
                ·
                  refine ⟨24814066735347231090257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1058733514041481859850965 24814066735347231090257)
                  ·
                    rfl

theorem cell23_434927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 3, 2, 1, 7].length) (baseStart_434927 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_434927 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_434927 prefixEnd_434927 := by exact prefixLift 434927
  have htrace : WordTrace (prefixWord ++ tailWord_434927) baseStart_434927 baseEnd_434927 := by
    simpa [prefixWord, tailWord_434927, baseEnd_434927] using wordTrace_append hprefix tailTrace_434927
  have hstable : (prefixWord ++ tailWord_434927).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_434927).length < 2 ^ (prefixWord ++ tailWord_434927).sum := by decide
  have hdescent : baseEnd_434927 < baseStart_434927 := by decide
  rcases family_descends (prefixWord ++ tailWord_434927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_434932 : List Nat := [2, 6, 1, 1, 2, 1, 3, 1, 2, 1, 3]
def baseStart_434932 : Nat := 118140960795 + 434932 * 2 ^ 59
def prefixEnd_434932 : Nat := 4983230072969 + 3 ^ 40 * 434932 * 2
def baseEnd_434932 : Nat := 223329168021397560249791

theorem tailTrace_434932 : CollatzResearch.WordTrace tailWord_434932 prefixEnd_434932 223329168021397560249791 := by
  unfold tailWord_434932
  simp only [CollatzResearch.WordTrace]
  refine ⟨7931636630161559658469525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10575515506882079544626033 7931636630161559658469525)
  ·
    refine ⟨371795467038823108990759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 7931636630161559658469525 371795467038823108990759)
    ·
      refine ⟨557693200558234663486139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 371795467038823108990759 557693200558234663486139)
      ·
        refine ⟨836539800837351995229209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 557693200558234663486139 836539800837351995229209)
        ·
          refine ⟨627404850628013996421907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 836539800837351995229209 627404850628013996421907)
          ·
            refine ⟨941107275942020994632861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 627404850628013996421907 941107275942020994632861)
            ·
              refine ⟨352915228478257872987323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 941107275942020994632861 352915228478257872987323)
              ·
                refine ⟨529372842717386809480985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 352915228478257872987323 529372842717386809480985)
                ·
                  refine ⟨397029632038040107110739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 529372842717386809480985 397029632038040107110739)
                  ·
                    refine ⟨595544448057060160666109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 397029632038040107110739 595544448057060160666109)
                    ·
                      refine ⟨223329168021397560249791, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 595544448057060160666109 223329168021397560249791)
                      ·
                        rfl

theorem cell23_434932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 2, 1, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 2, 1, 3, 1, 2, 1, 3].length) (baseStart_434932 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_434932 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_434932 prefixEnd_434932 := by exact prefixLift 434932
  have htrace : WordTrace (prefixWord ++ tailWord_434932) baseStart_434932 baseEnd_434932 := by
    simpa [prefixWord, tailWord_434932, baseEnd_434932] using wordTrace_append hprefix tailTrace_434932
  have hstable : (prefixWord ++ tailWord_434932).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_434932).length < 2 ^ (prefixWord ++ tailWord_434932).sum := by decide
  have hdescent : baseEnd_434932 < baseStart_434932 := by decide
  rcases family_descends (prefixWord ++ tailWord_434932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_434989 : List Nat := [1, 5, 3, 2, 1, 2, 2, 1, 2, 2, 2]
def baseStart_434989 : Nat := 118140960795 + 434989 * 2 ^ 59
def prefixEnd_434989 : Nat := 4983230072969 + 3 ^ 40 * 434989 * 2
def baseEnd_434989 : Nat := 223358436418703837237029

theorem tailTrace_434989 : CollatzResearch.WordTrace tailWord_434989 prefixEnd_434989 223358436418703837237029 := by
  unfold tailWord_434989
  simp only [CollatzResearch.WordTrace]
  refine ⟨15865352221116618051764021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10576901480744412034509347 15865352221116618051764021)
  ·
    refine ⟨1487376770729682942352877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 15865352221116618051764021 1487376770729682942352877)
    ·
      refine ⟨557766289023631103382329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1487376770729682942352877 557766289023631103382329)
      ·
        refine ⟨418324716767723327536747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 557766289023631103382329 418324716767723327536747)
        ·
          refine ⟨627487075151584991305121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 418324716767723327536747 627487075151584991305121)
          ·
            refine ⟨470615306363688743478841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 627487075151584991305121 470615306363688743478841)
            ·
              refine ⟨352961479772766557609131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 470615306363688743478841 352961479772766557609131)
              ·
                refine ⟨529442219659149836413697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 352961479772766557609131 529442219659149836413697)
                ·
                  refine ⟨397081664744362377310273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 529442219659149836413697 397081664744362377310273)
                  ·
                    refine ⟨297811248558271782982705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 397081664744362377310273 297811248558271782982705)
                    ·
                      refine ⟨223358436418703837237029, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 297811248558271782982705 223358436418703837237029)
                      ·
                        rfl

theorem cell23_434989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 1, 2, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 1, 2, 2, 1, 2, 2, 2].length) (baseStart_434989 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_434989 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_434989 prefixEnd_434989 := by exact prefixLift 434989
  have htrace : WordTrace (prefixWord ++ tailWord_434989) baseStart_434989 baseEnd_434989 := by
    simpa [prefixWord, tailWord_434989, baseEnd_434989] using wordTrace_append hprefix tailTrace_434989
  have hstable : (prefixWord ++ tailWord_434989).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_434989).length < 2 ^ (prefixWord ++ tailWord_434989).sum := by decide
  have hdescent : baseEnd_434989 < baseStart_434989 := by decide
  rcases family_descends (prefixWord ++ tailWord_434989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_434994 : List Nat := [3, 2, 1, 1, 3, 1, 2, 1, 1, 6, 2]
def baseStart_434994 : Nat := 118140960795 + 434994 * 2 ^ 59
def prefixEnd_434994 : Nat := 4983230072969 + 3 ^ 40 * 434994 * 2
def baseEnd_434994 : Nat := 223361003821976317674505

theorem tailTrace_434994 : CollatzResearch.WordTrace tailWord_434994 prefixEnd_434994 223361003821976317674505 := by
  unfold tailWord_434994
  simp only [CollatzResearch.WordTrace]
  refine ⟨3966383646524625976424009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10577023057399002603797357 3966383646524625976424009)
  ·
    refine ⟨2974787734893469482318007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3966383646524625976424009 2974787734893469482318007)
    ·
      refine ⟨4462181602340204223477011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2974787734893469482318007 4462181602340204223477011)
      ·
        refine ⟨6693272403510306335215517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4462181602340204223477011 6693272403510306335215517)
        ·
          refine ⟨2509977151316364875705819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6693272403510306335215517 2509977151316364875705819)
          ·
            refine ⟨3764965726974547313558729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2509977151316364875705819 3764965726974547313558729)
            ·
              refine ⟨2823724295230910485169047, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3764965726974547313558729 2823724295230910485169047)
              ·
                refine ⟨4235586442846365727753571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2823724295230910485169047 4235586442846365727753571)
                ·
                  refine ⟨6353379664269548591630357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4235586442846365727753571 6353379664269548591630357)
                  ·
                    refine ⟨297814671762635090232673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6353379664269548591630357 297814671762635090232673)
                    ·
                      refine ⟨223361003821976317674505, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 297814671762635090232673 223361003821976317674505)
                      ·
                        rfl

theorem cell23_434994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 2, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 2, 1, 1, 6, 2].length) (baseStart_434994 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_434994 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_434994 prefixEnd_434994 := by exact prefixLift 434994
  have htrace : WordTrace (prefixWord ++ tailWord_434994) baseStart_434994 baseEnd_434994 := by
    simpa [prefixWord, tailWord_434994, baseEnd_434994] using wordTrace_append hprefix tailTrace_434994
  have hstable : (prefixWord ++ tailWord_434994).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_434994).length < 2 ^ (prefixWord ++ tailWord_434994).sum := by decide
  have hdescent : baseEnd_434994 < baseStart_434994 := by decide
  rcases family_descends (prefixWord ++ tailWord_434994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_435034 : List Nat := [3, 1, 1, 2, 1, 5, 2, 2, 6]
def baseStart_435034 : Nat := 118140960795 + 435034 * 2 ^ 59
def prefixEnd_435034 : Nat := 4983230072969 + 3 ^ 40 * 435034 * 2
def baseEnd_435034 : Nat := 24820171449795129019369

theorem tailTrace_435034 : CollatzResearch.WordTrace tailWord_435034 prefixEnd_435034 24820171449795129019369 := by
  unfold tailWord_435034
  simp only [CollatzResearch.WordTrace]
  refine ⟨3966748376488397684288039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10577995670635727158101437 3966748376488397684288039)
  ·
    refine ⟨5950122564732596526432059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3966748376488397684288039 5950122564732596526432059)
    ·
      refine ⟨8925183847098894789648089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5950122564732596526432059 8925183847098894789648089)
      ·
        refine ⟨6693887885324171092236067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8925183847098894789648089 6693887885324171092236067)
        ·
          refine ⟨10040831827986256638354101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6693887885324171092236067 10040831827986256638354101)
          ·
            refine ⟨941327983873711559845697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 10040831827986256638354101 941327983873711559845697)
            ·
              refine ⟨705995987905283669884273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 941327983873711559845697 705995987905283669884273)
              ·
                refine ⟨529496990928962752413205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 705995987905283669884273 529496990928962752413205)
                ·
                  refine ⟨24820171449795129019369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 529496990928962752413205 24820171449795129019369)
                  ·
                    rfl

theorem cell23_435034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 5, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 5, 2, 2, 6].length) (baseStart_435034 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_435034 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_435034 prefixEnd_435034 := by exact prefixLift 435034
  have htrace : WordTrace (prefixWord ++ tailWord_435034) baseStart_435034 baseEnd_435034 := by
    simpa [prefixWord, tailWord_435034, baseEnd_435034] using wordTrace_append hprefix tailTrace_435034
  have hstable : (prefixWord ++ tailWord_435034).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_435034).length < 2 ^ (prefixWord ++ tailWord_435034).sum := by decide
  have hdescent : baseEnd_435034 < baseStart_435034 := by decide
  rcases family_descends (prefixWord ++ tailWord_435034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_435061 : List Nat := [1, 3, 4, 1, 1, 2, 1, 1, 5, 1, 3]
def baseStart_435061 : Nat := 118140960795 + 435061 * 2 ^ 59
def prefixEnd_435061 : Nat := 4983230072969 + 3 ^ 40 * 435061 * 2
def baseEnd_435061 : Nat := 223395407025827555536697

theorem tailTrace_435061 : CollatzResearch.WordTrace tailWord_435061 prefixEnd_435061 223395407025827555536697 := by
  unfold tailWord_435061
  simp only [CollatzResearch.WordTrace]
  refine ⟨15867978276855774348385037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10578652184570516232256691 15867978276855774348385037)
  ·
    refine ⟨5950491853820915380644389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15867978276855774348385037 5950491853820915380644389)
    ·
      refine ⟨1115717222591421633870823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5950491853820915380644389 1115717222591421633870823)
      ·
        refine ⟨1673575833887132450806235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1115717222591421633870823 1673575833887132450806235)
        ·
          refine ⟨2510363750830698676209353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1673575833887132450806235 2510363750830698676209353)
          ·
            refine ⟨1882772813123024007157015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2510363750830698676209353 1882772813123024007157015)
            ·
              refine ⟨2824159219684536010735523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1882772813123024007157015 2824159219684536010735523)
              ·
                refine ⟨4236238829526804016103285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2824159219684536010735523 4236238829526804016103285)
                ·
                  refine ⟨397147390268137876509683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4236238829526804016103285 397147390268137876509683)
                  ·
                    refine ⟨595721085402206814764525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 397147390268137876509683 595721085402206814764525)
                    ·
                      refine ⟨223395407025827555536697, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 595721085402206814764525 223395407025827555536697)
                      ·
                        rfl

theorem cell23_435061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 2, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 2, 1, 1, 5, 1, 3].length) (baseStart_435061 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_435061 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_435061 prefixEnd_435061 := by exact prefixLift 435061
  have htrace : WordTrace (prefixWord ++ tailWord_435061) baseStart_435061 baseEnd_435061 := by
    simpa [prefixWord, tailWord_435061, baseEnd_435061] using wordTrace_append hprefix tailTrace_435061
  have hstable : (prefixWord ++ tailWord_435061).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_435061).length < 2 ^ (prefixWord ++ tailWord_435061).sum := by decide
  have hdescent : baseEnd_435061 < baseStart_435061 := by decide
  rcases family_descends (prefixWord ++ tailWord_435061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_435071 : List Nat := [1, 1, 2, 2, 1, 1, 7, 1, 2, 3, 2]
def baseStart_435071 : Nat := 118140960795 + 435071 * 2 ^ 59
def prefixEnd_435071 : Nat := 4983230072969 + 3 ^ 40 * 435071 * 2
def baseEnd_435071 : Nat := 223400541832372516411651

theorem tailTrace_435071 : CollatzResearch.WordTrace tailWord_435071 prefixEnd_435071 223400541832372516411651 := by
  unfold tailWord_435071
  simp only [CollatzResearch.WordTrace]
  refine ⟨15868343006819546056249067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10578895337879697370832711 15868343006819546056249067)
  ·
    refine ⟨23802514510229319084373601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15868343006819546056249067 23802514510229319084373601)
    ·
      refine ⟨17851885882671989313280201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23802514510229319084373601 17851885882671989313280201)
      ·
        refine ⟨13388914412003991984960151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17851885882671989313280201 13388914412003991984960151)
        ·
          refine ⟨20083371618005987977440227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13388914412003991984960151 20083371618005987977440227)
          ·
            refine ⟨30125057427008981966160341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20083371618005987977440227 30125057427008981966160341)
            ·
              refine ⟨706056033445523014831883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 30125057427008981966160341 706056033445523014831883)
              ·
                refine ⟨1059084050168284522247825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 706056033445523014831883 1059084050168284522247825)
                ·
                  refine ⟨794313037626213391685869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1059084050168284522247825 794313037626213391685869)
                  ·
                    refine ⟨297867389109830021882201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 794313037626213391685869 297867389109830021882201)
                    ·
                      refine ⟨223400541832372516411651, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 297867389109830021882201 223400541832372516411651)
                      ·
                        rfl

theorem cell23_435071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 7, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 7, 1, 2, 3, 2].length) (baseStart_435071 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_435071 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_435071 prefixEnd_435071 := by exact prefixLift 435071
  have htrace : WordTrace (prefixWord ++ tailWord_435071) baseStart_435071 baseEnd_435071 := by
    simpa [prefixWord, tailWord_435071, baseEnd_435071] using wordTrace_append hprefix tailTrace_435071
  have hstable : (prefixWord ++ tailWord_435071).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_435071).length < 2 ^ (prefixWord ++ tailWord_435071).sum := by decide
  have hdescent : baseEnd_435071 < baseStart_435071 := by decide
  rcases family_descends (prefixWord ++ tailWord_435071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_435081 : List Nat := [1, 2, 1, 1, 5, 2, 4, 1, 1, 5]
def baseStart_435081 : Nat := 118140960795 + 435081 * 2 ^ 59
def prefixEnd_435081 : Nat := 4983230072969 + 3 ^ 40 * 435081 * 2
def baseEnd_435081 : Nat := 74468558879639159095535

theorem tailTrace_435081 : CollatzResearch.WordTrace tailWord_435081 prefixEnd_435081 74468558879639159095535 := by
  unfold tailWord_435081
  simp only [CollatzResearch.WordTrace]
  refine ⟨15868707736783317764113097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10579138491188878509408731 15868707736783317764113097)
  ·
    refine ⟨11901530802587488323084823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15868707736783317764113097 11901530802587488323084823)
    ·
      refine ⟨17852296203881232484627235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11901530802587488323084823 17852296203881232484627235)
      ·
        refine ⟨26778444305821848726940853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17852296203881232484627235 26778444305821848726940853)
        ·
          refine ⟨2510479153670798318150705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 26778444305821848726940853 2510479153670798318150705)
          ·
            refine ⟨1882859365253098738613029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2510479153670798318150705 1882859365253098738613029)
            ·
              refine ⟨353036130984956013489943, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1882859365253098738613029 353036130984956013489943)
              ·
                refine ⟨529554196477434020234915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 353036130984956013489943 529554196477434020234915)
                ·
                  refine ⟨794331294716151030352373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 529554196477434020234915 794331294716151030352373)
                  ·
                    refine ⟨74468558879639159095535, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 794331294716151030352373 74468558879639159095535)
                    ·
                      rfl

theorem cell23_435081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 2, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 2, 4, 1, 1, 5].length) (baseStart_435081 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_435081 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_435081 prefixEnd_435081 := by exact prefixLift 435081
  have htrace : WordTrace (prefixWord ++ tailWord_435081) baseStart_435081 baseEnd_435081 := by
    simpa [prefixWord, tailWord_435081, baseEnd_435081] using wordTrace_append hprefix tailTrace_435081
  have hstable : (prefixWord ++ tailWord_435081).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_435081).length < 2 ^ (prefixWord ++ tailWord_435081).sum := by decide
  have hdescent : baseEnd_435081 < baseStart_435081 := by decide
  rcases family_descends (prefixWord ++ tailWord_435081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_435097 : List Nat := [1, 2, 1, 2, 1, 3, 1, 4, 1, 1, 6]
def baseStart_435097 : Nat := 118140960795 + 435097 * 2 ^ 59
def prefixEnd_435097 : Nat := 4983230072969 + 3 ^ 40 * 435097 * 2
def baseEnd_435097 : Nat := 223413892329389414686531

theorem tailTrace_435097 : CollatzResearch.WordTrace tailWord_435097 prefixEnd_435097 223413892329389414686531 := by
  unfold tailWord_435097
  simp only [CollatzResearch.WordTrace]
  refine ⟨15869291304725352496695545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10579527536483568331130363 15869291304725352496695545)
  ·
    refine ⟨11901968478544014372521659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15869291304725352496695545 11901968478544014372521659)
    ·
      refine ⟨17852952717816021558782489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11901968478544014372521659 17852952717816021558782489)
      ·
        refine ⟨13389714538362016169086867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17852952717816021558782489 13389714538362016169086867)
        ·
          refine ⟨20084571807543024253630301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13389714538362016169086867 20084571807543024253630301)
          ·
            refine ⟨7531714427828634095111363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20084571807543024253630301 7531714427828634095111363)
            ·
              refine ⟨11297571641742951142667045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7531714427828634095111363 11297571641742951142667045)
              ·
                refine ⟨2118294682826803339250071, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11297571641742951142667045 2118294682826803339250071)
                ·
                  refine ⟨3177442024240205008875107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2118294682826803339250071 3177442024240205008875107)
                  ·
                    refine ⟨4766163036360307513312661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3177442024240205008875107 4766163036360307513312661)
                    ·
                      refine ⟨223413892329389414686531, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 4766163036360307513312661 223413892329389414686531)
                      ·
                        rfl

theorem cell23_435097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 1, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 1, 4, 1, 1, 6].length) (baseStart_435097 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_435097 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_435097 prefixEnd_435097 := by exact prefixLift 435097
  have htrace : WordTrace (prefixWord ++ tailWord_435097) baseStart_435097 baseEnd_435097 := by
    simpa [prefixWord, tailWord_435097, baseEnd_435097] using wordTrace_append hprefix tailTrace_435097
  have hstable : (prefixWord ++ tailWord_435097).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_435097).length < 2 ^ (prefixWord ++ tailWord_435097).sum := by decide
  have hdescent : baseEnd_435097 < baseStart_435097 := by decide
  rcases family_descends (prefixWord ++ tailWord_435097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_435104 : List Nat := [2, 1, 1, 4, 1, 1, 2, 1, 5, 2, 3]
def baseStart_435104 : Nat := 118140960795 + 435104 * 2 ^ 59
def prefixEnd_435104 : Nat := 4983230072969 + 3 ^ 40 * 435104 * 2
def baseEnd_435104 : Nat := 223417486693970887298999

theorem tailTrace_435104 : CollatzResearch.WordTrace tailWord_435104 prefixEnd_435104 223417486693970887298999 := by
  unfold tailWord_435104
  simp only [CollatzResearch.WordTrace]
  refine ⟨7934773307849996346100183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10579697743799995128133577 7934773307849996346100183)
  ·
    refine ⟨11902159961774994519150275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7934773307849996346100183 11902159961774994519150275)
    ·
      refine ⟨17853239942662491778725413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11902159961774994519150275 17853239942662491778725413)
      ·
        refine ⟨3347482489249217208511015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 17853239942662491778725413 3347482489249217208511015)
        ·
          refine ⟨5021223733873825812766523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3347482489249217208511015 5021223733873825812766523)
          ·
            refine ⟨7531835600810738719149785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5021223733873825812766523 7531835600810738719149785)
            ·
              refine ⟨5648876700608054039362339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7531835600810738719149785 5648876700608054039362339)
              ·
                refine ⟨8473315050912081059043509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5648876700608054039362339 8473315050912081059043509)
                ·
                  refine ⟨794373286023007599285329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 8473315050912081059043509 794373286023007599285329)
                  ·
                    refine ⟨595779964517255699463997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 794373286023007599285329 595779964517255699463997)
                    ·
                      refine ⟨223417486693970887298999, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 595779964517255699463997 223417486693970887298999)
                      ·
                        rfl

theorem cell23_435104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 2, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 2, 1, 5, 2, 3].length) (baseStart_435104 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_435104 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_435104 prefixEnd_435104 := by exact prefixLift 435104
  have htrace : WordTrace (prefixWord ++ tailWord_435104) baseStart_435104 baseEnd_435104 := by
    simpa [prefixWord, tailWord_435104, baseEnd_435104] using wordTrace_append hprefix tailTrace_435104
  have hstable : (prefixWord ++ tailWord_435104).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_435104).length < 2 ^ (prefixWord ++ tailWord_435104).sum := by decide
  have hdescent : baseEnd_435104 < baseStart_435104 := by decide
  rcases family_descends (prefixWord ++ tailWord_435104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_435151 : List Nat := [1, 1, 2, 1, 1, 6, 2, 1, 4, 1, 3]
def baseStart_435151 : Nat := 118140960795 + 435151 * 2 ^ 59
def prefixEnd_435151 : Nat := 4983230072969 + 3 ^ 40 * 435151 * 2
def baseEnd_435151 : Nat := 223441620284732203411283

theorem tailTrace_435151 : CollatzResearch.WordTrace tailWord_435151 prefixEnd_435151 223441620284732203411283 := by
  unfold tailWord_435151
  simp only [CollatzResearch.WordTrace]
  refine ⟨15871260846529719719161307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10580840564353146479440871 15871260846529719719161307)
  ·
    refine ⟨23806891269794579578741961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15871260846529719719161307 23806891269794579578741961)
    ·
      refine ⟨17855168452345934684056471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23806891269794579578741961 17855168452345934684056471)
      ·
        refine ⟨26782752678518902026084707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17855168452345934684056471 26782752678518902026084707)
        ·
          refine ⟨40174129017778353039127061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26782752678518902026084707 40174129017778353039127061)
          ·
            refine ⟨1883162297708360298709081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 40174129017778353039127061 1883162297708360298709081)
            ·
              refine ⟨1412371723281270224031811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1883162297708360298709081 1412371723281270224031811)
              ·
                refine ⟨2118557584921905336047717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1412371723281270224031811 2118557584921905336047717)
                ·
                  refine ⟨397229547172857250508947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2118557584921905336047717 397229547172857250508947)
                  ·
                    refine ⟨595844320759285875763421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 397229547172857250508947 595844320759285875763421)
                    ·
                      refine ⟨223441620284732203411283, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 595844320759285875763421 223441620284732203411283)
                      ·
                        rfl

theorem cell23_435151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 6, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 6, 2, 1, 4, 1, 3].length) (baseStart_435151 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_435151 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_435151 prefixEnd_435151 := by exact prefixLift 435151
  have htrace : WordTrace (prefixWord ++ tailWord_435151) baseStart_435151 baseEnd_435151 := by
    simpa [prefixWord, tailWord_435151, baseEnd_435151] using wordTrace_append hprefix tailTrace_435151
  have hstable : (prefixWord ++ tailWord_435151).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_435151).length < 2 ^ (prefixWord ++ tailWord_435151).sum := by decide
  have hdescent : baseEnd_435151 < baseStart_435151 := by decide
  rcases family_descends (prefixWord ++ tailWord_435151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_435177 : List Nat := [1, 2, 1, 1, 1, 2, 1, 1, 2, 2, 9]
def baseStart_435177 : Nat := 118140960795 + 435177 * 2 ^ 59
def prefixEnd_435177 : Nat := 4983230072969 + 3 ^ 40 * 435177 * 2
def baseEnd_435177 : Nat := 223454970781749101686163

theorem tailTrace_435177 : CollatzResearch.WordTrace tailWord_435177 prefixEnd_435177 223454970781749101686163 := by
  unfold tailWord_435177
  simp only [CollatzResearch.WordTrace]
  refine ⟨15872209144435526159607785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10581472762957017439738523 15872209144435526159607785)
  ·
    refine ⟨11904156858326644619705839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15872209144435526159607785 11904156858326644619705839)
    ·
      refine ⟨17856235287489966929558759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11904156858326644619705839 17856235287489966929558759)
      ·
        refine ⟨26784352931234950394338139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17856235287489966929558759 26784352931234950394338139)
        ·
          refine ⟨40176529396852425591507209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26784352931234950394338139 40176529396852425591507209)
          ·
            refine ⟨30132397047639319193630407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40176529396852425591507209 30132397047639319193630407)
            ·
              refine ⟨45198595571458978790445611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30132397047639319193630407 45198595571458978790445611)
              ·
                refine ⟨67797893357188468185668417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45198595571458978790445611 67797893357188468185668417)
                ·
                  refine ⟨50848420017891351139251313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 67797893357188468185668417 50848420017891351139251313)
                  ·
                    refine ⟨38136315013418513354438485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 50848420017891351139251313 38136315013418513354438485)
                    ·
                      refine ⟨223454970781749101686163, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 38136315013418513354438485 223454970781749101686163)
                      ·
                        rfl

theorem cell23_435177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 1, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 1, 2, 2, 9].length) (baseStart_435177 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_435177 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_435177 prefixEnd_435177 := by exact prefixLift 435177
  have htrace : WordTrace (prefixWord ++ tailWord_435177) baseStart_435177 baseEnd_435177 := by
    simpa [prefixWord, tailWord_435177, baseEnd_435177] using wordTrace_append hprefix tailTrace_435177
  have hstable : (prefixWord ++ tailWord_435177).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_435177).length < 2 ^ (prefixWord ++ tailWord_435177).sum := by decide
  have hdescent : baseEnd_435177 < baseStart_435177 := by decide
  rcases family_descends (prefixWord ++ tailWord_435177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_435178 : List Nat := [3, 1, 3, 1, 2, 3, 1, 1, 3, 3, 2]
def baseStart_435178 : Nat := 118140960795 + 435178 * 2 ^ 59
def prefixEnd_435178 : Nat := 4983230072969 + 3 ^ 40 * 435178 * 2
def baseEnd_435178 : Nat := 223455484262403597773659

theorem tailTrace_435178 : CollatzResearch.WordTrace tailWord_435178 prefixEnd_435178 223455484262403597773659 := by
  unfold tailWord_435178
  simp only [CollatzResearch.WordTrace]
  refine ⟨3968061404357975832598547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10581497078287935553596125 3968061404357975832598547)
  ·
    refine ⟨5952092106536963748897821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3968061404357975832598547 5952092106536963748897821)
    ·
      refine ⟨2232034539951361405836683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5952092106536963748897821 2232034539951361405836683)
      ·
        refine ⟨3348051809927042108755025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2232034539951361405836683 3348051809927042108755025)
        ·
          refine ⟨2511038857445281581566269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3348051809927042108755025 2511038857445281581566269)
          ·
            refine ⟨941639571541980593087351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2511038857445281581566269 941639571541980593087351)
            ·
              refine ⟨1412459357312970889631027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 941639571541980593087351 1412459357312970889631027)
              ·
                refine ⟨2118689035969456334446541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1412459357312970889631027 2118689035969456334446541)
                ·
                  refine ⟨794508388488546125417453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2118689035969456334446541 794508388488546125417453)
                  ·
                    refine ⟨297940645683204797031545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 794508388488546125417453 297940645683204797031545)
                    ·
                      refine ⟨223455484262403597773659, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 297940645683204797031545 223455484262403597773659)
                      ·
                        rfl

theorem cell23_435178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 3, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 3, 1, 1, 3, 3, 2].length) (baseStart_435178 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_435178 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_435178 prefixEnd_435178 := by exact prefixLift 435178
  have htrace : WordTrace (prefixWord ++ tailWord_435178) baseStart_435178 baseEnd_435178 := by
    simpa [prefixWord, tailWord_435178, baseEnd_435178] using wordTrace_append hprefix tailTrace_435178
  have hstable : (prefixWord ++ tailWord_435178).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_435178).length < 2 ^ (prefixWord ++ tailWord_435178).sum := by decide
  have hdescent : baseEnd_435178 < baseStart_435178 := by decide
  rcases family_descends (prefixWord ++ tailWord_435178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_435194 : List Nat := [3, 1, 1, 1, 1, 2, 1, 2, 4, 4, 3]
def baseStart_435194 : Nat := 118140960795 + 435194 * 2 ^ 59
def prefixEnd_435194 : Nat := 4983230072969 + 3 ^ 40 * 435194 * 2
def baseEnd_435194 : Nat := 223463699952875535173585

theorem tailTrace_435194 : CollatzResearch.WordTrace tailWord_435194 prefixEnd_435194 223463699952875535173585 := by
  unfold tailWord_435194
  simp only [CollatzResearch.WordTrace]
  refine ⟨3968207296343484515744159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10581886123582625375317757 3968207296343484515744159)
  ·
    refine ⟨5952310944515226773616239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3968207296343484515744159 5952310944515226773616239)
    ·
      refine ⟨8928466416772840160424359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5952310944515226773616239 8928466416772840160424359)
      ·
        refine ⟨13392699625159260240636539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8928466416772840160424359 13392699625159260240636539)
        ·
          refine ⟨20089049437738890360954809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13392699625159260240636539 20089049437738890360954809)
          ·
            refine ⟨15066787078304167770716107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20089049437738890360954809 15066787078304167770716107)
            ·
              refine ⟨22600180617456251656074161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15066787078304167770716107 22600180617456251656074161)
              ·
                refine ⟨16950135463092188742055621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22600180617456251656074161 16950135463092188742055621)
                ·
                  refine ⟨3178150399329785389135429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16950135463092188742055621 3178150399329785389135429)
                  ·
                    refine ⟨595903199874334760462893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3178150399329785389135429 595903199874334760462893)
                    ·
                      refine ⟨223463699952875535173585, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 595903199874334760462893 223463699952875535173585)
                      ·
                        rfl

theorem cell23_435194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 1, 2, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 1, 2, 4, 4, 3].length) (baseStart_435194 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_435194 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_435194 prefixEnd_435194 := by exact prefixLift 435194
  have htrace : WordTrace (prefixWord ++ tailWord_435194) baseStart_435194 baseEnd_435194 := by
    simpa [prefixWord, tailWord_435194, baseEnd_435194] using wordTrace_append hprefix tailTrace_435194
  have hstable : (prefixWord ++ tailWord_435194).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_435194).length < 2 ^ (prefixWord ++ tailWord_435194).sum := by decide
  have hdescent : baseEnd_435194 < baseStart_435194 := by decide
  rcases family_descends (prefixWord ++ tailWord_435194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_435221 : List Nat := [1, 3, 2, 1, 4, 2, 1, 1, 2, 2, 4]
def baseStart_435221 : Nat := 118140960795 + 435221 * 2 ^ 59
def prefixEnd_435221 : Nat := 4983230072969 + 3 ^ 40 * 435221 * 2
def baseEnd_435221 : Nat := 223477563930546929535961

theorem tailTrace_435221 : CollatzResearch.WordTrace tailWord_435221 prefixEnd_435221 223477563930546929535961 := by
  unfold tailWord_435221
  simp only [CollatzResearch.WordTrace]
  refine ⟨15873813956276121674209517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10582542637517414449473011 15873813956276121674209517)
  ·
    refine ⟨5952680233603545627828569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15873813956276121674209517 5952680233603545627828569)
    ·
      refine ⟨4464510175202659220871427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5952680233603545627828569 4464510175202659220871427)
      ·
        refine ⟨6696765262803988831307141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4464510175202659220871427 6696765262803988831307141)
        ·
          refine ⟨1255643486775747905870089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6696765262803988831307141 1255643486775747905870089)
          ·
            refine ⟨941732615081810929402567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1255643486775747905870089 941732615081810929402567)
            ·
              refine ⟨1412598922622716394103851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 941732615081810929402567 1412598922622716394103851)
              ·
                refine ⟨2118898383934074591155777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1412598922622716394103851 2118898383934074591155777)
                ·
                  refine ⟨1589173787950555943366833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2118898383934074591155777 1589173787950555943366833)
                  ·
                    refine ⟨1191880340962916957525125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1589173787950555943366833 1191880340962916957525125)
                    ·
                      refine ⟨223477563930546929535961, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1191880340962916957525125 223477563930546929535961)
                      ·
                        rfl

theorem cell23_435221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 2, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 2, 1, 1, 2, 2, 4].length) (baseStart_435221 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_435221 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_435221 prefixEnd_435221 := by exact prefixLift 435221
  have htrace : WordTrace (prefixWord ++ tailWord_435221) baseStart_435221 baseEnd_435221 := by
    simpa [prefixWord, tailWord_435221, baseEnd_435221] using wordTrace_append hprefix tailTrace_435221
  have hstable : (prefixWord ++ tailWord_435221).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_435221).length < 2 ^ (prefixWord ++ tailWord_435221).sum := by decide
  have hdescent : baseEnd_435221 < baseStart_435221 := by decide
  rcases family_descends (prefixWord ++ tailWord_435221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_435244 : List Nat := [2, 2, 1, 1, 1, 2, 5, 1, 1, 7]
def baseStart_435244 : Nat := 118140960795 + 435244 * 2 ^ 59
def prefixEnd_435244 : Nat := 4983230072969 + 3 ^ 40 * 435244 * 2
def baseEnd_435244 : Nat := 74496457995200113182785

theorem tailTrace_435244 : CollatzResearch.WordTrace tailWord_435244 prefixEnd_435244 74496457995200113182785 := by
  unfold tailWord_435244
  simp only [CollatzResearch.WordTrace]
  refine ⟨7937326417596398301148393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10583101890128531068197857 7937326417596398301148393)
  ·
    refine ⟨5952994813197298725861295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7937326417596398301148393 5952994813197298725861295)
    ·
      refine ⟨8929492219795948088791943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5952994813197298725861295 8929492219795948088791943)
      ·
        refine ⟨13394238329693922133187915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8929492219795948088791943 13394238329693922133187915)
        ·
          refine ⟨20091357494540883199781873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13394238329693922133187915 20091357494540883199781873)
          ·
            refine ⟨15068518120905662399836405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20091357494540883199781873 15068518120905662399836405)
            ·
              refine ⟨1412673573834905849984663, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 15068518120905662399836405 1412673573834905849984663)
              ·
                refine ⟨2119010360752358774976995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1412673573834905849984663 2119010360752358774976995)
                ·
                  refine ⟨3178515541128538162465493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2119010360752358774976995 3178515541128538162465493)
                  ·
                    refine ⟨74496457995200113182785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 3178515541128538162465493 74496457995200113182785)
                    ·
                      rfl

theorem cell23_435244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 7].length) (baseStart_435244 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_435244 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_435244 prefixEnd_435244 := by exact prefixLift 435244
  have htrace : WordTrace (prefixWord ++ tailWord_435244) baseStart_435244 baseEnd_435244 := by
    simpa [prefixWord, tailWord_435244, baseEnd_435244] using wordTrace_append hprefix tailTrace_435244
  have hstable : (prefixWord ++ tailWord_435244).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_435244).length < 2 ^ (prefixWord ++ tailWord_435244).sum := by decide
  have hdescent : baseEnd_435244 < baseStart_435244 := by decide
  rcases family_descends (prefixWord ++ tailWord_435244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_435298 : List Nat := [3, 3, 2, 2, 1, 1, 2, 1, 1, 3, 4]
def baseStart_435298 : Nat := 118140960795 + 435298 * 2 ^ 59
def prefixEnd_435298 : Nat := 4983230072969 + 3 ^ 40 * 435298 * 2
def baseEnd_435298 : Nat := 223517101940943128273107

theorem tailTrace_435298 : CollatzResearch.WordTrace tailWord_435298 prefixEnd_435298 223517101940943128273107 := by
  unfold tailWord_435298
  simp only [CollatzResearch.WordTrace]
  refine ⟨3969155594249290956190637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10584414917998109216508365 3969155594249290956190637)
  ·
    refine ⟨1488433347843484108571489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3969155594249290956190637 1488433347843484108571489)
    ·
      refine ⟨1116325010882613081428617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1488433347843484108571489 1116325010882613081428617)
      ·
        refine ⟨837243758161959811071463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1116325010882613081428617 837243758161959811071463)
        ·
          refine ⟨1255865637242939716607195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 837243758161959811071463 1255865637242939716607195)
          ·
            refine ⟨1883798455864409574910793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1255865637242939716607195 1883798455864409574910793)
            ·
              refine ⟨1412848841898307181183095, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1883798455864409574910793 1412848841898307181183095)
              ·
                refine ⟨2119273262847460771774643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1412848841898307181183095 2119273262847460771774643)
                ·
                  refine ⟨3178909894271191157661965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2119273262847460771774643 3178909894271191157661965)
                  ·
                    refine ⟨1192091210351696684123237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3178909894271191157661965 1192091210351696684123237)
                    ·
                      refine ⟨223517101940943128273107, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1192091210351696684123237 223517101940943128273107)
                      ·
                        rfl

theorem cell23_435298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 1, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 1, 2, 1, 1, 3, 4].length) (baseStart_435298 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_435298 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_435298 prefixEnd_435298 := by exact prefixLift 435298
  have htrace : WordTrace (prefixWord ++ tailWord_435298) baseStart_435298 baseEnd_435298 := by
    simpa [prefixWord, tailWord_435298, baseEnd_435298] using wordTrace_append hprefix tailTrace_435298
  have hstable : (prefixWord ++ tailWord_435298).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_435298).length < 2 ^ (prefixWord ++ tailWord_435298).sum := by decide
  have hdescent : baseEnd_435298 < baseStart_435298 := by decide
  rcases family_descends (prefixWord ++ tailWord_435298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_435301 : List Nat := [1, 3, 1, 3, 2, 1, 1, 3, 1, 4, 3]
def baseStart_435301 : Nat := 118140960795 + 435301 * 2 ^ 59
def prefixEnd_435301 : Nat := 4983230072969 + 3 ^ 40 * 435301 * 2
def baseEnd_435301 : Nat := 223518642382906616535593

theorem tailTrace_435301 : CollatzResearch.WordTrace tailWord_435301 prefixEnd_435301 223518642382906616535593 := by
  unfold tailWord_435301
  simp only [CollatzResearch.WordTrace]
  refine ⟨15876731795986295337121757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10584487863990863558081171 15876731795986295337121757)
  ·
    refine ⟨5953774423494860751420659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15876731795986295337121757 5953774423494860751420659)
    ·
      refine ⟨8930661635242291127130989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5953774423494860751420659 8930661635242291127130989)
      ·
        refine ⟨3348998113215859172674121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8930661635242291127130989 3348998113215859172674121)
        ·
          refine ⟨2511748584911894379505591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3348998113215859172674121 2511748584911894379505591)
          ·
            refine ⟨3767622877367841569258387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2511748584911894379505591 3767622877367841569258387)
            ·
              refine ⟨5651434316051762353887581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3767622877367841569258387 5651434316051762353887581)
              ·
                refine ⟨2119287868519410882707843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5651434316051762353887581 2119287868519410882707843)
                ·
                  refine ⟨3178931802779116324061765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2119287868519410882707843 3178931802779116324061765)
                  ·
                    refine ⟨596049713021084310761581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3178931802779116324061765 596049713021084310761581)
                    ·
                      refine ⟨223518642382906616535593, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 596049713021084310761581 223518642382906616535593)
                      ·
                        rfl

theorem cell23_435301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 1, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 1, 3, 1, 4, 3].length) (baseStart_435301 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_435301 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_435301 prefixEnd_435301 := by exact prefixLift 435301
  have htrace : WordTrace (prefixWord ++ tailWord_435301) baseStart_435301 baseEnd_435301 := by
    simpa [prefixWord, tailWord_435301, baseEnd_435301] using wordTrace_append hprefix tailTrace_435301
  have hstable : (prefixWord ++ tailWord_435301).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_435301).length < 2 ^ (prefixWord ++ tailWord_435301).sum := by decide
  have hdescent : baseEnd_435301 < baseStart_435301 := by decide
  rcases family_descends (prefixWord ++ tailWord_435301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_435344 : List Nat := [2, 1, 1, 1, 1, 1, 4, 1, 1, 3, 7]
def baseStart_435344 : Nat := 118140960795 + 435344 * 2 ^ 59
def prefixEnd_435344 : Nat := 4983230072969 + 3 ^ 40 * 435344 * 2
def baseEnd_435344 : Nat := 223540722051049948297895

theorem tailTrace_435344 : CollatzResearch.WordTrace tailWord_435344 prefixEnd_435344 223540722051049948297895 := by
  unfold tailWord_435344
  simp only [CollatzResearch.WordTrace]
  refine ⟨7939150067415256840468543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10585533423220342453958057 7939150067415256840468543)
  ·
    refine ⟨11908725101122885260702815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7939150067415256840468543 11908725101122885260702815)
    ·
      refine ⟨17863087651684327891054223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11908725101122885260702815 17863087651684327891054223)
      ·
        refine ⟨26794631477526491836581335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17863087651684327891054223 26794631477526491836581335)
        ·
          refine ⟨40191947216289737754872003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26794631477526491836581335 40191947216289737754872003)
          ·
            refine ⟨60287920824434606632308005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40191947216289737754872003 60287920824434606632308005)
            ·
              refine ⟨11303985154581488743557751, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 60287920824434606632308005 11303985154581488743557751)
              ·
                refine ⟨16955977731872233115336627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11303985154581488743557751 16955977731872233115336627)
                ·
                  refine ⟨25433966597808349673004941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16955977731872233115336627 25433966597808349673004941)
                  ·
                    refine ⟨9537737474178131127376853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25433966597808349673004941 9537737474178131127376853)
                    ·
                      refine ⟨223540722051049948297895, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 9537737474178131127376853 223540722051049948297895)
                      ·
                        rfl

theorem cell23_435344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 4, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 4, 1, 1, 3, 7].length) (baseStart_435344 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_435344 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_435344 prefixEnd_435344 := by exact prefixLift 435344
  have htrace : WordTrace (prefixWord ++ tailWord_435344) baseStart_435344 baseEnd_435344 := by
    simpa [prefixWord, tailWord_435344, baseEnd_435344] using wordTrace_append hprefix tailTrace_435344
  have hstable : (prefixWord ++ tailWord_435344).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_435344).length < 2 ^ (prefixWord ++ tailWord_435344).sum := by decide
  have hdescent : baseEnd_435344 < baseStart_435344 := by decide
  rcases family_descends (prefixWord ++ tailWord_435344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_435388 : List Nat := [2, 2, 2, 3, 2, 1, 1, 2, 3, 1, 4]
def baseStart_435388 : Nat := 118140960795 + 435388 * 2 ^ 59
def prefixEnd_435388 : Nat := 4983230072969 + 3 ^ 40 * 435388 * 2
def baseEnd_435388 : Nat := 223563315199847776147693

theorem tailTrace_435388 : CollatzResearch.WordTrace tailWord_435388 prefixEnd_435388 223563315199847776147693 := by
  unfold tailWord_435388
  simp only [CollatzResearch.WordTrace]
  refine ⟨7939952473335554597769409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10586603297780739463692545 7939952473335554597769409)
  ·
    refine ⟨5954964355001665948327057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7939952473335554597769409 5954964355001665948327057)
    ·
      refine ⟨4466223266251249461245293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5954964355001665948327057 4466223266251249461245293)
      ·
        refine ⟨1674833724844218547966985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4466223266251249461245293 1674833724844218547966985)
        ·
          refine ⟨1256125293633163910975239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1674833724844218547966985 1256125293633163910975239)
          ·
            refine ⟨1884187940449745866462859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1256125293633163910975239 1884187940449745866462859)
            ·
              refine ⟨2826281910674618799694289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1884187940449745866462859 2826281910674618799694289)
              ·
                refine ⟨2119711433005964099770717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2826281910674618799694289 2119711433005964099770717)
                ·
                  refine ⟨794891787377236537414019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2119711433005964099770717 794891787377236537414019)
                  ·
                    refine ⟨1192337681065854806121029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 794891787377236537414019 1192337681065854806121029)
                    ·
                      refine ⟨223563315199847776147693, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1192337681065854806121029 223563315199847776147693)
                      ·
                        rfl

theorem cell23_435388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 1, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 1, 1, 2, 3, 1, 4].length) (baseStart_435388 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_435388 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_435388 prefixEnd_435388 := by exact prefixLift 435388
  have htrace : WordTrace (prefixWord ++ tailWord_435388) baseStart_435388 baseEnd_435388 := by
    simpa [prefixWord, tailWord_435388, baseEnd_435388] using wordTrace_append hprefix tailTrace_435388
  have hstable : (prefixWord ++ tailWord_435388).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_435388).length < 2 ^ (prefixWord ++ tailWord_435388).sum := by decide
  have hdescent : baseEnd_435388 < baseStart_435388 := by decide
  rcases family_descends (prefixWord ++ tailWord_435388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_435391 : List Nat := [1, 1, 2, 2, 2, 2, 2, 4, 1, 1, 5]
def baseStart_435391 : Nat := 118140960795 + 435391 * 2 ^ 59
def prefixEnd_435391 : Nat := 4983230072969 + 3 ^ 40 * 435391 * 2
def baseEnd_435391 : Nat := 223564855641811264410179

theorem tailTrace_435391 : CollatzResearch.WordTrace tailWord_435391 prefixEnd_435391 223564855641811264410179 := by
  unfold tailWord_435391
  simp only [CollatzResearch.WordTrace]
  refine ⟨15880014365660240707898027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10586676243773493805265351 15880014365660240707898027)
  ·
    refine ⟨23820021548490361061847041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15880014365660240707898027 23820021548490361061847041)
    ·
      refine ⟨17865016161367770796385281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23820021548490361061847041 17865016161367770796385281)
      ·
        refine ⟨13398762121025828097288961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17865016161367770796385281 13398762121025828097288961)
        ·
          refine ⟨10049071590769371072966721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13398762121025828097288961 10049071590769371072966721)
          ·
            refine ⟨7536803693077028304725041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10049071590769371072966721 7536803693077028304725041)
            ·
              refine ⟨5652602769807771228543781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7536803693077028304725041 5652602769807771228543781)
              ·
                refine ⟨1059863019338957105351959, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5652602769807771228543781 1059863019338957105351959)
                ·
                  refine ⟨1589794529008435658027939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1059863019338957105351959 1589794529008435658027939)
                  ·
                    refine ⟨2384691793512653487041909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1589794529008435658027939 2384691793512653487041909)
                    ·
                      refine ⟨223564855641811264410179, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 2384691793512653487041909 223564855641811264410179)
                      ·
                        rfl

theorem cell23_435391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 2, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 2, 4, 1, 1, 5].length) (baseStart_435391 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_435391 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_435391 prefixEnd_435391 := by exact prefixLift 435391
  have htrace : WordTrace (prefixWord ++ tailWord_435391) baseStart_435391 baseEnd_435391 := by
    simpa [prefixWord, tailWord_435391, baseEnd_435391] using wordTrace_append hprefix tailTrace_435391
  have hstable : (prefixWord ++ tailWord_435391).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_435391).length < 2 ^ (prefixWord ++ tailWord_435391).sum := by decide
  have hdescent : baseEnd_435391 < baseStart_435391 := by decide
  rcases family_descends (prefixWord ++ tailWord_435391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_435425 : List Nat := [1, 2, 3, 1, 3, 3, 1, 3, 1, 2, 3]
def baseStart_435425 : Nat := 118140960795 + 435425 * 2 ^ 59
def prefixEnd_435425 : Nat := 4983230072969 + 3 ^ 40 * 435425 * 2
def baseEnd_435425 : Nat := 223582313984064131385023

theorem tailTrace_435425 : CollatzResearch.WordTrace tailWord_435425 prefixEnd_435425 223582313984064131385023 := by
  unfold tailWord_435425
  simp only [CollatzResearch.WordTrace]
  refine ⟨15881254447537064514635729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10587502965024709676423819 15881254447537064514635729)
  ·
    refine ⟨11910940835652798385976797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15881254447537064514635729 11910940835652798385976797)
    ·
      refine ⟨4466602813369799394741299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11910940835652798385976797 4466602813369799394741299)
      ·
        refine ⟨6699904220054699092111949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4466602813369799394741299 6699904220054699092111949)
        ·
          refine ⟨2512464082520512159541981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6699904220054699092111949 2512464082520512159541981)
          ·
            refine ⟨942174030945192059828243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2512464082520512159541981 942174030945192059828243)
            ·
              refine ⟨1413261046417788089742365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 942174030945192059828243 1413261046417788089742365)
              ·
                refine ⟨529972892406670533653387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1413261046417788089742365 529972892406670533653387)
                ·
                  refine ⟨794959338610005800480081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 529972892406670533653387 794959338610005800480081)
                  ·
                    refine ⟨596219503957504350360061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 794959338610005800480081 596219503957504350360061)
                    ·
                      refine ⟨223582313984064131385023, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 596219503957504350360061 223582313984064131385023)
                      ·
                        rfl

theorem cell23_435425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 3, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 3, 1, 3, 1, 2, 3].length) (baseStart_435425 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_435425 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_435425 prefixEnd_435425 := by exact prefixLift 435425
  have htrace : WordTrace (prefixWord ++ tailWord_435425) baseStart_435425 baseEnd_435425 := by
    simpa [prefixWord, tailWord_435425, baseEnd_435425] using wordTrace_append hprefix tailTrace_435425
  have hstable : (prefixWord ++ tailWord_435425).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_435425).length < 2 ^ (prefixWord ++ tailWord_435425).sum := by decide
  have hdescent : baseEnd_435425 < baseStart_435425 := by decide
  rcases family_descends (prefixWord ++ tailWord_435425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_435438 : List Nat := [4, 1, 2, 1, 1, 1, 2, 2, 3, 3, 3]
def baseStart_435438 : Nat := 118140960795 + 435438 * 2 ^ 59
def prefixEnd_435438 : Nat := 4983230072969 + 3 ^ 40 * 435438 * 2
def baseEnd_435438 : Nat := 223588989232572580522463

theorem tailTrace_435438 : CollatzResearch.WordTrace tailWord_435438 prefixEnd_435438 223588989232572580522463 := by
  unfold tailWord_435438
  simp only [CollatzResearch.WordTrace]
  refine ⟨1985216074561245966857371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 10587819064326645156572645 1985216074561245966857371)
  ·
    refine ⟨2977824111841868950286057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1985216074561245966857371 2977824111841868950286057)
    ·
      refine ⟨2233368083881401712714543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2977824111841868950286057 2233368083881401712714543)
      ·
        refine ⟨3350052125822102569071815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2233368083881401712714543 3350052125822102569071815)
        ·
          refine ⟨5025078188733153853607723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3350052125822102569071815 5025078188733153853607723)
          ·
            refine ⟨7537617283099730780411585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5025078188733153853607723 7537617283099730780411585)
            ·
              refine ⟨5653212962324798085308689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7537617283099730780411585 5653212962324798085308689)
              ·
                refine ⟨4239909721743598563981517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5653212962324798085308689 4239909721743598563981517)
                ·
                  refine ⟨1589966145653849461493069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4239909721743598563981517 1589966145653849461493069)
                  ·
                    refine ⟨596237304620193548059901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1589966145653849461493069 596237304620193548059901)
                    ·
                      refine ⟨223588989232572580522463, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 596237304620193548059901 223588989232572580522463)
                      ·
                        rfl

theorem cell23_435438_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 2, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 2, 2, 3, 3, 3].length) (baseStart_435438 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_435438 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_435438 prefixEnd_435438 := by exact prefixLift 435438
  have htrace : WordTrace (prefixWord ++ tailWord_435438) baseStart_435438 baseEnd_435438 := by
    simpa [prefixWord, tailWord_435438, baseEnd_435438] using wordTrace_append hprefix tailTrace_435438
  have hstable : (prefixWord ++ tailWord_435438).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_435438).length < 2 ^ (prefixWord ++ tailWord_435438).sum := by decide
  have hdescent : baseEnd_435438 < baseStart_435438 := by decide
  rcases family_descends (prefixWord ++ tailWord_435438) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_435452 : List Nat := [2, 2, 2, 1, 6, 1, 1, 1, 1, 2, 4]
def baseStart_435452 : Nat := 118140960795 + 435452 * 2 ^ 59
def prefixEnd_435452 : Nat := 4983230072969 + 3 ^ 40 * 435452 * 2
def baseEnd_435452 : Nat := 223596177961735525747399

theorem tailTrace_435452 : CollatzResearch.WordTrace tailWord_435452 prefixEnd_435452 223596177961735525747399 := by
  unfold tailWord_435452
  simp only [CollatzResearch.WordTrace]
  refine ⟨7941119609219624062934305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10588159478959498750579073 7941119609219624062934305)
  ·
    refine ⟨5955839706914718047200729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7941119609219624062934305 5955839706914718047200729)
    ·
      refine ⟨4466879780186038535400547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5955839706914718047200729 4466879780186038535400547)
      ·
        refine ⟨6700319670279057803100821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4466879780186038535400547 6700319670279057803100821)
        ·
          refine ⟨314077484544330834520351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 6700319670279057803100821 314077484544330834520351)
          ·
            refine ⟨471116226816496251780527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 314077484544330834520351 471116226816496251780527)
            ·
              refine ⟨706674340224744377670791, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 471116226816496251780527 706674340224744377670791)
              ·
                refine ⟨1060011510337116566506187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 706674340224744377670791 1060011510337116566506187)
                ·
                  refine ⟨1590017265505674849759281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1060011510337116566506187 1590017265505674849759281)
                  ·
                    refine ⟨1192512949129256137319461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1590017265505674849759281 1192512949129256137319461)
                    ·
                      refine ⟨223596177961735525747399, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1192512949129256137319461 223596177961735525747399)
                      ·
                        rfl

theorem cell23_435452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 6, 1, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 6, 1, 1, 1, 1, 2, 4].length) (baseStart_435452 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_435452 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_435452 prefixEnd_435452 := by exact prefixLift 435452
  have htrace : WordTrace (prefixWord ++ tailWord_435452) baseStart_435452 baseEnd_435452 := by
    simpa [prefixWord, tailWord_435452, baseEnd_435452] using wordTrace_append hprefix tailTrace_435452
  have hstable : (prefixWord ++ tailWord_435452).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_435452).length < 2 ^ (prefixWord ++ tailWord_435452).sum := by decide
  have hdescent : baseEnd_435452 < baseStart_435452 := by decide
  rcases family_descends (prefixWord ++ tailWord_435452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_435455 : List Nat := [1, 1, 2, 2, 1, 7, 1, 1, 1, 3, 3]
def baseStart_435455 : Nat := 118140960795 + 435455 * 2 ^ 59
def prefixEnd_435455 : Nat := 4983230072969 + 3 ^ 40 * 435455 * 2
def baseEnd_435455 : Nat := 223597718403699014009885

theorem tailTrace_435455 : CollatzResearch.WordTrace tailWord_435455 prefixEnd_435455 223597718403699014009885 := by
  unfold tailWord_435455
  simp only [CollatzResearch.WordTrace]
  refine ⟨15882348637428379638227819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10588232424952253092151879 15882348637428379638227819)
  ·
    refine ⟨23823522956142569457341729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15882348637428379638227819 23823522956142569457341729)
    ·
      refine ⟨17867642217106927093006297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23823522956142569457341729 17867642217106927093006297)
      ·
        refine ⟨13400731662830195319754723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17867642217106927093006297 13400731662830195319754723)
        ·
          refine ⟨20101097494245292979632085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13400731662830195319754723 20101097494245292979632085)
          ·
            refine ⟨471119472521374054210127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 20101097494245292979632085 471119472521374054210127)
            ·
              refine ⟨706679208782061081315191, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 471119472521374054210127 706679208782061081315191)
              ·
                refine ⟨1060018813173091621972787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 706679208782061081315191 1060018813173091621972787)
                ·
                  refine ⟨1590028219759637432959181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1060018813173091621972787 1590028219759637432959181)
                  ·
                    refine ⟨596260582409864037359693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1590028219759637432959181 596260582409864037359693)
                    ·
                      refine ⟨223597718403699014009885, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 596260582409864037359693 223597718403699014009885)
                      ·
                        rfl

theorem cell23_435455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 7, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 7, 1, 1, 1, 3, 3].length) (baseStart_435455 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_435455 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_435455 prefixEnd_435455 := by exact prefixLift 435455
  have htrace : WordTrace (prefixWord ++ tailWord_435455) baseStart_435455 baseEnd_435455 := by
    simpa [prefixWord, tailWord_435455, baseEnd_435455] using wordTrace_append hprefix tailTrace_435455
  have hstable : (prefixWord ++ tailWord_435455).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_435455).length < 2 ^ (prefixWord ++ tailWord_435455).sum := by decide
  have hdescent : baseEnd_435455 < baseStart_435455 := by decide
  rcases family_descends (prefixWord ++ tailWord_435455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_435482 : List Nat := [3, 1, 1, 3, 3, 1, 2, 3, 1, 3, 2]
def baseStart_435482 : Nat := 118140960795 + 435482 * 2 ^ 59
def prefixEnd_435482 : Nat := 4983230072969 + 3 ^ 40 * 435482 * 2
def baseEnd_435482 : Nat := 223611582381370408372261

theorem tailTrace_435482 : CollatzResearch.WordTrace tailWord_435482 prefixEnd_435482 223611582381370408372261 := by
  unfold tailWord_435482
  simp only [CollatzResearch.WordTrace]
  refine ⟨3970833352082640812365175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10588888938887042166307133 3970833352082640812365175)
  ·
    refine ⟨5956250028123961218547763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3970833352082640812365175 5956250028123961218547763)
    ·
      refine ⟨8934375042185941827821645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5956250028123961218547763 8934375042185941827821645)
      ·
        refine ⟨3350390640819728185433117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8934375042185941827821645 3350390640819728185433117)
        ·
          refine ⟨1256396490307398069537419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3350390640819728185433117 1256396490307398069537419)
          ·
            refine ⟨1884594735461097104306129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1256396490307398069537419 1884594735461097104306129)
            ·
              refine ⟨1413446051595822828229597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1884594735461097104306129 1413446051595822828229597)
              ·
                refine ⟨530042269348433560586099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1413446051595822828229597 530042269348433560586099)
                ·
                  refine ⟨795063404022650340879149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 530042269348433560586099 795063404022650340879149)
                  ·
                    refine ⟨298148776508493877829681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 795063404022650340879149 298148776508493877829681)
                    ·
                      refine ⟨223611582381370408372261, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 298148776508493877829681 223611582381370408372261)
                      ·
                        rfl

theorem cell23_435482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 1, 2, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 1, 2, 3, 1, 3, 2].length) (baseStart_435482 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_435482 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_435482 prefixEnd_435482 := by exact prefixLift 435482
  have htrace : WordTrace (prefixWord ++ tailWord_435482) baseStart_435482 baseEnd_435482 := by
    simpa [prefixWord, tailWord_435482, baseEnd_435482] using wordTrace_append hprefix tailTrace_435482
  have hstable : (prefixWord ++ tailWord_435482).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_435482).length < 2 ^ (prefixWord ++ tailWord_435482).sum := by decide
  have hdescent : baseEnd_435482 < baseStart_435482 := by decide
  rcases family_descends (prefixWord ++ tailWord_435482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_435518 : List Nat := [4, 2, 1, 2, 1, 1, 2, 1, 9]
def baseStart_435518 : Nat := 118140960795 + 435518 * 2 ^ 59
def prefixEnd_435518 : Nat := 4983230072969 + 3 ^ 40 * 435518 * 2
def baseEnd_435518 : Nat := 24847785298325807502455

theorem tailTrace_435518 : CollatzResearch.WordTrace tailWord_435518 prefixEnd_435518 24847785298325807502455 := by
  unfold tailWord_435518
  simp only [CollatzResearch.WordTrace]
  refine ⟨1985580804525017674721401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 10589764290800094265180805 1985580804525017674721401)
  ·
    refine ⟨1489185603393763256041051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1985580804525017674721401 1489185603393763256041051)
    ·
      refine ⟨2233778405090644884061577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1489185603393763256041051 2233778405090644884061577)
      ·
        refine ⟨1675333803817983663046183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2233778405090644884061577 1675333803817983663046183)
        ·
          refine ⟨2513000705726975494569275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1675333803817983663046183 2513000705726975494569275)
          ·
            refine ⟨3769501058590463241853913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2513000705726975494569275 3769501058590463241853913)
            ·
              refine ⟨2827125793942847431390435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3769501058590463241853913 2827125793942847431390435)
              ·
                refine ⟨4240688690914271147085653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2827125793942847431390435 4240688690914271147085653)
                ·
                  refine ⟨24847785298325807502455, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 4240688690914271147085653 24847785298325807502455)
                  ·
                    rfl

theorem cell23_435518_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 2, 1, 9].length) (baseStart_435518 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_435518 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_435518 prefixEnd_435518 := by exact prefixLift 435518
  have htrace : WordTrace (prefixWord ++ tailWord_435518) baseStart_435518 baseEnd_435518 := by
    simpa [prefixWord, tailWord_435518, baseEnd_435518] using wordTrace_append hprefix tailTrace_435518
  have hstable : (prefixWord ++ tailWord_435518).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_435518).length < 2 ^ (prefixWord ++ tailWord_435518).sum := by decide
  have hdescent : baseEnd_435518 < baseStart_435518 := by decide
  rcases family_descends (prefixWord ++ tailWord_435518) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_435528 : List Nat := [2, 1, 3, 1, 1, 2, 1, 2, 4, 3, 3]
def baseStart_435528 : Nat := 118140960795 + 435528 * 2 ^ 59
def prefixEnd_435528 : Nat := 4983230072969 + 3 ^ 40 * 435528 * 2
def baseEnd_435528 : Nat := 223635202491477228397049

theorem tailTrace_435528 : CollatzResearch.WordTrace tailWord_435528 prefixEnd_435528 223635202491477228397049 := by
  unfold tailWord_435528
  simp only [CollatzResearch.WordTrace]
  refine ⟨7942505583081956552817619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10590007444109275403756825 7942505583081956552817619)
  ·
    refine ⟨11913758374622934829226429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7942505583081956552817619 11913758374622934829226429)
    ·
      refine ⟨4467659390483600560959911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11913758374622934829226429 4467659390483600560959911)
      ·
        refine ⟨6701489085725400841439867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4467659390483600560959911 6701489085725400841439867)
        ·
          refine ⟨10052233628588101262159801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6701489085725400841439867 10052233628588101262159801)
          ·
            refine ⟨7539175221441075946619851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10052233628588101262159801 7539175221441075946619851)
            ·
              refine ⟨11308762832161613919929777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7539175221441075946619851 11308762832161613919929777)
              ·
                refine ⟨8481572124121210439947333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11308762832161613919929777 8481572124121210439947333)
                ·
                  refine ⟨1590294773272726957490125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8481572124121210439947333 1590294773272726957490125)
                  ·
                    refine ⟨596360539977272609058797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1590294773272726957490125 596360539977272609058797)
                    ·
                      refine ⟨223635202491477228397049, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 596360539977272609058797 223635202491477228397049)
                      ·
                        rfl

theorem cell23_435528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 1, 2, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 1, 2, 4, 3, 3].length) (baseStart_435528 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_435528 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_435528 prefixEnd_435528 := by exact prefixLift 435528
  have htrace : WordTrace (prefixWord ++ tailWord_435528) baseStart_435528 baseEnd_435528 := by
    simpa [prefixWord, tailWord_435528, baseEnd_435528] using wordTrace_append hprefix tailTrace_435528
  have hstable : (prefixWord ++ tailWord_435528).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_435528).length < 2 ^ (prefixWord ++ tailWord_435528).sum := by decide
  have hdescent : baseEnd_435528 < baseStart_435528 := by decide
  rcases family_descends (prefixWord ++ tailWord_435528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_435531 : List Nat := [1, 1, 1, 1, 3, 1, 1, 2, 5, 7]
def baseStart_435531 : Nat := 118140960795 + 435531 * 2 ^ 59
def prefixEnd_435531 : Nat := 4983230072969 + 3 ^ 40 * 435531 * 2
def baseEnd_435531 : Nat := 74545580977813572219845

theorem tailTrace_435531 : CollatzResearch.WordTrace tailWord_435531 prefixEnd_435531 74545580977813572219845 := by
  unfold tailWord_435531
  simp only [CollatzResearch.WordTrace]
  refine ⟨15885120585153044617994447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10590080390102029745329631 15885120585153044617994447)
  ·
    refine ⟨23827680877729566926991671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15885120585153044617994447 23827680877729566926991671)
    ·
      refine ⟨35741521316594350390487507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23827680877729566926991671 35741521316594350390487507)
      ·
        refine ⟨53612281974891525585731261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35741521316594350390487507 53612281974891525585731261)
        ·
          refine ⟨20104605740584322094649223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 53612281974891525585731261 20104605740584322094649223)
          ·
            refine ⟨30156908610876483141973835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20104605740584322094649223 30156908610876483141973835)
            ·
              refine ⟨45235362916314724712960753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30156908610876483141973835 45235362916314724712960753)
              ·
                refine ⟨33926522187236043534720565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45235362916314724712960753 33926522187236043534720565)
                ·
                  refine ⟨3180611455053379081380053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 33926522187236043534720565 3180611455053379081380053)
                  ·
                    refine ⟨74545580977813572219845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 3180611455053379081380053 74545580977813572219845)
                    ·
                      rfl

theorem cell23_435531_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 2, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 2, 5, 7].length) (baseStart_435531 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_435531 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_435531 prefixEnd_435531 := by exact prefixLift 435531
  have htrace : WordTrace (prefixWord ++ tailWord_435531) baseStart_435531 baseEnd_435531 := by
    simpa [prefixWord, tailWord_435531, baseEnd_435531] using wordTrace_append hprefix tailTrace_435531
  have hstable : (prefixWord ++ tailWord_435531).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_435531).length < 2 ^ (prefixWord ++ tailWord_435531).sum := by decide
  have hdescent : baseEnd_435531 < baseStart_435531 := by decide
  rcases family_descends (prefixWord ++ tailWord_435531) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_435533 : List Nat := [1, 6, 1, 3, 1, 1, 3, 1, 1, 3, 2]
def baseStart_435533 : Nat := 118140960795 + 435533 * 2 ^ 59
def prefixEnd_435533 : Nat := 4983230072969 + 3 ^ 40 * 435533 * 2
def baseEnd_435533 : Nat := 223637769894749708834527

theorem tailTrace_435533 : CollatzResearch.WordTrace tailWord_435533 prefixEnd_435533 223637769894749708834527 := by
  unfold tailWord_435533
  simp only [CollatzResearch.WordTrace]
  refine ⟨15885193531145798959567253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10590129020763865973044835 15885193531145798959567253)
  ·
    refine ⟨744618446772459326229715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 15885193531145798959567253 744618446772459326229715)
    ·
      refine ⟨1116927670158688989344573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 744618446772459326229715 1116927670158688989344573)
      ·
        refine ⟨418847876309508371004215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1116927670158688989344573 418847876309508371004215)
        ·
          refine ⟨628271814464262556506323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 418847876309508371004215 628271814464262556506323)
          ·
            refine ⟨942407721696393834759485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 628271814464262556506323 942407721696393834759485)
            ·
              refine ⟨353402895636147688034807, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 942407721696393834759485 353402895636147688034807)
              ·
                refine ⟨530104343454221532052211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 353402895636147688034807 530104343454221532052211)
                ·
                  refine ⟨795156515181332298078317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 530104343454221532052211 795156515181332298078317)
                  ·
                    refine ⟨298183693192999611779369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 795156515181332298078317 298183693192999611779369)
                    ·
                      refine ⟨223637769894749708834527, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 298183693192999611779369 223637769894749708834527)
                      ·
                        rfl

theorem cell23_435533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 1, 1, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 1, 1, 3, 1, 1, 3, 2].length) (baseStart_435533 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_435533 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_435533 prefixEnd_435533 := by exact prefixLift 435533
  have htrace : WordTrace (prefixWord ++ tailWord_435533) baseStart_435533 baseEnd_435533 := by
    simpa [prefixWord, tailWord_435533, baseEnd_435533] using wordTrace_append hprefix tailTrace_435533
  have hstable : (prefixWord ++ tailWord_435533).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_435533).length < 2 ^ (prefixWord ++ tailWord_435533).sum := by decide
  have hdescent : baseEnd_435533 < baseStart_435533 := by decide
  rcases family_descends (prefixWord ++ tailWord_435533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_435552 : List Nat := [2, 1, 1, 3, 4, 1, 4, 2, 5]
def baseStart_435552 : Nat := 118140960795 + 435552 * 2 ^ 59
def prefixEnd_435552 : Nat := 4983230072969 + 3 ^ 40 * 435552 * 2
def baseEnd_435552 : Nat := 24849725114131681610771

theorem tailTrace_435552 : CollatzResearch.WordTrace tailWord_435552 prefixEnd_435552 24849725114131681610771 := by
  unfold tailWord_435552
  simp only [CollatzResearch.WordTrace]
  refine ⟨7942943259038482602254455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10590591012051310136339273 7942943259038482602254455)
  ·
    refine ⟨11914414888557723903381683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7942943259038482602254455 11914414888557723903381683)
    ·
      refine ⟨17871622332836585855072525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11914414888557723903381683 17871622332836585855072525)
      ·
        refine ⟨6701858374813719695652197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17871622332836585855072525 6701858374813719695652197)
        ·
          refine ⟨1256598445277572442934787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6701858374813719695652197 1256598445277572442934787)
          ·
            refine ⟨1884897667916358664402181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1256598445277572442934787 1884897667916358664402181)
            ·
              refine ⟨353418312734317249575409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1884897667916358664402181 353418312734317249575409)
              ·
                refine ⟨265063734550737937181557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 353418312734317249575409 265063734550737937181557)
                ·
                  refine ⟨24849725114131681610771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 265063734550737937181557 24849725114131681610771)
                  ·
                    rfl

theorem cell23_435552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 1, 4, 2, 5].length) (baseStart_435552 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_435552 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_435552 prefixEnd_435552 := by exact prefixLift 435552
  have htrace : WordTrace (prefixWord ++ tailWord_435552) baseStart_435552 baseEnd_435552 := by
    simpa [prefixWord, tailWord_435552, baseEnd_435552] using wordTrace_append hprefix tailTrace_435552
  have hstable : (prefixWord ++ tailWord_435552).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_435552).length < 2 ^ (prefixWord ++ tailWord_435552).sum := by decide
  have hdescent : baseEnd_435552 < baseStart_435552 := by decide
  rcases family_descends (prefixWord ++ tailWord_435552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_435555 : List Nat := [1, 1, 1, 5, 2, 2, 1, 1, 2, 5, 2]
def baseStart_435555 : Nat := 118140960795 + 435555 * 2 ^ 59
def prefixEnd_435555 : Nat := 4983230072969 + 3 ^ 40 * 435555 * 2
def baseEnd_435555 : Nat := 223649066469148622759425

theorem tailTrace_435555 : CollatzResearch.WordTrace tailWord_435555 prefixEnd_435555 223649066469148622759425 := by
  unfold tailWord_435555
  simp only [CollatzResearch.WordTrace]
  refine ⟨15885995937066096716868119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10590663958044064477912079 15885995937066096716868119)
  ·
    refine ⟨23828993905599145075302179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15885995937066096716868119 23828993905599145075302179)
    ·
      refine ⟨35743490858398717612953269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23828993905599145075302179 35743490858398717612953269)
      ·
        refine ⟨3350952267974879776214369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 35743490858398717612953269 3350952267974879776214369)
        ·
          refine ⟨2513214200981159832160777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3350952267974879776214369 2513214200981159832160777)
          ·
            refine ⟨1884910650735869874120583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2513214200981159832160777 1884910650735869874120583)
            ·
              refine ⟨2827365976103804811180875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1884910650735869874120583 2827365976103804811180875)
              ·
                refine ⟨4241048964155707216771313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2827365976103804811180875 4241048964155707216771313)
                ·
                  refine ⟨3180786723116780412578485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4241048964155707216771313 3180786723116780412578485)
                  ·
                    refine ⟨298198755292198163679233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3180786723116780412578485 298198755292198163679233)
                    ·
                      refine ⟨223649066469148622759425, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 298198755292198163679233 223649066469148622759425)
                      ·
                        rfl

theorem cell23_435555_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 2, 1, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 2, 1, 1, 2, 5, 2].length) (baseStart_435555 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_435555 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_435555 prefixEnd_435555 := by exact prefixLift 435555
  have htrace : WordTrace (prefixWord ++ tailWord_435555) baseStart_435555 baseEnd_435555 := by
    simpa [prefixWord, tailWord_435555, baseEnd_435555] using wordTrace_append hprefix tailTrace_435555
  have hstable : (prefixWord ++ tailWord_435555).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_435555).length < 2 ^ (prefixWord ++ tailWord_435555).sum := by decide
  have hdescent : baseEnd_435555 < baseStart_435555 := by decide
  rcases family_descends (prefixWord ++ tailWord_435555) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_435562 : List Nat := [3, 1, 3, 3, 2, 1, 1, 1, 2, 3, 3]
def baseStart_435562 : Nat := 118140960795 + 435562 * 2 ^ 59
def prefixEnd_435562 : Nat := 4983230072969 + 3 ^ 40 * 435562 * 2
def baseEnd_435562 : Nat := 223652660833730095371893

theorem tailTrace_435562 : CollatzResearch.WordTrace tailWord_435562 prefixEnd_435562 223652660833730095371893 := by
  unfold tailWord_435562
  simp only [CollatzResearch.WordTrace]
  refine ⟨3971562812010184228093235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10590834165360491274915293 3971562812010184228093235)
  ·
    refine ⟨5957344218015276342139853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3971562812010184228093235 5957344218015276342139853)
    ·
      refine ⟨2234004081755728628302445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5957344218015276342139853 2234004081755728628302445)
      ·
        refine ⟨837751530658398235613417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2234004081755728628302445 837751530658398235613417)
        ·
          refine ⟨628313647993798676710063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 837751530658398235613417 628313647993798676710063)
          ·
            refine ⟨942470471990698015065095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 628313647993798676710063 942470471990698015065095)
            ·
              refine ⟨1413705707986047022597643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 942470471990698015065095 1413705707986047022597643)
              ·
                refine ⟨2120558561979070533896465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1413705707986047022597643 2120558561979070533896465)
                ·
                  refine ⟨1590418921484302900422349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2120558561979070533896465 1590418921484302900422349)
                  ·
                    refine ⟨596407095556613587658381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1590418921484302900422349 596407095556613587658381)
                    ·
                      refine ⟨223652660833730095371893, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 596407095556613587658381 223652660833730095371893)
                      ·
                        rfl

theorem cell23_435562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 2, 1, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 2, 1, 1, 1, 2, 3, 3].length) (baseStart_435562 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_435562 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_435562 prefixEnd_435562 := by exact prefixLift 435562
  have htrace : WordTrace (prefixWord ++ tailWord_435562) baseStart_435562 baseEnd_435562 := by
    simpa [prefixWord, tailWord_435562, baseEnd_435562] using wordTrace_append hprefix tailTrace_435562
  have hstable : (prefixWord ++ tailWord_435562).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_435562).length < 2 ^ (prefixWord ++ tailWord_435562).sum := by decide
  have hdescent : baseEnd_435562 < baseStart_435562 := by decide
  rcases family_descends (prefixWord ++ tailWord_435562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_435568 : List Nat := [2, 1, 1, 1, 4, 2, 2, 2, 1, 3, 4]
def baseStart_435568 : Nat := 118140960795 + 435568 * 2 ^ 59
def prefixEnd_435568 : Nat := 4983230072969 + 3 ^ 40 * 435568 * 2
def baseEnd_435568 : Nat := 223655741717657071896865

theorem tailTrace_435568 : CollatzResearch.WordTrace tailWord_435568 prefixEnd_435568 223655741717657071896865 := by
  unfold tailWord_435568
  simp only [CollatzResearch.WordTrace]
  refine ⟨7943235043009499968545679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10590980057345999958060905 7943235043009499968545679)
  ·
    refine ⟨11914852564514249952818519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7943235043009499968545679 11914852564514249952818519)
    ·
      refine ⟨17872278846771374929227779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11914852564514249952818519 17872278846771374929227779)
      ·
        refine ⟨26808418270157062393841669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17872278846771374929227779 26808418270157062393841669)
        ·
          refine ⟨5026578425654449198845313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 26808418270157062393841669 5026578425654449198845313)
          ·
            refine ⟨3769933819240836899133985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5026578425654449198845313 3769933819240836899133985)
            ·
              refine ⟨2827450364430627674350489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3769933819240836899133985 2827450364430627674350489)
              ·
                refine ⟨2120587773322970755762867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2827450364430627674350489 2120587773322970755762867)
                ·
                  refine ⟨3180881659984456133644301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2120587773322970755762867 3180881659984456133644301)
                  ·
                    refine ⟨1192830622494171050116613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3180881659984456133644301 1192830622494171050116613)
                    ·
                      refine ⟨223655741717657071896865, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1192830622494171050116613 223655741717657071896865)
                      ·
                        rfl

theorem cell23_435568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 2, 2, 1, 3, 4].length) (baseStart_435568 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_435568 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_435568 prefixEnd_435568 := by exact prefixLift 435568
  have htrace : WordTrace (prefixWord ++ tailWord_435568) baseStart_435568 baseEnd_435568 := by
    simpa [prefixWord, tailWord_435568, baseEnd_435568] using wordTrace_append hprefix tailTrace_435568
  have hstable : (prefixWord ++ tailWord_435568).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_435568).length < 2 ^ (prefixWord ++ tailWord_435568).sum := by decide
  have hdescent : baseEnd_435568 < baseStart_435568 := by decide
  rcases family_descends (prefixWord ++ tailWord_435568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_435605 : List Nat := [1, 3, 2, 1, 1, 2, 2, 4, 2, 2, 3]
def baseStart_435605 : Nat := 118140960795 + 435605 * 2 ^ 59
def prefixEnd_435605 : Nat := 4983230072969 + 3 ^ 40 * 435605 * 2
def baseEnd_435605 : Nat := 223674740501873427134195

theorem tailTrace_435605 : CollatzResearch.WordTrace tailWord_435605 prefixEnd_435605 223674740501873427134195 := by
  unfold tailWord_435605
  simp only [CollatzResearch.WordTrace]
  refine ⟨15887819586884955256188269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10591879724589970170792179 15887819586884955256188269)
  ·
    refine ⟨5957932345081858221070601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15887819586884955256188269 5957932345081858221070601)
    ·
      refine ⟨4468449258811393665802951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5957932345081858221070601 4468449258811393665802951)
      ·
        refine ⟨6702673888217090498704427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4468449258811393665802951 6702673888217090498704427)
        ·
          refine ⟨10054010832325635748056641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6702673888217090498704427 10054010832325635748056641)
          ·
            refine ⟨7540508124244226811042481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10054010832325635748056641 7540508124244226811042481)
            ·
              refine ⟨5655381093183170108281861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7540508124244226811042481 5655381093183170108281861)
              ·
                refine ⟨1060383954971844395302849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5655381093183170108281861 1060383954971844395302849)
                ·
                  refine ⟨795287966228883296477137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1060383954971844395302849 795287966228883296477137)
                  ·
                    refine ⟨596465974671662472357853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 795287966228883296477137 596465974671662472357853)
                    ·
                      refine ⟨223674740501873427134195, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 596465974671662472357853 223674740501873427134195)
                      ·
                        rfl

theorem cell23_435605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 2, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 2, 4, 2, 2, 3].length) (baseStart_435605 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_435605 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_435605 prefixEnd_435605 := by exact prefixLift 435605
  have htrace : WordTrace (prefixWord ++ tailWord_435605) baseStart_435605 baseEnd_435605 := by
    simpa [prefixWord, tailWord_435605, baseEnd_435605] using wordTrace_append hprefix tailTrace_435605
  have hstable : (prefixWord ++ tailWord_435605).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_435605).length < 2 ^ (prefixWord ++ tailWord_435605).sum := by decide
  have hdescent : baseEnd_435605 < baseStart_435605 := by decide
  rcases family_descends (prefixWord ++ tailWord_435605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_435655 : List Nat := [1, 1, 4, 1, 1, 3, 1, 5, 1, 5]
def baseStart_435655 : Nat := 118140960795 + 435655 * 2 ^ 59
def prefixEnd_435655 : Nat := 4983230072969 + 3 ^ 40 * 435655 * 2
def baseEnd_435655 : Nat := 74566804844866077169655

theorem tailTrace_435655 : CollatzResearch.WordTrace tailWord_435655 prefixEnd_435655 74566804844866077169655 := by
  unfold tailWord_435655
  simp only [CollatzResearch.WordTrace]
  refine ⟨15889643236703813795508419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10593095491135875863672279 15889643236703813795508419)
  ·
    refine ⟨23834464855055720693262629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15889643236703813795508419 23834464855055720693262629)
    ·
      refine ⟨4468962160322947629986743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 23834464855055720693262629 4468962160322947629986743)
      ·
        refine ⟨6703443240484421444980115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4468962160322947629986743 6703443240484421444980115)
        ·
          refine ⟨10055164860726632167470173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6703443240484421444980115 10055164860726632167470173)
          ·
            refine ⟨3770686822772487062801315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10055164860726632167470173 3770686822772487062801315)
            ·
              refine ⟨5656030234158730594201973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3770686822772487062801315 5656030234158730594201973)
              ·
                refine ⟨530252834452380993206435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 5656030234158730594201973 530252834452380993206435)
                ·
                  refine ⟨795379251678571489809653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 530252834452380993206435 795379251678571489809653)
                  ·
                    refine ⟨74566804844866077169655, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 795379251678571489809653 74566804844866077169655)
                    ·
                      rfl

theorem cell23_435655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 1, 5, 1, 5].length) (baseStart_435655 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_435655 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_435655 prefixEnd_435655 := by exact prefixLift 435655
  have htrace : WordTrace (prefixWord ++ tailWord_435655) baseStart_435655 baseEnd_435655 := by
    simpa [prefixWord, tailWord_435655, baseEnd_435655] using wordTrace_append hprefix tailTrace_435655
  have hstable : (prefixWord ++ tailWord_435655).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_435655).length < 2 ^ (prefixWord ++ tailWord_435655).sum := by decide
  have hdescent : baseEnd_435655 < baseStart_435655 := by decide
  rcases family_descends (prefixWord ++ tailWord_435655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_435662 : List Nat := [4, 1, 1, 1, 2, 1, 3, 1, 4, 3, 2]
def baseStart_435662 : Nat := 118140960795 + 435662 * 2 ^ 59
def prefixEnd_435662 : Nat := 4983230072969 + 3 ^ 40 * 435662 * 2
def baseEnd_435662 : Nat := 223704008899179704121433

theorem tailTrace_435662 : CollatzResearch.WordTrace tailWord_435662 prefixEnd_435662 223704008899179704121433 := by
  unfold tailWord_435662
  simp only [CollatzResearch.WordTrace]
  refine ⟨1986237318459806748876655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 10593265698452302660675493 1986237318459806748876655)
  ·
    refine ⟨2979355977689710123314983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1986237318459806748876655 2979355977689710123314983)
    ·
      refine ⟨4469033966534565184972475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2979355977689710123314983 4469033966534565184972475)
      ·
        refine ⟨6703550949801847777458713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4469033966534565184972475 6703550949801847777458713)
        ·
          refine ⟨5027663212351385833094035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6703550949801847777458713 5027663212351385833094035)
          ·
            refine ⟨7541494818527078749641053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5027663212351385833094035 7541494818527078749641053)
            ·
              refine ⟨2828060556947654531115395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7541494818527078749641053 2828060556947654531115395)
              ·
                refine ⟨4242090835421481796673093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2828060556947654531115395 4242090835421481796673093)
                ·
                  refine ⟨795392031641527836876205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4242090835421481796673093 795392031641527836876205)
                  ·
                    refine ⟨298272011865572938828577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 795392031641527836876205 298272011865572938828577)
                    ·
                      refine ⟨223704008899179704121433, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 298272011865572938828577 223704008899179704121433)
                      ·
                        rfl

theorem cell23_435662_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 3, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 3, 1, 4, 3, 2].length) (baseStart_435662 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_435662 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_435662 prefixEnd_435662 := by exact prefixLift 435662
  have htrace : WordTrace (prefixWord ++ tailWord_435662) baseStart_435662 baseEnd_435662 := by
    simpa [prefixWord, tailWord_435662, baseEnd_435662] using wordTrace_append hprefix tailTrace_435662
  have hstable : (prefixWord ++ tailWord_435662).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_435662).length < 2 ^ (prefixWord ++ tailWord_435662).sum := by decide
  have hdescent : baseEnd_435662 < baseStart_435662 := by decide
  rcases family_descends (prefixWord ++ tailWord_435662) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_435702 : List Nat := [5, 1, 1, 1, 2, 3, 1, 2, 1, 6]
def baseStart_435702 : Nat := 118140960795 + 435702 * 2 ^ 59
def prefixEnd_435702 : Nat := 4983230072969 + 3 ^ 40 * 435702 * 2
def baseEnd_435702 : Nat := 74574849375119849207083

theorem tailTrace_435702 : CollatzResearch.WordTrace tailWord_435702 prefixEnd_435702 74574849375119849207083 := by
  unfold tailWord_435702
  simp only [CollatzResearch.WordTrace]
  refine ⟨993209841720846301404335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 10594238311689027214979573 993209841720846301404335)
  ·
    refine ⟨1489814762581269452106503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 993209841720846301404335 1489814762581269452106503)
    ·
      refine ⟨2234722143871904178159755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1489814762581269452106503 2234722143871904178159755)
      ·
        refine ⟨3352083215807856267239633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2234722143871904178159755 3352083215807856267239633)
        ·
          refine ⟨2514062411855892200429725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3352083215807856267239633 2514062411855892200429725)
          ·
            refine ⟨942773404445959575161147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2514062411855892200429725 942773404445959575161147)
            ·
              refine ⟨1414160106668939362741721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 942773404445959575161147 1414160106668939362741721)
              ·
                refine ⟨1060620080001704522056291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1414160106668939362741721 1060620080001704522056291)
                ·
                  refine ⟨1590930120002556783084437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1060620080001704522056291 1590930120002556783084437)
                  ·
                    refine ⟨74574849375119849207083, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1590930120002556783084437 74574849375119849207083)
                    ·
                      rfl

theorem cell23_435702_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 3, 1, 2, 1, 6].length) (baseStart_435702 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_435702 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_435702 prefixEnd_435702 := by exact prefixLift 435702
  have htrace : WordTrace (prefixWord ++ tailWord_435702) baseStart_435702 baseEnd_435702 := by
    simpa [prefixWord, tailWord_435702, baseEnd_435702] using wordTrace_append hprefix tailTrace_435702
  have hstable : (prefixWord ++ tailWord_435702).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_435702).length < 2 ^ (prefixWord ++ tailWord_435702).sum := by decide
  have hdescent : baseEnd_435702 < baseStart_435702 := by decide
  rcases family_descends (prefixWord ++ tailWord_435702) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_435709 : List Nat := [1, 4, 1, 1, 1, 5, 3, 1, 1, 1, 4]
def baseStart_435709 : Nat := 118140960795 + 435709 * 2 ^ 59
def prefixEnd_435709 : Nat := 4983230072969 + 3 ^ 40 * 435709 * 2
def baseEnd_435709 : Nat := 223728142489941020233717

theorem tailTrace_435709 : CollatzResearch.WordTrace tailWord_435709 prefixEnd_435709 223728142489941020233717 := by
  unfold tailWord_435709
  simp only [CollatzResearch.WordTrace]
  refine ⟨15891612778508181017974181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10594408519005454011982787 15891612778508181017974181)
  ·
    refine ⟨2979677395970283940870159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 15891612778508181017974181 2979677395970283940870159)
    ·
      refine ⟨4469516093955425911305239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2979677395970283940870159 4469516093955425911305239)
      ·
        refine ⟨6704274140933138866957859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4469516093955425911305239 6704274140933138866957859)
        ·
          refine ⟨10056411211399708300436789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6704274140933138866957859 10056411211399708300436789)
          ·
            refine ⟨942788551068722653165949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 10056411211399708300436789 942788551068722653165949)
            ·
              refine ⟨353545706650770994937231, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 942788551068722653165949 353545706650770994937231)
              ·
                refine ⟨530318559976156492405847, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 353545706650770994937231 530318559976156492405847)
                ·
                  refine ⟨795477839964234738608771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 530318559976156492405847 795477839964234738608771)
                  ·
                    refine ⟨1193216759946352107913157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 795477839964234738608771 1193216759946352107913157)
                    ·
                      refine ⟨223728142489941020233717, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1193216759946352107913157 223728142489941020233717)
                      ·
                        rfl

theorem cell23_435709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 5, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 5, 3, 1, 1, 1, 4].length) (baseStart_435709 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_435709 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_435709 prefixEnd_435709 := by exact prefixLift 435709
  have htrace : WordTrace (prefixWord ++ tailWord_435709) baseStart_435709 baseEnd_435709 := by
    simpa [prefixWord, tailWord_435709, baseEnd_435709] using wordTrace_append hprefix tailTrace_435709
  have hstable : (prefixWord ++ tailWord_435709).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_435709).length < 2 ^ (prefixWord ++ tailWord_435709).sum := by decide
  have hdescent : baseEnd_435709 < baseStart_435709 := by decide
  rcases family_descends (prefixWord ++ tailWord_435709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_435719 : List Nat := [1, 1, 4, 3, 2, 2, 2, 2, 2, 4]
def baseStart_435719 : Nat := 118140960795 + 435719 * 2 ^ 59
def prefixEnd_435719 : Nat := 4983230072969 + 3 ^ 40 * 435719 * 2
def baseEnd_435719 : Nat := 74577759098828660369557

theorem tailTrace_435719 : CollatzResearch.WordTrace tailWord_435719 prefixEnd_435719 74577759098828660369557 := by
  unfold tailWord_435719
  simp only [CollatzResearch.WordTrace]
  refine ⟨15891977508471952725838211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10594651672314635150558807 15891977508471952725838211)
  ·
    refine ⟨23837966262707929088757317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15891977508471952725838211 23837966262707929088757317)
    ·
      refine ⟨4469618674257736704141997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 23837966262707929088757317 4469618674257736704141997)
      ·
        refine ⟨1676107002846651264053249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4469618674257736704141997 1676107002846651264053249)
        ·
          refine ⟨1257080252134988448039937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1676107002846651264053249 1257080252134988448039937)
          ·
            refine ⟨942810189101241336029953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1257080252134988448039937 942810189101241336029953)
            ·
              refine ⟨707107641825931002022465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 942810189101241336029953 707107641825931002022465)
              ·
                refine ⟨530330731369448251516849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 707107641825931002022465 530330731369448251516849)
                ·
                  refine ⟨397748048527086188637637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 530330731369448251516849 397748048527086188637637)
                  ·
                    refine ⟨74577759098828660369557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 397748048527086188637637 74577759098828660369557)
                    ·
                      rfl

theorem cell23_435719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 2, 2, 2, 2, 4].length) (baseStart_435719 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_435719 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_435719 prefixEnd_435719 := by exact prefixLift 435719
  have htrace : WordTrace (prefixWord ++ tailWord_435719) baseStart_435719 baseEnd_435719 := by
    simpa [prefixWord, tailWord_435719, baseEnd_435719] using wordTrace_append hprefix tailTrace_435719
  have hstable : (prefixWord ++ tailWord_435719).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_435719).length < 2 ^ (prefixWord ++ tailWord_435719).sum := by decide
  have hdescent : baseEnd_435719 < baseStart_435719 := by decide
  rcases family_descends (prefixWord ++ tailWord_435719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_435775 : List Nat := [1, 1, 2, 2, 3, 3, 1, 2, 2, 6]
def baseStart_435775 : Nat := 118140960795 + 435775 * 2 ^ 59
def prefixEnd_435775 : Nat := 4983230072969 + 3 ^ 40 * 435775 * 2
def baseEnd_435775 : Nat := 74587344071045920669471

theorem tailTrace_435775 : CollatzResearch.WordTrace tailWord_435775 prefixEnd_435775 74587344071045920669471 := by
  unfold tailWord_435775
  simp only [CollatzResearch.WordTrace]
  refine ⟨15894019996269074289876779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10596013330846049526584519 15894019996269074289876779)
  ·
    refine ⟨23841029994403611434815169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15894019996269074289876779 23841029994403611434815169)
    ·
      refine ⟨17880772495802708576111377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23841029994403611434815169 17880772495802708576111377)
      ·
        refine ⟨13410579371852031432083533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17880772495802708576111377 13410579371852031432083533)
        ·
          refine ⟨5028967264444511787031325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13410579371852031432083533 5028967264444511787031325)
          ·
            refine ⟨1885862724166691920136747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5028967264444511787031325 1885862724166691920136747)
            ·
              refine ⟨2828794086250037880205121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1885862724166691920136747 2828794086250037880205121)
              ·
                refine ⟨2121595564687528410153841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2828794086250037880205121 2121595564687528410153841)
                ·
                  refine ⟨1591196673515646307615381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2121595564687528410153841 1591196673515646307615381)
                  ·
                    refine ⟨74587344071045920669471, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1591196673515646307615381 74587344071045920669471)
                    ·
                      rfl

theorem cell23_435775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 3, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 3, 1, 2, 2, 6].length) (baseStart_435775 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_435775 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_435775 prefixEnd_435775 := by exact prefixLift 435775
  have htrace : WordTrace (prefixWord ++ tailWord_435775) baseStart_435775 baseEnd_435775 := by
    simpa [prefixWord, tailWord_435775, baseEnd_435775] using wordTrace_append hprefix tailTrace_435775
  have hstable : (prefixWord ++ tailWord_435775).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_435775).length < 2 ^ (prefixWord ++ tailWord_435775).sum := by decide
  have hdescent : baseEnd_435775 < baseStart_435775 := by decide
  rcases family_descends (prefixWord ++ tailWord_435775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_435785 : List Nat := [1, 2, 1, 1, 2, 2, 1, 3, 1, 6, 3]
def baseStart_435785 : Nat := 118140960795 + 435785 * 2 ^ 59
def prefixEnd_435785 : Nat := 4983230072969 + 3 ^ 40 * 435785 * 2
def baseEnd_435785 : Nat := 223767167019682722883367

theorem tailTrace_435785 : CollatzResearch.WordTrace tailWord_435785 prefixEnd_435785 223767167019682722883367 := by
  unfold tailWord_435785
  simp only [CollatzResearch.WordTrace]
  refine ⟨15894384726232845997740809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10596256484155230665160539 15894384726232845997740809)
  ·
    refine ⟨11920788544674634498305607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15894384726232845997740809 11920788544674634498305607)
    ·
      refine ⟨17881182817011951747458411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11920788544674634498305607 17881182817011951747458411)
      ·
        refine ⟨26821774225517927621187617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17881182817011951747458411 26821774225517927621187617)
        ·
          refine ⟨20116330669138445715890713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26821774225517927621187617 20116330669138445715890713)
          ·
            refine ⟨15087248001853834286918035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20116330669138445715890713 15087248001853834286918035)
            ·
              refine ⟨22630872002780751430377053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15087248001853834286918035 22630872002780751430377053)
              ·
                refine ⟨8486577001042781786391395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22630872002780751430377053 8486577001042781786391395)
                ·
                  refine ⟨12729865501564172679587093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8486577001042781786391395 12729865501564172679587093)
                  ·
                    refine ⟨596712445385820594355645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12729865501564172679587093 596712445385820594355645)
                    ·
                      refine ⟨223767167019682722883367, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 596712445385820594355645 223767167019682722883367)
                      ·
                        rfl

theorem cell23_435785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 1, 3, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 1, 3, 1, 6, 3].length) (baseStart_435785 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_435785 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_435785 prefixEnd_435785 := by exact prefixLift 435785
  have htrace : WordTrace (prefixWord ++ tailWord_435785) baseStart_435785 baseEnd_435785 := by
    simpa [prefixWord, tailWord_435785, baseEnd_435785] using wordTrace_append hprefix tailTrace_435785
  have hstable : (prefixWord ++ tailWord_435785).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_435785).length < 2 ^ (prefixWord ++ tailWord_435785).sum := by decide
  have hdescent : baseEnd_435785 < baseStart_435785 := by decide
  rcases family_descends (prefixWord ++ tailWord_435785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_435799 : List Nat := [1, 1, 3, 2, 2, 3, 3, 1, 1, 4, 2]
def baseStart_435799 : Nat := 118140960795 + 435799 * 2 ^ 59
def prefixEnd_435799 : Nat := 4983230072969 + 3 ^ 40 * 435799 * 2
def baseEnd_435799 : Nat := 223774355748845668108303

theorem tailTrace_435799 : CollatzResearch.WordTrace tailWord_435799 prefixEnd_435799 223774355748845668108303 := by
  unfold tailWord_435799
  simp only [CollatzResearch.WordTrace]
  refine ⟨15894895348182126388750451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10596596898788084259166967 15894895348182126388750451)
  ·
    refine ⟨23842343022273189583125677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15894895348182126388750451 23842343022273189583125677)
    ·
      refine ⟨8940878633352446093672129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23842343022273189583125677 8940878633352446093672129)
      ·
        refine ⟨6705658975014334570254097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8940878633352446093672129 6705658975014334570254097)
        ·
          refine ⟨5029244231260750927690573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6705658975014334570254097 5029244231260750927690573)
          ·
            refine ⟨1885966586722781597883965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5029244231260750927690573 1885966586722781597883965)
            ·
              refine ⟨707237470021043099206487, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1885966586722781597883965 707237470021043099206487)
              ·
                refine ⟨1060856205031564648809731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 707237470021043099206487 1060856205031564648809731)
                ·
                  refine ⟨1591284307547346973214597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1060856205031564648809731 1591284307547346973214597)
                  ·
                    refine ⟨298365807665127557477737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1591284307547346973214597 298365807665127557477737)
                    ·
                      refine ⟨223774355748845668108303, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 298365807665127557477737 223774355748845668108303)
                      ·
                        rfl

theorem cell23_435799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 3, 3, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 3, 3, 1, 1, 4, 2].length) (baseStart_435799 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_435799 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_435799 prefixEnd_435799 := by exact prefixLift 435799
  have htrace : WordTrace (prefixWord ++ tailWord_435799) baseStart_435799 baseEnd_435799 := by
    simpa [prefixWord, tailWord_435799, baseEnd_435799] using wordTrace_append hprefix tailTrace_435799
  have hstable : (prefixWord ++ tailWord_435799).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_435799).length < 2 ^ (prefixWord ++ tailWord_435799).sum := by decide
  have hdescent : baseEnd_435799 < baseStart_435799 := by decide
  rcases family_descends (prefixWord ++ tailWord_435799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_435816 : List Nat := [2, 1, 4, 3, 1, 1, 1, 2, 4, 2, 2]
def baseStart_435816 : Nat := 118140960795 + 435816 * 2 ^ 59
def prefixEnd_435816 : Nat := 4983230072969 + 3 ^ 40 * 435816 * 2
def baseEnd_435816 : Nat := 223783084919972101595725

theorem tailTrace_435816 : CollatzResearch.WordTrace tailWord_435816 prefixEnd_435816 223783084919972101595725 := by
  unfold tailWord_435816
  simp only [CollatzResearch.WordTrace]
  refine ⟨7947757694560269146059651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10597010259413692194746201 7947757694560269146059651)
  ·
    refine ⟨11921636541840403719089477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7947757694560269146059651 11921636541840403719089477)
    ·
      refine ⟨2235306851595075697329277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 11921636541840403719089477 2235306851595075697329277)
      ·
        refine ⟨838240069348153386498479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2235306851595075697329277 838240069348153386498479)
        ·
          refine ⟨1257360104022230079747719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 838240069348153386498479 1257360104022230079747719)
          ·
            refine ⟨1886040156033345119621579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1257360104022230079747719 1886040156033345119621579)
            ·
              refine ⟨2829060234050017679432369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1886040156033345119621579 2829060234050017679432369)
              ·
                refine ⟨2121795175537513259574277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2829060234050017679432369 2121795175537513259574277)
                ·
                  refine ⟨397836595413283736170177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2121795175537513259574277 397836595413283736170177)
                  ·
                    refine ⟨298377446559962802127633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 397836595413283736170177 298377446559962802127633)
                    ·
                      refine ⟨223783084919972101595725, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 298377446559962802127633 223783084919972101595725)
                      ·
                        rfl

theorem cell23_435816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 1, 1, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 1, 1, 2, 4, 2, 2].length) (baseStart_435816 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_435816 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_435816 prefixEnd_435816 := by exact prefixLift 435816
  have htrace : WordTrace (prefixWord ++ tailWord_435816) baseStart_435816 baseEnd_435816 := by
    simpa [prefixWord, tailWord_435816, baseEnd_435816] using wordTrace_append hprefix tailTrace_435816
  have hstable : (prefixWord ++ tailWord_435816).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_435816).length < 2 ^ (prefixWord ++ tailWord_435816).sum := by decide
  have hdescent : baseEnd_435816 < baseStart_435816 := by decide
  rcases family_descends (prefixWord ++ tailWord_435816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_435850 : List Nat := [3, 1, 2, 3, 2, 3, 2, 1, 2, 2, 2]
def baseStart_435850 : Nat := 118140960795 + 435850 * 2 ^ 59
def prefixEnd_435850 : Nat := 4983230072969 + 3 ^ 40 * 435850 * 2
def baseEnd_435850 : Nat := 223800543262224968570569

theorem tailTrace_435850 : CollatzResearch.WordTrace tailWord_435850 prefixEnd_435850 223800543262224968570569 := by
  unfold tailWord_435850
  simp only [CollatzResearch.WordTrace]
  refine ⟨3974188867749340524714251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10597836980664908065904669 3974188867749340524714251)
  ·
    refine ⟨5961283301624010787071377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3974188867749340524714251 5961283301624010787071377)
    ·
      refine ⟨4470962476218008090303533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5961283301624010787071377 4470962476218008090303533)
      ·
        refine ⟨1676610928581753033863825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4470962476218008090303533 1676610928581753033863825)
        ·
          refine ⟨1257458196436314775397869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1676610928581753033863825 1257458196436314775397869)
          ·
            refine ⟨471546823663618040774201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1257458196436314775397869 471546823663618040774201)
            ·
              refine ⟨353660117747713530580651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 471546823663618040774201 353660117747713530580651)
              ·
                refine ⟨530490176621570295870977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 353660117747713530580651 530490176621570295870977)
                ·
                  refine ⟨397867632466177721903233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 530490176621570295870977 397867632466177721903233)
                  ·
                    refine ⟨298400724349633291427425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 397867632466177721903233 298400724349633291427425)
                    ·
                      refine ⟨223800543262224968570569, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 298400724349633291427425 223800543262224968570569)
                      ·
                        rfl

theorem cell23_435850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 3, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 3, 2, 1, 2, 2, 2].length) (baseStart_435850 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_435850 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_435850 prefixEnd_435850 := by exact prefixLift 435850
  have htrace : WordTrace (prefixWord ++ tailWord_435850) baseStart_435850 baseEnd_435850 := by
    simpa [prefixWord, tailWord_435850, baseEnd_435850] using wordTrace_append hprefix tailTrace_435850
  have hstable : (prefixWord ++ tailWord_435850).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_435850).length < 2 ^ (prefixWord ++ tailWord_435850).sum := by decide
  have hdescent : baseEnd_435850 < baseStart_435850 := by decide
  rcases family_descends (prefixWord ++ tailWord_435850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_435912 : List Nat := [2, 1, 3, 1, 2, 2, 1, 5, 6]
def baseStart_435912 : Nat := 118140960795 + 435912 * 2 ^ 59
def prefixEnd_435912 : Nat := 4983230072969 + 3 ^ 40 * 435912 * 2
def baseEnd_435912 : Nat := 24870264340311525110587

theorem tailTrace_435912 : CollatzResearch.WordTrace tailWord_435912 prefixEnd_435912 24870264340311525110587 := by
  unfold tailWord_435912
  simp only [CollatzResearch.WordTrace]
  refine ⟨7949508398386373343806995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10599344531181831125075993 7949508398386373343806995)
  ·
    refine ⟨11924262597579560015710493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7949508398386373343806995 11924262597579560015710493)
    ·
      refine ⟨4471598474092335005891435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11924262597579560015710493 4471598474092335005891435)
      ·
        refine ⟨6707397711138502508837153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4471598474092335005891435 6707397711138502508837153)
        ·
          refine ⟨5030548283353876881627865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6707397711138502508837153 5030548283353876881627865)
          ·
            refine ⟨3772911212515407661220899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5030548283353876881627865 3772911212515407661220899)
            ·
              refine ⟨5659366818773111491831349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3772911212515407661220899 5659366818773111491831349)
              ·
                refine ⟨530565639259979202359189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 5659366818773111491831349 530565639259979202359189)
                ·
                  refine ⟨24870264340311525110587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 530565639259979202359189 24870264340311525110587)
                  ·
                    rfl

theorem cell23_435912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 1, 5, 6].length) (baseStart_435912 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_435912 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_435912 prefixEnd_435912 := by exact prefixLift 435912
  have htrace : WordTrace (prefixWord ++ tailWord_435912) baseStart_435912 baseEnd_435912 := by
    simpa [prefixWord, tailWord_435912, baseEnd_435912] using wordTrace_append hprefix tailTrace_435912
  have hstable : (prefixWord ++ tailWord_435912).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_435912).length < 2 ^ (prefixWord ++ tailWord_435912).sum := by decide
  have hdescent : baseEnd_435912 < baseStart_435912 := by decide
  rcases family_descends (prefixWord ++ tailWord_435912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_435916 : List Nat := [2, 2, 1, 5, 2, 1, 1, 2, 3, 4]
def baseStart_435916 : Nat := 118140960795 + 435916 * 2 ^ 59
def prefixEnd_435916 : Nat := 4983230072969 + 3 ^ 40 * 435916 * 2
def baseEnd_435916 : Nat := 74611477661807236781755

theorem tailTrace_435916 : CollatzResearch.WordTrace tailWord_435916 prefixEnd_435916 74611477661807236781755 := by
  unfold tailWord_435916
  simp only [CollatzResearch.WordTrace]
  refine ⟨7949581344379127685379801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10599441792505503580506401 7949581344379127685379801)
  ·
    refine ⟨5962186008284345764034851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7949581344379127685379801 5962186008284345764034851)
    ·
      refine ⟨8943279012426518646052277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5962186008284345764034851 8943279012426518646052277)
      ·
        refine ⟨838432407414986123067401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 8943279012426518646052277 838432407414986123067401)
        ·
          refine ⟨628824305561239592300551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 838432407414986123067401 628824305561239592300551)
          ·
            refine ⟨943236458341859388450827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 628824305561239592300551 943236458341859388450827)
            ·
              refine ⟨1414854687512789082676241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 943236458341859388450827 1414854687512789082676241)
              ·
                refine ⟨1061141015634591812007181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1414854687512789082676241 1061141015634591812007181)
                ·
                  refine ⟨397927880862971929502693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1061141015634591812007181 397927880862971929502693)
                  ·
                    refine ⟨74611477661807236781755, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 397927880862971929502693 74611477661807236781755)
                    ·
                      rfl

theorem cell23_435916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 2, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 2, 1, 1, 2, 3, 4].length) (baseStart_435916 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_435916 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_435916 prefixEnd_435916 := by exact prefixLift 435916
  have htrace : WordTrace (prefixWord ++ tailWord_435916) baseStart_435916 baseEnd_435916 := by
    simpa [prefixWord, tailWord_435916, baseEnd_435916] using wordTrace_append hprefix tailTrace_435916
  have hstable : (prefixWord ++ tailWord_435916).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_435916).length < 2 ^ (prefixWord ++ tailWord_435916).sum := by decide
  have hdescent : baseEnd_435916 < baseStart_435916 := by decide
  rcases family_descends (prefixWord ++ tailWord_435916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_435979 : List Nat := [1, 1, 1, 1, 5, 1, 3, 4, 1, 1, 4]
def baseStart_435979 : Nat := 118140960795 + 435979 * 2 ^ 59
def prefixEnd_435979 : Nat := 4983230072969 + 3 ^ 40 * 435979 * 2
def baseEnd_435979 : Nat := 223866782266654963857475

theorem tailTrace_435979 : CollatzResearch.WordTrace tailWord_435979 prefixEnd_435979 223866782266654963857475 := by
  unfold tailWord_435979
  simp only [CollatzResearch.WordTrace]
  refine ⟨15901460487530017130302991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10600973658353344753535327 15901460487530017130302991)
  ·
    refine ⟨23852190731295025695454487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15901460487530017130302991 23852190731295025695454487)
    ·
      refine ⟨35778286096942538543181731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23852190731295025695454487 35778286096942538543181731)
      ·
        refine ⟨53667429145413807814772597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35778286096942538543181731 53667429145413807814772597)
        ·
          refine ⟨5031321482382544482634931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 53667429145413807814772597 5031321482382544482634931)
          ·
            refine ⟨7546982223573816723952397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5031321482382544482634931 7546982223573816723952397)
            ·
              refine ⟨2830118333840181271482149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7546982223573816723952397 2830118333840181271482149)
              ·
                refine ⟨530647187595033988402903, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2830118333840181271482149 530647187595033988402903)
                ·
                  refine ⟨795970781392550982604355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 530647187595033988402903 795970781392550982604355)
                  ·
                    refine ⟨1193956172088826473906533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 795970781392550982604355 1193956172088826473906533)
                    ·
                      refine ⟨223866782266654963857475, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1193956172088826473906533 223866782266654963857475)
                      ·
                        rfl

theorem cell23_435979_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 3, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 3, 4, 1, 1, 4].length) (baseStart_435979 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_435979 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_435979 prefixEnd_435979 := by exact prefixLift 435979
  have htrace : WordTrace (prefixWord ++ tailWord_435979) baseStart_435979 baseEnd_435979 := by
    simpa [prefixWord, tailWord_435979, baseEnd_435979] using wordTrace_append hprefix tailTrace_435979
  have hstable : (prefixWord ++ tailWord_435979).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_435979).length < 2 ^ (prefixWord ++ tailWord_435979).sum := by decide
  have hdescent : baseEnd_435979 < baseStart_435979 := by decide
  rcases family_descends (prefixWord ++ tailWord_435979) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_435989 : List Nat := [1, 3, 2, 1, 2, 3, 1, 2, 4, 4]
def baseStart_435989 : Nat := 118140960795 + 435989 * 2 ^ 59
def prefixEnd_435989 : Nat := 4983230072969 + 3 ^ 40 * 435989 * 2
def baseEnd_435989 : Nat := 74623972357733308244143

theorem tailTrace_435989 : CollatzResearch.WordTrace tailWord_435989 prefixEnd_435989 74623972357733308244143 := by
  unfold tailWord_435989
  simp only [CollatzResearch.WordTrace]
  refine ⟨15901825217493788838167021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10601216811662525892111347 15901825217493788838167021)
  ·
    refine ⟨5963184456560170814312633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15901825217493788838167021 5963184456560170814312633)
    ·
      refine ⟨4472388342420128110734475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5963184456560170814312633 4472388342420128110734475)
      ·
        refine ⟨6708582513630192166101713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4472388342420128110734475 6708582513630192166101713)
        ·
          refine ⟨5031436885222644124576285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6708582513630192166101713 5031436885222644124576285)
          ·
            refine ⟨1886788831958491546716107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5031436885222644124576285 1886788831958491546716107)
            ·
              refine ⟨2830183247937737320074161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1886788831958491546716107 2830183247937737320074161)
              ·
                refine ⟨2122637435953302990055621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2830183247937737320074161 2122637435953302990055621)
                ·
                  refine ⟨397994519241244310635429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2122637435953302990055621 397994519241244310635429)
                  ·
                    refine ⟨74623972357733308244143, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 397994519241244310635429 74623972357733308244143)
                    ·
                      rfl

theorem cell23_435989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 3, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 3, 1, 2, 4, 4].length) (baseStart_435989 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_435989 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_435989 prefixEnd_435989 := by exact prefixLift 435989
  have htrace : WordTrace (prefixWord ++ tailWord_435989) baseStart_435989 baseEnd_435989 := by
    simpa [prefixWord, tailWord_435989, baseEnd_435989] using wordTrace_append hprefix tailTrace_435989
  have hstable : (prefixWord ++ tailWord_435989).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_435989).length < 2 ^ (prefixWord ++ tailWord_435989).sum := by decide
  have hdescent : baseEnd_435989 < baseStart_435989 := by decide
  rcases family_descends (prefixWord ++ tailWord_435989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_435999 : List Nat := [1, 1, 2, 4, 2, 1, 4, 1, 1, 1, 5]
def baseStart_435999 : Nat := 118140960795 + 435999 * 2 ^ 59
def prefixEnd_435999 : Nat := 4983230072969 + 3 ^ 40 * 435999 * 2
def baseEnd_435999 : Nat := 223877051879744885607383

theorem tailTrace_435999 : CollatzResearch.WordTrace tailWord_435999 prefixEnd_435999 223877051879744885607383 := by
  unfold tailWord_435999
  simp only [CollatzResearch.WordTrace]
  refine ⟨15902189947457560546031051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10601459964971707030687367 15902189947457560546031051)
  ·
    refine ⟨23853284921186340819046577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15902189947457560546031051 23853284921186340819046577)
    ·
      refine ⟨17889963690889755614284933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23853284921186340819046577 17889963690889755614284933)
      ·
        refine ⟨3354368192041829177678425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 17889963690889755614284933 3354368192041829177678425)
        ·
          refine ⟨2515776144031371883258819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3354368192041829177678425 2515776144031371883258819)
          ·
            refine ⟨3773664216047057824888229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2515776144031371883258819 3773664216047057824888229)
            ·
              refine ⟨707562040508823342166543, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3773664216047057824888229 707562040508823342166543)
              ·
                refine ⟨1061343060763235013249815, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 707562040508823342166543 1061343060763235013249815)
                ·
                  refine ⟨1592014591144852519874723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1061343060763235013249815 1592014591144852519874723)
                  ·
                    refine ⟨2388021886717278779812085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1592014591144852519874723 2388021886717278779812085)
                    ·
                      refine ⟨223877051879744885607383, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 2388021886717278779812085 223877051879744885607383)
                      ·
                        rfl

theorem cell23_435999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 4, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 4, 1, 1, 1, 5].length) (baseStart_435999 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_435999 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_435999 prefixEnd_435999 := by exact prefixLift 435999
  have htrace : WordTrace (prefixWord ++ tailWord_435999) baseStart_435999 baseEnd_435999 := by
    simpa [prefixWord, tailWord_435999, baseEnd_435999] using wordTrace_append hprefix tailTrace_435999
  have hstable : (prefixWord ++ tailWord_435999).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_435999).length < 2 ^ (prefixWord ++ tailWord_435999).sum := by decide
  have hdescent : baseEnd_435999 < baseStart_435999 := by decide
  rcases family_descends (prefixWord ++ tailWord_435999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_436019 : List Nat := [1, 1, 1, 2, 7, 1, 2, 8]
def baseStart_436019 : Nat := 118140960795 + 436019 * 2 ^ 59
def prefixEnd_436019 : Nat := 4983230072969 + 3 ^ 40 * 436019 * 2
def baseEnd_436019 : Nat := 8292123018253141013233

theorem tailTrace_436019 : CollatzResearch.WordTrace tailWord_436019 prefixEnd_436019 8292123018253141013233 := by
  unfold tailWord_436019
  simp only [CollatzResearch.WordTrace]
  refine ⟨15902919407385103961759111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10601946271590069307839407 15902919407385103961759111)
  ·
    refine ⟨23854379111077655942638667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15902919407385103961759111 23854379111077655942638667)
    ·
      refine ⟨35781568666616483913958001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23854379111077655942638667 35781568666616483913958001)
      ·
        refine ⟨26836176499962362935468501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35781568666616483913958001 26836176499962362935468501)
        ·
          refine ⟨628972886717867881300043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 26836176499962362935468501 628972886717867881300043)
          ·
            refine ⟨943459330076801821950065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 628972886717867881300043 943459330076801821950065)
            ·
              refine ⟨707594497557601366462549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 943459330076801821950065 707594497557601366462549)
              ·
                refine ⟨8292123018253141013233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 707594497557601366462549 8292123018253141013233)
                ·
                  rfl

theorem cell23_436019_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 7, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 7, 1, 2, 8].length) (baseStart_436019 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_436019 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_436019 prefixEnd_436019 := by exact prefixLift 436019
  have htrace : WordTrace (prefixWord ++ tailWord_436019) baseStart_436019 baseEnd_436019 := by
    simpa [prefixWord, tailWord_436019, baseEnd_436019] using wordTrace_append hprefix tailTrace_436019
  have hstable : (prefixWord ++ tailWord_436019).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_436019).length < 2 ^ (prefixWord ++ tailWord_436019).sum := by decide
  have hdescent : baseEnd_436019 < baseStart_436019 := by decide
  rcases family_descends (prefixWord ++ tailWord_436019) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_436063 : List Nat := [1, 1, 2, 3, 1, 5, 2, 2, 2, 1, 3]
def baseStart_436063 : Nat := 118140960795 + 436063 * 2 ^ 59
def prefixEnd_436063 : Nat := 4983230072969 + 3 ^ 40 * 436063 * 2
def baseEnd_436063 : Nat := 223909914641632635207089

theorem tailTrace_436063 : CollatzResearch.WordTrace tailWord_436063 prefixEnd_436063 223909914641632635207089 := by
  unfold tailWord_436063
  simp only [CollatzResearch.WordTrace]
  refine ⟨15904524219225699476360843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10603016146150466317573895 15904524219225699476360843)
  ·
    refine ⟨23856786328838549214541265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15904524219225699476360843 23856786328838549214541265)
    ·
      refine ⟨17892589746628911910905949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23856786328838549214541265 17892589746628911910905949)
      ·
        refine ⟨6709721154985841966589731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17892589746628911910905949 6709721154985841966589731)
        ·
          refine ⟨10064581732478762949884597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6709721154985841966589731 10064581732478762949884597)
          ·
            refine ⟨943554537419884026551681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 10064581732478762949884597 943554537419884026551681)
            ·
              refine ⟨707665903064913019913761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 943554537419884026551681 707665903064913019913761)
              ·
                refine ⟨530749427298684764935321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 707665903064913019913761 530749427298684764935321)
                ·
                  refine ⟨398062070474013573701491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 530749427298684764935321 398062070474013573701491)
                  ·
                    refine ⟨597093105711020360552237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 398062070474013573701491 597093105711020360552237)
                    ·
                      refine ⟨223909914641632635207089, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 597093105711020360552237 223909914641632635207089)
                      ·
                        rfl

theorem cell23_436063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 5, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 5, 2, 2, 2, 1, 3].length) (baseStart_436063 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_436063 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_436063 prefixEnd_436063 := by exact prefixLift 436063
  have htrace : WordTrace (prefixWord ++ tailWord_436063) baseStart_436063 baseEnd_436063 := by
    simpa [prefixWord, tailWord_436063, baseEnd_436063] using wordTrace_append hprefix tailTrace_436063
  have hstable : (prefixWord ++ tailWord_436063).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_436063).length < 2 ^ (prefixWord ++ tailWord_436063).sum := by decide
  have hdescent : baseEnd_436063 < baseStart_436063 := by decide
  rcases family_descends (prefixWord ++ tailWord_436063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_436089 : List Nat := [1, 2, 1, 3, 2, 2, 1, 2, 2, 4, 3]
def baseStart_436089 : Nat := 118140960795 + 436089 * 2 ^ 59
def prefixEnd_436089 : Nat := 4983230072969 + 3 ^ 40 * 436089 * 2
def baseEnd_436089 : Nat := 223923265138649533481969

theorem tailTrace_436089 : CollatzResearch.WordTrace tailWord_436089 prefixEnd_436089 223923265138649533481969 := by
  unfold tailWord_436089
  simp only [CollatzResearch.WordTrace]
  refine ⟨15905472517131505916807321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10603648344754337277871547 15905472517131505916807321)
  ·
    refine ⟨11929104387848629437605491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15905472517131505916807321 11929104387848629437605491)
    ·
      refine ⟨17893656581772944156408237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11929104387848629437605491 17893656581772944156408237)
      ·
        refine ⟨6710121218164854058653089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17893656581772944156408237 6710121218164854058653089)
        ·
          refine ⟨5032590913623640543989817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6710121218164854058653089 5032590913623640543989817)
          ·
            refine ⟨3774443185217730407992363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5032590913623640543989817 3774443185217730407992363)
            ·
              refine ⟨5661664777826595611988545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3774443185217730407992363 5661664777826595611988545)
              ·
                refine ⟨4246248583369946708991409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5661664777826595611988545 4246248583369946708991409)
                ·
                  refine ⟨3184686437527460031743557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4246248583369946708991409 3184686437527460031743557)
                  ·
                    refine ⟨597128707036398755951917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3184686437527460031743557 597128707036398755951917)
                    ·
                      refine ⟨223923265138649533481969, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 597128707036398755951917 223923265138649533481969)
                      ·
                        rfl

theorem cell23_436089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 1, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 1, 2, 2, 4, 3].length) (baseStart_436089 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_436089 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_436089 prefixEnd_436089 := by exact prefixLift 436089
  have htrace : WordTrace (prefixWord ++ tailWord_436089) baseStart_436089 baseEnd_436089 := by
    simpa [prefixWord, tailWord_436089, baseEnd_436089] using wordTrace_append hprefix tailTrace_436089
  have hstable : (prefixWord ++ tailWord_436089).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_436089).length < 2 ^ (prefixWord ++ tailWord_436089).sum := by decide
  have hdescent : baseEnd_436089 < baseStart_436089 := by decide
  rcases family_descends (prefixWord ++ tailWord_436089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_436116 : List Nat := [2, 4, 2, 1, 1, 2, 1, 2, 2, 2, 4]
def baseStart_436116 : Nat := 118140960795 + 436116 * 2 ^ 59
def prefixEnd_436116 : Nat := 4983230072969 + 3 ^ 40 * 436116 * 2
def baseEnd_436116 : Nat := 223937129116320927844345

theorem tailTrace_436116 : CollatzResearch.WordTrace tailWord_436116 prefixEnd_436116 223937129116320927844345 := by
  unfold tailWord_436116
  simp only [CollatzResearch.WordTrace]
  refine ⟨7953228644016844764020101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10604304858689126352026801 7953228644016844764020101)
  ·
    refine ⟨1491230370753158393253769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 7953228644016844764020101 1491230370753158393253769)
    ·
      refine ⟨1118422778064868794940327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1491230370753158393253769 1118422778064868794940327)
      ·
        refine ⟨1677634167097303192410491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1118422778064868794940327 1677634167097303192410491)
        ·
          refine ⟨2516451250645954788615737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1677634167097303192410491 2516451250645954788615737)
          ·
            refine ⟨1887338437984466091461803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2516451250645954788615737 1887338437984466091461803)
            ·
              refine ⟨2831007656976699137192705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1887338437984466091461803 2831007656976699137192705)
              ·
                refine ⟨2123255742732524352894529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2831007656976699137192705 2123255742732524352894529)
                ·
                  refine ⟨1592441807049393264670897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2123255742732524352894529 1592441807049393264670897)
                  ·
                    refine ⟨1194331355287044948503173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1592441807049393264670897 1194331355287044948503173)
                    ·
                      refine ⟨223937129116320927844345, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1194331355287044948503173 223937129116320927844345)
                      ·
                        rfl

theorem cell23_436116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 2, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 2, 1, 2, 2, 2, 4].length) (baseStart_436116 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_436116 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_436116 prefixEnd_436116 := by exact prefixLift 436116
  have htrace : WordTrace (prefixWord ++ tailWord_436116) baseStart_436116 baseEnd_436116 := by
    simpa [prefixWord, tailWord_436116, baseEnd_436116] using wordTrace_append hprefix tailTrace_436116
  have hstable : (prefixWord ++ tailWord_436116).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_436116).length < 2 ^ (prefixWord ++ tailWord_436116).sum := by decide
  have hdescent : baseEnd_436116 < baseStart_436116 := by decide
  rcases family_descends (prefixWord ++ tailWord_436116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_436146 : List Nat := [3, 2, 1, 1, 1, 1, 1, 4, 2, 5, 2]
def baseStart_436146 : Nat := 118140960795 + 436146 * 2 ^ 59
def prefixEnd_436146 : Nat := 4983230072969 + 3 ^ 40 * 436146 * 2
def baseEnd_436146 : Nat := 223952533535955810469207

theorem tailTrace_436146 : CollatzResearch.WordTrace tailWord_436146 prefixEnd_436146 223952533535955810469207 := by
  unfold tailWord_436146
  simp only [CollatzResearch.WordTrace]
  refine ⟨3976887869481251162908073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10605034318616669767754861 3976887869481251162908073)
  ·
    refine ⟨2982665902110938372181055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3976887869481251162908073 2982665902110938372181055)
    ·
      refine ⟨4473998853166407558271583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2982665902110938372181055 4473998853166407558271583)
      ·
        refine ⟨6710998279749611337407375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4473998853166407558271583 6710998279749611337407375)
        ·
          refine ⟨10066497419624417006111063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6710998279749611337407375 10066497419624417006111063)
          ·
            refine ⟨15099746129436625509166595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10066497419624417006111063 15099746129436625509166595)
            ·
              refine ⟨22649619194154938263749893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15099746129436625509166595 22649619194154938263749893)
              ·
                refine ⟨4246803598904050924453105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22649619194154938263749893 4246803598904050924453105)
                ·
                  refine ⟨3185102699178038193339829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4246803598904050924453105 3185102699178038193339829)
                  ·
                    refine ⟨298603378047941080625609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3185102699178038193339829 298603378047941080625609)
                    ·
                      refine ⟨223952533535955810469207, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 298603378047941080625609 223952533535955810469207)
                      ·
                        rfl

theorem cell23_436146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 1, 4, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 1, 4, 2, 5, 2].length) (baseStart_436146 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_436146 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_436146 prefixEnd_436146 := by exact prefixLift 436146
  have htrace : WordTrace (prefixWord ++ tailWord_436146) baseStart_436146 baseEnd_436146 := by
    simpa [prefixWord, tailWord_436146, baseEnd_436146] using wordTrace_append hprefix tailTrace_436146
  have hstable : (prefixWord ++ tailWord_436146).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_436146).length < 2 ^ (prefixWord ++ tailWord_436146).sum := by decide
  have hdescent : baseEnd_436146 < baseStart_436146 := by decide
  rcases family_descends (prefixWord ++ tailWord_436146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_436159 : List Nat := [1, 1, 2, 2, 2, 1, 3, 3, 1, 3, 4]
def baseStart_436159 : Nat := 118140960795 + 436159 * 2 ^ 59
def prefixEnd_436159 : Nat := 4983230072969 + 3 ^ 40 * 436159 * 2
def baseEnd_436159 : Nat := 223959208784464259606647

theorem tailTrace_436159 : CollatzResearch.WordTrace tailWord_436159 prefixEnd_436159 223959208784464259606647 := by
  unfold tailWord_436159
  simp only [CollatzResearch.WordTrace]
  refine ⟨15908025626877907871855531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10605350417918605247903687 15908025626877907871855531)
  ·
    refine ⟨23862038440316861807783297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15908025626877907871855531 23862038440316861807783297)
    ·
      refine ⟨17896528830237646355837473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23862038440316861807783297 17896528830237646355837473)
      ·
        refine ⟨13422396622678234766878105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17896528830237646355837473 13422396622678234766878105)
        ·
          refine ⟨10066797467008676075158579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13422396622678234766878105 10066797467008676075158579)
          ·
            refine ⟨15100196200513014112737869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10066797467008676075158579 15100196200513014112737869)
            ·
              refine ⟨5662573575192380292276701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15100196200513014112737869 5662573575192380292276701)
              ·
                refine ⟨2123465090697142609603763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5662573575192380292276701 2123465090697142609603763)
                ·
                  refine ⟨3185197636045713914405645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2123465090697142609603763 3185197636045713914405645)
                  ·
                    refine ⟨1194449113517142717902117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3185197636045713914405645 1194449113517142717902117)
                    ·
                      refine ⟨223959208784464259606647, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1194449113517142717902117 223959208784464259606647)
                      ·
                        rfl

theorem cell23_436159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 3, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 3, 3, 1, 3, 4].length) (baseStart_436159 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_436159 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_436159 prefixEnd_436159 := by exact prefixLift 436159
  have htrace : WordTrace (prefixWord ++ tailWord_436159) baseStart_436159 baseEnd_436159 := by
    simpa [prefixWord, tailWord_436159, baseEnd_436159] using wordTrace_append hprefix tailTrace_436159
  have hstable : (prefixWord ++ tailWord_436159).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_436159).length < 2 ^ (prefixWord ++ tailWord_436159).sum := by decide
  have hdescent : baseEnd_436159 < baseStart_436159 := by decide
  rcases family_descends (prefixWord ++ tailWord_436159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_436176 : List Nat := [2, 1, 1, 1, 1, 2, 4, 1, 4, 4, 2]
def baseStart_436176 : Nat := 118140960795 + 436176 * 2 ^ 59
def prefixEnd_436176 : Nat := 4983230072969 + 3 ^ 40 * 436176 * 2
def baseEnd_436176 : Nat := 223967937955590693094069

theorem tailTrace_436176 : CollatzResearch.WordTrace tailWord_436176 prefixEnd_436176 223967937955590693094069 := by
  unfold tailWord_436176
  simp only [CollatzResearch.WordTrace]
  refine ⟨7954322833908159887612191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10605763778544213183482921 7954322833908159887612191)
  ·
    refine ⟨11931484250862239831418287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7954322833908159887612191 11931484250862239831418287)
    ·
      refine ⟨17897226376293359747127431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11931484250862239831418287 17897226376293359747127431)
      ·
        refine ⟨26845839564440039620691147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17897226376293359747127431 26845839564440039620691147)
        ·
          refine ⟨40268759346660059431036721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26845839564440039620691147 40268759346660059431036721)
          ·
            refine ⟨30201569509995044573277541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40268759346660059431036721 30201569509995044573277541)
            ·
              refine ⟨5662794283124070857489539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 30201569509995044573277541 5662794283124070857489539)
              ·
                refine ⟨8494191424686106286234309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5662794283124070857489539 8494191424686106286234309)
                ·
                  refine ⟨1592660892128644928668933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8494191424686106286234309 1592660892128644928668933)
                  ·
                    refine ⟨298623917274120924125425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1592660892128644928668933 298623917274120924125425)
                    ·
                      refine ⟨223967937955590693094069, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 298623917274120924125425 223967937955590693094069)
                      ·
                        rfl

theorem cell23_436176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 4, 1, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 4, 1, 4, 4, 2].length) (baseStart_436176 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_436176 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_436176 prefixEnd_436176 := by exact prefixLift 436176
  have htrace : WordTrace (prefixWord ++ tailWord_436176) baseStart_436176 baseEnd_436176 := by
    simpa [prefixWord, tailWord_436176, baseEnd_436176] using wordTrace_append hprefix tailTrace_436176
  have hstable : (prefixWord ++ tailWord_436176).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_436176).length < 2 ^ (prefixWord ++ tailWord_436176).sum := by decide
  have hdescent : baseEnd_436176 < baseStart_436176 := by decide
  rcases family_descends (prefixWord ++ tailWord_436176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_436179 : List Nat := [1, 1, 1, 2, 1, 1, 1, 1, 1, 10, 3]
def baseStart_436179 : Nat := 118140960795 + 436179 * 2 ^ 59
def prefixEnd_436179 : Nat := 4983230072969 + 3 ^ 40 * 436179 * 2
def baseEnd_436179 : Nat := 223969478397554181356555

theorem tailTrace_436179 : CollatzResearch.WordTrace tailWord_436179 prefixEnd_436179 223969478397554181356555 := by
  unfold tailWord_436179
  simp only [CollatzResearch.WordTrace]
  refine ⟨15908755086805451287583591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10605836724536967525055727 15908755086805451287583591)
  ·
    refine ⟨23863132630208176931375387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15908755086805451287583591 23863132630208176931375387)
    ·
      refine ⟨35794698945312265397063081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23863132630208176931375387 35794698945312265397063081)
      ·
        refine ⟨26846024208984199047797311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35794698945312265397063081 26846024208984199047797311)
        ·
          refine ⟨40269036313476298571695967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26846024208984199047797311 40269036313476298571695967)
          ·
            refine ⟨60403554470214447857543951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40269036313476298571695967 60403554470214447857543951)
            ·
              refine ⟨90605331705321671786315927, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60403554470214447857543951 90605331705321671786315927)
              ·
                refine ⟨135907997557982507679473891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 90605331705321671786315927 135907997557982507679473891)
                ·
                  refine ⟨203861996336973761519210837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 135907997557982507679473891 203861996336973761519210837)
                  ·
                    refine ⟨597251942393477816950813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 203861996336973761519210837 597251942393477816950813)
                    ·
                      refine ⟨223969478397554181356555, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 597251942393477816950813 223969478397554181356555)
                      ·
                        rfl

theorem cell23_436179_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 10, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 10, 3].length) (baseStart_436179 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_436179 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_436179 prefixEnd_436179 := by exact prefixLift 436179
  have htrace : WordTrace (prefixWord ++ tailWord_436179) baseStart_436179 baseEnd_436179 := by
    simpa [prefixWord, tailWord_436179, baseEnd_436179] using wordTrace_append hprefix tailTrace_436179
  have hstable : (prefixWord ++ tailWord_436179).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_436179).length < 2 ^ (prefixWord ++ tailWord_436179).sum := by decide
  have hdescent : baseEnd_436179 < baseStart_436179 := by decide
  rcases family_descends (prefixWord ++ tailWord_436179) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_436188 : List Nat := [2, 2, 6, 1, 1, 2, 2, 1, 2, 2, 2]
def baseStart_436188 : Nat := 118140960795 + 436188 * 2 ^ 59
def prefixEnd_436188 : Nat := 4983230072969 + 3 ^ 40 * 436188 * 2
def baseEnd_436188 : Nat := 223974099723444646144015

theorem tailTrace_436188 : CollatzResearch.WordTrace tailWord_436188 prefixEnd_436188 223974099723444646144015 := by
  unfold tailWord_436188
  simp only [CollatzResearch.WordTrace]
  refine ⟨7954541671886422912330609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10606055562515230549774145 7954541671886422912330609)
  ·
    refine ⟨5965906253914817184247957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7954541671886422912330609 5965906253914817184247957)
    ·
      refine ⟨279651855652257055511623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 5965906253914817184247957 279651855652257055511623)
      ·
        refine ⟨419477783478385583267435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 279651855652257055511623 419477783478385583267435)
        ·
          refine ⟨629216675217578374901153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 419477783478385583267435 629216675217578374901153)
          ·
            refine ⟨471912506413183781175865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 629216675217578374901153 471912506413183781175865)
            ·
              refine ⟨353934379809887835881899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 471912506413183781175865 353934379809887835881899)
              ·
                refine ⟨530901569714831753822849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 353934379809887835881899 530901569714831753822849)
                ·
                  refine ⟨398176177286123815367137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 530901569714831753822849 398176177286123815367137)
                  ·
                    refine ⟨298632132964592861525353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 398176177286123815367137 298632132964592861525353)
                    ·
                      refine ⟨223974099723444646144015, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 298632132964592861525353 223974099723444646144015)
                      ·
                        rfl

theorem cell23_436188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 1, 2, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 1, 2, 2, 1, 2, 2, 2].length) (baseStart_436188 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_436188 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_436188 prefixEnd_436188 := by exact prefixLift 436188
  have htrace : WordTrace (prefixWord ++ tailWord_436188) baseStart_436188 baseEnd_436188 := by
    simpa [prefixWord, tailWord_436188, baseEnd_436188] using wordTrace_append hprefix tailTrace_436188
  have hstable : (prefixWord ++ tailWord_436188).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_436188).length < 2 ^ (prefixWord ++ tailWord_436188).sum := by decide
  have hdescent : baseEnd_436188 < baseStart_436188 := by decide
  rcases family_descends (prefixWord ++ tailWord_436188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_436196 : List Nat := [2, 3, 1, 1, 1, 1, 3, 2, 4, 2, 3]
def baseStart_436196 : Nat := 118140960795 + 436196 * 2 ^ 59
def prefixEnd_436196 : Nat := 4983230072969 + 3 ^ 40 * 436196 * 2
def baseEnd_436196 : Nat := 223978207568680614843977

theorem tailTrace_436196 : CollatzResearch.WordTrace tailWord_436196 prefixEnd_436196 223978207568680614843977 := by
  unfold tailWord_436196
  simp only [CollatzResearch.WordTrace]
  refine ⟨7954687563871931595476221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10606250085162575460634961 7954687563871931595476221)
  ·
    refine ⟨2983007836451974348303583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7954687563871931595476221 2983007836451974348303583)
    ·
      refine ⟨4474511754677961522455375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2983007836451974348303583 4474511754677961522455375)
      ·
        refine ⟨6711767632016942283683063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4474511754677961522455375 6711767632016942283683063)
        ·
          refine ⟨10067651448025413425524595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6711767632016942283683063 10067651448025413425524595)
          ·
            refine ⟨15101477172038120138286893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10067651448025413425524595 15101477172038120138286893)
            ·
              refine ⟨5663053939514295051857585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15101477172038120138286893 5663053939514295051857585)
              ·
                refine ⟨4247290454635721288893189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5663053939514295051857585 4247290454635721288893189)
                ·
                  refine ⟨796366960244197741667473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4247290454635721288893189 796366960244197741667473)
                  ·
                    refine ⟨597275220183148306250605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 796366960244197741667473 597275220183148306250605)
                    ·
                      refine ⟨223978207568680614843977, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 597275220183148306250605 223978207568680614843977)
                      ·
                        rfl

theorem cell23_436196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 3, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 3, 2, 4, 2, 3].length) (baseStart_436196 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_436196 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_436196 prefixEnd_436196 := by exact prefixLift 436196
  have htrace : WordTrace (prefixWord ++ tailWord_436196) baseStart_436196 baseEnd_436196 := by
    simpa [prefixWord, tailWord_436196, baseEnd_436196] using wordTrace_append hprefix tailTrace_436196
  have hstable : (prefixWord ++ tailWord_436196).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_436196).length < 2 ^ (prefixWord ++ tailWord_436196).sum := by decide
  have hdescent : baseEnd_436196 < baseStart_436196 := by decide
  rcases family_descends (prefixWord ++ tailWord_436196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_436264 : List Nat := [2, 1, 5, 3, 2, 1, 1, 1, 2, 2, 3]
def baseStart_436264 : Nat := 118140960795 + 436264 * 2 ^ 59
def prefixEnd_436264 : Nat := 4983230072969 + 3 ^ 40 * 436264 * 2
def baseEnd_436264 : Nat := 224013124253186348793665

theorem tailTrace_436264 : CollatzResearch.WordTrace tailWord_436264 prefixEnd_436264 224013124253186348793665 := by
  unfold tailWord_436264
  simp only [CollatzResearch.WordTrace]
  refine ⟨7955927645748755402213923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10607903527665007202951897 7955927645748755402213923)
  ·
    refine ⟨11933891468623133103320885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7955927645748755402213923 11933891468623133103320885)
    ·
      refine ⟨1118802325183418728436333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 11933891468623133103320885 1118802325183418728436333)
      ·
        refine ⟨419550871943782023163625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1118802325183418728436333 419550871943782023163625)
        ·
          refine ⟨314663153957836517372719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 419550871943782023163625 314663153957836517372719)
          ·
            refine ⟨471994730936754776059079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 314663153957836517372719 471994730936754776059079)
            ·
              refine ⟨707992096405132164088619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 471994730936754776059079 707992096405132164088619)
              ·
                refine ⟨1061988144607698246132929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 707992096405132164088619 1061988144607698246132929)
                ·
                  refine ⟨796491108455773684599697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1061988144607698246132929 796491108455773684599697)
                  ·
                    refine ⟨597368331341830263449773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 796491108455773684599697 597368331341830263449773)
                    ·
                      refine ⟨224013124253186348793665, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 597368331341830263449773 224013124253186348793665)
                      ·
                        rfl

theorem cell23_436264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 2, 1, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 2, 1, 1, 1, 2, 2, 3].length) (baseStart_436264 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_436264 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_436264 prefixEnd_436264 := by exact prefixLift 436264
  have htrace : WordTrace (prefixWord ++ tailWord_436264) baseStart_436264 baseEnd_436264 := by
    simpa [prefixWord, tailWord_436264, baseEnd_436264] using wordTrace_append hprefix tailTrace_436264
  have hstable : (prefixWord ++ tailWord_436264).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_436264).length < 2 ^ (prefixWord ++ tailWord_436264).sum := by decide
  have hdescent : baseEnd_436264 < baseStart_436264 := by decide
  rcases family_descends (prefixWord ++ tailWord_436264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_436270 : List Nat := [4, 1, 3, 1, 1, 3, 1, 1, 1, 5, 2]
def baseStart_436270 : Nat := 118140960795 + 436270 * 2 ^ 59
def prefixEnd_436270 : Nat := 4983230072969 + 3 ^ 40 * 436270 * 2
def baseEnd_436270 : Nat := 224016205137113325318637

theorem tailTrace_436270 : CollatzResearch.WordTrace tailWord_436270 prefixEnd_436270 224016205137113325318637 := by
  unfold tailWord_436270
  simp only [CollatzResearch.WordTrace]
  refine ⟨1989009266184471728643283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 10608049419650515886097509 1989009266184471728643283)
  ·
    refine ⟨2983513899276707592964925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1989009266184471728643283 2983513899276707592964925)
    ·
      refine ⟨1118817712228765347361847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2983513899276707592964925 1118817712228765347361847)
      ·
        refine ⟨1678226568343148021042771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1118817712228765347361847 1678226568343148021042771)
        ·
          refine ⟨2517339852514722031564157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1678226568343148021042771 2517339852514722031564157)
          ·
            refine ⟨944002444693020761836559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2517339852514722031564157 944002444693020761836559)
            ·
              refine ⟨1416003667039531142754839, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 944002444693020761836559 1416003667039531142754839)
              ·
                refine ⟨2124005500559296714132259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1416003667039531142754839 2124005500559296714132259)
                ·
                  refine ⟨3186008250838945071198389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2124005500559296714132259 3186008250838945071198389)
                  ·
                    refine ⟨298688273516151100424849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3186008250838945071198389 298688273516151100424849)
                    ·
                      refine ⟨224016205137113325318637, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 298688273516151100424849 224016205137113325318637)
                      ·
                        rfl

theorem cell23_436270_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 3, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 3, 1, 1, 1, 5, 2].length) (baseStart_436270 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_436270 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_436270 prefixEnd_436270 := by exact prefixLift 436270
  have htrace : WordTrace (prefixWord ++ tailWord_436270) baseStart_436270 baseEnd_436270 := by
    simpa [prefixWord, tailWord_436270, baseEnd_436270] using wordTrace_append hprefix tailTrace_436270
  have hstable : (prefixWord ++ tailWord_436270).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_436270).length < 2 ^ (prefixWord ++ tailWord_436270).sum := by decide
  have hdescent : baseEnd_436270 < baseStart_436270 := by decide
  rcases family_descends (prefixWord ++ tailWord_436270) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_436294 : List Nat := [6, 1, 1, 1, 1, 1, 1, 6, 1, 1, 3]
def baseStart_436294 : Nat := 118140960795 + 436294 * 2 ^ 59
def prefixEnd_436294 : Nat := 4983230072969 + 3 ^ 40 * 436294 * 2
def baseEnd_436294 : Nat := 224028528672821231418527

theorem tailTrace_436294 : CollatzResearch.WordTrace tailWord_436294 prefixEnd_436294 224028528672821231418527 := by
  unfold tailWord_436294
  simp only [CollatzResearch.WordTrace]
  refine ⟨497279671293400810250623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 10608632987592550618679957 497279671293400810250623)
  ·
    refine ⟨745919506940101215375935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 497279671293400810250623 745919506940101215375935)
    ·
      refine ⟨1118879260410151823063903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 745919506940101215375935 1118879260410151823063903)
      ·
        refine ⟨1678318890615227734595855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1118879260410151823063903 1678318890615227734595855)
        ·
          refine ⟨2517478335922841601893783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1678318890615227734595855 2517478335922841601893783)
          ·
            refine ⟨3776217503884262402840675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2517478335922841601893783 3776217503884262402840675)
            ·
              refine ⟨5664326255826393604261013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3776217503884262402840675 5664326255826393604261013)
              ·
                refine ⟨265515293241862200199735, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 5664326255826393604261013 265515293241862200199735)
                ·
                  refine ⟨398272939862793300299603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 265515293241862200199735 398272939862793300299603)
                  ·
                    refine ⟨597409409794189950449405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 398272939862793300299603 597409409794189950449405)
                    ·
                      refine ⟨224028528672821231418527, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 597409409794189950449405 224028528672821231418527)
                      ·
                        rfl

theorem cell23_436294_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 1, 6, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 1, 6, 1, 1, 3].length) (baseStart_436294 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_436294 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_436294 prefixEnd_436294 := by exact prefixLift 436294
  have htrace : WordTrace (prefixWord ++ tailWord_436294) baseStart_436294 baseEnd_436294 := by
    simpa [prefixWord, tailWord_436294, baseEnd_436294] using wordTrace_append hprefix tailTrace_436294
  have hstable : (prefixWord ++ tailWord_436294).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_436294).length < 2 ^ (prefixWord ++ tailWord_436294).sum := by decide
  have hdescent : baseEnd_436294 < baseStart_436294 := by decide
  rcases family_descends (prefixWord ++ tailWord_436294) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_436300 : List Nat := [2, 2, 1, 3, 1, 1, 3, 3, 3, 2, 2]
def baseStart_436300 : Nat := 118140960795 + 436300 * 2 ^ 59
def prefixEnd_436300 : Nat := 4983230072969 + 3 ^ 40 * 436300 * 2
def baseEnd_436300 : Nat := 224031609556748207943499

theorem tailTrace_436300 : CollatzResearch.WordTrace tailWord_436300 prefixEnd_436300 224031609556748207943499 := by
  unfold tailWord_436300
  simp only [CollatzResearch.WordTrace]
  refine ⟨7956584159683544476369177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10608778879578059301825569 7956584159683544476369177)
  ·
    refine ⟨5967438119762658357276883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7956584159683544476369177 5967438119762658357276883)
    ·
      refine ⟨8951157179643987535915325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5967438119762658357276883 8951157179643987535915325)
      ·
        refine ⟨3356683942366495325968247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8951157179643987535915325 3356683942366495325968247)
        ·
          refine ⟨5035025913549742988952371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3356683942366495325968247 5035025913549742988952371)
          ·
            refine ⟨7552538870324614483428557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5035025913549742988952371 7552538870324614483428557)
            ·
              refine ⟨2832202076371730431285709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7552538870324614483428557 2832202076371730431285709)
              ·
                refine ⟨1062075778639398911732141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2832202076371730431285709 1062075778639398911732141)
                ·
                  refine ⟨398278416989774591899553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1062075778639398911732141 398278416989774591899553)
                  ·
                    refine ⟨298708812742330943924665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 398278416989774591899553 298708812742330943924665)
                    ·
                      refine ⟨224031609556748207943499, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 298708812742330943924665 224031609556748207943499)
                      ·
                        rfl

theorem cell23_436300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 3, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 3, 3, 3, 2, 2].length) (baseStart_436300 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_436300 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_436300 prefixEnd_436300 := by exact prefixLift 436300
  have htrace : WordTrace (prefixWord ++ tailWord_436300) baseStart_436300 baseEnd_436300 := by
    simpa [prefixWord, tailWord_436300, baseEnd_436300] using wordTrace_append hprefix tailTrace_436300
  have hstable : (prefixWord ++ tailWord_436300).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_436300).length < 2 ^ (prefixWord ++ tailWord_436300).sum := by decide
  have hdescent : baseEnd_436300 < baseStart_436300 := by decide
  rcases family_descends (prefixWord ++ tailWord_436300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_436317 : List Nat := [1, 4, 4, 1, 1, 2, 2, 2, 1, 1, 4]
def baseStart_436317 : Nat := 118140960795 + 436317 * 2 ^ 59
def prefixEnd_436317 : Nat := 4983230072969 + 3 ^ 40 * 436317 * 2
def baseEnd_436317 : Nat := 224040338727874641430921

theorem tailTrace_436317 : CollatzResearch.WordTrace tailWord_436317 prefixEnd_436317 224040338727874641430921 := by
  unfold tailWord_436317
  simp only [CollatzResearch.WordTrace]
  refine ⟨15913788360305500856107205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10609192240203667237404803 15913788360305500856107205)
  ·
    refine ⟨2983835317557281410520101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 15913788360305500856107205 2983835317557281410520101)
    ·
      refine ⟨559469122041990264472519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2983835317557281410520101 559469122041990264472519)
      ·
        refine ⟨839203683062985396708779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 559469122041990264472519 839203683062985396708779)
        ·
          refine ⟨1258805524594478095063169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 839203683062985396708779 1258805524594478095063169)
          ·
            refine ⟨944104143445858571297377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1258805524594478095063169 944104143445858571297377)
            ·
              refine ⟨708078107584393928473033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 944104143445858571297377 708078107584393928473033)
              ·
                refine ⟨531058580688295446354775, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 708078107584393928473033 531058580688295446354775)
                ·
                  refine ⟨796587871032443169532163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 531058580688295446354775 796587871032443169532163)
                  ·
                    refine ⟨1194881806548664754298245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 796587871032443169532163 1194881806548664754298245)
                    ·
                      refine ⟨224040338727874641430921, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1194881806548664754298245 224040338727874641430921)
                      ·
                        rfl

theorem cell23_436317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 2, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 2, 2, 2, 1, 1, 4].length) (baseStart_436317 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_436317 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_436317 prefixEnd_436317 := by exact prefixLift 436317
  have htrace : WordTrace (prefixWord ++ tailWord_436317) baseStart_436317 baseEnd_436317 := by
    simpa [prefixWord, tailWord_436317, baseEnd_436317] using wordTrace_append hprefix tailTrace_436317
  have hstable : (prefixWord ++ tailWord_436317).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_436317).length < 2 ^ (prefixWord ++ tailWord_436317).sum := by decide
  have hdescent : baseEnd_436317 < baseStart_436317 := by decide
  rcases family_descends (prefixWord ++ tailWord_436317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_436320 : List Nat := [2, 1, 1, 3, 2, 4, 2, 2, 1, 2, 3]
def baseStart_436320 : Nat := 118140960795 + 436320 * 2 ^ 59
def prefixEnd_436320 : Nat := 4983230072969 + 3 ^ 40 * 436320 * 2
def baseEnd_436320 : Nat := 224041879169838129693407

theorem tailTrace_436320 : CollatzResearch.WordTrace tailWord_436320 prefixEnd_436320 224041879169838129693407 := by
  unfold tailWord_436320
  simp only [CollatzResearch.WordTrace]
  refine ⟨7956948889647316184233207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10609265186196421578977609 7956948889647316184233207)
  ·
    refine ⟨11935423334470974276349811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7956948889647316184233207 11935423334470974276349811)
    ·
      refine ⟨17903135001706461414524717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11935423334470974276349811 17903135001706461414524717)
      ·
        refine ⟨6713675625639923030446769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17903135001706461414524717 6713675625639923030446769)
        ·
          refine ⟨5035256719229942272835077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6713675625639923030446769 5035256719229942272835077)
          ·
            refine ⟨944110634855614176156577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5035256719229942272835077 944110634855614176156577)
            ·
              refine ⟨708082976141710632117433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 944110634855614176156577 708082976141710632117433)
              ·
                refine ⟨531062232106282974088075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 708082976141710632117433 531062232106282974088075)
                ·
                  refine ⟨796593348159424461132113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 531062232106282974088075 796593348159424461132113)
                  ·
                    refine ⟨597445011119568345849085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 796593348159424461132113 597445011119568345849085)
                    ·
                      refine ⟨224041879169838129693407, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 597445011119568345849085 224041879169838129693407)
                      ·
                        rfl

theorem cell23_436320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 4, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 4, 2, 2, 1, 2, 3].length) (baseStart_436320 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_436320 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_436320 prefixEnd_436320 := by exact prefixLift 436320
  have htrace : WordTrace (prefixWord ++ tailWord_436320) baseStart_436320 baseEnd_436320 := by
    simpa [prefixWord, tailWord_436320, baseEnd_436320] using wordTrace_append hprefix tailTrace_436320
  have hstable : (prefixWord ++ tailWord_436320).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_436320).length < 2 ^ (prefixWord ++ tailWord_436320).sum := by decide
  have hdescent : baseEnd_436320 < baseStart_436320 := by decide
  rcases family_descends (prefixWord ++ tailWord_436320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_436333 : List Nat := [1, 5, 1, 1, 2, 1, 2, 1, 3, 3, 3]
def baseStart_436333 : Nat := 118140960795 + 436333 * 2 ^ 59
def prefixEnd_436333 : Nat := 4983230072969 + 3 ^ 40 * 436333 * 2
def baseEnd_436333 : Nat := 224048554418346578830847

theorem tailTrace_436333 : CollatzResearch.WordTrace tailWord_436333 prefixEnd_436333 224048554418346578830847 := by
  unfold tailWord_436333
  simp only [CollatzResearch.WordTrace]
  refine ⟨15914371928247535588689653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10609581285498357059126435 15914371928247535588689653)
  ·
    refine ⟨1491972368273206461439655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 15914371928247535588689653 1491972368273206461439655)
    ·
      refine ⟨2237958552409809692159483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1491972368273206461439655 2237958552409809692159483)
      ·
        refine ⟨3356937828614714538239225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2237958552409809692159483 3356937828614714538239225)
        ·
          refine ⟨2517703371461035903679419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3356937828614714538239225 2517703371461035903679419)
          ·
            refine ⟨3776555057191553855519129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2517703371461035903679419 3776555057191553855519129)
            ·
              refine ⟨2832416292893665391639347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3776555057191553855519129 2832416292893665391639347)
              ·
                refine ⟨4248624439340498087459021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2832416292893665391639347 4248624439340498087459021)
                ·
                  refine ⟨1593234164752686782797133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4248624439340498087459021 1593234164752686782797133)
                  ·
                    refine ⟨597462811782257543548925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1593234164752686782797133 597462811782257543548925)
                    ·
                      refine ⟨224048554418346578830847, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 597462811782257543548925 224048554418346578830847)
                      ·
                        rfl

theorem cell23_436333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 2, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 2, 1, 3, 3, 3].length) (baseStart_436333 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_436333 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_436333 prefixEnd_436333 := by exact prefixLift 436333
  have htrace : WordTrace (prefixWord ++ tailWord_436333) baseStart_436333 baseEnd_436333 := by
    simpa [prefixWord, tailWord_436333, baseEnd_436333] using wordTrace_append hprefix tailTrace_436333
  have hstable : (prefixWord ++ tailWord_436333).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_436333).length < 2 ^ (prefixWord ++ tailWord_436333).sum := by decide
  have hdescent : baseEnd_436333 < baseStart_436333 := by decide
  rcases family_descends (prefixWord ++ tailWord_436333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_436407 : List Nat := [1, 1, 3, 1, 4, 2, 1, 4, 2, 2, 2]
def baseStart_436407 : Nat := 118140960795 + 436407 * 2 ^ 59
def prefixEnd_436407 : Nat := 4983230072969 + 3 ^ 40 * 436407 * 2
def baseEnd_436407 : Nat := 224086551986779289305507

theorem tailTrace_436407 : CollatzResearch.WordTrace tailWord_436407 prefixEnd_436407 224086551986779289305507 := by
  unfold tailWord_436407
  simp only [CollatzResearch.WordTrace]
  refine ⟨15917070929979446226883475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10611380619986297484588983 15917070929979446226883475)
  ·
    refine ⟨23875606394969169340325213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15917070929979446226883475 23875606394969169340325213)
    ·
      refine ⟨8953352398113438502621955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23875606394969169340325213 8953352398113438502621955)
      ·
        refine ⟨13430028597170157753932933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8953352398113438502621955 13430028597170157753932933)
        ·
          refine ⟨2518130361969404578862425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13430028597170157753932933 2518130361969404578862425)
          ·
            refine ⟨1888597771477053434146819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2518130361969404578862425 1888597771477053434146819)
            ·
              refine ⟨2832896657215580151220229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1888597771477053434146819 2832896657215580151220229)
              ·
                refine ⟨531168123227921278353793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2832896657215580151220229 531168123227921278353793)
                ·
                  refine ⟨398376092420940958765345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 531168123227921278353793 398376092420940958765345)
                  ·
                    refine ⟨298782069315705719074009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 398376092420940958765345 298782069315705719074009)
                    ·
                      refine ⟨224086551986779289305507, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 298782069315705719074009 224086551986779289305507)
                      ·
                        rfl

theorem cell23_436407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 2, 1, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 2, 1, 4, 2, 2, 2].length) (baseStart_436407 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_436407 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_436407 prefixEnd_436407 := by exact prefixLift 436407
  have htrace : WordTrace (prefixWord ++ tailWord_436407) baseStart_436407 baseEnd_436407 := by
    simpa [prefixWord, tailWord_436407, baseEnd_436407] using wordTrace_append hprefix tailTrace_436407
  have hstable : (prefixWord ++ tailWord_436407).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_436407).length < 2 ^ (prefixWord ++ tailWord_436407).sum := by decide
  have hdescent : baseEnd_436407 < baseStart_436407 := by decide
  rcases family_descends (prefixWord ++ tailWord_436407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_436420 : List Nat := [2, 3, 3, 1, 2, 2, 1, 1, 2, 2, 4]
def baseStart_436420 : Nat := 118140960795 + 436420 * 2 ^ 59
def prefixEnd_436420 : Nat := 4983230072969 + 3 ^ 40 * 436420 * 2
def baseEnd_436420 : Nat := 224093227235287738442947

theorem tailTrace_436420 : CollatzResearch.WordTrace tailWord_436420 prefixEnd_436420 224093227235287738442947 := by
  unfold tailWord_436420
  simp only [CollatzResearch.WordTrace]
  refine ⟨7958772539466174723553357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10611696719288232964737809 7958772539466174723553357)
  ·
    refine ⟨2984539702299815521332509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7958772539466174723553357 2984539702299815521332509)
    ·
      refine ⟨1119202388362430820499691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2984539702299815521332509 1119202388362430820499691)
      ·
        refine ⟨1678803582543646230749537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1119202388362430820499691 1678803582543646230749537)
        ·
          refine ⟨1259102686907734673062153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1678803582543646230749537 1259102686907734673062153)
          ·
            refine ⟨944327015180801004796615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1259102686907734673062153 944327015180801004796615)
            ·
              refine ⟨1416490522771201507194923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 944327015180801004796615 1416490522771201507194923)
              ·
                refine ⟨2124735784156802260792385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1416490522771201507194923 2124735784156802260792385)
                ·
                  refine ⟨1593551838117601695594289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2124735784156802260792385 1593551838117601695594289)
                  ·
                    refine ⟨1195163878588201271695717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1593551838117601695594289 1195163878588201271695717)
                    ·
                      refine ⟨224093227235287738442947, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1195163878588201271695717 224093227235287738442947)
                      ·
                        rfl

theorem cell23_436420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 2, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 2, 1, 1, 2, 2, 4].length) (baseStart_436420 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_436420 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_436420 prefixEnd_436420 := by exact prefixLift 436420
  have htrace : WordTrace (prefixWord ++ tailWord_436420) baseStart_436420 baseEnd_436420 := by
    simpa [prefixWord, tailWord_436420, baseEnd_436420] using wordTrace_append hprefix tailTrace_436420
  have hstable : (prefixWord ++ tailWord_436420).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_436420).length < 2 ^ (prefixWord ++ tailWord_436420).sum := by decide
  have hdescent : baseEnd_436420 < baseStart_436420 := by decide
  rcases family_descends (prefixWord ++ tailWord_436420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_436480 : List Nat := [2, 1, 1, 2, 1, 1, 6, 1, 2, 4, 2]
def baseStart_436480 : Nat := 118140960795 + 436480 * 2 ^ 59
def prefixEnd_436480 : Nat := 4983230072969 + 3 ^ 40 * 436480 * 2
def baseEnd_436480 : Nat := 224124036074557503692671

theorem tailTrace_436480 : CollatzResearch.WordTrace tailWord_436480 prefixEnd_436480 224124036074557503692671 := by
  unfold tailWord_436480
  simp only [CollatzResearch.WordTrace]
  refine ⟨7959866729357489847145447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10613155639143319796193929 7959866729357489847145447)
  ·
    refine ⟨11939800094036234770718171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7959866729357489847145447 11939800094036234770718171)
    ·
      refine ⟨17909700141054352156077257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11939800094036234770718171 17909700141054352156077257)
      ·
        refine ⟨13432275105790764117057943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17909700141054352156077257 13432275105790764117057943)
        ·
          refine ⟨20148412658686146175586915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13432275105790764117057943 20148412658686146175586915)
          ·
            refine ⟨30222618988029219263380373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20148412658686146175586915 30222618988029219263380373)
            ·
              refine ⟨1416685265063869652970955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 30222618988029219263380373 1416685265063869652970955)
              ·
                refine ⟨2125027897595804479456433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1416685265063869652970955 2125027897595804479456433)
                ·
                  refine ⟨1593770923196853359592325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2125027897595804479456433 1593770923196853359592325)
                  ·
                    refine ⟨298832048099410004923561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1593770923196853359592325 298832048099410004923561)
                    ·
                      refine ⟨224124036074557503692671, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 298832048099410004923561 224124036074557503692671)
                      ·
                        rfl

theorem cell23_436480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 6, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 6, 1, 2, 4, 2].length) (baseStart_436480 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_436480 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_436480 prefixEnd_436480 := by exact prefixLift 436480
  have htrace : WordTrace (prefixWord ++ tailWord_436480) baseStart_436480 baseEnd_436480 := by
    simpa [prefixWord, tailWord_436480, baseEnd_436480] using wordTrace_append hprefix tailTrace_436480
  have hstable : (prefixWord ++ tailWord_436480).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_436480).length < 2 ^ (prefixWord ++ tailWord_436480).sum := by decide
  have hdescent : baseEnd_436480 < baseStart_436480 := by decide
  rcases family_descends (prefixWord ++ tailWord_436480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_436483 : List Nat := [1, 1, 1, 3, 2, 3, 1, 1, 3, 4, 3]
def baseStart_436483 : Nat := 118140960795 + 436483 * 2 ^ 59
def prefixEnd_436483 : Nat := 4983230072969 + 3 ^ 40 * 436483 * 2
def baseEnd_436483 : Nat := 224125576516520991955157

theorem tailTrace_436483 : CollatzResearch.WordTrace tailWord_436483 prefixEnd_436483 224125576516520991955157 := by
  unfold tailWord_436483
  simp only [CollatzResearch.WordTrace]
  refine ⟨15919842877704111206650103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10613228585136074137766735 15919842877704111206650103)
  ·
    refine ⟨23879764316556166809975155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15919842877704111206650103 23879764316556166809975155)
    ·
      refine ⟨35819646474834250214962733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23879764316556166809975155 35819646474834250214962733)
      ·
        refine ⟨13432367428062843830611025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35819646474834250214962733 13432367428062843830611025)
        ·
          refine ⟨10074275571047132872958269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13432367428062843830611025 10074275571047132872958269)
          ·
            refine ⟨3777853339142674827359351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10074275571047132872958269 3777853339142674827359351)
            ·
              refine ⟨5666780008714012241039027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3777853339142674827359351 5666780008714012241039027)
              ·
                refine ⟨8500170013071018361558541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5666780008714012241039027 8500170013071018361558541)
                ·
                  refine ⟨3187563754901631885584453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8500170013071018361558541 3187563754901631885584453)
                  ·
                    refine ⟨597668204044055978547085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3187563754901631885584453 597668204044055978547085)
                    ·
                      refine ⟨224125576516520991955157, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 597668204044055978547085 224125576516520991955157)
                      ·
                        rfl

theorem cell23_436483_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 1, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 1, 1, 3, 4, 3].length) (baseStart_436483 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_436483 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_436483 prefixEnd_436483 := by exact prefixLift 436483
  have htrace : WordTrace (prefixWord ++ tailWord_436483) baseStart_436483 baseEnd_436483 := by
    simpa [prefixWord, tailWord_436483, baseEnd_436483] using wordTrace_append hprefix tailTrace_436483
  have hstable : (prefixWord ++ tailWord_436483).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_436483).length < 2 ^ (prefixWord ++ tailWord_436483).sum := by decide
  have hdescent : baseEnd_436483 < baseStart_436483 := by decide
  rcases family_descends (prefixWord ++ tailWord_436483) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_436490 : List Nat := [3, 1, 2, 2, 1, 1, 4, 2, 3, 4]
def baseStart_436490 : Nat := 118140960795 + 436490 * 2 ^ 59
def prefixEnd_436490 : Nat := 4983230072969 + 3 ^ 40 * 436490 * 2
def baseEnd_436490 : Nat := 74709723627034154855875

theorem tailTrace_436490 : CollatzResearch.WordTrace tailWord_436490 prefixEnd_436490 74709723627034154855875 := by
  unfold tailWord_436490
  simp only [CollatzResearch.WordTrace]
  refine ⟨3980024547169687850538731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10613398792452500934769949 3980024547169687850538731)
  ·
    refine ⟨5970036820754531775808097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3980024547169687850538731 5970036820754531775808097)
    ·
      refine ⟨4477527615565898831856073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5970036820754531775808097 4477527615565898831856073)
      ·
        refine ⟨3358145711674424123892055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4477527615565898831856073 3358145711674424123892055)
        ·
          refine ⟨5037218567511636185838083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3358145711674424123892055 5037218567511636185838083)
          ·
            refine ⟨7555827851267454278757125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5037218567511636185838083 7555827851267454278757125)
            ·
              refine ⟨1416717722112647677266961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7555827851267454278757125 1416717722112647677266961)
              ·
                refine ⟨1062538291584485757950221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1416717722112647677266961 1062538291584485757950221)
                ·
                  refine ⟨398451859344182159231333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1062538291584485757950221 398451859344182159231333)
                  ·
                    refine ⟨74709723627034154855875, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 398451859344182159231333 74709723627034154855875)
                    ·
                      rfl

theorem cell23_436490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 4, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 4, 2, 3, 4].length) (baseStart_436490 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_436490 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_436490 prefixEnd_436490 := by exact prefixLift 436490
  have htrace : WordTrace (prefixWord ++ tailWord_436490) baseStart_436490 baseEnd_436490 := by
    simpa [prefixWord, tailWord_436490, baseEnd_436490] using wordTrace_append hprefix tailTrace_436490
  have hstable : (prefixWord ++ tailWord_436490).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_436490).length < 2 ^ (prefixWord ++ tailWord_436490).sum := by decide
  have hdescent : baseEnd_436490 < baseStart_436490 := by decide
  rcases family_descends (prefixWord ++ tailWord_436490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_436503 : List Nat := [1, 1, 3, 4, 1, 2, 1, 2, 8]
def baseStart_436503 : Nat := 118140960795 + 436503 * 2 ^ 59
def prefixEnd_436503 : Nat := 4983230072969 + 3 ^ 40 * 436503 * 2
def baseEnd_436503 : Nat := 24903982903290101522785

theorem tailTrace_436503 : CollatzResearch.WordTrace tailWord_436503 prefixEnd_436503 24903982903290101522785 := by
  unfold tailWord_436503
  simp only [CollatzResearch.WordTrace]
  refine ⟨15920572337631654622378163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10613714891754436414918775 15920572337631654622378163)
  ·
    refine ⟨23880858506447481933567245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15920572337631654622378163 23880858506447481933567245)
    ·
      refine ⟨8955321939917805725087717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23880858506447481933567245 8955321939917805725087717)
      ·
        refine ⟨1679122863734588573453947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8955321939917805725087717 1679122863734588573453947)
        ·
          refine ⟨2518684295601882860180921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1679122863734588573453947 2518684295601882860180921)
          ·
            refine ⟨1889013221701412145135691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2518684295601882860180921 1889013221701412145135691)
            ·
              refine ⟨2833519832552118217703537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1889013221701412145135691 2833519832552118217703537)
              ·
                refine ⟨2125139874414088663277653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2833519832552118217703537 2125139874414088663277653)
                ·
                  refine ⟨24903982903290101522785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 2125139874414088663277653 24903982903290101522785)
                  ·
                    rfl

theorem cell23_436503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 2, 1, 2, 8].length) (baseStart_436503 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_436503 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_436503 prefixEnd_436503 := by exact prefixLift 436503
  have htrace : WordTrace (prefixWord ++ tailWord_436503) baseStart_436503 baseEnd_436503 := by
    simpa [prefixWord, tailWord_436503, baseEnd_436503] using wordTrace_append hprefix tailTrace_436503
  have hstable : (prefixWord ++ tailWord_436503).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_436503).length < 2 ^ (prefixWord ++ tailWord_436503).sum := by decide
  have hdescent : baseEnd_436503 < baseStart_436503 := by decide
  rcases family_descends (prefixWord ++ tailWord_436503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_436507 : List Nat := [1, 1, 1, 1, 1, 1, 9, 3, 1, 4]
def baseStart_436507 : Nat := 118140960795 + 436507 * 2 ^ 59
def prefixEnd_436507 : Nat := 4983230072969 + 3 ^ 40 * 436507 * 2
def baseEnd_436507 : Nat := 74712633350742966018349

theorem tailTrace_436507 : CollatzResearch.WordTrace tailWord_436507 prefixEnd_436507 74712633350742966018349 := by
  unfold tailWord_436507
  simp only [CollatzResearch.WordTrace]
  refine ⟨15920718229617163305523775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10613812153078108870349183 15920718229617163305523775)
  ·
    refine ⟨23881077344425744958285663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15920718229617163305523775 23881077344425744958285663)
    ·
      refine ⟨35821616016638617437428495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23881077344425744958285663 35821616016638617437428495)
      ·
        refine ⟨53732424024957926156142743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35821616016638617437428495 53732424024957926156142743)
        ·
          refine ⟨80598636037436889234214115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53732424024957926156142743 80598636037436889234214115)
          ·
            refine ⟨120897954056155333851321173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80598636037436889234214115 120897954056155333851321173)
            ·
              refine ⟨708386449547785159285085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 120897954056155333851321173 708386449547785159285085)
              ·
                refine ⟨265644918580419434731907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 708386449547785159285085 265644918580419434731907)
                ·
                  refine ⟨398467377870629152097861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 265644918580419434731907 398467377870629152097861)
                  ·
                    refine ⟨74712633350742966018349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 398467377870629152097861 74712633350742966018349)
                    ·
                      rfl

theorem cell23_436507_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 9, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 9, 3, 1, 4].length) (baseStart_436507 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_436507 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_436507 prefixEnd_436507 := by exact prefixLift 436507
  have htrace : WordTrace (prefixWord ++ tailWord_436507) baseStart_436507 baseEnd_436507 := by
    simpa [prefixWord, tailWord_436507, baseEnd_436507] using wordTrace_append hprefix tailTrace_436507
  have hstable : (prefixWord ++ tailWord_436507).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_436507).length < 2 ^ (prefixWord ++ tailWord_436507).sum := by decide
  have hdescent : baseEnd_436507 < baseStart_436507 := by decide
  rcases family_descends (prefixWord ++ tailWord_436507) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_436517 : List Nat := [1, 3, 1, 2, 5, 1, 1, 2, 2, 2, 3]
def baseStart_436517 : Nat := 118140960795 + 436517 * 2 ^ 59
def prefixEnd_436517 : Nat := 4983230072969 + 3 ^ 40 * 436517 * 2
def baseEnd_436517 : Nat := 224143034858773858930001

theorem tailTrace_436517 : CollatzResearch.WordTrace tailWord_436517 prefixEnd_436517 224143034858773858930001 := by
  unfold tailWord_436517
  simp only [CollatzResearch.WordTrace]
  refine ⟨15921082959580935013387805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10614055306387290008925203 15921082959580935013387805)
  ·
    refine ⟨5970406109842850630020427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15921082959580935013387805 5970406109842850630020427)
    ·
      refine ⟨8955609164764275945030641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5970406109842850630020427 8955609164764275945030641)
      ·
        refine ⟨6716706873573206958772981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8955609164764275945030641 6716706873573206958772981)
        ·
          refine ⟨629691269397488152384967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 6716706873573206958772981 629691269397488152384967)
          ·
            refine ⟨944536904096232228577451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 629691269397488152384967 944536904096232228577451)
            ·
              refine ⟨1416805356144348342866177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 944536904096232228577451 1416805356144348342866177)
              ·
                refine ⟨1062604017108261257149633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1416805356144348342866177 1062604017108261257149633)
                ·
                  refine ⟨796953012831195942862225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1062604017108261257149633 796953012831195942862225)
                  ·
                    refine ⟨597714759623396957146669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 796953012831195942862225 597714759623396957146669)
                    ·
                      refine ⟨224143034858773858930001, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 597714759623396957146669 224143034858773858930001)
                      ·
                        rfl

theorem cell23_436517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 5, 1, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 5, 1, 1, 2, 2, 2, 3].length) (baseStart_436517 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_436517 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_436517 prefixEnd_436517 := by exact prefixLift 436517
  have htrace : WordTrace (prefixWord ++ tailWord_436517) baseStart_436517 baseEnd_436517 := by
    simpa [prefixWord, tailWord_436517, baseEnd_436517] using wordTrace_append hprefix tailTrace_436517
  have hstable : (prefixWord ++ tailWord_436517).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_436517).length < 2 ^ (prefixWord ++ tailWord_436517).sum := by decide
  have hdescent : baseEnd_436517 < baseStart_436517 := by decide
  rcases family_descends (prefixWord ++ tailWord_436517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_436537 : List Nat := [1, 2, 1, 6, 1, 1, 4, 1, 6]
def baseStart_436537 : Nat := 118140960795 + 436537 * 2 ^ 59
def prefixEnd_436537 : Nat := 4983230072969 + 3 ^ 40 * 436537 * 2
def baseEnd_436537 : Nat := 24905922719095975631101

theorem tailTrace_436537 : CollatzResearch.WordTrace tailWord_436537 prefixEnd_436537 24905922719095975631101 := by
  unfold tailWord_436537
  simp only [CollatzResearch.WordTrace]
  refine ⟨15921812419508478429115865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10614541613005652286077243 15921812419508478429115865)
  ·
    refine ⟨11941359314631358821836899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15921812419508478429115865 11941359314631358821836899)
    ·
      refine ⟨17912038971947038232755349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11941359314631358821836899 17912038971947038232755349)
      ·
        refine ⟨839626826810017417160407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 17912038971947038232755349 839626826810017417160407)
        ·
          refine ⟨1259440240215026125740611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 839626826810017417160407 1259440240215026125740611)
          ·
            refine ⟨1889160360322539188610917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1259440240215026125740611 1889160360322539188610917)
            ·
              refine ⟨354217567560476097864547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1889160360322539188610917 354217567560476097864547)
              ·
                refine ⟨531326351340714146796821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 354217567560476097864547 531326351340714146796821)
                ·
                  refine ⟨24905922719095975631101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 531326351340714146796821 24905922719095975631101)
                  ·
                    rfl

theorem cell23_436537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 1, 4, 1, 6].length) (baseStart_436537 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_436537 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_436537 prefixEnd_436537 := by exact prefixLift 436537
  have htrace : WordTrace (prefixWord ++ tailWord_436537) baseStart_436537 baseEnd_436537 := by
    simpa [prefixWord, tailWord_436537, baseEnd_436537] using wordTrace_append hprefix tailTrace_436537
  have hstable : (prefixWord ++ tailWord_436537).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_436537).length < 2 ^ (prefixWord ++ tailWord_436537).sum := by decide
  have hdescent : baseEnd_436537 < baseStart_436537 := by decide
  rcases family_descends (prefixWord ++ tailWord_436537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_436567 : List Nat := [1, 1, 3, 2, 3, 1, 5, 1, 1, 5]
def baseStart_436567 : Nat := 118140960795 + 436567 * 2 ^ 59
def prefixEnd_436567 : Nat := 4983230072969 + 3 ^ 40 * 436567 * 2
def baseEnd_436567 : Nat := 74722902963832887768257

theorem tailTrace_436567 : CollatzResearch.WordTrace tailWord_436567 prefixEnd_436567 74722902963832887768257 := by
  unfold tailWord_436567
  simp only [CollatzResearch.WordTrace]
  refine ⟨15922906609399793552707955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10615271072933195701805303 15922906609399793552707955)
  ·
    refine ⟨23884359914099690329061933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15922906609399793552707955 23884359914099690329061933)
    ·
      refine ⟨8956634967787383873398225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23884359914099690329061933 8956634967787383873398225)
      ·
        refine ⟨6717476225840537905048669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8956634967787383873398225 6717476225840537905048669)
        ·
          refine ⟨2519053584690201714393251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6717476225840537905048669 2519053584690201714393251)
          ·
            refine ⟨3778580377035302571589877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2519053584690201714393251 3778580377035302571589877)
            ·
              refine ⟨354241910347059616086551, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 3778580377035302571589877 354241910347059616086551)
              ·
                refine ⟨531362865520589424129827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 354241910347059616086551 531362865520589424129827)
                ·
                  refine ⟨797044298280884136194741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 531362865520589424129827 797044298280884136194741)
                  ·
                    refine ⟨74722902963832887768257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 797044298280884136194741 74722902963832887768257)
                    ·
                      rfl

theorem cell23_436567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 5, 1, 1, 5].length) (baseStart_436567 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_436567 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_436567 prefixEnd_436567 := by exact prefixLift 436567
  have htrace : WordTrace (prefixWord ++ tailWord_436567) baseStart_436567 baseEnd_436567 := by
    simpa [prefixWord, tailWord_436567, baseEnd_436567] using wordTrace_append hprefix tailTrace_436567
  have hstable : (prefixWord ++ tailWord_436567).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_436567).length < 2 ^ (prefixWord ++ tailWord_436567).sum := by decide
  have hdescent : baseEnd_436567 < baseStart_436567 := by decide
  rcases family_descends (prefixWord ++ tailWord_436567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_436581 : List Nat := [1, 3, 1, 3, 1, 3, 4, 2, 1, 1, 3]
def baseStart_436581 : Nat := 118140960795 + 436581 * 2 ^ 59
def prefixEnd_436581 : Nat := 4983230072969 + 3 ^ 40 * 436581 * 2
def baseEnd_436581 : Nat := 224175897620661608529707

theorem tailTrace_436581 : CollatzResearch.WordTrace tailWord_436581 prefixEnd_436581 224175897620661608529707 := by
  unfold tailWord_436581
  simp only [CollatzResearch.WordTrace]
  refine ⟨15923417231349073943717597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10615611487566049295811731 15923417231349073943717597)
  ·
    refine ⟨5971281461755902728894099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15923417231349073943717597 5971281461755902728894099)
    ·
      refine ⟨8956922192633854093341149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5971281461755902728894099 8956922192633854093341149)
      ·
        refine ⟨3358845822237695285002931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8956922192633854093341149 3358845822237695285002931)
        ·
          refine ⟨5038268733356542927504397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3358845822237695285002931 5038268733356542927504397)
          ·
            refine ⟨1889350775008703597814149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5038268733356542927504397 1889350775008703597814149)
            ·
              refine ⟨354253270314131924590153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1889350775008703597814149 354253270314131924590153)
              ·
                refine ⟨265689952735598943442615, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 354253270314131924590153 265689952735598943442615)
                ·
                  refine ⟨398534929103398415163923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 265689952735598943442615 398534929103398415163923)
                  ·
                    refine ⟨597802393655097622745885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 398534929103398415163923 597802393655097622745885)
                    ·
                      refine ⟨224175897620661608529707, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 597802393655097622745885 224175897620661608529707)
                      ·
                        rfl

theorem cell23_436581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 3, 4, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 3, 4, 2, 1, 1, 3].length) (baseStart_436581 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_436581 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_436581 prefixEnd_436581 := by exact prefixLift 436581
  have htrace : WordTrace (prefixWord ++ tailWord_436581) baseStart_436581 baseEnd_436581 := by
    simpa [prefixWord, tailWord_436581, baseEnd_436581] using wordTrace_append hprefix tailTrace_436581
  have hstable : (prefixWord ++ tailWord_436581).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_436581).length < 2 ^ (prefixWord ++ tailWord_436581).sum := by decide
  have hdescent : baseEnd_436581 < baseStart_436581 := by decide
  rcases family_descends (prefixWord ++ tailWord_436581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_436597 : List Nat := [1, 3, 4, 1, 2, 2, 2, 1, 1, 6]
def baseStart_436597 : Nat := 118140960795 + 436597 * 2 ^ 59
def prefixEnd_436597 : Nat := 4983230072969 + 3 ^ 40 * 436597 * 2
def baseEnd_436597 : Nat := 74728037770377848643211

theorem tailTrace_436597 : CollatzResearch.WordTrace tailWord_436597 prefixEnd_436597 74728037770377848643211 := by
  unfold tailWord_436597
  simp only [CollatzResearch.WordTrace]
  refine ⟨15924000799291108676300045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10616000532860739117533363 15924000799291108676300045)
  ·
    refine ⟨5971500299734165753612517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15924000799291108676300045 5971500299734165753612517)
    ·
      refine ⟨1119656306200156078802347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5971500299734165753612517 1119656306200156078802347)
      ·
        refine ⟨1679484459300234118203521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1119656306200156078802347 1679484459300234118203521)
        ·
          refine ⟨1259613344475175588652641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1679484459300234118203521 1259613344475175588652641)
          ·
            refine ⟨944710008356381691489481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1259613344475175588652641 944710008356381691489481)
            ·
              refine ⟨708532506267286268617111, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 944710008356381691489481 708532506267286268617111)
              ·
                refine ⟨1062798759400929402925667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 708532506267286268617111 1062798759400929402925667)
                ·
                  refine ⟨1594198139101394104388501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1062798759400929402925667 1594198139101394104388501)
                  ·
                    refine ⟨74728037770377848643211, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1594198139101394104388501 74728037770377848643211)
                    ·
                      rfl

theorem cell23_436597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 2, 2, 1, 1, 6].length) (baseStart_436597 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_436597 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_436597 prefixEnd_436597 := by exact prefixLift 436597
  have htrace : WordTrace (prefixWord ++ tailWord_436597) baseStart_436597 baseEnd_436597 := by
    simpa [prefixWord, tailWord_436597, baseEnd_436597] using wordTrace_append hprefix tailTrace_436597
  have hstable : (prefixWord ++ tailWord_436597).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_436597).length < 2 ^ (prefixWord ++ tailWord_436597).sum := by decide
  have hdescent : baseEnd_436597 < baseStart_436597 := by decide
  rcases family_descends (prefixWord ++ tailWord_436597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_436618 : List Nat := [3, 1, 2, 5, 2, 1, 2, 1, 1, 5]
def baseStart_436618 : Nat := 118140960795 + 436618 * 2 ^ 59
def prefixEnd_436618 : Nat := 4983230072969 + 3 ^ 40 * 436618 * 2
def baseEnd_436618 : Nat := 74731632134959321255679

theorem tailTrace_436618 : CollatzResearch.WordTrace tailWord_436618 prefixEnd_436618 74731632134959321255679 := by
  unfold tailWord_436618
  simp only [CollatzResearch.WordTrace]
  refine ⟨3981191683053757315703627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10616511154810019508543005 3981191683053757315703627)
  ·
    refine ⟨5971787524580635973555441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3981191683053757315703627 5971787524580635973555441)
    ·
      refine ⟨4478840643435476980166581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5971787524580635973555441 4478840643435476980166581)
      ·
        refine ⟨419891310322075966890617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 4478840643435476980166581 419891310322075966890617)
        ·
          refine ⟨314918482741556975167963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 419891310322075966890617 314918482741556975167963)
          ·
            refine ⟨472377724112335462751945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 314918482741556975167963 472377724112335462751945)
            ·
              refine ⟨354283293084251597063959, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 472377724112335462751945 354283293084251597063959)
              ·
                refine ⟨531424939626377395595939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 354283293084251597063959 531424939626377395595939)
                ·
                  refine ⟨797137409439566093393909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 531424939626377395595939 797137409439566093393909)
                  ·
                    refine ⟨74731632134959321255679, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 797137409439566093393909 74731632134959321255679)
                    ·
                      rfl

theorem cell23_436618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 2, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 2, 1, 2, 1, 1, 5].length) (baseStart_436618 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_436618 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_436618 prefixEnd_436618 := by exact prefixLift 436618
  have htrace : WordTrace (prefixWord ++ tailWord_436618) baseStart_436618 baseEnd_436618 := by
    simpa [prefixWord, tailWord_436618, baseEnd_436618] using wordTrace_append hprefix tailTrace_436618
  have hstable : (prefixWord ++ tailWord_436618).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_436618).length < 2 ^ (prefixWord ++ tailWord_436618).sum := by decide
  have hdescent : baseEnd_436618 < baseStart_436618 := by decide
  rcases family_descends (prefixWord ++ tailWord_436618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_436638 : List Nat := [4, 3, 1, 2, 1, 2, 2, 1, 3, 2, 2]
def baseStart_436638 : Nat := 118140960795 + 436638 * 2 ^ 59
def prefixEnd_436638 : Nat := 4983230072969 + 3 ^ 40 * 436638 * 2
def baseEnd_436638 : Nat := 224205166017967885516945

theorem tailTrace_436638 : CollatzResearch.WordTrace tailWord_436638 prefixEnd_436638 224205166017967885516945 := by
  unfold tailWord_436638
  simp only [CollatzResearch.WordTrace]
  refine ⟨1990687024017821584817821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 10616997461428381785695045 1990687024017821584817821)
  ·
    refine ⟨746507634006683094306683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1990687024017821584817821 746507634006683094306683)
    ·
      refine ⟨1119761451010024641460025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 746507634006683094306683 1119761451010024641460025)
      ·
        refine ⟨839821088257518481095019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1119761451010024641460025 839821088257518481095019)
        ·
          refine ⟨1259731632386277721642529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 839821088257518481095019 1259731632386277721642529)
          ·
            refine ⟨944798724289708291231897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1259731632386277721642529 944798724289708291231897)
            ·
              refine ⟨708599043217281218423923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 944798724289708291231897 708599043217281218423923)
              ·
                refine ⟨1062898564825921827635885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 708599043217281218423923 1062898564825921827635885)
                ·
                  refine ⟨398586961809720685363457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1062898564825921827635885 398586961809720685363457)
                  ·
                    refine ⟨298940221357290514022593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 398586961809720685363457 298940221357290514022593)
                    ·
                      refine ⟨224205166017967885516945, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 298940221357290514022593 224205166017967885516945)
                      ·
                        rfl

theorem cell23_436638_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 2, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 2, 2, 1, 3, 2, 2].length) (baseStart_436638 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_436638 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_436638 prefixEnd_436638 := by exact prefixLift 436638
  have htrace : WordTrace (prefixWord ++ tailWord_436638) baseStart_436638 baseEnd_436638 := by
    simpa [prefixWord, tailWord_436638, baseEnd_436638] using wordTrace_append hprefix tailTrace_436638
  have hstable : (prefixWord ++ tailWord_436638).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_436638).length < 2 ^ (prefixWord ++ tailWord_436638).sum := by decide
  have hdescent : baseEnd_436638 < baseStart_436638 := by decide
  rcases family_descends (prefixWord ++ tailWord_436638) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_436670 : List Nat := [4, 2, 1, 1, 1, 1, 2, 2, 1, 8]
def baseStart_436670 : Nat := 118140960795 + 436670 * 2 ^ 59
def prefixEnd_436670 : Nat := 4983230072969 + 3 ^ 40 * 436670 * 2
def baseEnd_436670 : Nat := 74740532466303920105599

theorem tailTrace_436670 : CollatzResearch.WordTrace tailWord_436670 prefixEnd_436670 74740532466303920105599 := by
  unfold tailWord_436670
  simp only [CollatzResearch.WordTrace]
  refine ⟨1990832916003330267963433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 10617775552017761429138309 1990832916003330267963433)
  ·
    refine ⟨1493124687002497700972575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1990832916003330267963433 1493124687002497700972575)
    ·
      refine ⟨2239687030503746551458863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1493124687002497700972575 2239687030503746551458863)
      ·
        refine ⟨3359530545755619827188295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2239687030503746551458863 3359530545755619827188295)
        ·
          refine ⟨5039295818633429740782443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3359530545755619827188295 5039295818633429740782443)
          ·
            refine ⟨7558943727950144611173665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5039295818633429740782443 7558943727950144611173665)
            ·
              refine ⟨5669207795962608458380249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7558943727950144611173665 5669207795962608458380249)
              ·
                refine ⟨4251905846971956343785187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5669207795962608458380249 4251905846971956343785187)
                ·
                  refine ⟨6377858770457934515677781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4251905846971956343785187 6377858770457934515677781)
                  ·
                    refine ⟨74740532466303920105599, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 6377858770457934515677781 74740532466303920105599)
                    ·
                      rfl

theorem cell23_436670_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 2, 2, 1, 8].length) (baseStart_436670 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_436670 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_436670 prefixEnd_436670 := by exact prefixLift 436670
  have htrace : WordTrace (prefixWord ++ tailWord_436670) baseStart_436670 baseEnd_436670 := by
    simpa [prefixWord, tailWord_436670, baseEnd_436670] using wordTrace_append hprefix tailTrace_436670
  have hstable : (prefixWord ++ tailWord_436670).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_436670).length < 2 ^ (prefixWord ++ tailWord_436670).sum := by decide
  have hdescent : baseEnd_436670 < baseStart_436670 := by decide
  rcases family_descends (prefixWord ++ tailWord_436670) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_436680 : List Nat := [2, 1, 3, 1, 3, 2, 1, 1, 1, 3, 5]
def baseStart_436680 : Nat := 118140960795 + 436680 * 2 ^ 59
def prefixEnd_436680 : Nat := 4983230072969 + 3 ^ 40 * 436680 * 2
def baseEnd_436680 : Nat := 224226732205456721191751

theorem tailTrace_436680 : CollatzResearch.WordTrace tailWord_436680 prefixEnd_436680 224226732205456721191751 := by
  unfold tailWord_436680
  simp only [CollatzResearch.WordTrace]
  refine ⟨7963514028995206925785747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10618018705326942567714329 7963514028995206925785747)
  ·
    refine ⟨11945271043492810388678621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7963514028995206925785747 11945271043492810388678621)
    ·
      refine ⟨4479476641309803895754483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11945271043492810388678621 4479476641309803895754483)
      ·
        refine ⟨6719214961964705843631725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4479476641309803895754483 6719214961964705843631725)
        ·
          refine ⟨2519705610736764691361897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6719214961964705843631725 2519705610736764691361897)
          ·
            refine ⟨1889779208052573518521423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2519705610736764691361897 1889779208052573518521423)
            ·
              refine ⟨2834668812078860277782135, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1889779208052573518521423 2834668812078860277782135)
              ·
                refine ⟨4252003218118290416673203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2834668812078860277782135 4252003218118290416673203)
                ·
                  refine ⟨6378004827177435625009805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4252003218118290416673203 6378004827177435625009805)
                  ·
                    refine ⟨2391751810191538359378677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6378004827177435625009805 2391751810191538359378677)
                    ·
                      refine ⟨224226732205456721191751, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 2391751810191538359378677 224226732205456721191751)
                      ·
                        rfl

theorem cell23_436680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 2, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 2, 1, 1, 1, 3, 5].length) (baseStart_436680 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_436680 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_436680 prefixEnd_436680 := by exact prefixLift 436680
  have htrace : WordTrace (prefixWord ++ tailWord_436680) baseStart_436680 baseEnd_436680 := by
    simpa [prefixWord, tailWord_436680, baseEnd_436680] using wordTrace_append hprefix tailTrace_436680
  have hstable : (prefixWord ++ tailWord_436680).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_436680).length < 2 ^ (prefixWord ++ tailWord_436680).sum := by decide
  have hdescent : baseEnd_436680 < baseStart_436680 := by decide
  rcases family_descends (prefixWord ++ tailWord_436680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_436711 : List Nat := [1, 1, 5, 2, 1, 1, 3, 3, 2, 2, 2]
def baseStart_436711 : Nat := 118140960795 + 436711 * 2 ^ 59
def prefixEnd_436711 : Nat := 4983230072969 + 3 ^ 40 * 436711 * 2
def baseEnd_436711 : Nat := 224242650105746099904109

theorem tailTrace_436711 : CollatzResearch.WordTrace tailWord_436711 prefixEnd_436711 224242650105746099904109 := by
  unfold tailWord_436711
  simp only [CollatzResearch.WordTrace]
  refine ⟨15928158720878106145949987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10618772480585404097299991 15928158720878106145949987)
  ·
    refine ⟨23892238081317159218924981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15928158720878106145949987 23892238081317159218924981)
    ·
      refine ⟨2239897320123483676774217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 23892238081317159218924981 2239897320123483676774217)
      ·
        refine ⟨1679922990092612757580663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2239897320123483676774217 1679922990092612757580663)
        ·
          refine ⟨2519884485138919136370995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1679922990092612757580663 2519884485138919136370995)
          ·
            refine ⟨3779826727708378704556493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2519884485138919136370995 3779826727708378704556493)
            ·
              refine ⟨1417435022890642014208685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3779826727708378704556493 1417435022890642014208685)
              ·
                refine ⟨531538133583990755328257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1417435022890642014208685 531538133583990755328257)
                ·
                  refine ⟨398653600187993066496193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 531538133583990755328257 398653600187993066496193)
                  ·
                    refine ⟨298990200140994799872145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 398653600187993066496193 298990200140994799872145)
                    ·
                      refine ⟨224242650105746099904109, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 298990200140994799872145 224242650105746099904109)
                      ·
                        rfl

theorem cell23_436711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 3, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 3, 3, 2, 2, 2].length) (baseStart_436711 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_436711 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_436711 prefixEnd_436711 := by exact prefixLift 436711
  have htrace : WordTrace (prefixWord ++ tailWord_436711) baseStart_436711 baseEnd_436711 := by
    simpa [prefixWord, tailWord_436711, baseEnd_436711] using wordTrace_append hprefix tailTrace_436711
  have hstable : (prefixWord ++ tailWord_436711).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_436711).length < 2 ^ (prefixWord ++ tailWord_436711).sum := by decide
  have hdescent : baseEnd_436711 < baseStart_436711 := by decide
  rcases family_descends (prefixWord ++ tailWord_436711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_436747 : List Nat := [1, 1, 1, 1, 7, 1, 2, 2, 2, 5]
def baseStart_436747 : Nat := 118140960795 + 436747 * 2 ^ 59
def prefixEnd_436747 : Nat := 4983230072969 + 3 ^ 40 * 436747 * 2
def baseEnd_436747 : Nat := 74753711803102653017981

theorem tailTrace_436747 : CollatzResearch.WordTrace tailWord_436747 prefixEnd_436747 74753711803102653017981 := by
  unfold tailWord_436747
  simp only [CollatzResearch.WordTrace]
  refine ⟨15929471748747684294260495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10619647832498456196173663 15929471748747684294260495)
  ·
    refine ⟨23894207623121526441390743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15929471748747684294260495 23894207623121526441390743)
    ·
      refine ⟨35841311434682289662086115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23894207623121526441390743 35841311434682289662086115)
      ·
        refine ⟨53761967152023434493129173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35841311434682289662086115 53761967152023434493129173)
        ·
          refine ⟨1260046105125549245932715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 53761967152023434493129173 1260046105125549245932715)
          ·
            refine ⟨1890069157688323868899073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1260046105125549245932715 1890069157688323868899073)
            ·
              refine ⟨1417551868266242901674305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1890069157688323868899073 1417551868266242901674305)
              ·
                refine ⟨1063163901199682176255729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1417551868266242901674305 1063163901199682176255729)
                ·
                  refine ⟨797372925899761632191797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1063163901199682176255729 797372925899761632191797)
                  ·
                    refine ⟨74753711803102653017981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 797372925899761632191797 74753711803102653017981)
                    ·
                      rfl

theorem cell23_436747_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 1, 2, 2, 2, 5].length) (baseStart_436747 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_436747 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_436747 prefixEnd_436747 := by exact prefixLift 436747
  have htrace : WordTrace (prefixWord ++ tailWord_436747) baseStart_436747 baseEnd_436747 := by
    simpa [prefixWord, tailWord_436747, baseEnd_436747] using wordTrace_append hprefix tailTrace_436747
  have hstable : (prefixWord ++ tailWord_436747).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_436747).length < 2 ^ (prefixWord ++ tailWord_436747).sum := by decide
  have hdescent : baseEnd_436747 < baseStart_436747 := by decide
  rcases family_descends (prefixWord ++ tailWord_436747) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_436780 : List Nat := [2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 6]
def baseStart_436780 : Nat := 118140960795 + 436780 * 2 ^ 59
def prefixEnd_436780 : Nat := 4983230072969 + 3 ^ 40 * 436780 * 2
def baseEnd_436780 : Nat := 224278080270906329941291

theorem tailTrace_436780 : CollatzResearch.WordTrace tailWord_436780 prefixEnd_436780 224278080270906329941291 := by
  unfold tailWord_436780
  simp only [CollatzResearch.WordTrace]
  refine ⟨7965337678814065465105897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10620450238418753953474529 7965337678814065465105897)
  ·
    refine ⟨5974003259110549098829423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7965337678814065465105897 5974003259110549098829423)
    ·
      refine ⟨8961004888665823648244135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5974003259110549098829423 8961004888665823648244135)
      ·
        refine ⟨13441507332998735472366203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8961004888665823648244135 13441507332998735472366203)
        ·
          refine ⟨20162260999498103208549305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13441507332998735472366203 20162260999498103208549305)
          ·
            refine ⟨15121695749623577406411979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20162260999498103208549305 15121695749623577406411979)
            ·
              refine ⟨22682543624435366109617969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15121695749623577406411979 22682543624435366109617969)
              ·
                refine ⟨17011907718326524582213477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22682543624435366109617969 17011907718326524582213477)
                ·
                  refine ⟨3189732697186223359165027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17011907718326524582213477 3189732697186223359165027)
                  ·
                    refine ⟨4784599045779335038747541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3189732697186223359165027 4784599045779335038747541)
                    ·
                      refine ⟨224278080270906329941291, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 4784599045779335038747541 224278080270906329941291)
                      ·
                        rfl

theorem cell23_436780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 6].length) (baseStart_436780 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_436780 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_436780 prefixEnd_436780 := by exact prefixLift 436780
  have htrace : WordTrace (prefixWord ++ tailWord_436780) baseStart_436780 baseEnd_436780 := by
    simpa [prefixWord, tailWord_436780, baseEnd_436780] using wordTrace_append hprefix tailTrace_436780
  have hstable : (prefixWord ++ tailWord_436780).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_436780).length < 2 ^ (prefixWord ++ tailWord_436780).sum := by decide
  have hdescent : baseEnd_436780 < baseStart_436780 := by decide
  rcases family_descends (prefixWord ++ tailWord_436780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_436787 : List Nat := [1, 1, 1, 2, 4, 2, 3, 1, 1, 4, 3]
def baseStart_436787 : Nat := 118140960795 + 436787 * 2 ^ 59
def prefixEnd_436787 : Nat := 4983230072969 + 3 ^ 40 * 436787 * 2
def baseEnd_436787 : Nat := 224281674635487802553759

theorem tailTrace_436787 : CollatzResearch.WordTrace tailWord_436787 prefixEnd_436787 224281674635487802553759 := by
  unfold tailWord_436787
  simp only [CollatzResearch.WordTrace]
  refine ⟨15930930668602771125716615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10620620445735180750477743 15930930668602771125716615)
  ·
    refine ⟨23896396002904156688574923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15930930668602771125716615 23896396002904156688574923)
    ·
      refine ⟨35844594004356235032862385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23896396002904156688574923 35844594004356235032862385)
      ·
        refine ⟨26883445503267176274646789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35844594004356235032862385 26883445503267176274646789)
        ·
          refine ⟨5040646031862595551496273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 26883445503267176274646789 5040646031862595551496273)
          ·
            refine ⟨3780484523896946663622205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5040646031862595551496273 3780484523896946663622205)
            ·
              refine ⟨1417681696461354998858327, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3780484523896946663622205 1417681696461354998858327)
              ·
                refine ⟨2126522544692032498287491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1417681696461354998858327 2126522544692032498287491)
                ·
                  refine ⟨3189783817038048747431237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2126522544692032498287491 3189783817038048747431237)
                  ·
                    refine ⟨598084465694634140143357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3189783817038048747431237 598084465694634140143357)
                    ·
                      refine ⟨224281674635487802553759, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 598084465694634140143357 224281674635487802553759)
                      ·
                        rfl

theorem cell23_436787_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 3, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 3, 1, 1, 4, 3].length) (baseStart_436787 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_436787 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_436787 prefixEnd_436787 := by exact prefixLift 436787
  have htrace : WordTrace (prefixWord ++ tailWord_436787) baseStart_436787 baseEnd_436787 := by
    simpa [prefixWord, tailWord_436787, baseEnd_436787] using wordTrace_append hprefix tailTrace_436787
  have hstable : (prefixWord ++ tailWord_436787).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_436787).length < 2 ^ (prefixWord ++ tailWord_436787).sum := by decide
  have hdescent : baseEnd_436787 < baseStart_436787 := by decide
  rcases family_descends (prefixWord ++ tailWord_436787) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_436797 : List Nat := [1, 4, 1, 3, 2, 1, 1, 1, 2, 1, 6]
def baseStart_436797 : Nat := 118140960795 + 436797 * 2 ^ 59
def prefixEnd_436797 : Nat := 4983230072969 + 3 ^ 40 * 436797 * 2
def baseEnd_436797 : Nat := 224286809442032763428713

theorem tailTrace_436797 : CollatzResearch.WordTrace tailWord_436797 prefixEnd_436797 224286809442032763428713 := by
  unfold tailWord_436797
  simp only [CollatzResearch.WordTrace]
  refine ⟨15931295398566542833580645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10620863599044361889053763 15931295398566542833580645)
  ·
    refine ⟨2987117887231226781296371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 15931295398566542833580645 2987117887231226781296371)
    ·
      refine ⟨4480676830846840171944557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2987117887231226781296371 4480676830846840171944557)
      ·
        refine ⟨1680253811567565064479209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4480676830846840171944557 1680253811567565064479209)
        ·
          refine ⟨1260190358675673798359407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1680253811567565064479209 1260190358675673798359407)
          ·
            refine ⟨1890285538013510697539111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1260190358675673798359407 1890285538013510697539111)
            ·
              refine ⟨2835428307020266046308667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1890285538013510697539111 2835428307020266046308667)
              ·
                refine ⟨4253142460530399069463001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2835428307020266046308667 4253142460530399069463001)
                ·
                  refine ⟨3189856845397799302097251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4253142460530399069463001 3189856845397799302097251)
                  ·
                    refine ⟨4784785268096698953145877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3189856845397799302097251 4784785268096698953145877)
                    ·
                      refine ⟨224286809442032763428713, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 4784785268096698953145877 224286809442032763428713)
                      ·
                        rfl

theorem cell23_436797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 1, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 1, 1, 1, 2, 1, 6].length) (baseStart_436797 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_436797 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_436797 prefixEnd_436797 := by exact prefixLift 436797
  have htrace : WordTrace (prefixWord ++ tailWord_436797) baseStart_436797 baseEnd_436797 := by
    simpa [prefixWord, tailWord_436797, baseEnd_436797] using wordTrace_append hprefix tailTrace_436797
  have hstable : (prefixWord ++ tailWord_436797).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_436797).length < 2 ^ (prefixWord ++ tailWord_436797).sum := by decide
  have hdescent : baseEnd_436797 < baseStart_436797 := by decide
  rcases family_descends (prefixWord ++ tailWord_436797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_436807 : List Nat := [1, 1, 4, 1, 4, 2, 1, 1, 8]
def baseStart_436807 : Nat := 118140960795 + 436807 * 2 ^ 59
def prefixEnd_436807 : Nat := 4983230072969 + 3 ^ 40 * 436807 * 2
def baseEnd_436807 : Nat := 24921327138730858255963

theorem tailTrace_436807 : CollatzResearch.WordTrace tailWord_436807 prefixEnd_436807 24921327138730858255963 := by
  unfold tailWord_436807
  simp only [CollatzResearch.WordTrace]
  refine ⟨15931660128530314541444675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10621106752353543027629783 15931660128530314541444675)
  ·
    refine ⟨23897490192795471812167013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15931660128530314541444675 23897490192795471812167013)
    ·
      refine ⟨4480779411149150964781315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 23897490192795471812167013 4480779411149150964781315)
      ·
        refine ⟨6721169116723726447171973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4480779411149150964781315 6721169116723726447171973)
        ·
          refine ⟨1260219209385698708844745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6721169116723726447171973 1260219209385698708844745)
          ·
            refine ⟨945164407039274031633559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1260219209385698708844745 945164407039274031633559)
            ·
              refine ⟨1417746610558911047450339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 945164407039274031633559 1417746610558911047450339)
              ·
                refine ⟨2126619915838366571175509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1417746610558911047450339 2126619915838366571175509)
                ·
                  refine ⟨24921327138730858255963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 2126619915838366571175509 24921327138730858255963)
                  ·
                    rfl

theorem cell23_436807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 2, 1, 1, 8].length) (baseStart_436807 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_436807 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_436807 prefixEnd_436807 := by exact prefixLift 436807
  have htrace : WordTrace (prefixWord ++ tailWord_436807) baseStart_436807 baseEnd_436807 := by
    simpa [prefixWord, tailWord_436807, baseEnd_436807] using wordTrace_append hprefix tailTrace_436807
  have hstable : (prefixWord ++ tailWord_436807).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_436807).length < 2 ^ (prefixWord ++ tailWord_436807).sum := by decide
  have hdescent : baseEnd_436807 < baseStart_436807 := by decide
  rcases family_descends (prefixWord ++ tailWord_436807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_436844 : List Nat := [2, 2, 1, 1, 3, 1, 4, 1, 1, 5, 2]
def baseStart_436844 : Nat := 118140960795 + 436844 * 2 ^ 59
def prefixEnd_436844 : Nat := 4983230072969 + 3 ^ 40 * 436844 * 2
def baseEnd_436844 : Nat := 224310943032794079540997

theorem tailTrace_436844 : CollatzResearch.WordTrace tailWord_436844 prefixEnd_436844 224310943032794079540997 := by
  unfold tailWord_436844
  simp only [CollatzResearch.WordTrace]
  refine ⟨7966504814698134930270793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10622006419597513240361057 7966504814698134930270793)
  ·
    refine ⟨5974878611023601197703095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7966504814698134930270793 5974878611023601197703095)
    ·
      refine ⟨8962317916535401796554643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5974878611023601197703095 8962317916535401796554643)
      ·
        refine ⟨13443476874803102694831965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8962317916535401796554643 13443476874803102694831965)
        ·
          refine ⟨5041303828051163510561987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13443476874803102694831965 5041303828051163510561987)
          ·
            refine ⟨7561955742076745265842981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5041303828051163510561987 7561955742076745265842981)
            ·
              refine ⟨1417866701639389737345559, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7561955742076745265842981 1417866701639389737345559)
              ·
                refine ⟨2126800052459084606018339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1417866701639389737345559 2126800052459084606018339)
                ·
                  refine ⟨3190200078688626909027509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2126800052459084606018339 3190200078688626909027509)
                  ·
                    refine ⟨299081257377058772721329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3190200078688626909027509 299081257377058772721329)
                    ·
                      refine ⟨224310943032794079540997, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 299081257377058772721329 224310943032794079540997)
                      ·
                        rfl

theorem cell23_436844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 5, 2].length) (baseStart_436844 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_436844 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_436844 prefixEnd_436844 := by exact prefixLift 436844
  have htrace : WordTrace (prefixWord ++ tailWord_436844) baseStart_436844 baseEnd_436844 := by
    simpa [prefixWord, tailWord_436844, baseEnd_436844] using wordTrace_append hprefix tailTrace_436844
  have hstable : (prefixWord ++ tailWord_436844).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_436844).length < 2 ^ (prefixWord ++ tailWord_436844).sum := by decide
  have hdescent : baseEnd_436844 < baseStart_436844 := by decide
  rcases family_descends (prefixWord ++ tailWord_436844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_436851 : List Nat := [1, 1, 1, 2, 2, 1, 1, 9, 1, 1, 3]
def baseStart_436851 : Nat := 118140960795 + 436851 * 2 ^ 59
def prefixEnd_436851 : Nat := 4983230072969 + 3 ^ 40 * 436851 * 2
def baseEnd_436851 : Nat := 224314537397375552153465

theorem tailTrace_436851 : CollatzResearch.WordTrace tailWord_436851 prefixEnd_436851 224314537397375552153465 := by
  unfold tailWord_436851
  simp only [CollatzResearch.WordTrace]
  refine ⟨15933264940370910056046407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10622176626913940037364271 15933264940370910056046407)
  ·
    refine ⟨23899897410556365084069611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15933264940370910056046407 23899897410556365084069611)
    ·
      refine ⟨35849846115834547626104417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23899897410556365084069611 35849846115834547626104417)
      ·
        refine ⟨26887384586875910719578313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35849846115834547626104417 26887384586875910719578313)
        ·
          refine ⟨20165538440156933039683735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26887384586875910719578313 20165538440156933039683735)
          ·
            refine ⟨30248307660235399559525603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20165538440156933039683735 30248307660235399559525603)
            ·
              refine ⟨45372461490353099339288405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30248307660235399559525603 45372461490353099339288405)
              ·
                refine ⟨265854266545037691441143, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 45372461490353099339288405 265854266545037691441143)
                ·
                  refine ⟨398781399817556537161715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 265854266545037691441143 398781399817556537161715)
                  ·
                    refine ⟨598172099726334805742573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 398781399817556537161715 598172099726334805742573)
                    ·
                      refine ⟨224314537397375552153465, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 598172099726334805742573 224314537397375552153465)
                      ·
                        rfl

theorem cell23_436851_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 9, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 9, 1, 1, 3].length) (baseStart_436851 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_436851 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_436851 prefixEnd_436851 := by exact prefixLift 436851
  have htrace : WordTrace (prefixWord ++ tailWord_436851) baseStart_436851 baseEnd_436851 := by
    simpa [prefixWord, tailWord_436851, baseEnd_436851] using wordTrace_append hprefix tailTrace_436851
  have hstable : (prefixWord ++ tailWord_436851).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_436851).length < 2 ^ (prefixWord ++ tailWord_436851).sum := by decide
  have hdescent : baseEnd_436851 < baseStart_436851 := by decide
  rcases family_descends (prefixWord ++ tailWord_436851) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_436868 : List Nat := [2, 3, 2, 1, 3, 3, 1, 1, 3, 1, 3]
def baseStart_436868 : Nat := 118140960795 + 436868 * 2 ^ 59
def prefixEnd_436868 : Nat := 4983230072969 + 3 ^ 40 * 436868 * 2
def baseEnd_436868 : Nat := 224323266568501985640887

theorem tailTrace_436868 : CollatzResearch.WordTrace tailWord_436868 prefixEnd_436868 224323266568501985640887 := by
  unfold tailWord_436868
  simp only [CollatzResearch.WordTrace]
  refine ⟨7966942490654660979707629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10622589987539547972943505 7966942490654660979707629)
  ·
    refine ⟨2987603433995497867390361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7966942490654660979707629 2987603433995497867390361)
    ·
      refine ⟨2240702575496623400542771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2987603433995497867390361 2240702575496623400542771)
      ·
        refine ⟨3361053863244935100814157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2240702575496623400542771 3361053863244935100814157)
        ·
          refine ⟨1260395198716850662805309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3361053863244935100814157 1260395198716850662805309)
          ·
            refine ⟨472648199518818998551991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1260395198716850662805309 472648199518818998551991)
            ·
              refine ⟨708972299278228497827987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 472648199518818998551991 708972299278228497827987)
              ·
                refine ⟨1063458448917342746741981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 708972299278228497827987 1063458448917342746741981)
                ·
                  refine ⟨398796918344003530028243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1063458448917342746741981 398796918344003530028243)
                  ·
                    refine ⟨598195377516005295042365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 398796918344003530028243 598195377516005295042365)
                    ·
                      refine ⟨224323266568501985640887, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 598195377516005295042365 224323266568501985640887)
                      ·
                        rfl

theorem cell23_436868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 3, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 3, 1, 1, 3, 1, 3].length) (baseStart_436868 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_436868 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_436868 prefixEnd_436868 := by exact prefixLift 436868
  have htrace : WordTrace (prefixWord ++ tailWord_436868) baseStart_436868 baseEnd_436868 := by
    simpa [prefixWord, tailWord_436868, baseEnd_436868] using wordTrace_append hprefix tailTrace_436868
  have hstable : (prefixWord ++ tailWord_436868).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_436868).length < 2 ^ (prefixWord ++ tailWord_436868).sum := by decide
  have hdescent : baseEnd_436868 < baseStart_436868 := by decide
  rcases family_descends (prefixWord ++ tailWord_436868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_436887 : List Nat := [1, 1, 3, 3, 2, 1, 1, 3, 1, 1, 6]
def baseStart_436887 : Nat := 118140960795 + 436887 * 2 ^ 59
def prefixEnd_436887 : Nat := 4983230072969 + 3 ^ 40 * 436887 * 2
def baseEnd_436887 : Nat := 224333022700937411303299

theorem tailTrace_436887 : CollatzResearch.WordTrace tailWord_436887 prefixEnd_436887 224333022700937411303299 := by
  unfold tailWord_436887
  simp only [CollatzResearch.WordTrace]
  refine ⟨15934577968240488204356915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10623051978826992136237943 15934577968240488204356915)
  ·
    refine ⟨23901866952360732306535373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15934577968240488204356915 23901866952360732306535373)
    ·
      refine ⟨8963200107135274614950765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23901866952360732306535373 8963200107135274614950765)
      ·
        refine ⟨3361200040175727980606537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8963200107135274614950765 3361200040175727980606537)
        ·
          refine ⟨2520900030131795985454903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3361200040175727980606537 2520900030131795985454903)
          ·
            refine ⟨3781350045197693978182355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2520900030131795985454903 3781350045197693978182355)
            ·
              refine ⟨5672025067796540967273533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3781350045197693978182355 5672025067796540967273533)
              ·
                refine ⟨2127009400423702862727575, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5672025067796540967273533 2127009400423702862727575)
                ·
                  refine ⟨3190514100635554294091363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2127009400423702862727575 3190514100635554294091363)
                  ·
                    refine ⟨4785771150953331441137045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3190514100635554294091363 4785771150953331441137045)
                    ·
                      refine ⟨224333022700937411303299, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 4785771150953331441137045 224333022700937411303299)
                      ·
                        rfl

theorem cell23_436887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 1, 3, 1, 1, 6].length) (baseStart_436887 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_436887 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_436887 prefixEnd_436887 := by exact prefixLift 436887
  have htrace : WordTrace (prefixWord ++ tailWord_436887) baseStart_436887 baseEnd_436887 := by
    simpa [prefixWord, tailWord_436887, baseEnd_436887] using wordTrace_append hprefix tailTrace_436887
  have hstable : (prefixWord ++ tailWord_436887).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_436887).length < 2 ^ (prefixWord ++ tailWord_436887).sum := by decide
  have hdescent : baseEnd_436887 < baseStart_436887 := by decide
  rcases family_descends (prefixWord ++ tailWord_436887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_436924 : List Nat := [2, 2, 2, 3, 1, 1, 1, 2, 3, 3, 3]
def baseStart_436924 : Nat := 118140960795 + 436924 * 2 ^ 59
def prefixEnd_436924 : Nat := 4983230072969 + 3 ^ 40 * 436924 * 2
def baseEnd_436924 : Nat := 224352021485153766540629

theorem tailTrace_436924 : CollatzResearch.WordTrace tailWord_436924 prefixEnd_436924 224352021485153766540629 := by
  unfold tailWord_436924
  simp only [CollatzResearch.WordTrace]
  refine ⟨7967963734553221761726913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10623951646070962348969217 7967963734553221761726913)
  ·
    refine ⟨5975972800914916321295185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7967963734553221761726913 5975972800914916321295185)
    ·
      refine ⟨4481979600686187240971389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5975972800914916321295185 4481979600686187240971389)
      ·
        refine ⟨1680742350257320215364271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4481979600686187240971389 1680742350257320215364271)
        ·
          refine ⟨2521113525385980323046407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1680742350257320215364271 2521113525385980323046407)
          ·
            refine ⟨3781670288078970484569611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2521113525385980323046407 3781670288078970484569611)
            ·
              refine ⟨5672505432118455726854417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3781670288078970484569611 5672505432118455726854417)
              ·
                refine ⟨4254379074088841795140813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5672505432118455726854417 4254379074088841795140813)
                ·
                  refine ⟨1595392152783315673177805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4254379074088841795140813 1595392152783315673177805)
                  ·
                    refine ⟨598272057293743377441677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1595392152783315673177805 598272057293743377441677)
                    ·
                      refine ⟨224352021485153766540629, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 598272057293743377441677 224352021485153766540629)
                      ·
                        rfl

theorem cell23_436924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 1, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 1, 2, 3, 3, 3].length) (baseStart_436924 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_436924 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_436924 prefixEnd_436924 := by exact prefixLift 436924
  have htrace : WordTrace (prefixWord ++ tailWord_436924) baseStart_436924 baseEnd_436924 := by
    simpa [prefixWord, tailWord_436924, baseEnd_436924] using wordTrace_append hprefix tailTrace_436924
  have hstable : (prefixWord ++ tailWord_436924).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_436924).length < 2 ^ (prefixWord ++ tailWord_436924).sum := by decide
  have hdescent : baseEnd_436924 < baseStart_436924 := by decide
  rcases family_descends (prefixWord ++ tailWord_436924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_436925 : List Nat := [1, 4, 1, 2, 1, 4, 1, 4, 1, 2, 2]
def baseStart_436925 : Nat := 118140960795 + 436925 * 2 ^ 59
def prefixEnd_436925 : Nat := 4983230072969 + 3 ^ 40 * 436925 * 2
def baseEnd_436925 : Nat := 224352534965808262628125

theorem tailTrace_436925 : CollatzResearch.WordTrace tailWord_436925 prefixEnd_436925 224352534965808262628125 := by
  unfold tailWord_436925
  simp only [CollatzResearch.WordTrace]
  refine ⟨15935963942102820694240229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10623975961401880462826819 15935963942102820694240229)
  ·
    refine ⟨2987993239144278880170043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 15935963942102820694240229 2987993239144278880170043)
    ·
      refine ⟨4481989858716418320255065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2987993239144278880170043 4481989858716418320255065)
      ·
        refine ⟨3361492394037313740191299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4481989858716418320255065 3361492394037313740191299)
        ·
          refine ⟨5042238591055970610286949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3361492394037313740191299 5042238591055970610286949)
          ·
            refine ⟨945419735822994489428803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5042238591055970610286949 945419735822994489428803)
            ·
              refine ⟨1418129603734491734143205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 945419735822994489428803 1418129603734491734143205)
              ·
                refine ⟨265899300700217200151851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1418129603734491734143205 265899300700217200151851)
                ·
                  refine ⟨398848951050325800227777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 265899300700217200151851 398848951050325800227777)
                  ·
                    refine ⟨299136713287744350170833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 398848951050325800227777 299136713287744350170833)
                    ·
                      refine ⟨224352534965808262628125, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 299136713287744350170833 224352534965808262628125)
                      ·
                        rfl

theorem cell23_436925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 4, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 4, 1, 4, 1, 2, 2].length) (baseStart_436925 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_436925 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_436925 prefixEnd_436925 := by exact prefixLift 436925
  have htrace : WordTrace (prefixWord ++ tailWord_436925) baseStart_436925 baseEnd_436925 := by
    simpa [prefixWord, tailWord_436925, baseEnd_436925] using wordTrace_append hprefix tailTrace_436925
  have hstable : (prefixWord ++ tailWord_436925).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_436925).length < 2 ^ (prefixWord ++ tailWord_436925).sum := by decide
  have hdescent : baseEnd_436925 < baseStart_436925 := by decide
  rcases family_descends (prefixWord ++ tailWord_436925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_436927 : List Nat := [1, 1, 2, 2, 2, 4, 1, 1, 2, 7]
def baseStart_436927 : Nat := 118140960795 + 436927 * 2 ^ 59
def prefixEnd_436927 : Nat := 4983230072969 + 3 ^ 40 * 436927 * 2
def baseEnd_436927 : Nat := 74784520642372418267705

theorem tailTrace_436927 : CollatzResearch.WordTrace tailWord_436927 prefixEnd_436927 74784520642372418267705 := by
  unfold tailWord_436927
  simp only [CollatzResearch.WordTrace]
  refine ⟨15936036888095575035813035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10624024592063716690542023 15936036888095575035813035)
  ·
    refine ⟨23904055332143362553719553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15936036888095575035813035 23904055332143362553719553)
    ·
      refine ⟨17928041499107521915289665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23904055332143362553719553 17928041499107521915289665)
      ·
        refine ⟨13446031124330641436467249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17928041499107521915289665 13446031124330641436467249)
        ·
          refine ⟨10084523343247981077350437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13446031124330641436467249 10084523343247981077350437)
          ·
            refine ⟨1890848126858996452003207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10084523343247981077350437 1890848126858996452003207)
            ·
              refine ⟨2836272190288494678004811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1890848126858996452003207 2836272190288494678004811)
              ·
                refine ⟨4254408285432742017007217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2836272190288494678004811 4254408285432742017007217)
                ·
                  refine ⟨3190806214074556512755413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4254408285432742017007217 3190806214074556512755413)
                  ·
                    refine ⟨74784520642372418267705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 3190806214074556512755413 74784520642372418267705)
                    ·
                      rfl

theorem cell23_436927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 4, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 4, 1, 1, 2, 7].length) (baseStart_436927 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_436927 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_436927 prefixEnd_436927 := by exact prefixLift 436927
  have htrace : WordTrace (prefixWord ++ tailWord_436927) baseStart_436927 baseEnd_436927 := by
    simpa [prefixWord, tailWord_436927, baseEnd_436927] using wordTrace_append hprefix tailTrace_436927
  have hstable : (prefixWord ++ tailWord_436927).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_436927).length < 2 ^ (prefixWord ++ tailWord_436927).sum := by decide
  have hdescent : baseEnd_436927 < baseStart_436927 := by decide
  rcases family_descends (prefixWord ++ tailWord_436927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_436951 : List Nat := [1, 1, 3, 2, 1, 4, 2, 1, 3, 3, 2]
def baseStart_436951 : Nat := 118140960795 + 436951 * 2 ^ 59
def prefixEnd_436951 : Nat := 4983230072969 + 3 ^ 40 * 436951 * 2
def baseEnd_436951 : Nat := 224365885462825160903005

theorem tailTrace_436951 : CollatzResearch.WordTrace tailWord_436951 prefixEnd_436951 224365885462825160903005 := by
  unfold tailWord_436951
  simp only [CollatzResearch.WordTrace]
  refine ⟨15936912240008627134686707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10624608160005751423124471 15936912240008627134686707)
  ·
    refine ⟨23905368360012940702030061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15936912240008627134686707 23905368360012940702030061)
    ·
      refine ⟨8964513135004852763261273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23905368360012940702030061 8964513135004852763261273)
      ·
        refine ⟨6723384851253639572445955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8964513135004852763261273 6723384851253639572445955)
        ·
          refine ⟨10085077276880459358668933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6723384851253639572445955 10085077276880459358668933)
          ·
            refine ⟨1890951989415086129750425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10085077276880459358668933 1890951989415086129750425)
            ·
              refine ⟨1418213992061314597312819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1890951989415086129750425 1418213992061314597312819)
              ·
                refine ⟨2127320988091971895969229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1418213992061314597312819 2127320988091971895969229)
                ·
                  refine ⟨797745370534489460988461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2127320988091971895969229 797745370534489460988461)
                  ·
                    refine ⟨299154513950433547870673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 797745370534489460988461 299154513950433547870673)
                    ·
                      refine ⟨224365885462825160903005, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 299154513950433547870673 224365885462825160903005)
                      ·
                        rfl

theorem cell23_436951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 4, 2, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 4, 2, 1, 3, 3, 2].length) (baseStart_436951 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_436951 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_436951 prefixEnd_436951 := by exact prefixLift 436951
  have htrace : WordTrace (prefixWord ++ tailWord_436951) baseStart_436951 baseEnd_436951 := by
    simpa [prefixWord, tailWord_436951, baseEnd_436951] using wordTrace_append hprefix tailTrace_436951
  have hstable : (prefixWord ++ tailWord_436951).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_436951).length < 2 ^ (prefixWord ++ tailWord_436951).sum := by decide
  have hdescent : baseEnd_436951 < baseStart_436951 := by decide
  rcases family_descends (prefixWord ++ tailWord_436951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_436974 : List Nat := [4, 1, 2, 1, 1, 3, 1, 2, 2, 6]
def baseStart_436974 : Nat := 118140960795 + 436974 * 2 ^ 59
def prefixEnd_436974 : Nat := 4983230072969 + 3 ^ 40 * 436974 * 2
def baseEnd_436974 : Nat := 74792565172626190305133

theorem tailTrace_436974 : CollatzResearch.WordTrace tailWord_436974 prefixEnd_436974 74792565172626190305133 := by
  unfold tailWord_436974
  simp only [CollatzResearch.WordTrace]
  refine ⟨1992218889865662757846747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 10625167412616868041849317 1992218889865662757846747)
  ·
    refine ⟨2988328334798494136770121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1992218889865662757846747 2988328334798494136770121)
    ·
      refine ⟨2241246251098870602577591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2988328334798494136770121 2241246251098870602577591)
      ·
        refine ⟨3361869376648305903866387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2241246251098870602577591 3361869376648305903866387)
        ·
          refine ⟨5042804064972458855799581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3361869376648305903866387 5042804064972458855799581)
          ·
            refine ⟨1891051524364672070924843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5042804064972458855799581 1891051524364672070924843)
            ·
              refine ⟨2836577286547008106387265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1891051524364672070924843 2836577286547008106387265)
              ·
                refine ⟨2127432964910256079790449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2836577286547008106387265 2127432964910256079790449)
                ·
                  refine ⟨1595574723682692059842837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2127432964910256079790449 1595574723682692059842837)
                  ·
                    refine ⟨74792565172626190305133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1595574723682692059842837 74792565172626190305133)
                    ·
                      rfl

theorem cell23_436974_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 3, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 3, 1, 2, 2, 6].length) (baseStart_436974 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_436974 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_436974 prefixEnd_436974 := by exact prefixLift 436974
  have htrace : WordTrace (prefixWord ++ tailWord_436974) baseStart_436974 baseEnd_436974 := by
    simpa [prefixWord, tailWord_436974, baseEnd_436974] using wordTrace_append hprefix tailTrace_436974
  have hstable : (prefixWord ++ tailWord_436974).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_436974).length < 2 ^ (prefixWord ++ tailWord_436974).sum := by decide
  have hdescent : baseEnd_436974 < baseStart_436974 := by decide
  rcases family_descends (prefixWord ++ tailWord_436974) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_436997 : List Nat := [1, 3, 1, 1, 2, 1, 1, 2, 1, 1, 9]
def baseStart_436997 : Nat := 118140960795 + 436997 * 2 ^ 59
def prefixEnd_436997 : Nat := 4983230072969 + 3 ^ 40 * 436997 * 2
def baseEnd_436997 : Nat := 224389505572931980927793

theorem tailTrace_436997 : CollatzResearch.WordTrace tailWord_436997 prefixEnd_436997 224389505572931980927793 := by
  unfold tailWord_436997
  simp only [CollatzResearch.WordTrace]
  refine ⟨15938589997841976990861245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10625726665227984660574163 15938589997841976990861245)
  ·
    refine ⟨5976971249190741371572967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15938589997841976990861245 5976971249190741371572967)
    ·
      refine ⟨8965456873786112057359451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5976971249190741371572967 8965456873786112057359451)
      ·
        refine ⟨13448185310679168086039177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8965456873786112057359451 13448185310679168086039177)
        ·
          refine ⟨10086138983009376064529383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13448185310679168086039177 10086138983009376064529383)
          ·
            refine ⟨15129208474514064096794075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10086138983009376064529383 15129208474514064096794075)
            ·
              refine ⟨22693812711771096145191113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15129208474514064096794075 22693812711771096145191113)
              ·
                refine ⟨17020359533828322108893335, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22693812711771096145191113 17020359533828322108893335)
                ·
                  refine ⟨25530539300742483163340003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17020359533828322108893335 25530539300742483163340003)
                  ·
                    refine ⟨38295808951113724745010005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 25530539300742483163340003 38295808951113724745010005)
                    ·
                      refine ⟨224389505572931980927793, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 38295808951113724745010005 224389505572931980927793)
                      ·
                        rfl

theorem cell23_436997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 1, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 1, 2, 1, 1, 9].length) (baseStart_436997 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_436997 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_436997 prefixEnd_436997 := by exact prefixLift 436997
  have htrace : WordTrace (prefixWord ++ tailWord_436997) baseStart_436997 baseEnd_436997 := by
    simpa [prefixWord, tailWord_436997, baseEnd_436997] using wordTrace_append hprefix tailTrace_436997
  have hstable : (prefixWord ++ tailWord_436997).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_436997).length < 2 ^ (prefixWord ++ tailWord_436997).sum := by decide
  have hdescent : baseEnd_436997 < baseStart_436997 := by decide
  rcases family_descends (prefixWord ++ tailWord_436997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_437038 : List Nat := [4, 1, 3, 2, 1, 3, 1, 1, 7]
def baseStart_437038 : Nat := 118140960795 + 437038 * 2 ^ 59
def prefixEnd_437038 : Nat := 4983230072969 + 3 ^ 40 * 437038 * 2
def baseEnd_437038 : Nat := 24934506475529591168345

theorem tailTrace_437038 : CollatzResearch.WordTrace tailWord_437038 prefixEnd_437038 24934506475529591168345 := by
  unfold tailWord_437038
  simp only [CollatzResearch.WordTrace]
  refine ⟨1992510673836680124137971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 10626723593795627328735845 1992510673836680124137971)
  ·
    refine ⟨2988766010755020186206957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1992510673836680124137971 2988766010755020186206957)
    ·
      refine ⟨1120787254033132569827609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2988766010755020186206957 1120787254033132569827609)
      ·
        refine ⟨840590440524849427370707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1120787254033132569827609 840590440524849427370707)
        ·
          refine ⟨1260885660787274141056061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 840590440524849427370707 1260885660787274141056061)
          ·
            refine ⟨472832122795227802896023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1260885660787274141056061 472832122795227802896023)
            ·
              refine ⟨709248184192841704344035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 472832122795227802896023 709248184192841704344035)
              ·
                refine ⟨1063872276289262556516053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 709248184192841704344035 1063872276289262556516053)
                ·
                  refine ⟨24934506475529591168345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1063872276289262556516053 24934506475529591168345)
                  ·
                    rfl

theorem cell23_437038_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 3, 1, 1, 7].length) (baseStart_437038 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_437038 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_437038 prefixEnd_437038 := by exact prefixLift 437038
  have htrace : WordTrace (prefixWord ++ tailWord_437038) baseStart_437038 baseEnd_437038 := by
    simpa [prefixWord, tailWord_437038, baseEnd_437038] using wordTrace_append hprefix tailTrace_437038
  have hstable : (prefixWord ++ tailWord_437038).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_437038).length < 2 ^ (prefixWord ++ tailWord_437038).sum := by decide
  have hdescent : baseEnd_437038 < baseStart_437038 := by decide
  rcases family_descends (prefixWord ++ tailWord_437038) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_437041 : List Nat := [1, 2, 2, 3, 2, 1, 2, 1, 2, 5, 2]
def baseStart_437041 : Nat := 118140960795 + 437041 * 2 ^ 59
def prefixEnd_437041 : Nat := 4983230072969 + 3 ^ 40 * 437041 * 2
def baseEnd_437041 : Nat := 224412098721729808777591

theorem tailTrace_437041 : CollatzResearch.WordTrace tailWord_437041 prefixEnd_437041 224412098721729808777591 := by
  unfold tailWord_437041
  simp only [CollatzResearch.WordTrace]
  refine ⟨15940194809682572505462977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10626796539788381670308651 15940194809682572505462977)
  ·
    refine ⟨11955146107261929379097233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15940194809682572505462977 11955146107261929379097233)
    ·
      refine ⟨8966359580446447034322925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11955146107261929379097233 8966359580446447034322925)
      ·
        refine ⟨3362384842667417637871097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8966359580446447034322925 3362384842667417637871097)
        ·
          refine ⟨2521788632000563228403323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3362384842667417637871097 2521788632000563228403323)
          ·
            refine ⟨3782682948000844842604985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2521788632000563228403323 3782682948000844842604985)
            ·
              refine ⟨2837012211000633631953739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3782682948000844842604985 2837012211000633631953739)
              ·
                refine ⟨4255518316500950447930609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2837012211000633631953739 4255518316500950447930609)
                ·
                  refine ⟨3191638737375712835947957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4255518316500950447930609 3191638737375712835947957)
                  ·
                    refine ⟨299216131628973078370121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3191638737375712835947957 299216131628973078370121)
                    ·
                      refine ⟨224412098721729808777591, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 299216131628973078370121 224412098721729808777591)
                      ·
                        rfl

theorem cell23_437041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 2, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 2, 1, 2, 5, 2].length) (baseStart_437041 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_437041 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_437041 prefixEnd_437041 := by exact prefixLift 437041
  have htrace : WordTrace (prefixWord ++ tailWord_437041) baseStart_437041 baseEnd_437041 := by
    simpa [prefixWord, tailWord_437041, baseEnd_437041] using wordTrace_append hprefix tailTrace_437041
  have hstable : (prefixWord ++ tailWord_437041).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_437041).length < 2 ^ (prefixWord ++ tailWord_437041).sum := by decide
  have hdescent : baseEnd_437041 < baseStart_437041 := by decide
  rcases family_descends (prefixWord ++ tailWord_437041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_437155 : List Nat := [1, 1, 1, 4, 1, 2, 4, 4, 1, 1, 3]
def baseStart_437155 : Nat := 118140960795 + 437155 * 2 ^ 59
def prefixEnd_437155 : Nat := 4983230072969 + 3 ^ 40 * 437155 * 2
def baseEnd_437155 : Nat := 224470635516342362752067

theorem tailTrace_437155 : CollatzResearch.WordTrace tailWord_437155 prefixEnd_437155 224470635516342362752067 := by
  unfold tailWord_437155
  simp only [CollatzResearch.WordTrace]
  refine ⟨15944352731269569975112919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10629568487513046650075279 15944352731269569975112919)
  ·
    refine ⟨23916529096904354962669379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15944352731269569975112919 23916529096904354962669379)
    ·
      refine ⟨35874793645356532444004069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23916529096904354962669379 35874793645356532444004069)
      ·
        refine ⟨6726523808504349833250763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 35874793645356532444004069 6726523808504349833250763)
        ·
          refine ⟨10089785712756524749876145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6726523808504349833250763 10089785712756524749876145)
          ·
            refine ⟨7567339284567393562407109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10089785712756524749876145 7567339284567393562407109)
            ·
              refine ⟨1418876115856386292951333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7567339284567393562407109 1418876115856386292951333)
              ·
                refine ⟨266039271723072429928375, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1418876115856386292951333 266039271723072429928375)
                ·
                  refine ⟨399058907584608644892563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 266039271723072429928375 399058907584608644892563)
                  ·
                    refine ⟨598588361376912967338845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 399058907584608644892563 598588361376912967338845)
                    ·
                      refine ⟨224470635516342362752067, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 598588361376912967338845 224470635516342362752067)
                      ·
                        rfl

theorem cell23_437155_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 4, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 4, 4, 1, 1, 3].length) (baseStart_437155 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_437155 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_437155 prefixEnd_437155 := by exact prefixLift 437155
  have htrace : WordTrace (prefixWord ++ tailWord_437155) baseStart_437155 baseEnd_437155 := by
    simpa [prefixWord, tailWord_437155, baseEnd_437155] using wordTrace_append hprefix tailTrace_437155
  have hstable : (prefixWord ++ tailWord_437155).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_437155).length < 2 ^ (prefixWord ++ tailWord_437155).sum := by decide
  have hdescent : baseEnd_437155 < baseStart_437155 := by decide
  rcases family_descends (prefixWord ++ tailWord_437155) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_437172 : List Nat := [2, 5, 2, 1, 1, 1, 2, 2, 3, 1, 3]
def baseStart_437172 : Nat := 118140960795 + 437172 * 2 ^ 59
def prefixEnd_437172 : Nat := 4983230072969 + 3 ^ 40 * 437172 * 2
def baseEnd_437172 : Nat := 224479364687468796239489

theorem tailTrace_437172 : CollatzResearch.WordTrace tailWord_437172 prefixEnd_437172 224479364687468796239489 := by
  unfold tailWord_437172
  simp only [CollatzResearch.WordTrace]
  refine ⟨7972486386103990939240885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10629981848138654585654513 7972486386103990939240885)
  ·
    refine ⟨747420598697249150553833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 7972486386103990939240885 747420598697249150553833)
    ·
      refine ⟨560565449022936862915375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 747420598697249150553833 560565449022936862915375)
      ·
        refine ⟨840848173534405294373063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 560565449022936862915375 840848173534405294373063)
        ·
          refine ⟨1261272260301607941559595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 840848173534405294373063 1261272260301607941559595)
          ·
            refine ⟨1891908390452411912339393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1261272260301607941559595 1891908390452411912339393)
            ·
              refine ⟨1418931292839308934254545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1891908390452411912339393 1418931292839308934254545)
              ·
                refine ⟨1064198469629481700690909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1418931292839308934254545 1064198469629481700690909)
                ·
                  refine ⟨399074426111055637759091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1064198469629481700690909 399074426111055637759091)
                  ·
                    refine ⟨598611639166583456638637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 399074426111055637759091 598611639166583456638637)
                    ·
                      refine ⟨224479364687468796239489, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 598611639166583456638637 224479364687468796239489)
                      ·
                        rfl

theorem cell23_437172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 1, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 1, 2, 2, 3, 1, 3].length) (baseStart_437172 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_437172 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_437172 prefixEnd_437172 := by exact prefixLift 437172
  have htrace : WordTrace (prefixWord ++ tailWord_437172) baseStart_437172 baseEnd_437172 := by
    simpa [prefixWord, tailWord_437172, baseEnd_437172] using wordTrace_append hprefix tailTrace_437172
  have hstable : (prefixWord ++ tailWord_437172).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_437172).length < 2 ^ (prefixWord ++ tailWord_437172).sum := by decide
  have hdescent : baseEnd_437172 < baseStart_437172 := by decide
  rcases family_descends (prefixWord ++ tailWord_437172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_437178 : List Nat := [3, 1, 1, 1, 2, 1, 6, 2, 1, 1, 4]
def baseStart_437178 : Nat := 118140960795 + 437178 * 2 ^ 59
def prefixEnd_437178 : Nat := 4983230072969 + 3 ^ 40 * 437178 * 2
def baseEnd_437178 : Nat := 224482445571395772764461

theorem tailTrace_437178 : CollatzResearch.WordTrace tailWord_437178 prefixEnd_437178 224482445571395772764461 := by
  unfold tailWord_437178
  simp only [CollatzResearch.WordTrace]
  refine ⟨3986297902546561225800047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10630127740124163268800125 3986297902546561225800047)
  ·
    refine ⟨5979446853819841838700071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3986297902546561225800047 5979446853819841838700071)
    ·
      refine ⟨8969170280729762758050107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5979446853819841838700071 8969170280729762758050107)
      ·
        refine ⟨13453755421094644137075161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8969170280729762758050107 13453755421094644137075161)
        ·
          refine ⟨10090316565820983102806371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13453755421094644137075161 10090316565820983102806371)
          ·
            refine ⟨15135474848731474654209557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10090316565820983102806371 15135474848731474654209557)
            ·
              refine ⟨709475383534287874416073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 15135474848731474654209557 709475383534287874416073)
              ·
                refine ⟨532106537650715905812055, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 709475383534287874416073 532106537650715905812055)
                ·
                  refine ⟨798159806476073858718083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 532106537650715905812055 798159806476073858718083)
                  ·
                    refine ⟨1197239709714110788077125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 798159806476073858718083 1197239709714110788077125)
                    ·
                      refine ⟨224482445571395772764461, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1197239709714110788077125 224482445571395772764461)
                      ·
                        rfl

theorem cell23_437178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 6, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 6, 2, 1, 1, 4].length) (baseStart_437178 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_437178 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_437178 prefixEnd_437178 := by exact prefixLift 437178
  have htrace : WordTrace (prefixWord ++ tailWord_437178) baseStart_437178 baseEnd_437178 := by
    simpa [prefixWord, tailWord_437178, baseEnd_437178] using wordTrace_append hprefix tailTrace_437178
  have hstable : (prefixWord ++ tailWord_437178).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_437178).length < 2 ^ (prefixWord ++ tailWord_437178).sum := by decide
  have hdescent : baseEnd_437178 < baseStart_437178 := by decide
  rcases family_descends (prefixWord ++ tailWord_437178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_437191 : List Nat := [1, 1, 4, 1, 1, 2, 2, 4, 1, 2, 4]
def baseStart_437191 : Nat := 118140960795 + 437191 * 2 ^ 59
def prefixEnd_437191 : Nat := 4983230072969 + 3 ^ 40 * 437191 * 2
def baseEnd_437191 : Nat := 224489120819904221901901

theorem tailTrace_437191 : CollatzResearch.WordTrace tailWord_437191 prefixEnd_437191 224489120819904221901901 := by
  unfold tailWord_437191
  simp only [CollatzResearch.WordTrace]
  refine ⟨15945665759139148123423427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10630443839426098748948951 15945665759139148123423427)
  ·
    refine ⟨23918498638708722185135141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15945665759139148123423427 23918498638708722185135141)
    ·
      refine ⟨4484718494757885409712839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 23918498638708722185135141 4484718494757885409712839)
      ·
        refine ⟨6727077742136828114569259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4484718494757885409712839 6727077742136828114569259)
        ·
          refine ⟨10090616613205242171853889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6727077742136828114569259 10090616613205242171853889)
          ·
            refine ⟨7567962459903931628890417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10090616613205242171853889 7567962459903931628890417)
            ·
              refine ⟨5675971844927948721667813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7567962459903931628890417 5675971844927948721667813)
              ·
                refine ⟨1064244720923990385312715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5675971844927948721667813 1064244720923990385312715)
                ·
                  refine ⟨1596367081385985577969073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1064244720923990385312715 1596367081385985577969073)
                  ·
                    refine ⟨1197275311039489183476805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1596367081385985577969073 1197275311039489183476805)
                    ·
                      refine ⟨224489120819904221901901, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1197275311039489183476805 224489120819904221901901)
                      ·
                        rfl

theorem cell23_437191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 2, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 2, 4, 1, 2, 4].length) (baseStart_437191 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_437191 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_437191 prefixEnd_437191 := by exact prefixLift 437191
  have htrace : WordTrace (prefixWord ++ tailWord_437191) baseStart_437191 baseEnd_437191 := by
    simpa [prefixWord, tailWord_437191, baseEnd_437191] using wordTrace_append hprefix tailTrace_437191
  have hstable : (prefixWord ++ tailWord_437191).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_437191).length < 2 ^ (prefixWord ++ tailWord_437191).sum := by decide
  have hdescent : baseEnd_437191 < baseStart_437191 := by decide
  rcases family_descends (prefixWord ++ tailWord_437191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_437198 : List Nat := [4, 1, 1, 1, 2, 4, 2, 1, 1, 1, 5]
def baseStart_437198 : Nat := 118140960795 + 437198 * 2 ^ 59
def prefixEnd_437198 : Nat := 4983230072969 + 3 ^ 40 * 437198 * 2
def baseEnd_437198 : Nat := 224492715184485694514369

theorem tailTrace_437198 : CollatzResearch.WordTrace tailWord_437198 prefixEnd_437198 224492715184485694514369 := by
  unfold tailWord_437198
  simp only [CollatzResearch.WordTrace]
  refine ⟨1993240133764223539866031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 10630614046742525545952165 1993240133764223539866031)
  ·
    refine ⟨2989860200646335309799047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1993240133764223539866031 2989860200646335309799047)
    ·
      refine ⟨4484790300969502964698571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2989860200646335309799047 4484790300969502964698571)
      ·
        refine ⟨6727185451454254447047857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4484790300969502964698571 6727185451454254447047857)
        ·
          refine ⟨5045389088590690835285893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6727185451454254447047857 5045389088590690835285893)
          ·
            refine ⟨946010454110754531616105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5045389088590690835285893 946010454110754531616105)
            ·
              refine ⟨709507840583065898712079, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 946010454110754531616105 709507840583065898712079)
              ·
                refine ⟨1064261760874598848068119, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 709507840583065898712079 1064261760874598848068119)
                ·
                  refine ⟨1596392641311898272102179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1064261760874598848068119 1596392641311898272102179)
                  ·
                    refine ⟨2394588961967847408153269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1596392641311898272102179 2394588961967847408153269)
                    ·
                      refine ⟨224492715184485694514369, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 2394588961967847408153269 224492715184485694514369)
                      ·
                        rfl

theorem cell23_437198_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 4, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 4, 2, 1, 1, 1, 5].length) (baseStart_437198 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_437198 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_437198 prefixEnd_437198 := by exact prefixLift 437198
  have htrace : WordTrace (prefixWord ++ tailWord_437198) baseStart_437198 baseEnd_437198 := by
    simpa [prefixWord, tailWord_437198, baseEnd_437198] using wordTrace_append hprefix tailTrace_437198
  have hstable : (prefixWord ++ tailWord_437198).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_437198).length < 2 ^ (prefixWord ++ tailWord_437198).sum := by decide
  have hdescent : baseEnd_437198 < baseStart_437198 := by decide
  rcases family_descends (prefixWord ++ tailWord_437198) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_437206 : List Nat := [5, 2, 1, 1, 2, 2, 3, 2, 1, 1, 3]
def baseStart_437206 : Nat := 118140960795 + 437206 * 2 ^ 59
def prefixEnd_437206 : Nat := 4983230072969 + 3 ^ 40 * 437206 * 2
def baseEnd_437206 : Nat := 224496823029721663214333

theorem tailTrace_437206 : CollatzResearch.WordTrace tailWord_437206 prefixEnd_437206 224496823029721663214333 := by
  unfold tailWord_437206
  simp only [CollatzResearch.WordTrace]
  refine ⟨996638303380300355326217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 10630808569389870456812981 996638303380300355326217)
  ·
    refine ⟨747478727535225266494663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 996638303380300355326217 747478727535225266494663)
    ·
      refine ⟨1121218091302837899741995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 747478727535225266494663 1121218091302837899741995)
      ·
        refine ⟨1681827136954256849612993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1121218091302837899741995 1681827136954256849612993)
        ·
          refine ⟨1261370352715692637209745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1681827136954256849612993 1261370352715692637209745)
          ·
            refine ⟨946027764536769477907309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1261370352715692637209745 946027764536769477907309)
            ·
              refine ⟨354760411701288554215241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 946027764536769477907309 354760411701288554215241)
              ·
                refine ⟨266070308775966415661431, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 354760411701288554215241 266070308775966415661431)
                ·
                  refine ⟨399105463163949623492147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 266070308775966415661431 399105463163949623492147)
                  ·
                    refine ⟨598658194745924435238221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 399105463163949623492147 598658194745924435238221)
                    ·
                      refine ⟨224496823029721663214333, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 598658194745924435238221 224496823029721663214333)
                      ·
                        rfl

theorem cell23_437206_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 2, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 2, 3, 2, 1, 1, 3].length) (baseStart_437206 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_437206 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_437206 prefixEnd_437206 := by exact prefixLift 437206
  have htrace : WordTrace (prefixWord ++ tailWord_437206) baseStart_437206 baseEnd_437206 := by
    simpa [prefixWord, tailWord_437206, baseEnd_437206] using wordTrace_append hprefix tailTrace_437206
  have hstable : (prefixWord ++ tailWord_437206).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_437206).length < 2 ^ (prefixWord ++ tailWord_437206).sum := by decide
  have hdescent : baseEnd_437206 < baseStart_437206 := by decide
  rcases family_descends (prefixWord ++ tailWord_437206) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_437218 : List Nat := [3, 3, 3, 1, 1, 1, 1, 10]
def baseStart_437218 : Nat := 118140960795 + 437218 * 2 ^ 59
def prefixEnd_437218 : Nat := 4983230072969 + 3 ^ 40 * 437218 * 2
def baseEnd_437218 : Nat := 8314925362873170972751

theorem tailTrace_437218 : CollatzResearch.WordTrace tailWord_437218 prefixEnd_437218 8314925362873170972751 := by
  unfold tailWord_437218
  simp only [CollatzResearch.WordTrace]
  refine ⟨3986662632510332933664077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10631100353360887823104205 3986662632510332933664077)
  ·
    refine ⟨1494998487191374850124029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3986662632510332933664077 1494998487191374850124029)
    ·
      refine ⟨560624432696765568796511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1494998487191374850124029 560624432696765568796511)
      ·
        refine ⟨840936649045148353194767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 560624432696765568796511 840936649045148353194767)
        ·
          refine ⟨1261404973567722529792151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 840936649045148353194767 1261404973567722529792151)
          ·
            refine ⟨1892107460351583794688227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1261404973567722529792151 1892107460351583794688227)
            ·
              refine ⟨2838161190527375692032341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1892107460351583794688227 2838161190527375692032341)
              ·
                refine ⟨8314925362873170972751, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 2838161190527375692032341 8314925362873170972751)
                ·
                  rfl

theorem cell23_437218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 1, 1, 10].length) (baseStart_437218 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_437218 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_437218 prefixEnd_437218 := by exact prefixLift 437218
  have htrace : WordTrace (prefixWord ++ tailWord_437218) baseStart_437218 baseEnd_437218 := by
    simpa [prefixWord, tailWord_437218, baseEnd_437218] using wordTrace_append hprefix tailTrace_437218
  have hstable : (prefixWord ++ tailWord_437218).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_437218).length < 2 ^ (prefixWord ++ tailWord_437218).sum := by decide
  have hdescent : baseEnd_437218 < baseStart_437218 := by decide
  rcases family_descends (prefixWord ++ tailWord_437218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_437262 : List Nat := [4, 1, 1, 2, 2, 3, 2, 2, 2, 1, 3]
def baseStart_437262 : Nat := 118140960795 + 437262 * 2 ^ 59
def prefixEnd_437262 : Nat := 4983230072969 + 3 ^ 40 * 437262 * 2
def baseEnd_437262 : Nat := 224525577946373444114075

theorem tailTrace_437262 : CollatzResearch.WordTrace tailWord_437262 prefixEnd_437262 224525577946373444114075 := by
  unfold tailWord_437262
  simp only [CollatzResearch.WordTrace]
  refine ⟨1993531917735240906157255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 10632170227921284832838693 1993531917735240906157255)
  ·
    refine ⟨2990297876602861359235883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1993531917735240906157255 2990297876602861359235883)
    ·
      refine ⟨4485446814904292038853825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2990297876602861359235883 4485446814904292038853825)
      ·
        refine ⟨3364085111178219029140369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4485446814904292038853825 3364085111178219029140369)
        ·
          refine ⟨2523063833383664271855277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3364085111178219029140369 2523063833383664271855277)
          ·
            refine ⟨946148937518874101945729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2523063833383664271855277 946148937518874101945729)
            ·
              refine ⟨709611703139155576459297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 946148937518874101945729 709611703139155576459297)
              ·
                refine ⟨532208777354366682344473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 709611703139155576459297 532208777354366682344473)
                ·
                  refine ⟨399156583015775011758355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 532208777354366682344473 399156583015775011758355)
                  ·
                    refine ⟨598734874523662517637533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 399156583015775011758355 598734874523662517637533)
                    ·
                      refine ⟨224525577946373444114075, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 598734874523662517637533 224525577946373444114075)
                      ·
                        rfl

theorem cell23_437262_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 3, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 3, 2, 2, 2, 1, 3].length) (baseStart_437262 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_437262 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_437262 prefixEnd_437262 := by exact prefixLift 437262
  have htrace : WordTrace (prefixWord ++ tailWord_437262) baseStart_437262 baseEnd_437262 := by
    simpa [prefixWord, tailWord_437262, baseEnd_437262] using wordTrace_append hprefix tailTrace_437262
  have hstable : (prefixWord ++ tailWord_437262).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_437262).length < 2 ^ (prefixWord ++ tailWord_437262).sum := by decide
  have hdescent : baseEnd_437262 < baseStart_437262 := by decide
  rcases family_descends (prefixWord ++ tailWord_437262) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_437285 : List Nat := [1, 3, 1, 2, 2, 2, 4, 1, 1, 4, 2]
def baseStart_437285 : Nat := 118140960795 + 437285 * 2 ^ 59
def prefixEnd_437285 : Nat := 4983230072969 + 3 ^ 40 * 437285 * 2
def baseEnd_437285 : Nat := 224537388001426854126469

theorem tailTrace_437285 : CollatzResearch.WordTrace tailWord_437285 prefixEnd_437285 224537388001426854126469 := by
  unfold tailWord_437285
  simp only [CollatzResearch.WordTrace]
  refine ⟨15949094220798602177345309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10632729480532401451563539 15949094220798602177345309)
  ·
    refine ⟨5980910332799475816504491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15949094220798602177345309 5980910332799475816504491)
    ·
      refine ⟨8971365499199213724756737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5980910332799475816504491 8971365499199213724756737)
      ·
        refine ⟨6728524124399410293567553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8971365499199213724756737 6728524124399410293567553)
        ·
          refine ⟨5046393093299557720175665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6728524124399410293567553 5046393093299557720175665)
          ·
            refine ⟨3784794819974668290131749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5046393093299557720175665 3784794819974668290131749)
            ·
              refine ⟨709649028745250304399703, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3784794819974668290131749 709649028745250304399703)
              ·
                refine ⟨1064473543117875456599555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 709649028745250304399703 1064473543117875456599555)
                ·
                  refine ⟨1596710314676813184899333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1064473543117875456599555 1596710314676813184899333)
                  ·
                    refine ⟨299383184001902472168625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1596710314676813184899333 299383184001902472168625)
                    ·
                      refine ⟨224537388001426854126469, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 299383184001902472168625 224537388001426854126469)
                      ·
                        rfl

theorem cell23_437285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 4, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 4, 1, 1, 4, 2].length) (baseStart_437285 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_437285 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_437285 prefixEnd_437285 := by exact prefixLift 437285
  have htrace : WordTrace (prefixWord ++ tailWord_437285) baseStart_437285 baseEnd_437285 := by
    simpa [prefixWord, tailWord_437285, baseEnd_437285] using wordTrace_append hprefix tailTrace_437285
  have hstable : (prefixWord ++ tailWord_437285).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_437285).length < 2 ^ (prefixWord ++ tailWord_437285).sum := by decide
  have hdescent : baseEnd_437285 < baseStart_437285 := by decide
  rcases family_descends (prefixWord ++ tailWord_437285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_437291 : List Nat := [1, 1, 1, 1, 2, 1, 7, 2, 7]
def baseStart_437291 : Nat := 118140960795 + 437291 * 2 ^ 59
def prefixEnd_437291 : Nat := 4983230072969 + 3 ^ 40 * 437291 * 2
def baseEnd_437291 : Nat := 24948940987261536739049

theorem tailTrace_437291 : CollatzResearch.WordTrace tailWord_437291 prefixEnd_437291 24948940987261536739049 := by
  unfold tailWord_437291
  simp only [CollatzResearch.WordTrace]
  refine ⟨15949313058776865202063727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10632875372517910134709151 15949313058776865202063727)
  ·
    refine ⟨23923969588165297803095591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15949313058776865202063727 23923969588165297803095591)
    ·
      refine ⟨35885954382247946704643387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23923969588165297803095591 35885954382247946704643387)
      ·
        refine ⟨53828931573371920056965081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35885954382247946704643387 53828931573371920056965081)
        ·
          refine ⟨40371698680028940042723811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53828931573371920056965081 40371698680028940042723811)
          ·
            refine ⟨60557548020043410064085717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40371698680028940042723811 60557548020043410064085717)
            ·
              refine ⟨1419317531719767423377009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 60557548020043410064085717 1419317531719767423377009)
              ·
                refine ⟨1064488148789825567532757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1419317531719767423377009 1064488148789825567532757)
                ·
                  refine ⟨24948940987261536739049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1064488148789825567532757 24948940987261536739049)
                  ·
                    rfl

theorem cell23_437291_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 7, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 7, 2, 7].length) (baseStart_437291 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_437291 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_437291 prefixEnd_437291 := by exact prefixLift 437291
  have htrace : WordTrace (prefixWord ++ tailWord_437291) baseStart_437291 baseEnd_437291 := by
    simpa [prefixWord, tailWord_437291, baseEnd_437291] using wordTrace_append hprefix tailTrace_437291
  have hstable : (prefixWord ++ tailWord_437291).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_437291).length < 2 ^ (prefixWord ++ tailWord_437291).sum := by decide
  have hdescent : baseEnd_437291 < baseStart_437291 := by decide
  rcases family_descends (prefixWord ++ tailWord_437291) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_437301 : List Nat := [1, 3, 3, 1, 1, 1, 1, 2, 1, 2, 7]
def baseStart_437301 : Nat := 118140960795 + 437301 * 2 ^ 59
def prefixEnd_437301 : Nat := 4983230072969 + 3 ^ 40 * 437301 * 2
def baseEnd_437301 : Nat := 224545603691898791526395

theorem tailTrace_437301 : CollatzResearch.WordTrace tailWord_437301 prefixEnd_437301 224545603691898791526395 := by
  unfold tailWord_437301
  simp only [CollatzResearch.WordTrace]
  refine ⟨15949677788740636909927757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10633118525827091273285171 15949677788740636909927757)
  ·
    refine ⟨5981129170777738841222909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15949677788740636909927757 5981129170777738841222909)
    ·
      refine ⟨2242923439041652065458591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5981129170777738841222909 2242923439041652065458591)
      ·
        refine ⟨3364385158562478098187887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2242923439041652065458591 3364385158562478098187887)
        ·
          refine ⟨5046577737843717147281831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3364385158562478098187887 5046577737843717147281831)
          ·
            refine ⟨7569866606765575720922747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5046577737843717147281831 7569866606765575720922747)
            ·
              refine ⟨11354799910148363581384121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7569866606765575720922747 11354799910148363581384121)
              ·
                refine ⟨8516099932611272686038091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11354799910148363581384121 8516099932611272686038091)
                ·
                  refine ⟨12774149898916909029057137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8516099932611272686038091 12774149898916909029057137)
                  ·
                    refine ⟨9580612424187681771792853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12774149898916909029057137 9580612424187681771792853)
                    ·
                      refine ⟨224545603691898791526395, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 9580612424187681771792853 224545603691898791526395)
                      ·
                        rfl

theorem cell23_437301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 1, 2, 1, 2, 7].length) (baseStart_437301 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_437301 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_437301 prefixEnd_437301 := by exact prefixLift 437301
  have htrace : WordTrace (prefixWord ++ tailWord_437301) baseStart_437301 baseEnd_437301 := by
    simpa [prefixWord, tailWord_437301, baseEnd_437301] using wordTrace_append hprefix tailTrace_437301
  have hstable : (prefixWord ++ tailWord_437301).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_437301).length < 2 ^ (prefixWord ++ tailWord_437301).sum := by decide
  have hdescent : baseEnd_437301 < baseStart_437301 := by decide
  rcases family_descends (prefixWord ++ tailWord_437301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_437302 : List Nat := [5, 1, 2, 1, 1, 2, 2, 2, 1, 4, 2]
def baseStart_437302 : Nat := 118140960795 + 437302 * 2 ^ 59
def prefixEnd_437302 : Nat := 4983230072969 + 3 ^ 40 * 437302 * 2
def baseEnd_437302 : Nat := 224546117172553287613891

theorem tailTrace_437302 : CollatzResearch.WordTrace tailWord_437302 prefixEnd_437302 224546117172553287613891 := by
  unfold tailWord_437302
  simp only [CollatzResearch.WordTrace]
  refine ⟨996857141358563380044635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 10633142841158009387142773 996857141358563380044635)
  ·
    refine ⟨1495285712037845070066953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 996857141358563380044635 1495285712037845070066953)
    ·
      refine ⟨1121464284028383802550215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1495285712037845070066953 1121464284028383802550215)
      ·
        refine ⟨1682196426042575703825323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1121464284028383802550215 1682196426042575703825323)
        ·
          refine ⟨2523294639063863555737985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1682196426042575703825323 2523294639063863555737985)
          ·
            refine ⟨1892470979297897666803489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2523294639063863555737985 1892470979297897666803489)
            ·
              refine ⟨1419353234473423250102617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1892470979297897666803489 1419353234473423250102617)
              ·
                refine ⟨1064514925855067437576963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1419353234473423250102617 1064514925855067437576963)
                ·
                  refine ⟨1596772388782601156365445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1064514925855067437576963 1596772388782601156365445)
                  ·
                    refine ⟨299394822896737716818521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1596772388782601156365445 299394822896737716818521)
                    ·
                      refine ⟨224546117172553287613891, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 299394822896737716818521 224546117172553287613891)
                      ·
                        rfl

theorem cell23_437302_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 2, 2, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 2, 2, 2, 1, 4, 2].length) (baseStart_437302 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_437302 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_437302 prefixEnd_437302 := by exact prefixLift 437302
  have htrace : WordTrace (prefixWord ++ tailWord_437302) baseStart_437302 baseEnd_437302 := by
    simpa [prefixWord, tailWord_437302, baseEnd_437302] using wordTrace_append hprefix tailTrace_437302
  have hstable : (prefixWord ++ tailWord_437302).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_437302).length < 2 ^ (prefixWord ++ tailWord_437302).sum := by decide
  have hdescent : baseEnd_437302 < baseStart_437302 := by decide
  rcases family_descends (prefixWord ++ tailWord_437302) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_437319 : List Nat := [1, 1, 4, 1, 3, 4, 1, 2, 2, 2, 2]
def baseStart_437319 : Nat := 118140960795 + 437319 * 2 ^ 59
def prefixEnd_437319 : Nat := 4983230072969 + 3 ^ 40 * 437319 * 2
def baseEnd_437319 : Nat := 224554846343679721101313

theorem tailTrace_437319 : CollatzResearch.WordTrace tailWord_437319 prefixEnd_437319 224554846343679721101313 := by
  unfold tailWord_437319
  simp only [CollatzResearch.WordTrace]
  refine ⟨15950334302675425984083011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10633556201783617322722007 15950334302675425984083011)
  ·
    refine ⟨23925501454013138976124517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15950334302675425984083011 23925501454013138976124517)
    ·
      refine ⟨4486031522627463558023347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 23925501454013138976124517 4486031522627463558023347)
      ·
        refine ⟨6729047283941195337035021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4486031522627463558023347 6729047283941195337035021)
        ·
          refine ⟨2523392731477948251388133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6729047283941195337035021 2523392731477948251388133)
          ·
            refine ⟨473136137152115297135275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2523392731477948251388133 473136137152115297135275)
            ·
              refine ⟨709704205728172945702913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 473136137152115297135275 709704205728172945702913)
              ·
                refine ⟨532278154296129709277185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 709704205728172945702913 532278154296129709277185)
                ·
                  refine ⟨399208615722097281957889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 532278154296129709277185 399208615722097281957889)
                  ·
                    refine ⟨299406461791572961468417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 399208615722097281957889 299406461791572961468417)
                    ·
                      refine ⟨224554846343679721101313, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 299406461791572961468417 224554846343679721101313)
                      ·
                        rfl

theorem cell23_437319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 4, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 4, 1, 2, 2, 2, 2].length) (baseStart_437319 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_437319 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_437319 prefixEnd_437319 := by exact prefixLift 437319
  have htrace : WordTrace (prefixWord ++ tailWord_437319) baseStart_437319 baseEnd_437319 := by
    simpa [prefixWord, tailWord_437319, baseEnd_437319] using wordTrace_append hprefix tailTrace_437319
  have hstable : (prefixWord ++ tailWord_437319).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_437319).length < 2 ^ (prefixWord ++ tailWord_437319).sum := by decide
  have hdescent : baseEnd_437319 < baseStart_437319 := by decide
  rcases family_descends (prefixWord ++ tailWord_437319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_437325 : List Nat := [1, 6, 1, 1, 1, 3, 2, 1, 7]
def baseStart_437325 : Nat := 118140960795 + 437325 * 2 ^ 59
def prefixEnd_437325 : Nat := 4983230072969 + 3 ^ 40 * 437325 * 2
def baseEnd_437325 : Nat := 24950880803067410847365

theorem tailTrace_437325 : CollatzResearch.WordTrace tailWord_437325 prefixEnd_437325 24950880803067410847365 := by
  unfold tailWord_437325
  simp only [CollatzResearch.WordTrace]
  refine ⟨15950553140653689008801429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10633702093769126005867619 15950553140653689008801429)
  ·
    refine ⟨747682178468141672287567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 15950553140653689008801429 747682178468141672287567)
    ·
      refine ⟨1121523267702212508431351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 747682178468141672287567 1121523267702212508431351)
      ·
        refine ⟨1682284901553318762647027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1121523267702212508431351 1682284901553318762647027)
        ·
          refine ⟨2523427352329978143970541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1682284901553318762647027 2523427352329978143970541)
          ·
            refine ⟨946285257123741803988953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2523427352329978143970541 946285257123741803988953)
            ·
              refine ⟨709713942842806352991715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 946285257123741803988953 709713942842806352991715)
              ·
                refine ⟨1064570914264209529487573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 709713942842806352991715 1064570914264209529487573)
                ·
                  refine ⟨24950880803067410847365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1064570914264209529487573 24950880803067410847365)
                  ·
                    rfl

theorem cell23_437325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 3, 2, 1, 7].length) (baseStart_437325 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_437325 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_437325 prefixEnd_437325 := by exact prefixLift 437325
  have htrace : WordTrace (prefixWord ++ tailWord_437325) baseStart_437325 baseEnd_437325 := by
    simpa [prefixWord, tailWord_437325, baseEnd_437325] using wordTrace_append hprefix tailTrace_437325
  have hstable : (prefixWord ++ tailWord_437325).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_437325).length < 2 ^ (prefixWord ++ tailWord_437325).sum := by decide
  have hdescent : baseEnd_437325 < baseStart_437325 := by decide
  rcases family_descends (prefixWord ++ tailWord_437325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_437328 : List Nat := [2, 1, 1, 1, 1, 3, 1, 3, 1, 7, 2]
def baseStart_437328 : Nat := 118140960795 + 437328 * 2 ^ 59
def prefixEnd_437328 : Nat := 4983230072969 + 3 ^ 40 * 437328 * 2
def baseEnd_437328 : Nat := 224559467669570185888771

theorem tailTrace_437328 : CollatzResearch.WordTrace tailWord_437328 prefixEnd_437328 224559467669570185888771 := by
  unfold tailWord_437328
  simp only [CollatzResearch.WordTrace]
  refine ⟨7975331279821410260580319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10633775039761880347440425 7975331279821410260580319)
  ·
    refine ⟨11962996919732115390870479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7975331279821410260580319 11962996919732115390870479)
    ·
      refine ⟨17944495379598173086305719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11962996919732115390870479 17944495379598173086305719)
      ·
        refine ⟨26916743069397259629458579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17944495379598173086305719 26916743069397259629458579)
        ·
          refine ⟨40375114604095889444187869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26916743069397259629458579 40375114604095889444187869)
          ·
            refine ⟨15140667976535958541570451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40375114604095889444187869 15140667976535958541570451)
            ·
              refine ⟨22711001964803937812355677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15140667976535958541570451 22711001964803937812355677)
              ·
                refine ⟨8516625736801476679633379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22711001964803937812355677 8516625736801476679633379)
                ·
                  refine ⟨12774938605202215019450069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8516625736801476679633379 12774938605202215019450069)
                  ·
                    refine ⟨299412623559426914518361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 12774938605202215019450069 299412623559426914518361)
                    ·
                      refine ⟨224559467669570185888771, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 299412623559426914518361 224559467669570185888771)
                      ·
                        rfl

theorem cell23_437328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 1, 3, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 1, 3, 1, 7, 2].length) (baseStart_437328 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_437328 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_437328 prefixEnd_437328 := by exact prefixLift 437328
  have htrace : WordTrace (prefixWord ++ tailWord_437328) baseStart_437328 baseEnd_437328 := by
    simpa [prefixWord, tailWord_437328, baseEnd_437328] using wordTrace_append hprefix tailTrace_437328
  have hstable : (prefixWord ++ tailWord_437328).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_437328).length < 2 ^ (prefixWord ++ tailWord_437328).sum := by decide
  have hdescent : baseEnd_437328 < baseStart_437328 := by decide
  rcases family_descends (prefixWord ++ tailWord_437328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_437342 : List Nat := [4, 4, 1, 1, 1, 1, 2, 2, 7]
def baseStart_437342 : Nat := 118140960795 + 437342 * 2 ^ 59
def prefixEnd_437342 : Nat := 4983230072969 + 3 ^ 40 * 437342 * 2
def baseEnd_437342 : Nat := 24951850710970347901523

theorem tailTrace_437342 : CollatzResearch.WordTrace tailWord_437342 prefixEnd_437342 24951850710970347901523 := by
  unfold tailWord_437342
  simp only [CollatzResearch.WordTrace]
  refine ⟨1993896647699012614021285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 10634115454394733941446853 1993896647699012614021285)
  ·
    refine ⟨373855621443564865128991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1993896647699012614021285 373855621443564865128991)
    ·
      refine ⟨560783432165347297693487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 373855621443564865128991 560783432165347297693487)
      ·
        refine ⟨841175148248020946540231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 560783432165347297693487 841175148248020946540231)
        ·
          refine ⟨1261762722372031419810347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 841175148248020946540231 1261762722372031419810347)
          ·
            refine ⟨1892644083558047129715521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1261762722372031419810347 1892644083558047129715521)
            ·
              refine ⟨1419483062668535347286641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1892644083558047129715521 1419483062668535347286641)
              ·
                refine ⟨1064612297001401510464981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1419483062668535347286641 1064612297001401510464981)
                ·
                  refine ⟨24951850710970347901523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1064612297001401510464981 24951850710970347901523)
                  ·
                    rfl

theorem cell23_437342_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 1, 2, 2, 7].length) (baseStart_437342 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_437342 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_437342 prefixEnd_437342 := by exact prefixLift 437342
  have htrace : WordTrace (prefixWord ++ tailWord_437342) baseStart_437342 baseEnd_437342 := by
    simpa [prefixWord, tailWord_437342, baseEnd_437342] using wordTrace_append hprefix tailTrace_437342
  have hstable : (prefixWord ++ tailWord_437342).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_437342).length < 2 ^ (prefixWord ++ tailWord_437342).sum := by decide
  have hdescent : baseEnd_437342 < baseStart_437342 := by decide
  rcases family_descends (prefixWord ++ tailWord_437342) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_437368 : List Nat := [2, 1, 2, 1, 1, 1, 4, 2, 5, 4]
def baseStart_437368 : Nat := 118140960795 + 437368 * 2 ^ 59
def prefixEnd_437368 : Nat := 4983230072969 + 3 ^ 40 * 437368 * 2
def baseEnd_437368 : Nat := 74860002298583343129529

theorem tailTrace_437368 : CollatzResearch.WordTrace tailWord_437368 prefixEnd_437368 74860002298583343129529 := by
  unfold tailWord_437368
  simp only [CollatzResearch.WordTrace]
  refine ⟨7976060739748953676308379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10634747652998604901744505 7976060739748953676308379)
  ·
    refine ⟨11964091109623430514462569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7976060739748953676308379 11964091109623430514462569)
    ·
      refine ⟨8973068332217572885846927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11964091109623430514462569 8973068332217572885846927)
      ·
        refine ⟨13459602498326359328770391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8973068332217572885846927 13459602498326359328770391)
        ·
          refine ⟨20189403747489538993155587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13459602498326359328770391 20189403747489538993155587)
          ·
            refine ⟨30284105621234308489733381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20189403747489538993155587 30284105621234308489733381)
            ·
              refine ⟨5678269803981432841825009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 30284105621234308489733381 5678269803981432841825009)
              ·
                refine ⟨4258702352986074631368757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5678269803981432841825009 4258702352986074631368757)
                ·
                  refine ⟨399253345592444496690821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4258702352986074631368757 399253345592444496690821)
                  ·
                    refine ⟨74860002298583343129529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 399253345592444496690821 74860002298583343129529)
                    ·
                      rfl

theorem cell23_437368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 4, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 4, 2, 5, 4].length) (baseStart_437368 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_437368 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_437368 prefixEnd_437368 := by exact prefixLift 437368
  have htrace : WordTrace (prefixWord ++ tailWord_437368) baseStart_437368 baseEnd_437368 := by
    simpa [prefixWord, tailWord_437368, baseEnd_437368] using wordTrace_append hprefix tailTrace_437368
  have hstable : (prefixWord ++ tailWord_437368).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_437368).length < 2 ^ (prefixWord ++ tailWord_437368).sum := by decide
  have hdescent : baseEnd_437368 < baseStart_437368 := by decide
  rcases family_descends (prefixWord ++ tailWord_437368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_437371 : List Nat := [1, 1, 1, 1, 1, 4, 1, 3, 1, 3, 6]
def baseStart_437371 : Nat := 118140960795 + 437371 * 2 ^ 59
def prefixEnd_437371 : Nat := 4983230072969 + 3 ^ 40 * 437371 * 2
def baseEnd_437371 : Nat := 224581547337713517651073

theorem tailTrace_437371 : CollatzResearch.WordTrace tailWord_437371 prefixEnd_437371 224581547337713517651073 := by
  unfold tailWord_437371
  simp only [CollatzResearch.WordTrace]
  refine ⟨15952230898487038864975967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10634820598991359243317311 15952230898487038864975967)
  ·
    refine ⟨23928346347730558297463951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15952230898487038864975967 23928346347730558297463951)
    ·
      refine ⟨35892519521595837446195927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23928346347730558297463951 35892519521595837446195927)
      ·
        refine ⟨53838779282393756169293891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35892519521595837446195927 53838779282393756169293891)
        ·
          refine ⟨80758168923590634253940837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53838779282393756169293891 80758168923590634253940837)
          ·
            refine ⟨15142156673173243922613907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 80758168923590634253940837 15142156673173243922613907)
            ·
              refine ⟨22713235009759865883920861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15142156673173243922613907 22713235009759865883920861)
              ·
                refine ⟨8517463128659949706470323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22713235009759865883920861 8517463128659949706470323)
                ·
                  refine ⟨12776194692989924559705485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8517463128659949706470323 12776194692989924559705485)
                  ·
                    refine ⟨4791073009871221709889557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12776194692989924559705485 4791073009871221709889557)
                    ·
                      refine ⟨224581547337713517651073, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 4791073009871221709889557 224581547337713517651073)
                      ·
                        rfl

theorem cell23_437371_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 1, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 1, 3, 1, 3, 6].length) (baseStart_437371 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_437371 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_437371 prefixEnd_437371 := by exact prefixLift 437371
  have htrace : WordTrace (prefixWord ++ tailWord_437371) baseStart_437371 baseEnd_437371 := by
    simpa [prefixWord, tailWord_437371, baseEnd_437371] using wordTrace_append hprefix tailTrace_437371
  have hstable : (prefixWord ++ tailWord_437371).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_437371).length < 2 ^ (prefixWord ++ tailWord_437371).sum := by decide
  have hdescent : baseEnd_437371 < baseStart_437371 := by decide
  rcases family_descends (prefixWord ++ tailWord_437371) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_437385 : List Nat := [1, 2, 1, 1, 4, 3, 3, 1, 3, 4]
def baseStart_437385 : Nat := 118140960795 + 437385 * 2 ^ 59
def prefixEnd_437385 : Nat := 4983230072969 + 3 ^ 40 * 437385 * 2
def baseEnd_437385 : Nat := 74862912022292154292003

theorem tailTrace_437385 : CollatzResearch.WordTrace tailWord_437385 prefixEnd_437385 74862912022292154292003 := by
  unfold tailWord_437385
  simp only [CollatzResearch.WordTrace]
  refine ⟨15952741520436319255985609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10635161013624212837323739 15952741520436319255985609)
  ·
    refine ⟨11964556140327239441989207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15952741520436319255985609 11964556140327239441989207)
    ·
      refine ⟨17946834210490859162983811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11964556140327239441989207 17946834210490859162983811)
      ·
        refine ⟨26920251315736288744475717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17946834210490859162983811 26920251315736288744475717)
        ·
          refine ⟨5047547121700554139589197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 26920251315736288744475717 5047547121700554139589197)
          ·
            refine ⟨1892830170637707802345949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5047547121700554139589197 1892830170637707802345949)
            ·
              refine ⟨709811313989140425879731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1892830170637707802345949 709811313989140425879731)
              ·
                refine ⟨1064716970983710638819597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 709811313989140425879731 1064716970983710638819597)
                ·
                  refine ⟨399268864118891489557349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1064716970983710638819597 399268864118891489557349)
                  ·
                    refine ⟨74862912022292154292003, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 399268864118891489557349 74862912022292154292003)
                    ·
                      rfl

theorem cell23_437385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 3, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 3, 3, 1, 3, 4].length) (baseStart_437385 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_437385 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_437385 prefixEnd_437385 := by exact prefixLift 437385
  have htrace : WordTrace (prefixWord ++ tailWord_437385) baseStart_437385 baseEnd_437385 := by
    simpa [prefixWord, tailWord_437385, baseEnd_437385] using wordTrace_append hprefix tailTrace_437385
  have hstable : (prefixWord ++ tailWord_437385).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_437385).length < 2 ^ (prefixWord ++ tailWord_437385).sum := by decide
  have hdescent : baseEnd_437385 < baseStart_437385 := by decide
  rcases family_descends (prefixWord ++ tailWord_437385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_437391 : List Nat := [1, 1, 2, 1, 1, 1, 1, 2, 2, 4, 7]
def baseStart_437391 : Nat := 118140960795 + 437391 * 2 ^ 59
def prefixEnd_437391 : Nat := 4983230072969 + 3 ^ 40 * 437391 * 2
def baseEnd_437391 : Nat := 224591816950803439400981

theorem tailTrace_437391 : CollatzResearch.WordTrace tailWord_437391 prefixEnd_437391 224591816950803439400981 := by
  unfold tailWord_437391
  simp only [CollatzResearch.WordTrace]
  refine ⟨15952960358414582280704027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10635306905609721520469351 15952960358414582280704027)
  ·
    refine ⟨23929440537621873421056041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15952960358414582280704027 23929440537621873421056041)
    ·
      refine ⟨17947080403216405065792031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23929440537621873421056041 17947080403216405065792031)
      ·
        refine ⟨26920620604824607598688047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17947080403216405065792031 26920620604824607598688047)
        ·
          refine ⟨40380930907236911398032071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26920620604824607598688047 40380930907236911398032071)
          ·
            refine ⟨60571396360855367097048107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40380930907236911398032071 60571396360855367097048107)
            ·
              refine ⟨90857094541283050645572161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60571396360855367097048107 90857094541283050645572161)
              ·
                refine ⟨68142820905962287984179121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 90857094541283050645572161 68142820905962287984179121)
                ·
                  refine ⟨51107115679471715988134341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 68142820905962287984179121 51107115679471715988134341)
                  ·
                    refine ⟨9582584189900946747775189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 51107115679471715988134341 9582584189900946747775189)
                    ·
                      refine ⟨224591816950803439400981, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 9582584189900946747775189 224591816950803439400981)
                      ·
                        rfl

theorem cell23_437391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 2, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 2, 2, 4, 7].length) (baseStart_437391 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_437391 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_437391 prefixEnd_437391 := by exact prefixLift 437391
  have htrace : WordTrace (prefixWord ++ tailWord_437391) baseStart_437391 baseEnd_437391 := by
    simpa [prefixWord, tailWord_437391, baseEnd_437391] using wordTrace_append hprefix tailTrace_437391
  have hstable : (prefixWord ++ tailWord_437391).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_437391).length < 2 ^ (prefixWord ++ tailWord_437391).sum := by decide
  have hdescent : baseEnd_437391 < baseStart_437391 := by decide
  rcases family_descends (prefixWord ++ tailWord_437391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_437412 : List Nat := [2, 3, 1, 2, 3, 2, 2, 1, 2, 2, 3]
def baseStart_437412 : Nat := 118140960795 + 437412 * 2 ^ 59
def prefixEnd_437412 : Nat := 4983230072969 + 3 ^ 40 * 437412 * 2
def baseEnd_437412 : Nat := 224602600044547857238385

theorem tailTrace_437412 : CollatzResearch.WordTrace tailWord_437412 prefixEnd_437412 224602600044547857238385 := by
  unfold tailWord_437412
  simp only [CollatzResearch.WordTrace]
  refine ⟨7976863145669251433609245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10635817527559001911478993 7976863145669251433609245)
  ·
    refine ⟨2991323679625969287603467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7976863145669251433609245 2991323679625969287603467)
    ·
      refine ⟨4486985519438953931405201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2991323679625969287603467 4486985519438953931405201)
      ·
        refine ⟨3365239139579215448553901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4486985519438953931405201 3365239139579215448553901)
        ·
          refine ⟨1261964677342205793207713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3365239139579215448553901 1261964677342205793207713)
          ·
            refine ⟨946473508006654344905785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1261964677342205793207713 946473508006654344905785)
            ·
              refine ⟨709855131004990758679339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 946473508006654344905785 709855131004990758679339)
              ·
                refine ⟨1064782696507486138019009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 709855131004990758679339 1064782696507486138019009)
                ·
                  refine ⟨798587022380614603514257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1064782696507486138019009 798587022380614603514257)
                  ·
                    refine ⟨598940266785460952635693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 798587022380614603514257 598940266785460952635693)
                    ·
                      refine ⟨224602600044547857238385, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 598940266785460952635693 224602600044547857238385)
                      ·
                        rfl

theorem cell23_437412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 2, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 2, 2, 1, 2, 2, 3].length) (baseStart_437412 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_437412 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_437412 prefixEnd_437412 := by exact prefixLift 437412
  have htrace : WordTrace (prefixWord ++ tailWord_437412) baseStart_437412 baseEnd_437412 := by
    simpa [prefixWord, tailWord_437412, baseEnd_437412] using wordTrace_append hprefix tailTrace_437412
  have hstable : (prefixWord ++ tailWord_437412).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_437412).length < 2 ^ (prefixWord ++ tailWord_437412).sum := by decide
  have hdescent : baseEnd_437412 < baseStart_437412 := by decide
  rcases family_descends (prefixWord ++ tailWord_437412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_437435 : List Nat := [1, 1, 1, 1, 1, 2, 4, 3, 4, 3, 2]
def baseStart_437435 : Nat := 118140960795 + 437435 * 2 ^ 59
def prefixEnd_437435 : Nat := 4983230072969 + 3 ^ 40 * 437435 * 2
def baseEnd_437435 : Nat := 224614410099601267250779

theorem tailTrace_437435 : CollatzResearch.WordTrace tailWord_437435 prefixEnd_437435 224614410099601267250779 := by
  unfold tailWord_437435
  simp only [CollatzResearch.WordTrace]
  refine ⟨15954565170255177795305759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10636376780170118530203839 15954565170255177795305759)
  ·
    refine ⟨23931847755382766692958639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15954565170255177795305759 23931847755382766692958639)
    ·
      refine ⟨35897771633074150039437959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23931847755382766692958639 35897771633074150039437959)
      ·
        refine ⟨53846657449611225059156939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35897771633074150039437959 53846657449611225059156939)
        ·
          refine ⟨80769986174416837588735409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53846657449611225059156939 80769986174416837588735409)
          ·
            refine ⟨60577489630812628191551557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 80769986174416837588735409 60577489630812628191551557)
            ·
              refine ⟨11358279305777367785915917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 60577489630812628191551557 11358279305777367785915917)
              ·
                refine ⟨4259354739666512919718469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11358279305777367785915917 4259354739666512919718469)
                ·
                  refine ⟨798629013687471172447213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4259354739666512919718469 798629013687471172447213)
                  ·
                    refine ⟨299485880132801689667705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 798629013687471172447213 299485880132801689667705)
                    ·
                      refine ⟨224614410099601267250779, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 299485880132801689667705 224614410099601267250779)
                      ·
                        rfl

theorem cell23_437435_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 4, 3, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 4, 3, 4, 3, 2].length) (baseStart_437435 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_437435 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_437435 prefixEnd_437435 := by exact prefixLift 437435
  have htrace : WordTrace (prefixWord ++ tailWord_437435) baseStart_437435 baseEnd_437435 := by
    simpa [prefixWord, tailWord_437435, baseEnd_437435] using wordTrace_append hprefix tailTrace_437435
  have hstable : (prefixWord ++ tailWord_437435).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_437435).length < 2 ^ (prefixWord ++ tailWord_437435).sum := by decide
  have hdescent : baseEnd_437435 < baseStart_437435 := by decide
  rcases family_descends (prefixWord ++ tailWord_437435) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_437436 : List Nat := [2, 2, 2, 3, 2, 3, 2, 2, 1, 4]
def baseStart_437436 : Nat := 118140960795 + 437436 * 2 ^ 59
def prefixEnd_437436 : Nat := 4983230072969 + 3 ^ 40 * 437436 * 2
def baseEnd_437436 : Nat := 74871641193418587779425

theorem tailTrace_437436 : CollatzResearch.WordTrace tailWord_437436 prefixEnd_437436 74871641193418587779425 := by
  unfold tailWord_437436
  simp only [CollatzResearch.WordTrace]
  refine ⟨7977300821625777483046081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10636401095501036644061441 7977300821625777483046081)
  ·
    refine ⟨5982975616219333112284561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7977300821625777483046081 5982975616219333112284561)
    ·
      refine ⟨4487231712164499834213421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5982975616219333112284561 4487231712164499834213421)
      ·
        refine ⟨1682711892061687437830033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4487231712164499834213421 1682711892061687437830033)
        ·
          refine ⟨1262033919046265578372525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1682711892061687437830033 1262033919046265578372525)
          ·
            refine ⟨473262719642349591889697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1262033919046265578372525 473262719642349591889697)
            ·
              refine ⟨354947039731762193917273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 473262719642349591889697 354947039731762193917273)
              ·
                refine ⟨266210279798821645437955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 354947039731762193917273 266210279798821645437955)
                ·
                  refine ⟨399315419698232468156933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 266210279798821645437955 399315419698232468156933)
                  ·
                    refine ⟨74871641193418587779425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 399315419698232468156933 74871641193418587779425)
                    ·
                      rfl

theorem cell23_437436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 3, 2, 2, 1, 4].length) (baseStart_437436 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_437436 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_437436 prefixEnd_437436 := by exact prefixLift 437436
  have htrace : WordTrace (prefixWord ++ tailWord_437436) baseStart_437436 baseEnd_437436 := by
    simpa [prefixWord, tailWord_437436, baseEnd_437436] using wordTrace_append hprefix tailTrace_437436
  have hstable : (prefixWord ++ tailWord_437436).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_437436).length < 2 ^ (prefixWord ++ tailWord_437436).sum := by decide
  have hdescent : baseEnd_437436 < baseStart_437436 := by decide
  rcases family_descends (prefixWord ++ tailWord_437436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_437465 : List Nat := [1, 2, 1, 2, 3, 1, 1, 6, 1, 1, 4]
def baseStart_437465 : Nat := 118140960795 + 437465 * 2 ^ 59
def prefixEnd_437465 : Nat := 4983230072969 + 3 ^ 40 * 437465 * 2
def baseEnd_437465 : Nat := 224629814519236149875641

theorem tailTrace_437465 : CollatzResearch.WordTrace tailWord_437465 prefixEnd_437465 224629814519236149875641 := by
  unfold tailWord_437465
  simp only [CollatzResearch.WordTrace]
  refine ⟨15955659360146492918897849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10637106240097661945931899 15955659360146492918897849)
  ·
    refine ⟨11966744520109869689173387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15955659360146492918897849 11966744520109869689173387)
    ·
      refine ⟨17950116780164804533760081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11966744520109869689173387 17950116780164804533760081)
      ·
        refine ⟨13462587585123603400320061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17950116780164804533760081 13462587585123603400320061)
        ·
          refine ⟨5048470344421351275120023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13462587585123603400320061 5048470344421351275120023)
          ·
            refine ⟨7572705516632026912680035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5048470344421351275120023 7572705516632026912680035)
            ·
              refine ⟨11359058274948040369020053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7572705516632026912680035 11359058274948040369020053)
              ·
                refine ⟨532455856638189392297815, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 11359058274948040369020053 532455856638189392297815)
                ·
                  refine ⟨798683784957284088446723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 532455856638189392297815 798683784957284088446723)
                  ·
                    refine ⟨1198025677435926132670085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 798683784957284088446723 1198025677435926132670085)
                    ·
                      refine ⟨224629814519236149875641, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1198025677435926132670085 224629814519236149875641)
                      ·
                        rfl

theorem cell23_437465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 1, 6, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 1, 6, 1, 1, 4].length) (baseStart_437465 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_437465 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_437465 prefixEnd_437465 := by exact prefixLift 437465
  have htrace : WordTrace (prefixWord ++ tailWord_437465) baseStart_437465 baseEnd_437465 := by
    simpa [prefixWord, tailWord_437465, baseEnd_437465] using wordTrace_append hprefix tailTrace_437465
  have hstable : (prefixWord ++ tailWord_437465).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_437465).length < 2 ^ (prefixWord ++ tailWord_437465).sum := by decide
  have hdescent : baseEnd_437465 < baseStart_437465 := by decide
  rcases family_descends (prefixWord ++ tailWord_437465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_437469 : List Nat := [1, 4, 3, 2, 2, 1, 1, 1, 1, 5, 2]
def baseStart_437469 : Nat := 118140960795 + 437469 * 2 ^ 59
def prefixEnd_437469 : Nat := 4983230072969 + 3 ^ 40 * 437469 * 2
def baseEnd_437469 : Nat := 224631868441854134225623

theorem tailTrace_437469 : CollatzResearch.WordTrace tailWord_437469 prefixEnd_437469 224631868441854134225623 := by
  unfold tailWord_437469
  simp only [CollatzResearch.WordTrace]
  refine ⟨15955805252132001602043461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10637203501421334401362307 15955805252132001602043461)
  ·
    refine ⟨2991713484774750300383149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 15955805252132001602043461 2991713484774750300383149)
    ·
      refine ⟨1121892556790531362643681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2991713484774750300383149 1121892556790531362643681)
      ·
        refine ⟨841419417592898521982761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1121892556790531362643681 841419417592898521982761)
        ·
          refine ⟨631064563194673891487071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 841419417592898521982761 631064563194673891487071)
          ·
            refine ⟨946596844792010837230607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 631064563194673891487071 946596844792010837230607)
            ·
              refine ⟨1419895267188016255845911, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 946596844792010837230607 1419895267188016255845911)
              ·
                refine ⟨2129842900782024383768867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1419895267188016255845911 2129842900782024383768867)
                ·
                  refine ⟨3194764351173036575653301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2129842900782024383768867 3194764351173036575653301)
                  ·
                    refine ⟨299509157922472178967497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3194764351173036575653301 299509157922472178967497)
                    ·
                      refine ⟨224631868441854134225623, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 299509157922472178967497 224631868441854134225623)
                      ·
                        rfl

theorem cell23_437469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 2, 1, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 2, 1, 1, 1, 1, 5, 2].length) (baseStart_437469 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_437469 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_437469 prefixEnd_437469 := by exact prefixLift 437469
  have htrace : WordTrace (prefixWord ++ tailWord_437469) baseStart_437469 baseEnd_437469 := by
    simpa [prefixWord, tailWord_437469, baseEnd_437469] using wordTrace_append hprefix tailTrace_437469
  have hstable : (prefixWord ++ tailWord_437469).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_437469).length < 2 ^ (prefixWord ++ tailWord_437469).sum := by decide
  have hdescent : baseEnd_437469 < baseStart_437469 := by decide
  rcases family_descends (prefixWord ++ tailWord_437469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_437482 : List Nat := [3, 1, 3, 1, 1, 4, 1, 3, 1, 1, 4]
def baseStart_437482 : Nat := 118140960795 + 437482 * 2 ^ 59
def prefixEnd_437482 : Nat := 4983230072969 + 3 ^ 40 * 437482 * 2
def baseEnd_437482 : Nat := 224638543690362583363063

theorem tailTrace_437482 : CollatzResearch.WordTrace tailWord_437482 prefixEnd_437482 224638543690362583363063 := by
  unfold tailWord_437482
  simp only [CollatzResearch.WordTrace]
  refine ⟨3989069850271226205566675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10637519600723269881511133 3989069850271226205566675)
  ·
    refine ⟨5983604775406839308350013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3989069850271226205566675 5983604775406839308350013)
    ·
      refine ⟨2243851790777564740631255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5983604775406839308350013 2243851790777564740631255)
      ·
        refine ⟨3365777686166347110946883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2243851790777564740631255 3365777686166347110946883)
        ·
          refine ⟨5048666529249520666420325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3365777686166347110946883 5048666529249520666420325)
          ·
            refine ⟨946624974234285124953811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5048666529249520666420325 946624974234285124953811)
            ·
              refine ⟨1419937461351427687430717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 946624974234285124953811 1419937461351427687430717)
              ·
                refine ⟨532476548006785382786519, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1419937461351427687430717 532476548006785382786519)
                ·
                  refine ⟨798714822010178074179779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 532476548006785382786519 798714822010178074179779)
                  ·
                    refine ⟨1198072233015267111269669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 798714822010178074179779 1198072233015267111269669)
                    ·
                      refine ⟨224638543690362583363063, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1198072233015267111269669 224638543690362583363063)
                      ·
                        rfl

theorem cell23_437482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 4, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 4, 1, 3, 1, 1, 4].length) (baseStart_437482 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_437482 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_437482 prefixEnd_437482 := by exact prefixLift 437482
  have htrace : WordTrace (prefixWord ++ tailWord_437482) baseStart_437482 baseEnd_437482 := by
    simpa [prefixWord, tailWord_437482, baseEnd_437482] using wordTrace_append hprefix tailTrace_437482
  have hstable : (prefixWord ++ tailWord_437482).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_437482).length < 2 ^ (prefixWord ++ tailWord_437482).sum := by decide
  have hdescent : baseEnd_437482 < baseStart_437482 := by decide
  rcases family_descends (prefixWord ++ tailWord_437482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_437502 : List Nat := [4, 2, 2, 1, 1, 3, 1, 2, 1, 1, 5]
def baseStart_437502 : Nat := 118140960795 + 437502 * 2 ^ 59
def prefixEnd_437502 : Nat := 4983230072969 + 3 ^ 40 * 437502 * 2
def baseEnd_437502 : Nat := 224648813303452505112971

theorem tailTrace_437502 : CollatzResearch.WordTrace tailWord_437502 prefixEnd_437502 224648813303452505112971 := by
  unfold tailWord_437502
  simp only [CollatzResearch.WordTrace]
  refine ⟨1994626107626556029749345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 10638005907341632158663173 1994626107626556029749345)
  ·
    refine ⟨1495969580719917022312009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1994626107626556029749345 1495969580719917022312009)
    ·
      refine ⟨1121977185539937766734007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1495969580719917022312009 1121977185539937766734007)
      ·
        refine ⟨1682965778309906650101011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1121977185539937766734007 1682965778309906650101011)
        ·
          refine ⟨2524448667464859975151517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1682965778309906650101011 2524448667464859975151517)
          ·
            refine ⟨946668250299322490681819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2524448667464859975151517 946668250299322490681819)
            ·
              refine ⟨1420002375448983736022729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 946668250299322490681819 1420002375448983736022729)
              ·
                refine ⟨1065001781586737802017047, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1420002375448983736022729 1065001781586737802017047)
                ·
                  refine ⟨1597502672380106703025571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1065001781586737802017047 1597502672380106703025571)
                  ·
                    refine ⟨2396254008570160054538357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1597502672380106703025571 2396254008570160054538357)
                    ·
                      refine ⟨224648813303452505112971, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 2396254008570160054538357 224648813303452505112971)
                      ·
                        rfl

theorem cell23_437502_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 3, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 3, 1, 2, 1, 1, 5].length) (baseStart_437502 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_437502 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_437502 prefixEnd_437502 := by exact prefixLift 437502
  have htrace : WordTrace (prefixWord ++ tailWord_437502) baseStart_437502 baseEnd_437502 := by
    simpa [prefixWord, tailWord_437502, baseEnd_437502] using wordTrace_append hprefix tailTrace_437502
  have hstable : (prefixWord ++ tailWord_437502).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_437502).length < 2 ^ (prefixWord ++ tailWord_437502).sum := by decide
  have hdescent : baseEnd_437502 < baseStart_437502 := by decide
  rcases family_descends (prefixWord ++ tailWord_437502) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_437532 : List Nat := [2, 2, 3, 1, 1, 1, 3, 2, 4, 1, 3]
def baseStart_437532 : Nat := 118140960795 + 437532 * 2 ^ 59
def prefixEnd_437532 : Nat := 4983230072969 + 3 ^ 40 * 437532 * 2
def baseEnd_437532 : Nat := 224664217723087387737833

theorem tailTrace_437532 : CollatzResearch.WordTrace tailWord_437532 prefixEnd_437532 224664217723087387737833 := by
  unfold tailWord_437532
  simp only [CollatzResearch.WordTrace]
  refine ⟨7979051525451881680793425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10638735367269175574391233 7979051525451881680793425)
  ·
    refine ⟨5984288644088911260595069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7979051525451881680793425 5984288644088911260595069)
    ·
      refine ⟨2244108241533341722723151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5984288644088911260595069 2244108241533341722723151)
      ·
        refine ⟨3366162362300012584084727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2244108241533341722723151 3366162362300012584084727)
        ·
          refine ⟨5049243543450018876127091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3366162362300012584084727 5049243543450018876127091)
          ·
            refine ⟨7573865315175028314190637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5049243543450018876127091 7573865315175028314190637)
            ·
              refine ⟨2840199493190635617821489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7573865315175028314190637 2840199493190635617821489)
              ·
                refine ⟨2130149619892976713366117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2840199493190635617821489 2130149619892976713366117)
                ·
                  refine ⟨399403053729933133756147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2130149619892976713366117 399403053729933133756147)
                  ·
                    refine ⟨599104580594899700634221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 399403053729933133756147 599104580594899700634221)
                    ·
                      refine ⟨224664217723087387737833, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 599104580594899700634221 224664217723087387737833)
                      ·
                        rfl

theorem cell23_437532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 3, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 3, 2, 4, 1, 3].length) (baseStart_437532 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_437532 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_437532 prefixEnd_437532 := by exact prefixLift 437532
  have htrace : WordTrace (prefixWord ++ tailWord_437532) baseStart_437532 baseEnd_437532 := by
    simpa [prefixWord, tailWord_437532, baseEnd_437532] using wordTrace_append hprefix tailTrace_437532
  have hstable : (prefixWord ++ tailWord_437532).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_437532).length < 2 ^ (prefixWord ++ tailWord_437532).sum := by decide
  have hdescent : baseEnd_437532 < baseStart_437532 := by decide
  rcases family_descends (prefixWord ++ tailWord_437532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_437533 : List Nat := [1, 4, 2, 3, 1, 1, 3, 3, 1, 2, 2]
def baseStart_437533 : Nat := 118140960795 + 437533 * 2 ^ 59
def prefixEnd_437533 : Nat := 4983230072969 + 3 ^ 40 * 437533 * 2
def baseEnd_437533 : Nat := 224664731203741883825329

theorem tailTrace_437533 : CollatzResearch.WordTrace tailWord_437533 prefixEnd_437533 224664731203741883825329 := by
  unfold tailWord_437533
  simp only [CollatzResearch.WordTrace]
  refine ⟨15958139523900140532373253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10638759682600093688248835 15958139523900140532373253)
  ·
    refine ⟨2992151160731276349819985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 15958139523900140532373253 2992151160731276349819985)
    ·
      refine ⟨2244113370548457262364989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2992151160731276349819985 2244113370548457262364989)
      ·
        refine ⟨841542513955671473386871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2244113370548457262364989 841542513955671473386871)
        ·
          refine ⟨1262313770933507210080307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 841542513955671473386871 1262313770933507210080307)
          ·
            refine ⟨1893470656400260815120461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1262313770933507210080307 1893470656400260815120461)
            ·
              refine ⟨710051496150097805670173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1893470656400260815120461 710051496150097805670173)
              ·
                refine ⟨266269311056286677126315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 710051496150097805670173 266269311056286677126315)
                ·
                  refine ⟨399403966584430015689473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 266269311056286677126315 399403966584430015689473)
                  ·
                    refine ⟨299552974938322511767105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 399403966584430015689473 299552974938322511767105)
                    ·
                      refine ⟨224664731203741883825329, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 299552974938322511767105 224664731203741883825329)
                      ·
                        rfl

theorem cell23_437533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 1, 3, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 1, 3, 3, 1, 2, 2].length) (baseStart_437533 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_437533 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_437533 prefixEnd_437533 := by exact prefixLift 437533
  have htrace : WordTrace (prefixWord ++ tailWord_437533) baseStart_437533 baseEnd_437533 := by
    simpa [prefixWord, tailWord_437533, baseEnd_437533] using wordTrace_append hprefix tailTrace_437533
  have hstable : (prefixWord ++ tailWord_437533).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_437533).length < 2 ^ (prefixWord ++ tailWord_437533).sum := by decide
  have hdescent : baseEnd_437533 < baseStart_437533 := by decide
  rcases family_descends (prefixWord ++ tailWord_437533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_437575 : List Nat := [1, 1, 4, 1, 2, 3, 1, 2, 2, 1, 5]
def baseStart_437575 : Nat := 118140960795 + 437575 * 2 ^ 59
def prefixEnd_437575 : Nat := 4983230072969 + 3 ^ 40 * 437575 * 2
def baseEnd_437575 : Nat := 224686297391230719500135

theorem tailTrace_437575 : CollatzResearch.WordTrace tailWord_437575 prefixEnd_437575 224686297391230719500135 := by
  unfold tailWord_437575
  simp only [CollatzResearch.WordTrace]
  refine ⟨15959671389747981705402179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10639780926498654470268119 15959671389747981705402179)
  ·
    refine ⟨23939507084621972558103269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15959671389747981705402179 23939507084621972558103269)
    ·
      refine ⟨4488657578366619854644363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 23939507084621972558103269 4488657578366619854644363)
      ·
        refine ⟨6732986367549929781966545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4488657578366619854644363 6732986367549929781966545)
        ·
          refine ⟨5049739775662447336474909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6732986367549929781966545 5049739775662447336474909)
          ·
            refine ⟨1893652415873417751178091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5049739775662447336474909 1893652415873417751178091)
            ·
              refine ⟨2840478623810126626767137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1893652415873417751178091 2840478623810126626767137)
              ·
                refine ⟨2130358967857594970075353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2840478623810126626767137 2130358967857594970075353)
                ·
                  refine ⟨1597769225893196227556515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2130358967857594970075353 1597769225893196227556515)
                  ·
                    refine ⟨2396653838839794341334773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1597769225893196227556515 2396653838839794341334773)
                    ·
                      refine ⟨224686297391230719500135, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 2396653838839794341334773 224686297391230719500135)
                      ·
                        rfl

theorem cell23_437575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 3, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 3, 1, 2, 2, 1, 5].length) (baseStart_437575 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_437575 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_437575 prefixEnd_437575 := by exact prefixLift 437575
  have htrace : WordTrace (prefixWord ++ tailWord_437575) baseStart_437575 baseEnd_437575 := by
    simpa [prefixWord, tailWord_437575, baseEnd_437575] using wordTrace_append hprefix tailTrace_437575
  have hstable : (prefixWord ++ tailWord_437575).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_437575).length < 2 ^ (prefixWord ++ tailWord_437575).sum := by decide
  have hdescent : baseEnd_437575 < baseStart_437575 := by decide
  rcases family_descends (prefixWord ++ tailWord_437575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_437589 : List Nat := [1, 3, 2, 2, 3, 2, 1, 2, 1, 4, 2]
def baseStart_437589 : Nat := 118140960795 + 437589 * 2 ^ 59
def prefixEnd_437589 : Nat := 4983230072969 + 3 ^ 40 * 437589 * 2
def baseEnd_437589 : Nat := 224693486120393664725071

theorem tailTrace_437589 : CollatzResearch.WordTrace tailWord_437589 prefixEnd_437589 224693486120393664725071 := by
  unfold tailWord_437589
  simp only [CollatzResearch.WordTrace]
  refine ⟨15960182011697262096411821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10640121341131508064274547 15960182011697262096411821)
  ·
    refine ⟨5985068254386473286154433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15960182011697262096411821 5985068254386473286154433)
    ·
      refine ⟨4488801190789854964615825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5985068254386473286154433 4488801190789854964615825)
      ·
        refine ⟨3366600893092391223461869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4488801190789854964615825 3366600893092391223461869)
        ·
          refine ⟨1262475334909646708798201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3366600893092391223461869 1262475334909646708798201)
          ·
            refine ⟨946856501182235031598651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1262475334909646708798201 946856501182235031598651)
            ·
              refine ⟨1420284751773352547397977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 946856501182235031598651 1420284751773352547397977)
              ·
                refine ⟨1065213563830014410548483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1420284751773352547397977 1065213563830014410548483)
                ·
                  refine ⟨1597820345745021615822725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1065213563830014410548483 1597820345745021615822725)
                  ·
                    refine ⟨299591314827191552966761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1597820345745021615822725 299591314827191552966761)
                    ·
                      refine ⟨224693486120393664725071, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 299591314827191552966761 224693486120393664725071)
                      ·
                        rfl

theorem cell23_437589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 2, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 2, 1, 2, 1, 4, 2].length) (baseStart_437589 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_437589 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_437589 prefixEnd_437589 := by exact prefixLift 437589
  have htrace : WordTrace (prefixWord ++ tailWord_437589) baseStart_437589 baseEnd_437589 := by
    simpa [prefixWord, tailWord_437589, baseEnd_437589] using wordTrace_append hprefix tailTrace_437589
  have hstable : (prefixWord ++ tailWord_437589).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_437589).length < 2 ^ (prefixWord ++ tailWord_437589).sum := by decide
  have hdescent : baseEnd_437589 < baseStart_437589 := by decide
  rcases family_descends (prefixWord ++ tailWord_437589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_437602 : List Nat := [3, 3, 2, 1, 1, 1, 2, 2, 2, 2, 4]
def baseStart_437602 : Nat := 118140960795 + 437602 * 2 ^ 59
def prefixEnd_437602 : Nat := 4983230072969 + 3 ^ 40 * 437602 * 2
def baseEnd_437602 : Nat := 224700161368902113862511

theorem tailTrace_437602 : CollatzResearch.WordTrace tailWord_437602 prefixEnd_437602 224700161368902113862511 := by
  unfold tailWord_437602
  simp only [CollatzResearch.WordTrace]
  refine ⟨3990164040162541329158765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10640437440433443544423373 3990164040162541329158765)
  ·
    refine ⟨1496311515060952998434537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3990164040162541329158765 1496311515060952998434537)
    ·
      refine ⟨1122233636295714748825903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1496311515060952998434537 1122233636295714748825903)
      ·
        refine ⟨1683350454443572123238855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1122233636295714748825903 1683350454443572123238855)
        ·
          refine ⟨2525025681665358184858283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1683350454443572123238855 2525025681665358184858283)
          ·
            refine ⟨3787538522498037277287425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2525025681665358184858283 3787538522498037277287425)
            ·
              refine ⟨2840653891873527957965569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3787538522498037277287425 2840653891873527957965569)
              ·
                refine ⟨2130490418905145968474177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2840653891873527957965569 2130490418905145968474177)
                ·
                  refine ⟨1597867814178859476355633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2130490418905145968474177 1597867814178859476355633)
                  ·
                    refine ⟨1198400860634144607266725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1597867814178859476355633 1198400860634144607266725)
                    ·
                      refine ⟨224700161368902113862511, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1198400860634144607266725 224700161368902113862511)
                      ·
                        rfl

theorem cell23_437602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 2, 2, 2, 2, 4].length) (baseStart_437602 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_437602 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_437602 prefixEnd_437602 := by exact prefixLift 437602
  have htrace : WordTrace (prefixWord ++ tailWord_437602) baseStart_437602 baseEnd_437602 := by
    simpa [prefixWord, tailWord_437602, baseEnd_437602] using wordTrace_append hprefix tailTrace_437602
  have hstable : (prefixWord ++ tailWord_437602).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_437602).length < 2 ^ (prefixWord ++ tailWord_437602).sum := by decide
  have hdescent : baseEnd_437602 < baseStart_437602 := by decide
  rcases family_descends (prefixWord ++ tailWord_437602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_437625 : List Nat := [1, 2, 1, 3, 2, 1, 2, 2, 4, 5]
def baseStart_437625 : Nat := 118140960795 + 437625 * 2 ^ 59
def prefixEnd_437625 : Nat := 4983230072969 + 3 ^ 40 * 437625 * 2
def baseEnd_437625 : Nat := 74903990474651841291635

theorem tailTrace_437625 : CollatzResearch.WordTrace tailWord_437625 prefixEnd_437625 74903990474651841291635 := by
  unfold tailWord_437625
  simp only [CollatzResearch.WordTrace]
  refine ⟨15961495039566840244722329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10640996693044560163148219 15961495039566840244722329)
  ·
    refine ⟨11971121279675130183541747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15961495039566840244722329 11971121279675130183541747)
    ·
      refine ⟨17956681919512695275312621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11971121279675130183541747 17956681919512695275312621)
      ·
        refine ⟨6733755719817260728242233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17956681919512695275312621 6733755719817260728242233)
        ·
          refine ⟨5050316789862945546181675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6733755719817260728242233 5050316789862945546181675)
          ·
            refine ⟨7575475184794418319272513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5050316789862945546181675 7575475184794418319272513)
            ·
              refine ⟨5681606388595813739454385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7575475184794418319272513 5681606388595813739454385)
              ·
                refine ⟨4261204791446860304590789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5681606388595813739454385 4261204791446860304590789)
                ·
                  refine ⟨798975898396286307110773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4261204791446860304590789 798975898396286307110773)
                  ·
                    refine ⟨74903990474651841291635, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 798975898396286307110773 74903990474651841291635)
                    ·
                      rfl

theorem cell23_437625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 2, 2, 4, 5].length) (baseStart_437625 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_437625 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_437625 prefixEnd_437625 := by exact prefixLift 437625
  have htrace : WordTrace (prefixWord ++ tailWord_437625) baseStart_437625 baseEnd_437625 := by
    simpa [prefixWord, tailWord_437625, baseEnd_437625] using wordTrace_append hprefix tailTrace_437625
  have hstable : (prefixWord ++ tailWord_437625).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_437625).length < 2 ^ (prefixWord ++ tailWord_437625).sum := by decide
  have hdescent : baseEnd_437625 < baseStart_437625 := by decide
  rcases family_descends (prefixWord ++ tailWord_437625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_437646 : List Nat := [4, 1, 1, 4, 2, 1, 2, 3, 5]
def baseStart_437646 : Nat := 118140960795 + 437646 * 2 ^ 59
def prefixEnd_437646 : Nat := 4983230072969 + 3 ^ 40 * 437646 * 2
def baseEnd_437646 : Nat := 24969194946411104634701

theorem tailTrace_437646 : CollatzResearch.WordTrace tailWord_437646 prefixEnd_437646 24969194946411104634701 := by
  unfold tailWord_437646
  simp only [CollatzResearch.WordTrace]
  refine ⟨1995282621561345103904599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 10641507314993840554157861 1995282621561345103904599)
  ·
    refine ⟨2992923932342017655856899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1995282621561345103904599 2992923932342017655856899)
    ·
      refine ⟨4489385898513026483785349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2992923932342017655856899 4489385898513026483785349)
      ·
        refine ⟨841759855971192465709753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4489385898513026483785349 841759855971192465709753)
        ·
          refine ⟨631319891978394349282315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 841759855971192465709753 631319891978394349282315)
          ·
            refine ⟨946979837967591523923473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 631319891978394349282315 946979837967591523923473)
            ·
              refine ⟨710234878475693642942605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 946979837967591523923473 710234878475693642942605)
              ·
                refine ⟨266338079428385116103477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 710234878475693642942605 266338079428385116103477)
                ·
                  refine ⟨24969194946411104634701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 266338079428385116103477 24969194946411104634701)
                  ·
                    rfl

theorem cell23_437646_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 2, 1, 2, 3, 5].length) (baseStart_437646 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_437646 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_437646 prefixEnd_437646 := by exact prefixLift 437646
  have htrace : WordTrace (prefixWord ++ tailWord_437646) baseStart_437646 baseEnd_437646 := by
    simpa [prefixWord, tailWord_437646, baseEnd_437646] using wordTrace_append hprefix tailTrace_437646
  have hstable : (prefixWord ++ tailWord_437646).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_437646).length < 2 ^ (prefixWord ++ tailWord_437646).sum := by decide
  have hdescent : baseEnd_437646 < baseStart_437646 := by decide
  rcases family_descends (prefixWord ++ tailWord_437646) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_437682 : List Nat := [3, 2, 1, 1, 1, 1, 2, 1, 6, 2, 3]
def baseStart_437682 : Nat := 118140960795 + 437682 * 2 ^ 59
def prefixEnd_437682 : Nat := 4983230072969 + 3 ^ 40 * 437682 * 2
def baseEnd_437682 : Nat := 224741239821261800862143

theorem tailTrace_437682 : CollatzResearch.WordTrace tailWord_437682 prefixEnd_437682 224741239821261800862143 := by
  unfold tailWord_437682
  simp only [CollatzResearch.WordTrace]
  refine ⟨3990893500090084744886825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10642382666906892653031533 3990893500090084744886825)
  ·
    refine ⟨2993170125067563558665119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3990893500090084744886825 2993170125067563558665119)
    ·
      refine ⟨4489755187601345337997679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2993170125067563558665119 4489755187601345337997679)
      ·
        refine ⟨6734632781402018006996519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4489755187601345337997679 6734632781402018006996519)
        ·
          refine ⟨10101949172103027010494779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6734632781402018006996519 10101949172103027010494779)
          ·
            refine ⟨15152923758154540515742169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10101949172103027010494779 15152923758154540515742169)
            ·
              refine ⟨11364692818615905386806627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15152923758154540515742169 11364692818615905386806627)
              ·
                refine ⟨17047039227923858080209941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11364692818615905386806627 17047039227923858080209941)
                ·
                  refine ⟨799079963808930847509841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 17047039227923858080209941 799079963808930847509841)
                  ·
                    refine ⟨599309972856698135632381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 799079963808930847509841 599309972856698135632381)
                    ·
                      refine ⟨224741239821261800862143, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 599309972856698135632381 224741239821261800862143)
                      ·
                        rfl

theorem cell23_437682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 2, 1, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 2, 1, 6, 2, 3].length) (baseStart_437682 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_437682 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_437682 prefixEnd_437682 := by exact prefixLift 437682
  have htrace : WordTrace (prefixWord ++ tailWord_437682) baseStart_437682 baseEnd_437682 := by
    simpa [prefixWord, tailWord_437682, baseEnd_437682] using wordTrace_append hprefix tailTrace_437682
  have hstable : (prefixWord ++ tailWord_437682).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_437682).length < 2 ^ (prefixWord ++ tailWord_437682).sum := by decide
  have hdescent : baseEnd_437682 < baseStart_437682 := by decide
  rcases family_descends (prefixWord ++ tailWord_437682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_437706 : List Nat := [3, 1, 2, 1, 2, 3, 3, 3, 1, 4]
def baseStart_437706 : Nat := 118140960795 + 437706 * 2 ^ 59
def prefixEnd_437706 : Nat := 4983230072969 + 3 ^ 40 * 437706 * 2
def baseEnd_437706 : Nat := 74917854452323235654011

theorem tailTrace_437706 : CollatzResearch.WordTrace tailWord_437706 prefixEnd_437706 74917854452323235654011 := by
  unfold tailWord_437706
  simp only [CollatzResearch.WordTrace]
  refine ⟨3991112338068347769605243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10642966234848927385613981 3991112338068347769605243)
  ·
    refine ⟨5986668507102521654407865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3991112338068347769605243 5986668507102521654407865)
    ·
      refine ⟨4490001380326891240805899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5986668507102521654407865 4490001380326891240805899)
      ·
        refine ⟨6735002070490336861208849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4490001380326891240805899 6735002070490336861208849)
        ·
          refine ⟨5051251552867752645906637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6735002070490336861208849 5051251552867752645906637)
          ·
            refine ⟨1894219332325407242214989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5051251552867752645906637 1894219332325407242214989)
            ·
              refine ⟨710332249622027715830621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1894219332325407242214989 710332249622027715830621)
              ·
                refine ⟨266374593608260393436483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 710332249622027715830621 266374593608260393436483)
                ·
                  refine ⟨399561890412390590154725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 266374593608260393436483 399561890412390590154725)
                  ·
                    refine ⟨74917854452323235654011, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 399561890412390590154725 74917854452323235654011)
                    ·
                      rfl

theorem cell23_437706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 3, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 3, 3, 3, 1, 4].length) (baseStart_437706 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_437706 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_437706 prefixEnd_437706 := by exact prefixLift 437706
  have htrace : WordTrace (prefixWord ++ tailWord_437706) baseStart_437706 baseEnd_437706 := by
    simpa [prefixWord, tailWord_437706, baseEnd_437706] using wordTrace_append hprefix tailTrace_437706
  have hstable : (prefixWord ++ tailWord_437706).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_437706).length < 2 ^ (prefixWord ++ tailWord_437706).sum := by decide
  have hdescent : baseEnd_437706 < baseStart_437706 := by decide
  rcases family_descends (prefixWord ++ tailWord_437706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_437716 : List Nat := [2, 4, 1, 2, 3, 1, 1, 2, 2, 2, 3]
def baseStart_437716 : Nat := 118140960795 + 437716 * 2 ^ 59
def prefixEnd_437716 : Nat := 4983230072969 + 3 ^ 40 * 437716 * 2
def baseEnd_437716 : Nat := 224758698163514667836987

theorem tailTrace_437716 : CollatzResearch.WordTrace tailWord_437716 prefixEnd_437716 224758698163514667836987 := by
  unfold tailWord_437716
  simp only [CollatzResearch.WordTrace]
  refine ⟨7982407041118581393142501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10643209388158108524190001 7982407041118581393142501)
  ·
    refine ⟨1496701320209734011214219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 7982407041118581393142501 1496701320209734011214219)
    ·
      refine ⟨2245051980314601016821329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1496701320209734011214219 2245051980314601016821329)
      ·
        refine ⟨1683788985235950762615997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2245051980314601016821329 1683788985235950762615997)
        ·
          refine ⟨631420869463481535980999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1683788985235950762615997 631420869463481535980999)
          ·
            refine ⟨947131304195222303971499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 631420869463481535980999 947131304195222303971499)
            ·
              refine ⟨1420696956292833455957249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 947131304195222303971499 1420696956292833455957249)
              ·
                refine ⟨1065522717219625091967937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1420696956292833455957249 1065522717219625091967937)
                ·
                  refine ⟨799142037914718818975953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1065522717219625091967937 799142037914718818975953)
                  ·
                    refine ⟨599356528436039114231965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 799142037914718818975953 599356528436039114231965)
                    ·
                      refine ⟨224758698163514667836987, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 599356528436039114231965 224758698163514667836987)
                      ·
                        rfl

theorem cell23_437716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 3, 1, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 3, 1, 1, 2, 2, 2, 3].length) (baseStart_437716 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_437716 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_437716 prefixEnd_437716 := by exact prefixLift 437716
  have htrace : WordTrace (prefixWord ++ tailWord_437716) baseStart_437716 baseEnd_437716 := by
    simpa [prefixWord, tailWord_437716, baseEnd_437716] using wordTrace_append hprefix tailTrace_437716
  have hstable : (prefixWord ++ tailWord_437716).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_437716).length < 2 ^ (prefixWord ++ tailWord_437716).sum := by decide
  have hdescent : baseEnd_437716 < baseStart_437716 := by decide
  rcases family_descends (prefixWord ++ tailWord_437716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_437779 : List Nat := [1, 1, 1, 2, 1, 6, 1, 4, 2, 4]
def baseStart_437779 : Nat := 118140960795 + 437779 * 2 ^ 59
def prefixEnd_437779 : Nat := 4983230072969 + 3 ^ 40 * 437779 * 2
def baseEnd_437779 : Nat := 74930349148249307116399

theorem tailTrace_437779 : CollatzResearch.WordTrace tailWord_437779 prefixEnd_437779 74930349148249307116399 := by
  unfold tailWord_437779
  simp only [CollatzResearch.WordTrace]
  refine ⟨15967111881008924545828391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10644741254005949697218927 15967111881008924545828391)
  ·
    refine ⟨23950667821513386818742587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15967111881008924545828391 23950667821513386818742587)
    ·
      refine ⟨35926001732270080228113881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23950667821513386818742587 35926001732270080228113881)
      ·
        refine ⟨26944501299202560171085411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35926001732270080228113881 26944501299202560171085411)
        ·
          refine ⟨40416751948803840256628117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26944501299202560171085411 40416751948803840256628117)
          ·
            refine ⟨1894535247600180012029443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 40416751948803840256628117 1894535247600180012029443)
            ·
              refine ⟨2841802871400270018044165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1894535247600180012029443 2841802871400270018044165)
              ·
                refine ⟨532838038387550628383281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2841802871400270018044165 532838038387550628383281)
                ·
                  refine ⟨399628528790662971287461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 532838038387550628383281 399628528790662971287461)
                  ·
                    refine ⟨74930349148249307116399, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 399628528790662971287461 74930349148249307116399)
                    ·
                      rfl

theorem cell23_437779_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 6, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 6, 1, 4, 2, 4].length) (baseStart_437779 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_437779 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_437779 prefixEnd_437779 := by exact prefixLift 437779
  have htrace : WordTrace (prefixWord ++ tailWord_437779) baseStart_437779 baseEnd_437779 := by
    simpa [prefixWord, tailWord_437779, baseEnd_437779] using wordTrace_append hprefix tailTrace_437779
  have hstable : (prefixWord ++ tailWord_437779).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_437779).length < 2 ^ (prefixWord ++ tailWord_437779).sum := by decide
  have hdescent : baseEnd_437779 < baseStart_437779 := by decide
  rcases family_descends (prefixWord ++ tailWord_437779) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_437786 : List Nat := [3, 1, 1, 3, 1, 1, 1, 5, 3, 2, 2]
def baseStart_437786 : Nat := 118140960795 + 437786 * 2 ^ 59
def prefixEnd_437786 : Nat := 4983230072969 + 3 ^ 40 * 437786 * 2
def baseEnd_437786 : Nat := 224794641809329393961665

theorem tailTrace_437786 : CollatzResearch.WordTrace tailWord_437786 prefixEnd_437786 224794641809329393961665 := by
  unfold tailWord_437786
  simp only [CollatzResearch.WordTrace]
  refine ⟨3991841797995891185333303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10644911461322376494222141 3991841797995891185333303)
  ·
    refine ⟨5987762696993836777999955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3991841797995891185333303 5987762696993836777999955)
    ·
      refine ⟨8981644045490755166999933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5987762696993836777999955 8981644045490755166999933)
      ·
        refine ⟨3368116517059033187624975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8981644045490755166999933 3368116517059033187624975)
        ·
          refine ⟨5052174775588549781437463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3368116517059033187624975 5052174775588549781437463)
          ·
            refine ⟨7578262163382824672156195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5052174775588549781437463 7578262163382824672156195)
            ·
              refine ⟨11367393245074237008234293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7578262163382824672156195 11367393245074237008234293)
              ·
                refine ⟨1065693116725709719521965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 11367393245074237008234293 1065693116725709719521965)
                ·
                  refine ⟨399634918772141144820737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1065693116725709719521965 399634918772141144820737)
                  ·
                    refine ⟨299726189079105858615553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 399634918772141144820737 299726189079105858615553)
                    ·
                      refine ⟨224794641809329393961665, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 299726189079105858615553 224794641809329393961665)
                      ·
                        rfl

theorem cell23_437786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 1, 5, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 1, 5, 3, 2, 2].length) (baseStart_437786 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_437786 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_437786 prefixEnd_437786 := by exact prefixLift 437786
  have htrace : WordTrace (prefixWord ++ tailWord_437786) baseStart_437786 baseEnd_437786 := by
    simpa [prefixWord, tailWord_437786, baseEnd_437786] using wordTrace_append hprefix tailTrace_437786
  have hstable : (prefixWord ++ tailWord_437786).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_437786).length < 2 ^ (prefixWord ++ tailWord_437786).sum := by decide
  have hdescent : baseEnd_437786 < baseStart_437786 := by decide
  rcases family_descends (prefixWord ++ tailWord_437786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_437789 : List Nat := [1, 4, 2, 2, 1, 1, 1, 1, 5, 2, 3]
def baseStart_437789 : Nat := 118140960795 + 437789 * 2 ^ 59
def prefixEnd_437789 : Nat := 4983230072969 + 3 ^ 40 * 437789 * 2
def baseEnd_437789 : Nat := 224796182251292882224151

theorem tailTrace_437789 : CollatzResearch.WordTrace tailWord_437789 prefixEnd_437789 224796182251292882224151 := by
  unfold tailWord_437789
  simp only [CollatzResearch.WordTrace]
  refine ⟨15967476610972696253692421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10644984407315130835794947 15967476610972696253692421)
  ·
    refine ⟨2993901864557380547567329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 15967476610972696253692421 2993901864557380547567329)
    ·
      refine ⟨2245426398418035410675497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2993901864557380547567329 2245426398418035410675497)
      ·
        refine ⟨1684069798813526558006623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2245426398418035410675497 1684069798813526558006623)
        ·
          refine ⟨2526104698220289837009935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1684069798813526558006623 2526104698220289837009935)
          ·
            refine ⟨3789157047330434755514903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2526104698220289837009935 3789157047330434755514903)
            ·
              refine ⟨5683735570995652133272355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3789157047330434755514903 5683735570995652133272355)
              ·
                refine ⟨8525603356493478199908533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5683735570995652133272355 8525603356493478199908533)
                ·
                  refine ⟨799275314671263581241425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 8525603356493478199908533 799275314671263581241425)
                  ·
                    refine ⟨599456486003447685931069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 799275314671263581241425 599456486003447685931069)
                    ·
                      refine ⟨224796182251292882224151, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 599456486003447685931069 224796182251292882224151)
                      ·
                        rfl

theorem cell23_437789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 1, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 1, 1, 5, 2, 3].length) (baseStart_437789 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_437789 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_437789 prefixEnd_437789 := by exact prefixLift 437789
  have htrace : WordTrace (prefixWord ++ tailWord_437789) baseStart_437789 baseEnd_437789 := by
    simpa [prefixWord, tailWord_437789, baseEnd_437789] using wordTrace_append hprefix tailTrace_437789
  have hstable : (prefixWord ++ tailWord_437789).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_437789).length < 2 ^ (prefixWord ++ tailWord_437789).sum := by decide
  have hdescent : baseEnd_437789 < baseStart_437789 := by decide
  rcases family_descends (prefixWord ++ tailWord_437789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_437806 : List Nat := [4, 1, 3, 1, 2, 1, 2, 1, 3, 2, 3]
def baseStart_437806 : Nat := 118140960795 + 437806 * 2 ^ 59
def prefixEnd_437806 : Nat := 4983230072969 + 3 ^ 40 * 437806 * 2
def baseEnd_437806 : Nat := 224804911422419315711573

theorem tailTrace_437806 : CollatzResearch.WordTrace tailWord_437806 prefixEnd_437806 224804911422419315711573 := by
  unfold tailWord_437806
  simp only [CollatzResearch.WordTrace]
  refine ⟨1996012081488888519632659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 10645397767940738771374181 1996012081488888519632659)
  ·
    refine ⟨2994018122233332779448989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1996012081488888519632659 2994018122233332779448989)
    ·
      refine ⟨1122756795837499792293371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2994018122233332779448989 1122756795837499792293371)
      ·
        refine ⟨1684135193756249688440057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1122756795837499792293371 1684135193756249688440057)
        ·
          refine ⟨1263101395317187266330043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1684135193756249688440057 1263101395317187266330043)
          ·
            refine ⟨1894652092975780899495065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1263101395317187266330043 1894652092975780899495065)
            ·
              refine ⟨1420989069731835674621299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1894652092975780899495065 1420989069731835674621299)
              ·
                refine ⟨2131483604597753511931949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1420989069731835674621299 2131483604597753511931949)
                ·
                  refine ⟨799306351724157566974481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2131483604597753511931949 799306351724157566974481)
                  ·
                    refine ⟨599479763793118175230861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 799306351724157566974481 599479763793118175230861)
                    ·
                      refine ⟨224804911422419315711573, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 599479763793118175230861 224804911422419315711573)
                      ·
                        rfl

theorem cell23_437806_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 1, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 1, 2, 1, 3, 2, 3].length) (baseStart_437806 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_437806 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_437806 prefixEnd_437806 := by exact prefixLift 437806
  have htrace : WordTrace (prefixWord ++ tailWord_437806) baseStart_437806 baseEnd_437806 := by
    simpa [prefixWord, tailWord_437806, baseEnd_437806] using wordTrace_append hprefix tailTrace_437806
  have hstable : (prefixWord ++ tailWord_437806).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_437806).length < 2 ^ (prefixWord ++ tailWord_437806).sum := by decide
  have hdescent : baseEnd_437806 < baseStart_437806 := by decide
  rcases family_descends (prefixWord ++ tailWord_437806) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_437820 : List Nat := [2, 2, 2, 2, 5, 1, 2, 1, 1, 1, 4]
def baseStart_437820 : Nat := 118140960795 + 437820 * 2 ^ 59
def prefixEnd_437820 : Nat := 4983230072969 + 3 ^ 40 * 437820 * 2
def baseEnd_437820 : Nat := 224812100151582260936509

theorem tailTrace_437820 : CollatzResearch.WordTrace tailWord_437820 prefixEnd_437820 224812100151582260936509 := by
  unfold tailWord_437820
  simp only [CollatzResearch.WordTrace]
  refine ⟨7984303636930194274035457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10645738182573592365380609 7984303636930194274035457)
  ·
    refine ⟨5988227727697645705526593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7984303636930194274035457 5988227727697645705526593)
    ·
      refine ⟨4491170795773234279144945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5988227727697645705526593 4491170795773234279144945)
      ·
        refine ⟨3368378096829925709358709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4491170795773234279144945 3368378096829925709358709)
        ·
          refine ⟨315785446577805535252379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 3368378096829925709358709 315785446577805535252379)
          ·
            refine ⟨473678169866708302878569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 315785446577805535252379 473678169866708302878569)
            ·
              refine ⟨355258627400031227158927, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 473678169866708302878569 355258627400031227158927)
              ·
                refine ⟨532887941100046840738391, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 355258627400031227158927 532887941100046840738391)
                ·
                  refine ⟨799331911650070261107587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 532887941100046840738391 799331911650070261107587)
                  ·
                    refine ⟨1198997867475105391661381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 799331911650070261107587 1198997867475105391661381)
                    ·
                      refine ⟨224812100151582260936509, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1198997867475105391661381 224812100151582260936509)
                      ·
                        rfl

theorem cell23_437820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 5, 1, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 5, 1, 2, 1, 1, 1, 4].length) (baseStart_437820 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_437820 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_437820 prefixEnd_437820 := by exact prefixLift 437820
  have htrace : WordTrace (prefixWord ++ tailWord_437820) baseStart_437820 baseEnd_437820 := by
    simpa [prefixWord, tailWord_437820, baseEnd_437820] using wordTrace_append hprefix tailTrace_437820
  have hstable : (prefixWord ++ tailWord_437820).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_437820).length < 2 ^ (prefixWord ++ tailWord_437820).sum := by decide
  have hdescent : baseEnd_437820 < baseStart_437820 := by decide
  rcases family_descends (prefixWord ++ tailWord_437820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_437823 : List Nat := [1, 1, 2, 2, 3, 5, 2, 1, 1, 2, 3]
def baseStart_437823 : Nat := 118140960795 + 437823 * 2 ^ 59
def prefixEnd_437823 : Nat := 4983230072969 + 3 ^ 40 * 437823 * 2
def baseEnd_437823 : Nat := 224813640593545749198995

theorem tailTrace_437823 : CollatzResearch.WordTrace tailWord_437823 prefixEnd_437823 224813640593545749198995 := by
  unfold tailWord_437823
  simp only [CollatzResearch.WordTrace]
  refine ⟨15968716692849520060430123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10645811128566346706953415 15968716692849520060430123)
  ·
    refine ⟨23953075039274280090645185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15968716692849520060430123 23953075039274280090645185)
    ·
      refine ⟨17964806279455710067983889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23953075039274280090645185 17964806279455710067983889)
      ·
        refine ⟨13473604709591782550987917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17964806279455710067983889 13473604709591782550987917)
        ·
          refine ⟨5052601766096918456620469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13473604709591782550987917 5052601766096918456620469)
          ·
            refine ⟨473681415571586105308169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 5052601766096918456620469 473681415571586105308169)
            ·
              refine ⟨355261061678689578981127, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 473681415571586105308169 355261061678689578981127)
              ·
                refine ⟨532891592518034368471691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 355261061678689578981127 532891592518034368471691)
                ·
                  refine ⟨799337388777051552707537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 532891592518034368471691 799337388777051552707537)
                  ·
                    refine ⟨599503041582788664530653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 799337388777051552707537 599503041582788664530653)
                    ·
                      refine ⟨224813640593545749198995, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 599503041582788664530653 224813640593545749198995)
                      ·
                        rfl

theorem cell23_437823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 5, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 5, 2, 1, 1, 2, 3].length) (baseStart_437823 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_437823 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_437823 prefixEnd_437823 := by exact prefixLift 437823
  have htrace : WordTrace (prefixWord ++ tailWord_437823) baseStart_437823 baseEnd_437823 := by
    simpa [prefixWord, tailWord_437823, baseEnd_437823] using wordTrace_append hprefix tailTrace_437823
  have hstable : (prefixWord ++ tailWord_437823).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_437823).length < 2 ^ (prefixWord ++ tailWord_437823).sum := by decide
  have hdescent : baseEnd_437823 < baseStart_437823 := by decide
  rcases family_descends (prefixWord ++ tailWord_437823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_437836 : List Nat := [2, 2, 1, 3, 1, 4, 1, 1, 4, 1, 3]
def baseStart_437836 : Nat := 118140960795 + 437836 * 2 ^ 59
def prefixEnd_437836 : Nat := 4983230072969 + 3 ^ 40 * 437836 * 2
def baseEnd_437836 : Nat := 224820315842054198336435

theorem tailTrace_437836 : CollatzResearch.WordTrace tailWord_437836 prefixEnd_437836 224820315842054198336435 := by
  unfold tailWord_437836
  simp only [CollatzResearch.WordTrace]
  refine ⟨7984595420901211640326681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10646127227868282187102241 7984595420901211640326681)
  ·
    refine ⟨5988446565675908730245011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7984595420901211640326681 5988446565675908730245011)
    ·
      refine ⟨8982669848513863095367517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5988446565675908730245011 8982669848513863095367517)
      ·
        refine ⟨3368501193192698660762819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8982669848513863095367517 3368501193192698660762819)
        ·
          refine ⟨5052751789789047991144229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3368501193192698660762819 5052751789789047991144229)
          ·
            refine ⟨947390960585446498339543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5052751789789047991144229 947390960585446498339543)
            ·
              refine ⟨1421086440878169747509315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 947390960585446498339543 1421086440878169747509315)
              ·
                refine ⟨2131629661317254621263973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1421086440878169747509315 2131629661317254621263973)
                ·
                  refine ⟨399680561496985241486995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2131629661317254621263973 399680561496985241486995)
                  ·
                    refine ⟨599520842245477862230493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 399680561496985241486995 599520842245477862230493)
                    ·
                      refine ⟨224820315842054198336435, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 599520842245477862230493 224820315842054198336435)
                      ·
                        rfl

theorem cell23_437836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 4, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 4, 1, 1, 4, 1, 3].length) (baseStart_437836 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_437836 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_437836 prefixEnd_437836 := by exact prefixLift 437836
  have htrace : WordTrace (prefixWord ++ tailWord_437836) baseStart_437836 baseEnd_437836 := by
    simpa [prefixWord, tailWord_437836, baseEnd_437836] using wordTrace_append hprefix tailTrace_437836
  have hstable : (prefixWord ++ tailWord_437836).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_437836).length < 2 ^ (prefixWord ++ tailWord_437836).sum := by decide
  have hdescent : baseEnd_437836 < baseStart_437836 := by decide
  rcases family_descends (prefixWord ++ tailWord_437836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_437893 : List Nat := [1, 3, 1, 1, 4, 1, 2, 4, 2, 2, 2]
def baseStart_437893 : Nat := 118140960795 + 437893 * 2 ^ 59
def prefixEnd_437893 : Nat := 4983230072969 + 3 ^ 40 * 437893 * 2
def baseEnd_437893 : Nat := 224849584239360475323673

theorem tailTrace_437893 : CollatzResearch.WordTrace tailWord_437893 prefixEnd_437893 224849584239360475323673 := by
  unfold tailWord_437893
  simp only [CollatzResearch.WordTrace]
  refine ⟨15971269802595922015478333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10647513201730614676985555 15971269802595922015478333)
  ·
    refine ⟨5989226175973470755804375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15971269802595922015478333 5989226175973470755804375)
    ·
      refine ⟨8983839263960206133706563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5989226175973470755804375 8983839263960206133706563)
      ·
        refine ⟨13475758895940309200559845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8983839263960206133706563 13475758895940309200559845)
        ·
          refine ⟨2526704792988807975104971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13475758895940309200559845 2526704792988807975104971)
          ·
            refine ⟨3790057189483211962657457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2526704792988807975104971 3790057189483211962657457)
            ·
              refine ⟨2842542892112408971993093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3790057189483211962657457 2842542892112408971993093)
              ·
                refine ⟨532976792271076682248705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2842542892112408971993093 532976792271076682248705)
                ·
                  refine ⟨399732594203307511686529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 532976792271076682248705 399732594203307511686529)
                  ·
                    refine ⟨299799445652480633764897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 399732594203307511686529 299799445652480633764897)
                    ·
                      refine ⟨224849584239360475323673, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 299799445652480633764897 224849584239360475323673)
                      ·
                        rfl

theorem cell23_437893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 2, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 2, 4, 2, 2, 2].length) (baseStart_437893 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_437893 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_437893 prefixEnd_437893 := by exact prefixLift 437893
  have htrace : WordTrace (prefixWord ++ tailWord_437893) baseStart_437893 baseEnd_437893 := by
    simpa [prefixWord, tailWord_437893, baseEnd_437893] using wordTrace_append hprefix tailTrace_437893
  have hstable : (prefixWord ++ tailWord_437893).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_437893).length < 2 ^ (prefixWord ++ tailWord_437893).sum := by decide
  have hdescent : baseEnd_437893 < baseStart_437893 := by decide
  rcases family_descends (prefixWord ++ tailWord_437893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_437909 : List Nat := [1, 3, 2, 1, 1, 1, 1, 5, 2, 3, 3]
def baseStart_437909 : Nat := 118140960795 + 437909 * 2 ^ 59
def prefixEnd_437909 : Nat := 4983230072969 + 3 ^ 40 * 437909 * 2
def baseEnd_437909 : Nat := 224857799929832412723599

theorem tailTrace_437909 : CollatzResearch.WordTrace tailWord_437909 prefixEnd_437909 224857799929832412723599 := by
  unfold tailWord_437909
  simp only [CollatzResearch.WordTrace]
  refine ⟨15971853370537956748060781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10647902247025304498707187 15971853370537956748060781)
  ·
    refine ⟨5989445013951733780522793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15971853370537956748060781 5989445013951733780522793)
    ·
      refine ⟨4492083760463800335392095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5989445013951733780522793 4492083760463800335392095)
      ·
        refine ⟨6738125640695700503088143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4492083760463800335392095 6738125640695700503088143)
        ·
          refine ⟨10107188461043550754632215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6738125640695700503088143 10107188461043550754632215)
          ·
            refine ⟨15160782691565326131948323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10107188461043550754632215 15160782691565326131948323)
            ·
              refine ⟨22741174037347989197922485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15160782691565326131948323 22741174037347989197922485)
              ·
                refine ⟨2131985066001373987305233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 22741174037347989197922485 2131985066001373987305233)
                ·
                  refine ⟨1598988799501030490478925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2131985066001373987305233 1598988799501030490478925)
                  ·
                    refine ⟨599620799812886433929597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1598988799501030490478925 599620799812886433929597)
                    ·
                      refine ⟨224857799929832412723599, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 599620799812886433929597 224857799929832412723599)
                      ·
                        rfl

theorem cell23_437909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 5, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 5, 2, 3, 3].length) (baseStart_437909 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_437909 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_437909 prefixEnd_437909 := by exact prefixLift 437909
  have htrace : WordTrace (prefixWord ++ tailWord_437909) baseStart_437909 baseEnd_437909 := by
    simpa [prefixWord, tailWord_437909, baseEnd_437909] using wordTrace_append hprefix tailTrace_437909
  have hstable : (prefixWord ++ tailWord_437909).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_437909).length < 2 ^ (prefixWord ++ tailWord_437909).sum := by decide
  have hdescent : baseEnd_437909 < baseStart_437909 := by decide
  rcases family_descends (prefixWord ++ tailWord_437909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_437950 : List Nat := [4, 2, 1, 1, 2, 4, 2, 2, 5]
def baseStart_437950 : Nat := 118140960795 + 437950 * 2 ^ 59
def prefixEnd_437950 : Nat := 4983230072969 + 3 ^ 40 * 437950 * 2
def baseEnd_437950 : Nat := 24986539181851861367879

theorem tailTrace_437950 : CollatzResearch.WordTrace tailWord_437950 prefixEnd_437950 24986539181851861367879 := by
  unfold tailWord_437950
  simp only [CollatzResearch.WordTrace]
  refine ⟨1996668595423677593787913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 10648899175592947166868869 1996668595423677593787913)
  ·
    refine ⟨1497501446567758195340935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1996668595423677593787913 1497501446567758195340935)
    ·
      refine ⟨2246252169851637293011403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1497501446567758195340935 2246252169851637293011403)
      ·
        refine ⟨3369378254777455939517105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2246252169851637293011403 3369378254777455939517105)
        ·
          refine ⟨2527033691083091954637829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3369378254777455939517105 2527033691083091954637829)
          ·
            refine ⟨473818817078079741494593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2527033691083091954637829 473818817078079741494593)
            ·
              refine ⟨355364112808559806120945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 473818817078079741494593 355364112808559806120945)
              ·
                refine ⟨266523084606419854590709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 355364112808559806120945 266523084606419854590709)
                ·
                  refine ⟨24986539181851861367879, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 266523084606419854590709 24986539181851861367879)
                  ·
                    rfl

theorem cell23_437950_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 4, 2, 2, 5].length) (baseStart_437950 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_437950 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_437950 prefixEnd_437950 := by exact prefixLift 437950
  have htrace : WordTrace (prefixWord ++ tailWord_437950) baseStart_437950 baseEnd_437950 := by
    simpa [prefixWord, tailWord_437950, baseEnd_437950] using wordTrace_append hprefix tailTrace_437950
  have hstable : (prefixWord ++ tailWord_437950).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_437950).length < 2 ^ (prefixWord ++ tailWord_437950).sum := by decide
  have hdescent : baseEnd_437950 < baseStart_437950 := by decide
  rcases family_descends (prefixWord ++ tailWord_437950) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_437976 : List Nat := [2, 1, 2, 2, 3, 1, 3, 2, 3, 4]
def baseStart_437976 : Nat := 118140960795 + 437976 * 2 ^ 59
def prefixEnd_437976 : Nat := 4983230072969 + 3 ^ 40 * 437976 * 2
def baseEnd_437976 : Nat := 74964067711227883528597

theorem tailTrace_437976 : CollatzResearch.WordTrace tailWord_437976 prefixEnd_437976 74964067711227883528597 := by
  unfold tailWord_437976
  simp only [CollatzResearch.WordTrace]
  refine ⟨7987148530647613595374891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10649531374196818127166521 7987148530647613595374891)
  ·
    refine ⟨11980722795971420393062337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7987148530647613595374891 11980722795971420393062337)
    ·
      refine ⟨8985542096978565294796753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11980722795971420393062337 8985542096978565294796753)
      ·
        refine ⟨6739156572733923971097565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8985542096978565294796753 6739156572733923971097565)
        ·
          refine ⟨2527183714775221489161587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6739156572733923971097565 2527183714775221489161587)
          ·
            refine ⟨3790775572162832233742381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2527183714775221489161587 3790775572162832233742381)
            ·
              refine ⟨1421540839561062087653393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3790775572162832233742381 1421540839561062087653393)
              ·
                refine ⟨1066155629670796565740045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1421540839561062087653393 1066155629670796565740045)
                ·
                  refine ⟨399808361126548712152517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1066155629670796565740045 399808361126548712152517)
                  ·
                    refine ⟨74964067711227883528597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 399808361126548712152517 74964067711227883528597)
                    ·
                      rfl

theorem cell23_437976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 3, 2, 3, 4].length) (baseStart_437976 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_437976 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_437976 prefixEnd_437976 := by exact prefixLift 437976
  have htrace : WordTrace (prefixWord ++ tailWord_437976) baseStart_437976 baseEnd_437976 := by
    simpa [prefixWord, tailWord_437976, baseEnd_437976] using wordTrace_append hprefix tailTrace_437976
  have hstable : (prefixWord ++ tailWord_437976).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_437976).length < 2 ^ (prefixWord ++ tailWord_437976).sum := by decide
  have hdescent : baseEnd_437976 < baseStart_437976 := by decide
  rcases family_descends (prefixWord ++ tailWord_437976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_437980 : List Nat := [2, 2, 5, 1, 2, 2, 1, 1, 2, 5]
def baseStart_437980 : Nat := 118140960795 + 437980 * 2 ^ 59
def prefixEnd_437980 : Nat := 4983230072969 + 3 ^ 40 * 437980 * 2
def baseEnd_437980 : Nat := 74964752352100544978591

theorem tailTrace_437980 : CollatzResearch.WordTrace tailWord_437980 prefixEnd_437980 74964752352100544978591 := by
  unfold tailWord_437980
  simp only [CollatzResearch.WordTrace]
  refine ⟨7987221476640367936947697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10649628635520490582596929 7987221476640367936947697)
  ·
    refine ⟨5990416107480275952710773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7987221476640367936947697 5990416107480275952710773)
    ·
      refine ⟨561601510076275870566635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 5990416107480275952710773 561601510076275870566635)
      ·
        refine ⟨842402265114413805849953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 561601510076275870566635 842402265114413805849953)
        ·
          refine ⟨631801698835810354387465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 842402265114413805849953 631801698835810354387465)
          ·
            refine ⟨473851274126857765790599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 631801698835810354387465 473851274126857765790599)
            ·
              refine ⟨710776911190286648685899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 473851274126857765790599 710776911190286648685899)
              ·
                refine ⟨1066165366785429973028849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 710776911190286648685899 1066165366785429973028849)
                ·
                  refine ⟨799624025089072479771637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1066165366785429973028849 799624025089072479771637)
                  ·
                    refine ⟨74964752352100544978591, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 799624025089072479771637 74964752352100544978591)
                    ·
                      rfl

theorem cell23_437980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 2, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 2, 2, 1, 1, 2, 5].length) (baseStart_437980 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_437980 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_437980 prefixEnd_437980 := by exact prefixLift 437980
  have htrace : WordTrace (prefixWord ++ tailWord_437980) baseStart_437980 baseEnd_437980 := by
    simpa [prefixWord, tailWord_437980, baseEnd_437980] using wordTrace_append hprefix tailTrace_437980
  have hstable : (prefixWord ++ tailWord_437980).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_437980).length < 2 ^ (prefixWord ++ tailWord_437980).sum := by decide
  have hdescent : baseEnd_437980 < baseStart_437980 := by decide
  rcases family_descends (prefixWord ++ tailWord_437980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_437989 : List Nat := [1, 3, 1, 4, 1, 1, 2, 2, 8]
def baseStart_437989 : Nat := 118140960795 + 437989 * 2 ^ 59
def prefixEnd_437989 : Nat := 4983230072969 + 3 ^ 40 * 437989 * 2
def baseEnd_437989 : Nat := 24988764264688011080359

theorem tailTrace_437989 : CollatzResearch.WordTrace tailWord_437989 prefixEnd_437989 24988764264688011080359 := by
  unfold tailWord_437989
  simp only [CollatzResearch.WordTrace]
  refine ⟨15974771210248130410973021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10649847473498753607315347 15974771210248130410973021)
  ·
    refine ⟨5990539203843048904114883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15974771210248130410973021 5990539203843048904114883)
    ·
      refine ⟨8985808805764573356172325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5990539203843048904114883 8985808805764573356172325)
      ·
        refine ⟨1684839151080857504282311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8985808805764573356172325 1684839151080857504282311)
        ·
          refine ⟨2527258726621286256423467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1684839151080857504282311 2527258726621286256423467)
          ·
            refine ⟨3790888089931929384635201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2527258726621286256423467 3790888089931929384635201)
            ·
              refine ⟨2843166067448947038476401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3790888089931929384635201 2843166067448947038476401)
              ·
                refine ⟨2132374550586710278857301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2843166067448947038476401 2132374550586710278857301)
                ·
                  refine ⟨24988764264688011080359, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 2132374550586710278857301 24988764264688011080359)
                  ·
                    rfl

theorem cell23_437989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 2, 2, 8].length) (baseStart_437989 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_437989 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_437989 prefixEnd_437989 := by exact prefixLift 437989
  have htrace : WordTrace (prefixWord ++ tailWord_437989) baseStart_437989 baseEnd_437989 := by
    simpa [prefixWord, tailWord_437989, baseEnd_437989] using wordTrace_append hprefix tailTrace_437989
  have hstable : (prefixWord ++ tailWord_437989).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_437989).length < 2 ^ (prefixWord ++ tailWord_437989).sum := by decide
  have hdescent : baseEnd_437989 < baseStart_437989 := by decide
  rcases family_descends (prefixWord ++ tailWord_437989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_438006 : List Nat := [5, 1, 1, 1, 1, 4, 1, 1, 8]
def baseStart_438006 : Nat := 118140960795 + 438006 * 2 ^ 59
def prefixEnd_438006 : Nat := 4983230072969 + 3 ^ 40 * 438006 * 2
def baseEnd_438006 : Nat := 24989734172590948134517

theorem tailTrace_438006 : CollatzResearch.WordTrace tailWord_438006 prefixEnd_438006 24989734172590948134517 := by
  unfold tailWord_438006
  simp only [CollatzResearch.WordTrace]
  refine ⟨998461953199158894646367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 10650260834124361542894581 998461953199158894646367)
  ·
    refine ⟨1497692929798738341969551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 998461953199158894646367 1497692929798738341969551)
    ·
      refine ⟨2246539394698107512954327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1497692929798738341969551 2246539394698107512954327)
      ·
        refine ⟨3369809092047161269431491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2246539394698107512954327 3369809092047161269431491)
        ·
          refine ⟨5054713638070741904147237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3369809092047161269431491 5054713638070741904147237)
          ·
            refine ⟨947758807138264107027607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5054713638070741904147237 947758807138264107027607)
            ·
              refine ⟨1421638210707396160541411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 947758807138264107027607 1421638210707396160541411)
              ·
                refine ⟨2132457316061094240812117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1421638210707396160541411 2132457316061094240812117)
                ·
                  refine ⟨24989734172590948134517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 2132457316061094240812117 24989734172590948134517)
                  ·
                    rfl

theorem cell23_438006_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 4, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 4, 1, 1, 8].length) (baseStart_438006 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_438006 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_438006 prefixEnd_438006 := by exact prefixLift 438006
  have htrace : WordTrace (prefixWord ++ tailWord_438006) baseStart_438006 baseEnd_438006 := by
    simpa [prefixWord, tailWord_438006, baseEnd_438006] using wordTrace_append hprefix tailTrace_438006
  have hstable : (prefixWord ++ tailWord_438006).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_438006).length < 2 ^ (prefixWord ++ tailWord_438006).sum := by decide
  have hdescent : baseEnd_438006 < baseStart_438006 := by decide
  rcases family_descends (prefixWord ++ tailWord_438006) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_438016 : List Nat := [2, 1, 1, 2, 1, 1, 2, 2, 7, 1, 3]
def baseStart_438016 : Nat := 118140960795 + 438016 * 2 ^ 59
def prefixEnd_438016 : Nat := 4983230072969 + 3 ^ 40 * 438016 * 2
def baseEnd_438016 : Nat := 224912742359863494085607

theorem tailTrace_438016 : CollatzResearch.WordTrace tailWord_438016 prefixEnd_438016 224912742359863494085607 := by
  unfold tailWord_438016
  simp only [CollatzResearch.WordTrace]
  refine ⟨7987877990575157011102951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10650503987433542681470601 7987877990575157011102951)
  ·
    refine ⟨11981816985862735516654427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7987877990575157011102951 11981816985862735516654427)
    ·
      refine ⟨17972725478794103274981641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11981816985862735516654427 17972725478794103274981641)
      ·
        refine ⟨13479544109095577456236231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17972725478794103274981641 13479544109095577456236231)
        ·
          refine ⟨20219316163643366184354347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13479544109095577456236231 20219316163643366184354347)
          ·
            refine ⟨30328974245465049276531521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20219316163643366184354347 30328974245465049276531521)
            ·
              refine ⟨22746730684098786957398641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30328974245465049276531521 22746730684098786957398641)
              ·
                refine ⟨17060048013074090218048981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22746730684098786957398641 17060048013074090218048981)
                ·
                  refine ⟨399844875306423989485523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17060048013074090218048981 399844875306423989485523)
                  ·
                    refine ⟨599767312959635984228285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 399844875306423989485523 599767312959635984228285)
                    ·
                      refine ⟨224912742359863494085607, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 599767312959635984228285 224912742359863494085607)
                      ·
                        rfl

theorem cell23_438016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 2, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 2, 7, 1, 3].length) (baseStart_438016 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_438016 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_438016 prefixEnd_438016 := by exact prefixLift 438016
  have htrace : WordTrace (prefixWord ++ tailWord_438016) baseStart_438016 baseEnd_438016 := by
    simpa [prefixWord, tailWord_438016, baseEnd_438016] using wordTrace_append hprefix tailTrace_438016
  have hstable : (prefixWord ++ tailWord_438016).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_438016).length < 2 ^ (prefixWord ++ tailWord_438016).sum := by decide
  have hdescent : baseEnd_438016 < baseStart_438016 := by decide
  rcases family_descends (prefixWord ++ tailWord_438016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_438019 : List Nat := [1, 1, 1, 3, 2, 2, 2, 1, 5, 5]
def baseStart_438019 : Nat := 118140960795 + 438019 * 2 ^ 59
def prefixEnd_438019 : Nat := 4983230072969 + 3 ^ 40 * 438019 * 2
def baseEnd_438019 : Nat := 74971427600608994116031

theorem tailTrace_438019 : CollatzResearch.WordTrace tailWord_438019 prefixEnd_438019 74971427600608994116031 := by
  unfold tailWord_438019
  simp only [CollatzResearch.WordTrace]
  refine ⟨15975865400139445534565111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10650576933426297023043407 15975865400139445534565111)
  ·
    refine ⟨23963798100209168301847667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15975865400139445534565111 23963798100209168301847667)
    ·
      refine ⟨35945697150313752452771501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23963798100209168301847667 35945697150313752452771501)
      ·
        refine ⟨13479636431367657169789313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35945697150313752452771501 13479636431367657169789313)
        ·
          refine ⟨10109727323525742877341985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13479636431367657169789313 10109727323525742877341985)
          ·
            refine ⟨7582295492644307158006489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10109727323525742877341985 7582295492644307158006489)
            ·
              refine ⟨5686721619483230368504867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7582295492644307158006489 5686721619483230368504867)
              ·
                refine ⟨8530082429224845552757301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5686721619483230368504867 8530082429224845552757301)
                ·
                  refine ⟨799695227739829270570997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 8530082429224845552757301 799695227739829270570997)
                  ·
                    refine ⟨74971427600608994116031, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 799695227739829270570997 74971427600608994116031)
                    ·
                      rfl

theorem cell23_438019_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 2, 1, 5, 5].length) (baseStart_438019 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_438019 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_438019 prefixEnd_438019 := by exact prefixLift 438019
  have htrace : WordTrace (prefixWord ++ tailWord_438019) baseStart_438019 baseEnd_438019 := by
    simpa [prefixWord, tailWord_438019, baseEnd_438019] using wordTrace_append hprefix tailTrace_438019
  have hstable : (prefixWord ++ tailWord_438019).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_438019).length < 2 ^ (prefixWord ++ tailWord_438019).sum := by decide
  have hdescent : baseEnd_438019 < baseStart_438019 := by decide
  rcases family_descends (prefixWord ++ tailWord_438019) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_438067 : List Nat := [1, 1, 1, 2, 8, 1, 1, 1, 3, 1, 3]
def baseStart_438067 : Nat := 118140960795 + 438067 * 2 ^ 59
def prefixEnd_438067 : Nat := 4983230072969 + 3 ^ 40 * 438067 * 2
def baseEnd_438067 : Nat := 224938929873242794547873

theorem tailTrace_438067 : CollatzResearch.WordTrace tailWord_438067 prefixEnd_438067 224938929873242794547873 := by
  unfold tailWord_438067
  simp only [CollatzResearch.WordTrace]
  refine ⟨15977616103965549732312455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10651744069310366488208303 15977616103965549732312455)
  ·
    refine ⟨23966424155948324598468683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15977616103965549732312455 23966424155948324598468683)
    ·
      refine ⟨35949636233922486897703025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23966424155948324598468683 35949636233922486897703025)
      ·
        refine ⟨26962227175441865173277269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35949636233922486897703025 26962227175441865173277269)
        ·
          refine ⟨315963599712209357499343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 26962227175441865173277269 315963599712209357499343)
          ·
            refine ⟨473945399568314036249015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 315963599712209357499343 473945399568314036249015)
            ·
              refine ⟨710918099352471054373523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 473945399568314036249015 710918099352471054373523)
              ·
                refine ⟨1066377149028706581560285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 710918099352471054373523 1066377149028706581560285)
                ·
                  refine ⟨399891430885764968085107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1066377149028706581560285 399891430885764968085107)
                  ·
                    refine ⟨599837146328647452127661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 399891430885764968085107 599837146328647452127661)
                    ·
                      refine ⟨224938929873242794547873, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 599837146328647452127661 224938929873242794547873)
                      ·
                        rfl

theorem cell23_438067_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 8, 1, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 8, 1, 1, 1, 3, 1, 3].length) (baseStart_438067 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_438067 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_438067 prefixEnd_438067 := by exact prefixLift 438067
  have htrace : WordTrace (prefixWord ++ tailWord_438067) baseStart_438067 baseEnd_438067 := by
    simpa [prefixWord, tailWord_438067, baseEnd_438067] using wordTrace_append hprefix tailTrace_438067
  have hstable : (prefixWord ++ tailWord_438067).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_438067).length < 2 ^ (prefixWord ++ tailWord_438067).sum := by decide
  have hdescent : baseEnd_438067 < baseStart_438067 := by decide
  rcases family_descends (prefixWord ++ tailWord_438067) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_438076 : List Nat := [2, 2, 2, 2, 1, 1, 4, 2, 1, 1, 5]
def baseStart_438076 : Nat := 118140960795 + 438076 * 2 ^ 59
def prefixEnd_438076 : Nat := 4983230072969 + 3 ^ 40 * 438076 * 2
def baseEnd_438076 : Nat := 224943551199133259335331

theorem tailTrace_438076 : CollatzResearch.WordTrace tailWord_438076 prefixEnd_438076 224943551199133259335331 := by
  unfold tailWord_438076
  simp only [CollatzResearch.WordTrace]
  refine ⟨7988972180466472134695041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10651962907288629512926721 7988972180466472134695041)
  ·
    refine ⟨5991729135349854101021281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7988972180466472134695041 5991729135349854101021281)
    ·
      refine ⟨4493796851512390575765961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5991729135349854101021281 4493796851512390575765961)
      ·
        refine ⟨3370347638634292931824471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4493796851512390575765961 3370347638634292931824471)
        ·
          refine ⟨5055521457951439397736707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3370347638634292931824471 5055521457951439397736707)
          ·
            refine ⟨7583282186927159096605061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5055521457951439397736707 7583282186927159096605061)
            ·
              refine ⟨1421865410048842330613449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7583282186927159096605061 1421865410048842330613449)
              ·
                refine ⟨1066399057536631747960087, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1421865410048842330613449 1066399057536631747960087)
                ·
                  refine ⟨1599598586304947621940131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1066399057536631747960087 1599598586304947621940131)
                  ·
                    refine ⟨2399397879457421432910197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1599598586304947621940131 2399397879457421432910197)
                    ·
                      refine ⟨224943551199133259335331, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 2399397879457421432910197 224943551199133259335331)
                      ·
                        rfl

theorem cell23_438076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 4, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 4, 2, 1, 1, 5].length) (baseStart_438076 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_438076 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_438076 prefixEnd_438076 := by exact prefixLift 438076
  have htrace : WordTrace (prefixWord ++ tailWord_438076) baseStart_438076 baseEnd_438076 := by
    simpa [prefixWord, tailWord_438076, baseEnd_438076] using wordTrace_append hprefix tailTrace_438076
  have hstable : (prefixWord ++ tailWord_438076).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_438076).length < 2 ^ (prefixWord ++ tailWord_438076).sum := by decide
  have hdescent : baseEnd_438076 < baseStart_438076 := by decide
  rcases family_descends (prefixWord ++ tailWord_438076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_438083 : List Nat := [1, 1, 1, 3, 1, 6, 1, 3, 2, 4]
def baseStart_438083 : Nat := 118140960795 + 438083 * 2 ^ 59
def prefixEnd_438083 : Nat := 4983230072969 + 3 ^ 40 * 438083 * 2
def baseEnd_438083 : Nat := 74982381854571577315933

theorem tailTrace_438083 : CollatzResearch.WordTrace tailWord_438083 prefixEnd_438083 74982381854571577315933 := by
  unfold tailWord_438083
  simp only [CollatzResearch.WordTrace]
  refine ⟨15978199671907584464894903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10652133114605056309929935 15978199671907584464894903)
  ·
    refine ⟨23967299507861376697342355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15978199671907584464894903 23967299507861376697342355)
    ·
      refine ⟨35950949261792065046013533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23967299507861376697342355 35950949261792065046013533)
      ·
        refine ⟨13481605973172024392255075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35950949261792065046013533 13481605973172024392255075)
        ·
          refine ⟨20222408959758036588382613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13481605973172024392255075 20222408959758036588382613)
          ·
            refine ⟨947925419988657965080435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 20222408959758036588382613 947925419988657965080435)
            ·
              refine ⟨1421888129982986947620653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 947925419988657965080435 1421888129982986947620653)
              ·
                refine ⟨533208048743620105357745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1421888129982986947620653 533208048743620105357745)
                ·
                  refine ⟨399906036557715079018309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 533208048743620105357745 399906036557715079018309)
                  ·
                    refine ⟨74982381854571577315933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 399906036557715079018309 74982381854571577315933)
                    ·
                      rfl

theorem cell23_438083_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 6, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 6, 1, 3, 2, 4].length) (baseStart_438083 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_438083 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_438083 prefixEnd_438083 := by exact prefixLift 438083
  have htrace : WordTrace (prefixWord ++ tailWord_438083) baseStart_438083 baseEnd_438083 := by
    simpa [prefixWord, tailWord_438083, baseEnd_438083] using wordTrace_append hprefix tailTrace_438083
  have hstable : (prefixWord ++ tailWord_438083).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_438083).length < 2 ^ (prefixWord ++ tailWord_438083).sum := by decide
  have hdescent : baseEnd_438083 < baseStart_438083 := by decide
  rcases family_descends (prefixWord ++ tailWord_438083) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_438103 : List Nat := [1, 1, 3, 2, 5, 1, 1, 2, 1, 2, 4]
def baseStart_438103 : Nat := 118140960795 + 438103 * 2 ^ 59
def prefixEnd_438103 : Nat := 4983230072969 + 3 ^ 40 * 438103 * 2
def baseEnd_438103 : Nat := 224957415176804653697707

theorem tailTrace_438103 : CollatzResearch.WordTrace tailWord_438103 prefixEnd_438103 224957415176804653697707 := by
  unfold tailWord_438103
  simp only [CollatzResearch.WordTrace]
  refine ⟨15978929131835127880622963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10652619421223418587081975 15978929131835127880622963)
  ·
    refine ⟨23968393697752691820934445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15978929131835127880622963 23968393697752691820934445)
    ·
      refine ⟨8988147636657259432850417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23968393697752691820934445 8988147636657259432850417)
      ·
        refine ⟨6741110727492944574637813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8988147636657259432850417 6741110727492944574637813)
        ·
          refine ⟨631979130702463553872295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 6741110727492944574637813 631979130702463553872295)
          ·
            refine ⟨947968696053695330808443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 631979130702463553872295 947968696053695330808443)
            ·
              refine ⟨1421953044080542996212665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 947968696053695330808443 1421953044080542996212665)
              ·
                refine ⟨1066464783060407247159499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1421953044080542996212665 1066464783060407247159499)
                ·
                  refine ⟨1599697174590610870739249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1066464783060407247159499 1599697174590610870739249)
                  ·
                    refine ⟨1199772880942958153054437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1599697174590610870739249 1199772880942958153054437)
                    ·
                      refine ⟨224957415176804653697707, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1199772880942958153054437 224957415176804653697707)
                      ·
                        rfl

theorem cell23_438103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 5, 1, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 5, 1, 1, 2, 1, 2, 4].length) (baseStart_438103 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_438103 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_438103 prefixEnd_438103 := by exact prefixLift 438103
  have htrace : WordTrace (prefixWord ++ tailWord_438103) baseStart_438103 baseEnd_438103 := by
    simpa [prefixWord, tailWord_438103, baseEnd_438103] using wordTrace_append hprefix tailTrace_438103
  have hstable : (prefixWord ++ tailWord_438103).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_438103).length < 2 ^ (prefixWord ++ tailWord_438103).sum := by decide
  have hdescent : baseEnd_438103 < baseStart_438103 := by decide
  rcases family_descends (prefixWord ++ tailWord_438103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_438124 : List Nat := [2, 2, 1, 1, 4, 2, 4, 2, 1, 2, 2]
def baseStart_438124 : Nat := 118140960795 + 438124 * 2 ^ 59
def prefixEnd_438124 : Nat := 4983230072969 + 3 ^ 40 * 438124 * 2
def baseEnd_438124 : Nat := 224968198270549071535111

theorem tailTrace_438124 : CollatzResearch.WordTrace tailWord_438124 prefixEnd_438124 224968198270549071535111 := by
  unfold tailWord_438124
  simp only [CollatzResearch.WordTrace]
  refine ⟨7989847532379524233568713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10653130043172698978091617 7989847532379524233568713)
  ·
    refine ⟨5992385649284643175176535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7989847532379524233568713 5992385649284643175176535)
    ·
      refine ⟨8988578473926964762764803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5992385649284643175176535 8988578473926964762764803)
      ·
        refine ⟨13482867710890447144147205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8988578473926964762764803 13482867710890447144147205)
        ·
          refine ⟨2528037695791958839527601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13482867710890447144147205 2528037695791958839527601)
          ·
            refine ⟨1896028271843969129645701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2528037695791958839527601 1896028271843969129645701)
            ·
              refine ⟨355505300970744211808569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1896028271843969129645701 355505300970744211808569)
              ·
                refine ⟨266628975728058158856427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 355505300970744211808569 266628975728058158856427)
                ·
                  refine ⟨399943463592087238284641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 266628975728058158856427 399943463592087238284641)
                  ·
                    refine ⟨299957597694065428713481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 399943463592087238284641 299957597694065428713481)
                    ·
                      refine ⟨224968198270549071535111, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 299957597694065428713481 224968198270549071535111)
                      ·
                        rfl

theorem cell23_438124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 2, 4, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 2, 4, 2, 1, 2, 2].length) (baseStart_438124 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_438124 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_438124 prefixEnd_438124 := by exact prefixLift 438124
  have htrace : WordTrace (prefixWord ++ tailWord_438124) baseStart_438124 baseEnd_438124 := by
    simpa [prefixWord, tailWord_438124, baseEnd_438124] using wordTrace_append hprefix tailTrace_438124
  have hstable : (prefixWord ++ tailWord_438124).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_438124).length < 2 ^ (prefixWord ++ tailWord_438124).sum := by decide
  have hdescent : baseEnd_438124 < baseStart_438124 := by decide
  rcases family_descends (prefixWord ++ tailWord_438124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_438167 : List Nat := [1, 1, 3, 3, 1, 3, 4, 1, 1, 3, 2]
def baseStart_438167 : Nat := 118140960795 + 438167 * 2 ^ 59
def prefixEnd_438167 : Nat := 4983230072969 + 3 ^ 40 * 438167 * 2
def baseEnd_438167 : Nat := 224990277938692403297413

theorem tailTrace_438167 : CollatzResearch.WordTrace tailWord_438167 prefixEnd_438167 224990277938692403297413 := by
  unfold tailWord_438167
  simp only [CollatzResearch.WordTrace]
  refine ⟨15981263403603266810952755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10654175602402177873968503 15981263403603266810952755)
  ·
    refine ⟨23971895105404900216429133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15981263403603266810952755 23971895105404900216429133)
    ·
      refine ⟨8989460664526837581160925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23971895105404900216429133 8989460664526837581160925)
      ·
        refine ⟨3371047749197564092935347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8989460664526837581160925 3371047749197564092935347)
        ·
          refine ⟨5056571623796346139403021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3371047749197564092935347 5056571623796346139403021)
          ·
            refine ⟨1896214358923629802276133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5056571623796346139403021 1896214358923629802276133)
            ·
              refine ⟨355540192298180587926775, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1896214358923629802276133 355540192298180587926775)
              ·
                refine ⟨533310288447270881890163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 355540192298180587926775 533310288447270881890163)
                ·
                  refine ⟨799965432670906322835245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 533310288447270881890163 799965432670906322835245)
                  ·
                    refine ⟨299987037251589871063217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 799965432670906322835245 299987037251589871063217)
                    ·
                      refine ⟨224990277938692403297413, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 299987037251589871063217 224990277938692403297413)
                      ·
                        rfl

theorem cell23_438167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 3, 4, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 3, 4, 1, 1, 3, 2].length) (baseStart_438167 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_438167 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_438167 prefixEnd_438167 := by exact prefixLift 438167
  have htrace : WordTrace (prefixWord ++ tailWord_438167) baseStart_438167 baseEnd_438167 := by
    simpa [prefixWord, tailWord_438167, baseEnd_438167] using wordTrace_append hprefix tailTrace_438167
  have hstable : (prefixWord ++ tailWord_438167).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_438167).length < 2 ^ (prefixWord ++ tailWord_438167).sum := by decide
  have hdescent : baseEnd_438167 < baseStart_438167 := by decide
  rcases family_descends (prefixWord ++ tailWord_438167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_438174 : List Nat := [4, 3, 1, 3, 1, 1, 1, 1, 4, 1, 3]
def baseStart_438174 : Nat := 118140960795 + 438174 * 2 ^ 59
def prefixEnd_438174 : Nat := 4983230072969 + 3 ^ 40 * 438174 * 2
def baseEnd_438174 : Nat := 224993872303273875909881

theorem tailTrace_438174 : CollatzResearch.WordTrace tailWord_438174 prefixEnd_438174 224993872303273875909881 := by
  unfold tailWord_438174
  simp only [CollatzResearch.WordTrace]
  refine ⟨1997689839322238375807197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 10654345809718604670971717 1997689839322238375807197)
  ·
    refine ⟨749133689745839390927699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1997689839322238375807197 749133689745839390927699)
    ·
      refine ⟨1123700534618759086391549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 749133689745839390927699 1123700534618759086391549)
      ·
        refine ⟨421387700482034657396831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1123700534618759086391549 421387700482034657396831)
        ·
          refine ⟨632081550723051986095247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 421387700482034657396831 632081550723051986095247)
          ·
            refine ⟨948122326084577979142871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 632081550723051986095247 948122326084577979142871)
            ·
              refine ⟨1422183489126866968714307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 948122326084577979142871 1422183489126866968714307)
              ·
                refine ⟨2133275233690300453071461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1422183489126866968714307 2133275233690300453071461)
                ·
                  refine ⟨399989106316931334950899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2133275233690300453071461 399989106316931334950899)
                  ·
                    refine ⟨599983659475397002426349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 399989106316931334950899 599983659475397002426349)
                    ·
                      refine ⟨224993872303273875909881, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 599983659475397002426349 224993872303273875909881)
                      ·
                        rfl

theorem cell23_438174_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 1, 1, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 1, 1, 1, 1, 4, 1, 3].length) (baseStart_438174 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_438174 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_438174 prefixEnd_438174 := by exact prefixLift 438174
  have htrace : WordTrace (prefixWord ++ tailWord_438174) baseStart_438174 baseEnd_438174 := by
    simpa [prefixWord, tailWord_438174, baseEnd_438174] using wordTrace_append hprefix tailTrace_438174
  have hstable : (prefixWord ++ tailWord_438174).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_438174).length < 2 ^ (prefixWord ++ tailWord_438174).sum := by decide
  have hdescent : baseEnd_438174 < baseStart_438174 := by decide
  rcases family_descends (prefixWord ++ tailWord_438174) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_438193 : List Nat := [1, 2, 2, 4, 2, 1, 2, 1, 2, 2, 4]
def baseStart_438193 : Nat := 118140960795 + 438193 * 2 ^ 59
def prefixEnd_438193 : Nat := 4983230072969 + 3 ^ 40 * 438193 * 2
def baseEnd_438193 : Nat := 225003628435709301572293

theorem tailTrace_438193 : CollatzResearch.WordTrace tailWord_438193 prefixEnd_438193 225003628435709301572293 := by
  unfold tailWord_438193
  simp only [CollatzResearch.WordTrace]
  refine ⟨15982211701509073251399233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10654807801006048834266155 15982211701509073251399233)
  ·
    refine ⟨11986658776131804938549425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15982211701509073251399233 11986658776131804938549425)
    ·
      refine ⟨8989994082098853703912069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11986658776131804938549425 8989994082098853703912069)
      ·
        refine ⟨1685623890393535069483513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8989994082098853703912069 1685623890393535069483513)
        ·
          refine ⟨1264217917795151302112635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1685623890393535069483513 1264217917795151302112635)
          ·
            refine ⟨1896326876692726953168953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1264217917795151302112635 1896326876692726953168953)
            ·
              refine ⟨1422245157519545214876715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1896326876692726953168953 1422245157519545214876715)
              ·
                refine ⟨2133367736279317822315073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1422245157519545214876715 2133367736279317822315073)
                ·
                  refine ⟨1600025802209488366736305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2133367736279317822315073 1600025802209488366736305)
                  ·
                    refine ⟨1200019351657116275052229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1600025802209488366736305 1200019351657116275052229)
                    ·
                      refine ⟨225003628435709301572293, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1200019351657116275052229 225003628435709301572293)
                      ·
                        rfl

theorem cell23_438193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 1, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 1, 2, 1, 2, 2, 4].length) (baseStart_438193 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_438193 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_438193 prefixEnd_438193 := by exact prefixLift 438193
  have htrace : WordTrace (prefixWord ++ tailWord_438193) baseStart_438193 baseEnd_438193 := by
    simpa [prefixWord, tailWord_438193, baseEnd_438193] using wordTrace_append hprefix tailTrace_438193
  have hstable : (prefixWord ++ tailWord_438193).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_438193).length < 2 ^ (prefixWord ++ tailWord_438193).sum := by decide
  have hdescent : baseEnd_438193 < baseStart_438193 := by decide
  rcases family_descends (prefixWord ++ tailWord_438193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_438197 : List Nat := [1, 3, 3, 2, 1, 4, 1, 1, 1, 4, 2]
def baseStart_438197 : Nat := 118140960795 + 438197 * 2 ^ 59
def prefixEnd_438197 : Nat := 4983230072969 + 3 ^ 40 * 438197 * 2
def baseEnd_438197 : Nat := 225005682358327285922275

theorem tailTrace_438197 : CollatzResearch.WordTrace tailWord_438197 prefixEnd_438197 225005682358327285922275 := by
  unfold tailWord_438197
  simp only [CollatzResearch.WordTrace]
  refine ⟨15982357593494581934544845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10654905062329721289696563 15982357593494581934544845)
  ·
    refine ⟨5993384097560468225454317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15982357593494581934544845 5993384097560468225454317)
    ·
      refine ⟨2247519036585175584545369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5993384097560468225454317 2247519036585175584545369)
      ·
        refine ⟨1685639277438881688409027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2247519036585175584545369 1685639277438881688409027)
        ·
          refine ⟨2528458916158322532613541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1685639277438881688409027 2528458916158322532613541)
          ·
            refine ⟨474086046779685474865039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2528458916158322532613541 474086046779685474865039)
            ·
              refine ⟨711129070169528212297559, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 474086046779685474865039 711129070169528212297559)
              ·
                refine ⟨1066693605254292318446339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 711129070169528212297559 1066693605254292318446339)
                ·
                  refine ⟨1600040407881438477669509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1066693605254292318446339 1600040407881438477669509)
                  ·
                    refine ⟨300007576477769714563033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1600040407881438477669509 300007576477769714563033)
                    ·
                      refine ⟨225005682358327285922275, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 300007576477769714563033 225005682358327285922275)
                      ·
                        rfl

theorem cell23_438197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 4, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 4, 1, 1, 1, 4, 2].length) (baseStart_438197 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_438197 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_438197 prefixEnd_438197 := by exact prefixLift 438197
  have htrace : WordTrace (prefixWord ++ tailWord_438197) baseStart_438197 baseEnd_438197 := by
    simpa [prefixWord, tailWord_438197, baseEnd_438197] using wordTrace_append hprefix tailTrace_438197
  have hstable : (prefixWord ++ tailWord_438197).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_438197).length < 2 ^ (prefixWord ++ tailWord_438197).sum := by decide
  have hdescent : baseEnd_438197 < baseStart_438197 := by decide
  rcases family_descends (prefixWord ++ tailWord_438197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_438220 : List Nat := [2, 2, 1, 4, 1, 2, 3, 3, 5]
def baseStart_438220 : Nat := 118140960795 + 438220 * 2 ^ 59
def prefixEnd_438220 : Nat := 4983230072969 + 3 ^ 40 * 438220 * 2
def baseEnd_438220 : Nat := 25001943601486743992741

theorem tailTrace_438220 : CollatzResearch.WordTrace tailWord_438220 prefixEnd_438220 25001943601486743992741 := by
  unfold tailWord_438220
  simp only [CollatzResearch.WordTrace]
  refine ⟨7991598236205628431316057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10655464314940837908421409 7991598236205628431316057)
  ·
    refine ⟨5993698677154221323487043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7991598236205628431316057 5993698677154221323487043)
    ·
      refine ⟨8990548015731331985230565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5993698677154221323487043 8990548015731331985230565)
      ·
        refine ⟨1685727752949624747230731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8990548015731331985230565 1685727752949624747230731)
        ·
          refine ⟨2528591629424437120846097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1685727752949624747230731 2528591629424437120846097)
          ·
            refine ⟨1896443722068327840634573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2528591629424437120846097 1896443722068327840634573)
            ·
              refine ⟨711166395775622940237965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1896443722068327840634573 711166395775622940237965)
              ·
                refine ⟨266687398415858602589237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 711166395775622940237965 266687398415858602589237)
                ·
                  refine ⟨25001943601486743992741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 266687398415858602589237 25001943601486743992741)
                  ·
                    rfl

theorem cell23_438220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 2, 3, 3, 5].length) (baseStart_438220 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_438220 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_438220 prefixEnd_438220 := by exact prefixLift 438220
  have htrace : WordTrace (prefixWord ++ tailWord_438220) baseStart_438220 baseEnd_438220 := by
    simpa [prefixWord, tailWord_438220, baseEnd_438220] using wordTrace_append hprefix tailTrace_438220
  have hstable : (prefixWord ++ tailWord_438220).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_438220).length < 2 ^ (prefixWord ++ tailWord_438220).sum := by decide
  have hdescent : baseEnd_438220 < baseStart_438220 := by decide
  rcases family_descends (prefixWord ++ tailWord_438220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_438237 : List Nat := [1, 4, 3, 1, 4, 1, 1, 1, 7]
def baseStart_438237 : Nat := 118140960795 + 438237 * 2 ^ 59
def prefixEnd_438237 : Nat := 4983230072969 + 3 ^ 40 * 438237 * 2
def baseEnd_438237 : Nat := 25002913509389681046899

theorem tailTrace_438237 : CollatzResearch.WordTrace tailWord_438237 prefixEnd_438237 25002913509389681046899 := by
  unfold tailWord_438237
  simp only [CollatzResearch.WordTrace]
  refine ⟨15983816513349668766000965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10655877675566445844000643 15983816513349668766000965)
  ·
    refine ⟨2996965596253062893625181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 15983816513349668766000965 2996965596253062893625181)
    ·
      refine ⟨1123862098594898585109443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2996965596253062893625181 1123862098594898585109443)
      ·
        refine ⟨1685793147892347877664165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1123862098594898585109443 1685793147892347877664165)
        ·
          refine ⟨316086215229815227062031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1685793147892347877664165 316086215229815227062031)
          ·
            refine ⟨474129322844722840593047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 316086215229815227062031 474129322844722840593047)
            ·
              refine ⟨711193984267084260889571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 474129322844722840593047 711193984267084260889571)
              ·
                refine ⟨1066790976400626391334357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 711193984267084260889571 1066790976400626391334357)
                ·
                  refine ⟨25002913509389681046899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1066790976400626391334357 25002913509389681046899)
                  ·
                    rfl

theorem cell23_438237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 4, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 4, 1, 1, 1, 7].length) (baseStart_438237 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_438237 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_438237 prefixEnd_438237 := by exact prefixLift 438237
  have htrace : WordTrace (prefixWord ++ tailWord_438237) baseStart_438237 baseEnd_438237 := by
    simpa [prefixWord, tailWord_438237, baseEnd_438237] using wordTrace_append hprefix tailTrace_438237
  have hstable : (prefixWord ++ tailWord_438237).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_438237).length < 2 ^ (prefixWord ++ tailWord_438237).sum := by decide
  have hdescent : baseEnd_438237 < baseStart_438237 := by decide
  rcases family_descends (prefixWord ++ tailWord_438237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_438243 : List Nat := [1, 1, 1, 6, 1, 3, 1, 1, 1, 2, 5]
def baseStart_438243 : Nat := 118140960795 + 438243 * 2 ^ 59
def prefixEnd_438243 : Nat := 4983230072969 + 3 ^ 40 * 438243 * 2
def baseEnd_438243 : Nat := 225029302468434105947063

theorem tailTrace_438243 : CollatzResearch.WordTrace tailWord_438243 prefixEnd_438243 225029302468434105947063 := by
  unfold tailWord_438243
  simp only [CollatzResearch.WordTrace]
  refine ⟨15984035351327931790719383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10656023567551954527146255 15984035351327931790719383)
  ·
    refine ⟨23976053026991897686079075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15984035351327931790719383 23976053026991897686079075)
    ·
      refine ⟨35964079540487846529118613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23976053026991897686079075 35964079540487846529118613)
      ·
        refine ⟨1685816228460367806052435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 35964079540487846529118613 1685816228460367806052435)
        ·
          refine ⟨2528724342690551709078653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1685816228460367806052435 2528724342690551709078653)
          ·
            refine ⟨948271628508956890904495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2528724342690551709078653 948271628508956890904495)
            ·
              refine ⟨1422407442763435336356743, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 948271628508956890904495 1422407442763435336356743)
              ·
                refine ⟨2133611164145153004535115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1422407442763435336356743 2133611164145153004535115)
                ·
                  refine ⟨3200416746217729506802673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2133611164145153004535115 3200416746217729506802673)
                  ·
                    refine ⟨2400312559663297130102005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3200416746217729506802673 2400312559663297130102005)
                    ·
                      refine ⟨225029302468434105947063, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 2400312559663297130102005 225029302468434105947063)
                      ·
                        rfl

theorem cell23_438243_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 3, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 3, 1, 1, 1, 2, 5].length) (baseStart_438243 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_438243 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_438243 prefixEnd_438243 := by exact prefixLift 438243
  have htrace : WordTrace (prefixWord ++ tailWord_438243) baseStart_438243 baseEnd_438243 := by
    simpa [prefixWord, tailWord_438243, baseEnd_438243] using wordTrace_append hprefix tailTrace_438243
  have hstable : (prefixWord ++ tailWord_438243).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_438243).length < 2 ^ (prefixWord ++ tailWord_438243).sum := by decide
  have hdescent : baseEnd_438243 < baseStart_438243 := by decide
  rcases family_descends (prefixWord ++ tailWord_438243) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_438266 : List Nat := [3, 1, 1, 1, 1, 2, 1, 1, 3, 3, 6]
def baseStart_438266 : Nat := 118140960795 + 438266 * 2 ^ 59
def prefixEnd_438266 : Nat := 4983230072969 + 3 ^ 40 * 438266 * 2
def baseEnd_438266 : Nat := 225041112523487515959457

theorem tailTrace_438266 : CollatzResearch.WordTrace tailWord_438266 prefixEnd_438266 225041112523487515959457 := by
  unfold tailWord_438266
  simp only [CollatzResearch.WordTrace]
  refine ⟨3996218557561151679701663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10656582820163071145871101 3996218557561151679701663)
  ·
    refine ⟨5994327836341727519552495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3996218557561151679701663 5994327836341727519552495)
    ·
      refine ⟨8991491754512591279328743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5994327836341727519552495 8991491754512591279328743)
      ·
        refine ⟨13487237631768886918993115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8991491754512591279328743 13487237631768886918993115)
        ·
          refine ⟨20230856447653330378489673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13487237631768886918993115 20230856447653330378489673)
          ·
            refine ⟨15173142335739997783867255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20230856447653330378489673 15173142335739997783867255)
            ·
              refine ⟨22759713503609996675800883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15173142335739997783867255 22759713503609996675800883)
              ·
                refine ⟨34139570255414995013701325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22759713503609996675800883 34139570255414995013701325)
                ·
                  refine ⟨12802338845780623130137997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34139570255414995013701325 12802338845780623130137997)
                  ·
                    refine ⟨4800877067167733673801749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12802338845780623130137997 4800877067167733673801749)
                    ·
                      refine ⟨225041112523487515959457, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 4800877067167733673801749 225041112523487515959457)
                      ·
                        rfl

theorem cell23_438266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 1, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 1, 1, 3, 3, 6].length) (baseStart_438266 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_438266 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_438266 prefixEnd_438266 := by exact prefixLift 438266
  have htrace : WordTrace (prefixWord ++ tailWord_438266) baseStart_438266 baseEnd_438266 := by
    simpa [prefixWord, tailWord_438266, baseEnd_438266] using wordTrace_append hprefix tailTrace_438266
  have hstable : (prefixWord ++ tailWord_438266).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_438266).length < 2 ^ (prefixWord ++ tailWord_438266).sum := by decide
  have hdescent : baseEnd_438266 < baseStart_438266 := by decide
  rcases family_descends (prefixWord ++ tailWord_438266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_438320 : List Nat := [2, 1, 1, 1, 2, 5, 1, 1, 5, 1, 3]
def baseStart_438320 : Nat := 118140960795 + 438320 * 2 ^ 59
def prefixEnd_438320 : Nat := 4983230072969 + 3 ^ 40 * 438320 * 2
def baseEnd_438320 : Nat := 225068840478830304684209

theorem tailTrace_438320 : CollatzResearch.WordTrace tailWord_438320 prefixEnd_438320 225068840478830304684209 := by
  unfold tailWord_438320
  simp only [CollatzResearch.WordTrace]
  refine ⟨7993421886024486970636207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10657895848032649294181609 7993421886024486970636207)
  ·
    refine ⟨11990132829036730455954311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7993421886024486970636207 11990132829036730455954311)
    ·
      refine ⟨17985199243555095683931467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11990132829036730455954311 17985199243555095683931467)
      ·
        refine ⟨26977798865332643525897201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17985199243555095683931467 26977798865332643525897201)
        ·
          refine ⟨20233349148999482644422901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26977798865332643525897201 20233349148999482644422901)
          ·
            refine ⟨1896876482718701497914647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 20233349148999482644422901 1896876482718701497914647)
            ·
              refine ⟨2845314724078052246871971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1896876482718701497914647 2845314724078052246871971)
              ·
                refine ⟨4267972086117078370307957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2845314724078052246871971 4267972086117078370307957)
                ·
                  refine ⟨400122383073476097216371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4267972086117078370307957 400122383073476097216371)
                  ·
                    refine ⟨600183574610214145824557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 400122383073476097216371 600183574610214145824557)
                    ·
                      refine ⟨225068840478830304684209, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 600183574610214145824557 225068840478830304684209)
                      ·
                        rfl

theorem cell23_438320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 5, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 5, 1, 1, 5, 1, 3].length) (baseStart_438320 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_438320 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_438320 prefixEnd_438320 := by exact prefixLift 438320
  have htrace : WordTrace (prefixWord ++ tailWord_438320) baseStart_438320 baseEnd_438320 := by
    simpa [prefixWord, tailWord_438320, baseEnd_438320] using wordTrace_append hprefix tailTrace_438320
  have hstable : (prefixWord ++ tailWord_438320).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_438320).length < 2 ^ (prefixWord ++ tailWord_438320).sum := by decide
  have hdescent : baseEnd_438320 < baseStart_438320 := by decide
  rcases family_descends (prefixWord ++ tailWord_438320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_438323 : List Nat := [1, 1, 1, 2, 4, 1, 4, 1, 3, 5]
def baseStart_438323 : Nat := 118140960795 + 438323 * 2 ^ 59
def prefixEnd_438323 : Nat := 4983230072969 + 3 ^ 40 * 438323 * 2
def baseEnd_438323 : Nat := 75023460306931264315565

theorem tailTrace_438323 : CollatzResearch.WordTrace tailWord_438323 prefixEnd_438323 75023460306931264315565 := by
  unfold tailWord_438323
  simp only [CollatzResearch.WordTrace]
  refine ⟨15986953191038105453631623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10657968794025403635754415 15986953191038105453631623)
  ·
    refine ⟨23980429786557158180447435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15986953191038105453631623 23980429786557158180447435)
    ·
      refine ⟨35970644679835737270671153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23980429786557158180447435 35970644679835737270671153)
      ·
        refine ⟨26977983509876802953003365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35970644679835737270671153 26977983509876802953003365)
        ·
          refine ⟨5058371908101900553688131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 26977983509876802953003365 5058371908101900553688131)
          ·
            refine ⟨7587557862152850830532197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5058371908101900553688131 7587557862152850830532197)
            ·
              refine ⟨1422667099153659530724787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7587557862152850830532197 1422667099153659530724787)
              ·
                refine ⟨2134000648730489296087181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1422667099153659530724787 2134000648730489296087181)
                ·
                  refine ⟨800250243273933486032693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2134000648730489296087181 800250243273933486032693)
                  ·
                    refine ⟨75023460306931264315565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 800250243273933486032693 75023460306931264315565)
                    ·
                      rfl

theorem cell23_438323_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 4, 1, 3, 5].length) (baseStart_438323 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_438323 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_438323 prefixEnd_438323 := by exact prefixLift 438323
  have htrace : WordTrace (prefixWord ++ tailWord_438323) baseStart_438323 baseEnd_438323 := by
    simpa [prefixWord, tailWord_438323, baseEnd_438323] using wordTrace_append hprefix tailTrace_438323
  have hstable : (prefixWord ++ tailWord_438323).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_438323).length < 2 ^ (prefixWord ++ tailWord_438323).sum := by decide
  have hdescent : baseEnd_438323 < baseStart_438323 := by decide
  rcases family_descends (prefixWord ++ tailWord_438323) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_438354 : List Nat := [3, 2, 2, 1, 4, 1, 2, 1, 3, 1, 3]
def baseStart_438354 : Nat := 118140960795 + 438354 * 2 ^ 59
def prefixEnd_438354 : Nat := 4983230072969 + 3 ^ 40 * 438354 * 2
def baseEnd_438354 : Nat := 225086298821083171659053

theorem tailTrace_438354 : CollatzResearch.WordTrace tailWord_438354 prefixEnd_438354 225086298821083171659053 := by
  unfold tailWord_438354
  simp only [CollatzResearch.WordTrace]
  refine ⟨3997020963481449437002529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10658722569283865165340077 3997020963481449437002529)
  ·
    refine ⟨2997765722611087077751897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3997020963481449437002529 2997765722611087077751897)
    ·
      refine ⟨2248324291958315308313923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2997765722611087077751897 2248324291958315308313923)
      ·
        refine ⟨3372486437937472962470885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2248324291958315308313923 3372486437937472962470885)
        ·
          refine ⟨632341207113276180463291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3372486437937472962470885 632341207113276180463291)
          ·
            refine ⟨948511810669914270694937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 632341207113276180463291 948511810669914270694937)
            ·
              refine ⟨711383858002435703021203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 948511810669914270694937 711383858002435703021203)
              ·
                refine ⟨1067075787003653554531805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 711383858002435703021203 1067075787003653554531805)
                ·
                  refine ⟨400153420126370082949427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1067075787003653554531805 400153420126370082949427)
                  ·
                    refine ⟨600230130189555124424141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 400153420126370082949427 600230130189555124424141)
                    ·
                      refine ⟨225086298821083171659053, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 600230130189555124424141 225086298821083171659053)
                      ·
                        rfl

theorem cell23_438354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 4, 1, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 4, 1, 2, 1, 3, 1, 3].length) (baseStart_438354 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_438354 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_438354 prefixEnd_438354 := by exact prefixLift 438354
  have htrace : WordTrace (prefixWord ++ tailWord_438354) baseStart_438354 baseEnd_438354 := by
    simpa [prefixWord, tailWord_438354, baseEnd_438354] using wordTrace_append hprefix tailTrace_438354
  have hstable : (prefixWord ++ tailWord_438354).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_438354).length < 2 ^ (prefixWord ++ tailWord_438354).sum := by decide
  have hdescent : baseEnd_438354 < baseStart_438354 := by decide
  rcases family_descends (prefixWord ++ tailWord_438354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_438377 : List Nat := [1, 2, 1, 1, 1, 5, 1, 4, 3, 2, 2]
def baseStart_438377 : Nat := 118140960795 + 438377 * 2 ^ 59
def prefixEnd_438377 : Nat := 4983230072969 + 3 ^ 40 * 438377 * 2
def baseEnd_438377 : Nat := 225098108876136581671447

theorem tailTrace_438377 : CollatzResearch.WordTrace tailWord_438377 prefixEnd_438377 225098108876136581671447 := by
  unfold tailWord_438377
  simp only [CollatzResearch.WordTrace]
  refine ⟨15988922732842472676097385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10659281821894981784064923 15988922732842472676097385)
  ·
    refine ⟨11991692049631854507073039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15988922732842472676097385 11991692049631854507073039)
    ·
      refine ⟨17987538074447781760609559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11991692049631854507073039 17987538074447781760609559)
      ·
        refine ⟨26981307111671672640914339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17987538074447781760609559 26981307111671672640914339)
        ·
          refine ⟨40471960667507508961371509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26981307111671672640914339 40471960667507508961371509)
          ·
            refine ⟨3794246312578828965128579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 40471960667507508961371509 3794246312578828965128579)
            ·
              refine ⟨5691369468868243447692869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3794246312578828965128579 5691369468868243447692869)
              ·
                refine ⟨1067131775412795646442413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5691369468868243447692869 1067131775412795646442413)
                ·
                  refine ⟨400174415779798367415905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1067131775412795646442413 400174415779798367415905)
                  ·
                    refine ⟨300130811834848775561929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 400174415779798367415905 300130811834848775561929)
                    ·
                      refine ⟨225098108876136581671447, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 300130811834848775561929 225098108876136581671447)
                      ·
                        rfl

theorem cell23_438377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 1, 4, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 1, 4, 3, 2, 2].length) (baseStart_438377 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_438377 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_438377 prefixEnd_438377 := by exact prefixLift 438377
  have htrace : WordTrace (prefixWord ++ tailWord_438377) baseStart_438377 baseEnd_438377 := by
    simpa [prefixWord, tailWord_438377, baseEnd_438377] using wordTrace_append hprefix tailTrace_438377
  have hstable : (prefixWord ++ tailWord_438377).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_438377).length < 2 ^ (prefixWord ++ tailWord_438377).sum := by decide
  have hdescent : baseEnd_438377 < baseStart_438377 := by decide
  rcases family_descends (prefixWord ++ tailWord_438377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_438383 : List Nat := [1, 1, 2, 1, 3, 5, 1, 9]
def baseStart_438383 : Nat := 118140960795 + 438383 * 2 ^ 59
def prefixEnd_438383 : Nat := 4983230072969 + 3 ^ 40 * 438383 * 2
def baseEnd_438383 : Nat := 8337081102224576229497

theorem tailTrace_438383 : CollatzResearch.WordTrace tailWord_438383 prefixEnd_438383 8337081102224576229497 := by
  unfold tailWord_438383
  simp only [CollatzResearch.WordTrace]
  refine ⟨15989141570820735700815803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10659427713880490467210535 15989141570820735700815803)
  ·
    refine ⟨23983712356231103551223705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15989141570820735700815803 23983712356231103551223705)
    ·
      refine ⟨17987784267173327663417779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23983712356231103551223705 17987784267173327663417779)
      ·
        refine ⟨26981676400759991495126669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17987784267173327663417779 26981676400759991495126669)
        ·
          refine ⟨10118128650284996810672501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26981676400759991495126669 10118128650284996810672501)
          ·
            refine ⟨948574560964218451000547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 10118128650284996810672501 948574560964218451000547)
            ·
              refine ⟨1422861841446327676500821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 948574560964218451000547 1422861841446327676500821)
              ·
                refine ⟨8337081102224576229497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 1422861841446327676500821 8337081102224576229497)
                ·
                  rfl

theorem cell23_438383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 5, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 5, 1, 9].length) (baseStart_438383 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_438383 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_438383 prefixEnd_438383 := by exact prefixLift 438383
  have htrace : WordTrace (prefixWord ++ tailWord_438383) baseStart_438383 baseEnd_438383 := by
    simpa [prefixWord, tailWord_438383, baseEnd_438383] using wordTrace_append hprefix tailTrace_438383
  have hstable : (prefixWord ++ tailWord_438383).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_438383).length < 2 ^ (prefixWord ++ tailWord_438383).sum := by decide
  have hdescent : baseEnd_438383 < baseStart_438383 := by decide
  rcases family_descends (prefixWord ++ tailWord_438383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_438397 : List Nat := [1, 4, 1, 1, 3, 2, 2, 3, 1, 2, 3]
def baseStart_438397 : Nat := 118140960795 + 438397 * 2 ^ 59
def prefixEnd_438397 : Nat := 4983230072969 + 3 ^ 40 * 438397 * 2
def baseEnd_438397 : Nat := 225108378489226503421355

theorem tailTrace_438397 : CollatzResearch.WordTrace tailWord_438397 prefixEnd_438397 225108378489226503421355 := by
  unfold tailWord_438397
  simp only [CollatzResearch.WordTrace]
  refine ⟨15989652192770016091825445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10659768128513344061216963 15989652192770016091825445)
  ·
    refine ⟨2998059786144378017217271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 15989652192770016091825445 2998059786144378017217271)
    ·
      refine ⟨4497089679216567025825907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2998059786144378017217271 4497089679216567025825907)
      ·
        refine ⟨6745634518824850538738861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4497089679216567025825907 6745634518824850538738861)
        ·
          refine ⟨2529612944559318952027073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6745634518824850538738861 2529612944559318952027073)
          ·
            refine ⟨1897209708419489214020305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2529612944559318952027073 1897209708419489214020305)
            ·
              refine ⟨1422907281314616910515229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1897209708419489214020305 1422907281314616910515229)
              ·
                refine ⟨533590230492981341443211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1422907281314616910515229 533590230492981341443211)
                ·
                  refine ⟨800385345739472012164817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 533590230492981341443211 800385345739472012164817)
                  ·
                    refine ⟨600289009304604009123613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 800385345739472012164817 600289009304604009123613)
                    ·
                      refine ⟨225108378489226503421355, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 600289009304604009123613 225108378489226503421355)
                      ·
                        rfl

theorem cell23_438397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 2, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 2, 2, 3, 1, 2, 3].length) (baseStart_438397 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_438397 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_438397 prefixEnd_438397 := by exact prefixLift 438397
  have htrace : WordTrace (prefixWord ++ tailWord_438397) baseStart_438397 baseEnd_438397 := by
    simpa [prefixWord, tailWord_438397, baseEnd_438397] using wordTrace_append hprefix tailTrace_438397
  have hstable : (prefixWord ++ tailWord_438397).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_438397).length < 2 ^ (prefixWord ++ tailWord_438397).sum := by decide
  have hdescent : baseEnd_438397 < baseStart_438397 := by decide
  rcases family_descends (prefixWord ++ tailWord_438397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_438437 : List Nat := [1, 3, 1, 2, 1, 3, 3, 1, 3, 3, 2]
def baseStart_438437 : Nat := 118140960795 + 438437 * 2 ^ 59
def prefixEnd_438437 : Nat := 4983230072969 + 3 ^ 40 * 438437 * 2
def baseEnd_438437 : Nat := 225128917715406346921171

theorem tailTrace_438437 : CollatzResearch.WordTrace tailWord_438437 prefixEnd_438437 225128917715406346921171 := by
  unfold tailWord_438437
  simp only [CollatzResearch.WordTrace]
  refine ⟨15991111112625102923281565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10660740741750068615521043 15991111112625102923281565)
  ·
    refine ⟨5996666667234413596230587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15991111112625102923281565 5996666667234413596230587)
    ·
      refine ⟨8995000000851620394345881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5996666667234413596230587 8995000000851620394345881)
      ·
        refine ⟨6746250000638715295759411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8995000000851620394345881 6746250000638715295759411)
        ·
          refine ⟨10119375000958072943639117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6746250000638715295759411 10119375000958072943639117)
          ·
            refine ⟨3794765625359277353864669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10119375000958072943639117 3794765625359277353864669)
            ·
              refine ⟨1423037109509729007699251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3794765625359277353864669 1423037109509729007699251)
              ·
                refine ⟨2134555664264593511548877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1423037109509729007699251 2134555664264593511548877)
                ·
                  refine ⟨800458374099222566830829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2134555664264593511548877 800458374099222566830829)
                  ·
                    refine ⟨300171890287208462561561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 800458374099222566830829 300171890287208462561561)
                    ·
                      refine ⟨225128917715406346921171, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 300171890287208462561561 225128917715406346921171)
                      ·
                        rfl

theorem cell23_438437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 3, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 3, 1, 3, 3, 2].length) (baseStart_438437 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_438437 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_438437 prefixEnd_438437 := by exact prefixLift 438437
  have htrace : WordTrace (prefixWord ++ tailWord_438437) baseStart_438437 baseEnd_438437 := by
    simpa [prefixWord, tailWord_438437, baseEnd_438437] using wordTrace_append hprefix tailTrace_438437
  have hstable : (prefixWord ++ tailWord_438437).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_438437).length < 2 ^ (prefixWord ++ tailWord_438437).sum := by decide
  have hdescent : baseEnd_438437 < baseStart_438437 := by decide
  rcases family_descends (prefixWord ++ tailWord_438437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_438462 : List Nat := [4, 2, 1, 1, 5, 1, 2, 2, 1, 2, 2]
def baseStart_438462 : Nat := 118140960795 + 438462 * 2 ^ 59
def prefixEnd_438462 : Nat := 4983230072969 + 3 ^ 40 * 438462 * 2
def baseEnd_438462 : Nat := 225141754731768749108557

theorem tailTrace_438462 : CollatzResearch.WordTrace tailWord_438462 prefixEnd_438462 225141754731768749108557 := by
  unfold tailWord_438462
  simp only [CollatzResearch.WordTrace]
  refine ⟨1999002867191816524117705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 10661348625023021461961093 1999002867191816524117705)
  ·
    refine ⟨1499252150393862393088279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1999002867191816524117705 1499252150393862393088279)
    ·
      refine ⟨2248878225590793589632419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1499252150393862393088279 2248878225590793589632419)
      ·
        refine ⟨3373317338386190384448629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2248878225590793589632419 3373317338386190384448629)
        ·
          refine ⟨316248500473705348542059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 3373317338386190384448629 316248500473705348542059)
          ·
            refine ⟨474372750710558022813089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 316248500473705348542059 474372750710558022813089)
            ·
              refine ⟨355779563032918517109817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 474372750710558022813089 355779563032918517109817)
              ·
                refine ⟨266834672274688887832363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 355779563032918517109817 266834672274688887832363)
                ·
                  refine ⟨400252008412033331748545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 266834672274688887832363 400252008412033331748545)
                  ·
                    refine ⟨300189006309024998811409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 400252008412033331748545 300189006309024998811409)
                    ·
                      refine ⟨225141754731768749108557, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 300189006309024998811409 225141754731768749108557)
                      ·
                        rfl

theorem cell23_438462_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 5, 1, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 5, 1, 2, 2, 1, 2, 2].length) (baseStart_438462 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_438462 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_438462 prefixEnd_438462 := by exact prefixLift 438462
  have htrace : WordTrace (prefixWord ++ tailWord_438462) baseStart_438462 baseEnd_438462 := by
    simpa [prefixWord, tailWord_438462, baseEnd_438462] using wordTrace_append hprefix tailTrace_438462
  have hstable : (prefixWord ++ tailWord_438462).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_438462).length < 2 ^ (prefixWord ++ tailWord_438462).sum := by decide
  have hdescent : baseEnd_438462 < baseStart_438462 := by decide
  rcases family_descends (prefixWord ++ tailWord_438462) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_438463 : List Nat := [1, 1, 2, 2, 2, 2, 1, 1, 2, 3, 6]
def baseStart_438463 : Nat := 118140960795 + 438463 * 2 ^ 59
def prefixEnd_438463 : Nat := 4983230072969 + 3 ^ 40 * 438463 * 2
def baseEnd_438463 : Nat := 225142268212423245196051

theorem tailTrace_438463 : CollatzResearch.WordTrace tailWord_438463 prefixEnd_438463 225142268212423245196051 := by
  unfold tailWord_438463
  simp only [CollatzResearch.WordTrace]
  refine ⟨15992059410530909363728043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10661372940353939575818695 15992059410530909363728043)
  ·
    refine ⟨23988089115796364045592065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15992059410530909363728043 23988089115796364045592065)
    ·
      refine ⟨17991066836847273034194049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23988089115796364045592065 17991066836847273034194049)
      ·
        refine ⟨13493300127635454775645537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17991066836847273034194049 13493300127635454775645537)
        ·
          refine ⟨10119975095726591081734153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13493300127635454775645537 10119975095726591081734153)
          ·
            refine ⟨7589981321794943311300615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10119975095726591081734153 7589981321794943311300615)
            ·
              refine ⟨11384971982692414966950923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7589981321794943311300615 11384971982692414966950923)
              ·
                refine ⟨17077457974038622450426385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11384971982692414966950923 17077457974038622450426385)
                ·
                  refine ⟨12808093480528966837819789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17077457974038622450426385 12808093480528966837819789)
                  ·
                    refine ⟨4803035055198362564182421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12808093480528966837819789 4803035055198362564182421)
                    ·
                      refine ⟨225142268212423245196051, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 4803035055198362564182421 225142268212423245196051)
                      ·
                        rfl

theorem cell23_438463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 1, 1, 2, 3, 6].length) (baseStart_438463 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_438463 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_438463 prefixEnd_438463 := by exact prefixLift 438463
  have htrace : WordTrace (prefixWord ++ tailWord_438463) baseStart_438463 baseEnd_438463 := by
    simpa [prefixWord, tailWord_438463, baseEnd_438463] using wordTrace_append hprefix tailTrace_438463
  have hstable : (prefixWord ++ tailWord_438463).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_438463).length < 2 ^ (prefixWord ++ tailWord_438463).sum := by decide
  have hdescent : baseEnd_438463 < baseStart_438463 := by decide
  rcases family_descends (prefixWord ++ tailWord_438463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_438467 : List Nat := [1, 1, 1, 3, 1, 1, 1, 2, 8, 2, 2]
def baseStart_438467 : Nat := 118140960795 + 438467 * 2 ^ 59
def prefixEnd_438467 : Nat := 4983230072969 + 3 ^ 40 * 438467 * 2
def baseEnd_438467 : Nat := 225144322135041229546033

theorem tailTrace_438467 : CollatzResearch.WordTrace tailWord_438467 prefixEnd_438467 225144322135041229546033 := by
  unfold tailWord_438467
  simp only [CollatzResearch.WordTrace]
  refine ⟨15992205302516418046873655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10661470201677612031249103 15992205302516418046873655)
  ·
    refine ⟨23988307953774627070310483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15992205302516418046873655 23988307953774627070310483)
    ·
      refine ⟨35982461930661940605465725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23988307953774627070310483 35982461930661940605465725)
      ·
        refine ⟨13493423223998227727049647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35982461930661940605465725 13493423223998227727049647)
        ·
          refine ⟨20240134835997341590574471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13493423223998227727049647 20240134835997341590574471)
          ·
            refine ⟨30360202253996012385861707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20240134835997341590574471 30360202253996012385861707)
            ·
              refine ⟨45540303380994018578792561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30360202253996012385861707 45540303380994018578792561)
              ·
                refine ⟨34155227535745513934094421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45540303380994018578792561 34155227535745513934094421)
                ·
                  refine ⟨400256572684517741415169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 34155227535745513934094421 400256572684517741415169)
                  ·
                    refine ⟨300192429513388306061377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 400256572684517741415169 300192429513388306061377)
                    ·
                      refine ⟨225144322135041229546033, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 300192429513388306061377 225144322135041229546033)
                      ·
                        rfl

theorem cell23_438467_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 2, 8, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 2, 8, 2, 2].length) (baseStart_438467 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_438467 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_438467 prefixEnd_438467 := by exact prefixLift 438467
  have htrace : WordTrace (prefixWord ++ tailWord_438467) baseStart_438467 baseEnd_438467 := by
    simpa [prefixWord, tailWord_438467, baseEnd_438467] using wordTrace_append hprefix tailTrace_438467
  have hstable : (prefixWord ++ tailWord_438467).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_438467).length < 2 ^ (prefixWord ++ tailWord_438467).sum := by decide
  have hdescent : baseEnd_438467 < baseStart_438467 := by decide
  rcases family_descends (prefixWord ++ tailWord_438467) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_438500 : List Nat := [2, 3, 1, 1, 1, 2, 1, 1, 3, 5, 3]
def baseStart_438500 : Nat := 118140960795 + 438500 * 2 ^ 59
def prefixEnd_438500 : Nat := 4983230072969 + 3 ^ 40 * 438500 * 2
def baseEnd_438500 : Nat := 225161266996639600433381

theorem tailTrace_438500 : CollatzResearch.WordTrace tailWord_438500 prefixEnd_438500 225161266996639600433381 := by
  unfold tailWord_438500
  simp only [CollatzResearch.WordTrace]
  refine ⟨7996704455698432341412477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10662272607597909788549969 7996704455698432341412477)
  ·
    refine ⟨2998764170886912128029679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7996704455698432341412477 2998764170886912128029679)
    ·
      refine ⟨4498146256330368192044519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2998764170886912128029679 4498146256330368192044519)
      ·
        refine ⟨6747219384495552288066779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4498146256330368192044519 6747219384495552288066779)
        ·
          refine ⟨10120829076743328432100169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6747219384495552288066779 10120829076743328432100169)
          ·
            refine ⟨7590621807557496324075127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10120829076743328432100169 7590621807557496324075127)
            ·
              refine ⟨11385932711336244486112691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7590621807557496324075127 11385932711336244486112691)
              ·
                refine ⟨17078899067004366729169037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11385932711336244486112691 17078899067004366729169037)
                ·
                  refine ⟨6404587150126637523438389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17078899067004366729169037 6404587150126637523438389)
                  ·
                    refine ⟨600430045324372267822349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6404587150126637523438389 600430045324372267822349)
                    ·
                      refine ⟨225161266996639600433381, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 600430045324372267822349 225161266996639600433381)
                      ·
                        rfl

theorem cell23_438500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 1, 1, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 1, 1, 3, 5, 3].length) (baseStart_438500 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_438500 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_438500 prefixEnd_438500 := by exact prefixLift 438500
  have htrace : WordTrace (prefixWord ++ tailWord_438500) baseStart_438500 baseEnd_438500 := by
    simpa [prefixWord, tailWord_438500, baseEnd_438500] using wordTrace_append hprefix tailTrace_438500
  have hstable : (prefixWord ++ tailWord_438500).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_438500).length < 2 ^ (prefixWord ++ tailWord_438500).sum := by decide
  have hdescent : baseEnd_438500 < baseStart_438500 := by decide
  rcases family_descends (prefixWord ++ tailWord_438500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_438507 : List Nat := [1, 1, 1, 1, 2, 5, 4, 3, 5]
def baseStart_438507 : Nat := 118140960795 + 438507 * 2 ^ 59
def prefixEnd_438507 : Nat := 4983230072969 + 3 ^ 40 * 438507 * 2
def baseEnd_438507 : Nat := 25018317929024563671761

theorem tailTrace_438507 : CollatzResearch.WordTrace tailWord_438507 prefixEnd_438507 25018317929024563671761 := by
  unfold tailWord_438507
  simp only [CollatzResearch.WordTrace]
  refine ⟨15993664222371504878329775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10662442814914336585553183 15993664222371504878329775)
  ·
    refine ⟨23990496333557257317494663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15993664222371504878329775 23990496333557257317494663)
    ·
      refine ⟨35985744500335885976241995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23990496333557257317494663 35985744500335885976241995)
      ·
        refine ⟨53978616750503828964362993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35985744500335885976241995 53978616750503828964362993)
        ·
          refine ⟨40483962562877871723272245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53978616750503828964362993 40483962562877871723272245)
          ·
            refine ⟨3795371490269800474056773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 40483962562877871723272245 3795371490269800474056773)
            ·
              refine ⟨711632154425587588885645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3795371490269800474056773 711632154425587588885645)
              ·
                refine ⟨266862057909595345832117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 711632154425587588885645 266862057909595345832117)
                ·
                  refine ⟨25018317929024563671761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 266862057909595345832117 25018317929024563671761)
                  ·
                    rfl

theorem cell23_438507_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 4, 3, 5].length) (baseStart_438507 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_438507 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_438507 prefixEnd_438507 := by exact prefixLift 438507
  have htrace : WordTrace (prefixWord ++ tailWord_438507) baseStart_438507 baseEnd_438507 := by
    simpa [prefixWord, tailWord_438507, baseEnd_438507] using wordTrace_append hprefix tailTrace_438507
  have hstable : (prefixWord ++ tailWord_438507).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_438507).length < 2 ^ (prefixWord ++ tailWord_438507).sum := by decide
  have hdescent : baseEnd_438507 < baseStart_438507 := by decide
  rcases family_descends (prefixWord ++ tailWord_438507) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_438520 : List Nat := [2, 1, 2, 1, 1, 2, 1, 6, 2, 5]
def baseStart_438520 : Nat := 118140960795 + 438520 * 2 ^ 59
def prefixEnd_438520 : Nat := 4983230072969 + 3 ^ 40 * 438520 * 2
def baseEnd_438520 : Nat := 75057178869909840727763

theorem tailTrace_438520 : CollatzResearch.WordTrace tailWord_438520 prefixEnd_438520 75057178869909840727763 := by
  unfold tailWord_438520
  simp only [CollatzResearch.WordTrace]
  refine ⟨7997069185662204049276507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10662758914216272065702009 7997069185662204049276507)
  ·
    refine ⟨11995603778493306073914761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7997069185662204049276507 11995603778493306073914761)
    ·
      refine ⟨8996702833869979555436071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11995603778493306073914761 8996702833869979555436071)
      ·
        refine ⟨13495054250804969333154107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8996702833869979555436071 13495054250804969333154107)
        ·
          refine ⟨20242581376207453999731161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13495054250804969333154107 20242581376207453999731161)
          ·
            refine ⟨15181936032155590499798371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20242581376207453999731161 15181936032155590499798371)
            ·
              refine ⟨22772904048233385749697557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15181936032155590499798371 22772904048233385749697557)
              ·
                refine ⟨1067479877260939957017073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 22772904048233385749697557 1067479877260939957017073)
                ·
                  refine ⟨800609907945704967762805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1067479877260939957017073 800609907945704967762805)
                  ·
                    refine ⟨75057178869909840727763, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 800609907945704967762805 75057178869909840727763)
                    ·
                      rfl

theorem cell23_438520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 6, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 6, 2, 5].length) (baseStart_438520 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_438520 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_438520 prefixEnd_438520 := by exact prefixLift 438520
  have htrace : WordTrace (prefixWord ++ tailWord_438520) baseStart_438520 baseEnd_438520 := by
    simpa [prefixWord, tailWord_438520, baseEnd_438520] using wordTrace_append hprefix tailTrace_438520
  have hstable : (prefixWord ++ tailWord_438520).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_438520).length < 2 ^ (prefixWord ++ tailWord_438520).sum := by decide
  have hdescent : baseEnd_438520 < baseStart_438520 := by decide
  rcases family_descends (prefixWord ++ tailWord_438520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_438535 : List Nat := [1, 1, 4, 5, 1, 1, 3, 1, 2, 2, 2]
def baseStart_438535 : Nat := 118140960795 + 438535 * 2 ^ 59
def prefixEnd_438535 : Nat := 4983230072969 + 3 ^ 40 * 438535 * 2
def baseEnd_438535 : Nat := 225179238819546963495721

theorem tailTrace_438535 : CollatzResearch.WordTrace tailWord_438535 prefixEnd_438535 225179238819546963495721 := by
  unfold tailWord_438535
  simp only [CollatzResearch.WordTrace]
  refine ⟨15994685466270065660349059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10663123644180043773566039 15994685466270065660349059)
  ·
    refine ⟨23992028199405098490523589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15994685466270065660349059 23992028199405098490523589)
    ·
      refine ⟨4498505287388455966973173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 23992028199405098490523589 4498505287388455966973173)
      ·
        refine ⟨421734870692667746903735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 4498505287388455966973173 421734870692667746903735)
        ·
          refine ⟨632602306039001620355603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 421734870692667746903735 632602306039001620355603)
          ·
            refine ⟨948903459058502430533405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 632602306039001620355603 948903459058502430533405)
            ·
              refine ⟨355838797146938411450027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 948903459058502430533405 355838797146938411450027)
              ·
                refine ⟨533758195720407617175041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 355838797146938411450027 533758195720407617175041)
                ·
                  refine ⟨400318646790305712881281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 533758195720407617175041 400318646790305712881281)
                  ·
                    refine ⟨300238985092729284660961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 400318646790305712881281 300238985092729284660961)
                    ·
                      refine ⟨225179238819546963495721, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 300238985092729284660961 225179238819546963495721)
                      ·
                        rfl

theorem cell23_438535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 1, 1, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 1, 1, 3, 1, 2, 2, 2].length) (baseStart_438535 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_438535 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_438535 prefixEnd_438535 := by exact prefixLift 438535
  have htrace : WordTrace (prefixWord ++ tailWord_438535) baseStart_438535 baseEnd_438535 := by
    simpa [prefixWord, tailWord_438535, baseEnd_438535] using wordTrace_append hprefix tailTrace_438535
  have hstable : (prefixWord ++ tailWord_438535).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_438535).length < 2 ^ (prefixWord ++ tailWord_438535).sum := by decide
  have hdescent : baseEnd_438535 < baseStart_438535 := by decide
  rcases family_descends (prefixWord ++ tailWord_438535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_438540 : List Nat := [2, 2, 1, 2, 2, 2, 1, 1, 3, 3, 4]
def baseStart_438540 : Nat := 118140960795 + 438540 * 2 ^ 59
def prefixEnd_438540 : Nat := 4983230072969 + 3 ^ 40 * 438540 * 2
def baseEnd_438540 : Nat := 225181806222819443933197

theorem tailTrace_438540 : CollatzResearch.WordTrace tailWord_438540 prefixEnd_438540 225181806222819443933197 := by
  unfold tailWord_438540
  simp only [CollatzResearch.WordTrace]
  refine ⟨7997433915625975757140537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10663245220834634342854049 7997433915625975757140537)
  ·
    refine ⟨5998075436719481817855403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7997433915625975757140537 5998075436719481817855403)
    ·
      refine ⟨8997113155079222726783105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5998075436719481817855403 8997113155079222726783105)
      ·
        refine ⟨6747834866309417045087329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8997113155079222726783105 6747834866309417045087329)
        ·
          refine ⟨5060876149732062783815497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6747834866309417045087329 5060876149732062783815497)
          ·
            refine ⟨3795657112299047087861623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5060876149732062783815497 3795657112299047087861623)
            ·
              refine ⟨5693485668448570631792435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3795657112299047087861623 5693485668448570631792435)
              ·
                refine ⟨8540228502672855947688653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5693485668448570631792435 8540228502672855947688653)
                ·
                  refine ⟨3202585688502320980383245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8540228502672855947688653 3202585688502320980383245)
                  ·
                    refine ⟨1200969633188370367643717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3202585688502320980383245 1200969633188370367643717)
                    ·
                      refine ⟨225181806222819443933197, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1200969633188370367643717 225181806222819443933197)
                      ·
                        rfl

theorem cell23_438540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 1, 1, 3, 3, 4].length) (baseStart_438540 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_438540 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_438540 prefixEnd_438540 := by exact prefixLift 438540
  have htrace : WordTrace (prefixWord ++ tailWord_438540) baseStart_438540 baseEnd_438540 := by
    simpa [prefixWord, tailWord_438540, baseEnd_438540] using wordTrace_append hprefix tailTrace_438540
  have hstable : (prefixWord ++ tailWord_438540).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_438540).length < 2 ^ (prefixWord ++ tailWord_438540).sum := by decide
  have hdescent : baseEnd_438540 < baseStart_438540 := by decide
  rcases family_descends (prefixWord ++ tailWord_438540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_438558 : List Nat := [4, 3, 2, 1, 1, 3, 1, 3, 5]
def baseStart_438558 : Nat := 118140960795 + 438558 * 2 ^ 59
def prefixEnd_438558 : Nat := 4983230072969 + 3 ^ 40 * 438558 * 2
def baseEnd_438558 : Nat := 25021227652733374834235

theorem tailTrace_438558 : CollatzResearch.WordTrace tailWord_438558 prefixEnd_438558 25021227652733374834235 := by
  unfold tailWord_438558
  simp only [CollatzResearch.WordTrace]
  refine ⟨1999440543148342573554541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 10663682896791160392290885 1999440543148342573554541)
  ·
    refine ⟨749790203680628465082953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1999440543148342573554541 749790203680628465082953)
    ·
      refine ⟨562342652760471348812215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 749790203680628465082953 562342652760471348812215)
      ·
        refine ⟨843513979140707023218323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 562342652760471348812215 843513979140707023218323)
        ·
          refine ⟨1265270968711060534827485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 843513979140707023218323 1265270968711060534827485)
          ·
            refine ⟨474476613266647700560307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1265270968711060534827485 474476613266647700560307)
            ·
              refine ⟨711714919899971550840461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 474476613266647700560307 711714919899971550840461)
              ·
                refine ⟨266893094962489331565173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 711714919899971550840461 266893094962489331565173)
                ·
                  refine ⟨25021227652733374834235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 266893094962489331565173 25021227652733374834235)
                  ·
                    rfl

theorem cell23_438558_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 3, 1, 3, 5].length) (baseStart_438558 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_438558 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_438558 prefixEnd_438558 := by exact prefixLift 438558
  have htrace : WordTrace (prefixWord ++ tailWord_438558) baseStart_438558 baseEnd_438558 := by
    simpa [prefixWord, tailWord_438558, baseEnd_438558] using wordTrace_append hprefix tailTrace_438558
  have hstable : (prefixWord ++ tailWord_438558).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_438558).length < 2 ^ (prefixWord ++ tailWord_438558).sum := by decide
  have hdescent : baseEnd_438558 < baseStart_438558 := by decide
  rcases family_descends (prefixWord ++ tailWord_438558) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_438584 : List Nat := [2, 1, 2, 1, 3, 1, 2, 6, 1, 4]
def baseStart_438584 : Nat := 118140960795 + 438584 * 2 ^ 59
def prefixEnd_438584 : Nat := 4983230072969 + 3 ^ 40 * 438584 * 2
def baseEnd_438584 : Nat := 75068133123872423927665

theorem tailTrace_438584 : CollatzResearch.WordTrace tailWord_438584 prefixEnd_438584 75068133123872423927665 := by
  unfold tailWord_438584
  simp only [CollatzResearch.WordTrace]
  refine ⟨7998236321546273514441403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10664315095395031352588537 7998236321546273514441403)
  ·
    refine ⟨11997354482319410271662105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7998236321546273514441403 11997354482319410271662105)
    ·
      refine ⟨8998015861739557703746579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11997354482319410271662105 8998015861739557703746579)
      ·
        refine ⟨13497023792609336555619869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8998015861739557703746579 13497023792609336555619869)
        ·
          refine ⟨5061383922228501208357451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13497023792609336555619869 5061383922228501208357451)
          ·
            refine ⟨7592075883342751812536177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5061383922228501208357451 7592075883342751812536177)
            ·
              refine ⟨5694056912507063859402133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7592075883342751812536177 5694056912507063859402133)
              ·
                refine ⟨266908917773768618409475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 5694056912507063859402133 266908917773768618409475)
                ·
                  refine ⟨400363376660652927614213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 266908917773768618409475 400363376660652927614213)
                  ·
                    refine ⟨75068133123872423927665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 400363376660652927614213 75068133123872423927665)
                    ·
                      rfl

theorem cell23_438584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 2, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 2, 6, 1, 4].length) (baseStart_438584 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_438584 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_438584 prefixEnd_438584 := by exact prefixLift 438584
  have htrace : WordTrace (prefixWord ++ tailWord_438584) baseStart_438584 baseEnd_438584 := by
    simpa [prefixWord, tailWord_438584, baseEnd_438584] using wordTrace_append hprefix tailTrace_438584
  have hstable : (prefixWord ++ tailWord_438584).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_438584).length < 2 ^ (prefixWord ++ tailWord_438584).sum := by decide
  have hdescent : baseEnd_438584 < baseStart_438584 := by decide
  rcases family_descends (prefixWord ++ tailWord_438584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_438600 : List Nat := [2, 1, 3, 1, 1, 2, 2, 2, 1, 2, 6]
def baseStart_438600 : Nat := 118140960795 + 438600 * 2 ^ 59
def prefixEnd_438600 : Nat := 4983230072969 + 3 ^ 40 * 438600 * 2
def baseEnd_438600 : Nat := 225212615062089209182921

theorem tailTrace_438600 : CollatzResearch.WordTrace tailWord_438600 prefixEnd_438600 225212615062089209182921 := by
  unfold tailWord_438600
  simp only [CollatzResearch.WordTrace]
  refine ⟨7998528105517290880732627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10664704140689721174310169 7998528105517290880732627)
  ·
    refine ⟨11997792158275936321098941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7998528105517290880732627 11997792158275936321098941)
    ·
      refine ⟨4499172059353476120412103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11997792158275936321098941 4499172059353476120412103)
      ·
        refine ⟨6748758089030214180618155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4499172059353476120412103 6748758089030214180618155)
        ·
          refine ⟨10123137133545321270927233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6748758089030214180618155 10123137133545321270927233)
          ·
            refine ⟨7592352850158990953195425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10123137133545321270927233 7592352850158990953195425)
            ·
              refine ⟨5694264637619243214896569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7592352850158990953195425 5694264637619243214896569)
              ·
                refine ⟨4270698478214432411172427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5694264637619243214896569 4270698478214432411172427)
                ·
                  refine ⟨6406047717321648616758641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4270698478214432411172427 6406047717321648616758641)
                  ·
                    refine ⟨4804535787991236462568981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6406047717321648616758641 4804535787991236462568981)
                    ·
                      refine ⟨225212615062089209182921, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 4804535787991236462568981 225212615062089209182921)
                      ·
                        rfl

theorem cell23_438600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 2, 2, 1, 2, 6].length) (baseStart_438600 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_438600 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_438600 prefixEnd_438600 := by exact prefixLift 438600
  have htrace : WordTrace (prefixWord ++ tailWord_438600) baseStart_438600 baseEnd_438600 := by
    simpa [prefixWord, tailWord_438600, baseEnd_438600] using wordTrace_append hprefix tailTrace_438600
  have hstable : (prefixWord ++ tailWord_438600).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_438600).length < 2 ^ (prefixWord ++ tailWord_438600).sum := by decide
  have hdescent : baseEnd_438600 < baseStart_438600 := by decide
  rcases family_descends (prefixWord ++ tailWord_438600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_438664 : List Nat := [2, 1, 3, 3, 1, 1, 2, 4, 1, 1, 4]
def baseStart_438664 : Nat := 118140960795 + 438664 * 2 ^ 59
def prefixEnd_438664 : Nat := 4983230072969 + 3 ^ 40 * 438664 * 2
def baseEnd_438664 : Nat := 225245477823976958782627

theorem tailTrace_438664 : CollatzResearch.WordTrace tailWord_438664 prefixEnd_438664 225245477823976958782627 := by
  unfold tailWord_438664
  simp only [CollatzResearch.WordTrace]
  refine ⟨7999695241401360345897523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10666260321868480461196697 7999695241401360345897523)
  ·
    refine ⟨11999542862102040518846285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7999695241401360345897523 11999542862102040518846285)
    ·
      refine ⟨4499828573288265194567357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11999542862102040518846285 4499828573288265194567357)
      ·
        refine ⟨1687435714983099447962759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4499828573288265194567357 1687435714983099447962759)
        ·
          refine ⟨2531153572474649171944139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1687435714983099447962759 2531153572474649171944139)
          ·
            refine ⟨3796730358711973757916209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2531153572474649171944139 3796730358711973757916209)
            ·
              refine ⟨2847547769033980318437157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3796730358711973757916209 2847547769033980318437157)
              ·
                refine ⟨533915206693871309706967, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2847547769033980318437157 533915206693871309706967)
                ·
                  refine ⟨800872810040806964560451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 533915206693871309706967 800872810040806964560451)
                  ·
                    refine ⟨1201309215061210446840677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 800872810040806964560451 1201309215061210446840677)
                    ·
                      refine ⟨225245477823976958782627, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1201309215061210446840677 225245477823976958782627)
                      ·
                        rfl

theorem cell23_438664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 2, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 2, 4, 1, 1, 4].length) (baseStart_438664 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_438664 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_438664 prefixEnd_438664 := by exact prefixLift 438664
  have htrace : WordTrace (prefixWord ++ tailWord_438664) baseStart_438664 baseEnd_438664 := by
    simpa [prefixWord, tailWord_438664, baseEnd_438664] using wordTrace_append hprefix tailTrace_438664
  have hstable : (prefixWord ++ tailWord_438664).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_438664).length < 2 ^ (prefixWord ++ tailWord_438664).sum := by decide
  have hdescent : baseEnd_438664 < baseStart_438664 := by decide
  rcases family_descends (prefixWord ++ tailWord_438664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_438691 : List Nat := [1, 1, 1, 4, 1, 6, 1, 2, 2, 4]
def baseStart_438691 : Nat := 118140960795 + 438691 * 2 ^ 59
def prefixEnd_438691 : Nat := 4983230072969 + 3 ^ 40 * 438691 * 2
def baseEnd_438691 : Nat := 75086447267216117715001

theorem tailTrace_438691 : CollatzResearch.WordTrace tailWord_438691 prefixEnd_438691 75086447267216117715001 := by
  unfold tailWord_438691
  simp only [CollatzResearch.WordTrace]
  refine ⟨16000375253704904303027927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10666916835803269535351951 16000375253704904303027927)
  ·
    refine ⟨24000562880557356454541891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16000375253704904303027927 24000562880557356454541891)
    ·
      refine ⟨36000844320836034681812837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24000562880557356454541891 36000844320836034681812837)
      ·
        refine ⟨6750158310156756502839907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 36000844320836034681812837 6750158310156756502839907)
        ·
          refine ⟨10125237465235134754259861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6750158310156756502839907 10125237465235134754259861)
          ·
            refine ⟨474620506182896941605931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 10125237465235134754259861 474620506182896941605931)
            ·
              refine ⟨711930759274345412408897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 474620506182896941605931 711930759274345412408897)
              ·
                refine ⟨533948069455759059306673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 711930759274345412408897 533948069455759059306673)
                ·
                  refine ⟨400461052091819294480005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 533948069455759059306673 400461052091819294480005)
                  ·
                    refine ⟨75086447267216117715001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 400461052091819294480005 75086447267216117715001)
                    ·
                      rfl

theorem cell23_438691_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 6, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 6, 1, 2, 2, 4].length) (baseStart_438691 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_438691 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_438691 prefixEnd_438691 := by exact prefixLift 438691
  have htrace : WordTrace (prefixWord ++ tailWord_438691) baseStart_438691 baseEnd_438691 := by
    simpa [prefixWord, tailWord_438691, baseEnd_438691] using wordTrace_append hprefix tailTrace_438691
  have hstable : (prefixWord ++ tailWord_438691).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_438691).length < 2 ^ (prefixWord ++ tailWord_438691).sum := by decide
  have hdescent : baseEnd_438691 < baseStart_438691 := by decide
  rcases family_descends (prefixWord ++ tailWord_438691) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_438697 : List Nat := [1, 2, 1, 1, 1, 1, 3, 4, 3, 3, 3]
def baseStart_438697 : Nat := 118140960795 + 438697 * 2 ^ 59
def prefixEnd_438697 : Nat := 4983230072969 + 3 ^ 40 * 438697 * 2
def baseEnd_438697 : Nat := 225262422685575329669975

theorem tailTrace_438697 : CollatzResearch.WordTrace tailWord_438697 prefixEnd_438697 225262422685575329669975 := by
  unfold tailWord_438697
  simp only [CollatzResearch.WordTrace]
  refine ⟨16000594091683167327746345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10667062727788778218497563 16000594091683167327746345)
  ·
    refine ⟨12000445568762375495809759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16000594091683167327746345 12000445568762375495809759)
    ·
      refine ⟨18000668353143563243714639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12000445568762375495809759 18000668353143563243714639)
      ·
        refine ⟨27001002529715344865571959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18000668353143563243714639 27001002529715344865571959)
        ·
          refine ⟨40501503794573017298357939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27001002529715344865571959 40501503794573017298357939)
          ·
            refine ⟨60752255691859525947536909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40501503794573017298357939 60752255691859525947536909)
            ·
              refine ⟨22782095884447322230326341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 60752255691859525947536909 22782095884447322230326341)
              ·
                refine ⟨4271642978333872918186189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22782095884447322230326341 4271642978333872918186189)
                ·
                  refine ⟨1601866116875202344319821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4271642978333872918186189 1601866116875202344319821)
                  ·
                    refine ⟨600699793828200879119933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1601866116875202344319821 600699793828200879119933)
                    ·
                      refine ⟨225262422685575329669975, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 600699793828200879119933 225262422685575329669975)
                      ·
                        rfl

theorem cell23_438697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 3, 4, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 3, 4, 3, 3, 3].length) (baseStart_438697 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_438697 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_438697 prefixEnd_438697 := by exact prefixLift 438697
  have htrace : WordTrace (prefixWord ++ tailWord_438697) baseStart_438697 baseEnd_438697 := by
    simpa [prefixWord, tailWord_438697, baseEnd_438697] using wordTrace_append hprefix tailTrace_438697
  have hstable : (prefixWord ++ tailWord_438697).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_438697).length < 2 ^ (prefixWord ++ tailWord_438697).sum := by decide
  have hdescent : baseEnd_438697 < baseStart_438697 := by decide
  rcases family_descends (prefixWord ++ tailWord_438697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_438701 : List Nat := [1, 5, 2, 2, 2, 1, 1, 2, 1, 1, 5]
def baseStart_438701 : Nat := 118140960795 + 438701 * 2 ^ 59
def prefixEnd_438701 : Nat := 4983230072969 + 3 ^ 40 * 438701 * 2
def baseEnd_438701 : Nat := 225264476608193314019957

theorem tailTrace_438701 : CollatzResearch.WordTrace tailWord_438701 prefixEnd_438701 225264476608193314019957 := by
  unfold tailWord_438701
  simp only [CollatzResearch.WordTrace]
  refine ⟨16000739983668676010891957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10667159989112450673927971 16000739983668676010891957)
  ·
    refine ⟨1500069373468938376021121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 16000739983668676010891957 1500069373468938376021121)
    ·
      refine ⟨1125052030101703782015841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1500069373468938376021121 1125052030101703782015841)
      ·
        refine ⟨843789022576277836511881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1125052030101703782015841 843789022576277836511881)
        ·
          refine ⟨632841766932208377383911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 843789022576277836511881 632841766932208377383911)
          ·
            refine ⟨949262650398312566075867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 632841766932208377383911 949262650398312566075867)
            ·
              refine ⟨1423893975597468849113801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 949262650398312566075867 1423893975597468849113801)
              ·
                refine ⟨1067920481698101636835351, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1423893975597468849113801 1067920481698101636835351)
                ·
                  refine ⟨1601880722547152455253027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1067920481698101636835351 1601880722547152455253027)
                  ·
                    refine ⟨2402821083820728682879541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1601880722547152455253027 2402821083820728682879541)
                    ·
                      refine ⟨225264476608193314019957, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 2402821083820728682879541 225264476608193314019957)
                      ·
                        rfl

theorem cell23_438701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 2, 1, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 2, 1, 1, 2, 1, 1, 5].length) (baseStart_438701 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_438701 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_438701 prefixEnd_438701 := by exact prefixLift 438701
  have htrace : WordTrace (prefixWord ++ tailWord_438701) baseStart_438701 baseEnd_438701 := by
    simpa [prefixWord, tailWord_438701, baseEnd_438701] using wordTrace_append hprefix tailTrace_438701
  have hstable : (prefixWord ++ tailWord_438701).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_438701).length < 2 ^ (prefixWord ++ tailWord_438701).sum := by decide
  have hdescent : baseEnd_438701 < baseStart_438701 := by decide
  rcases family_descends (prefixWord ++ tailWord_438701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_438727 : List Nat := [1, 1, 4, 1, 1, 4, 1, 1, 2, 2, 5]
def baseStart_438727 : Nat := 118140960795 + 438727 * 2 ^ 59
def prefixEnd_438727 : Nat := 4983230072969 + 3 ^ 40 * 438727 * 2
def baseEnd_438727 : Nat := 225277827105210212294837

theorem tailTrace_438727 : CollatzResearch.WordTrace tailWord_438727 prefixEnd_438727 225277827105210212294837 := by
  unfold tailWord_438727
  simp only [CollatzResearch.WordTrace]
  refine ⟨16001688281574482451338435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10667792187716321634225623 16001688281574482451338435)
  ·
    refine ⟨24002532422361723677007653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16001688281574482451338435 24002532422361723677007653)
    ·
      refine ⟨4500474829192823189438935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 24002532422361723677007653 4500474829192823189438935)
      ·
        refine ⟨6750712243789234784158403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4500474829192823189438935 6750712243789234784158403)
        ·
          refine ⟨10126068365683852176237605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6750712243789234784158403 10126068365683852176237605)
          ·
            refine ⟨1898637818565722283044551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10126068365683852176237605 1898637818565722283044551)
            ·
              refine ⟨2847956727848583424566827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1898637818565722283044551 2847956727848583424566827)
              ·
                refine ⟨4271935091772875136850241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2847956727848583424566827 4271935091772875136850241)
                ·
                  refine ⟨3203951318829656352637681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4271935091772875136850241 3203951318829656352637681)
                  ·
                    refine ⟨2402963489122242264478261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3203951318829656352637681 2402963489122242264478261)
                    ·
                      refine ⟨225277827105210212294837, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 2402963489122242264478261 225277827105210212294837)
                      ·
                        rfl

theorem cell23_438727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 4, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 4, 1, 1, 2, 2, 5].length) (baseStart_438727 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_438727 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_438727 prefixEnd_438727 := by exact prefixLift 438727
  have htrace : WordTrace (prefixWord ++ tailWord_438727) baseStart_438727 baseEnd_438727 := by
    simpa [prefixWord, tailWord_438727, baseEnd_438727] using wordTrace_append hprefix tailTrace_438727
  have hstable : (prefixWord ++ tailWord_438727).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_438727).length < 2 ^ (prefixWord ++ tailWord_438727).sum := by decide
  have hdescent : baseEnd_438727 < baseStart_438727 := by decide
  rcases family_descends (prefixWord ++ tailWord_438727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_438732 : List Nat := [2, 2, 1, 4, 3, 2, 1, 3, 1, 2, 2]
def baseStart_438732 : Nat := 118140960795 + 438732 * 2 ^ 59
def prefixEnd_438732 : Nat := 4983230072969 + 3 ^ 40 * 438732 * 2
def baseEnd_438732 : Nat := 225280394508482692732315

theorem tailTrace_438732 : CollatzResearch.WordTrace tailWord_438732 prefixEnd_438732 225280394508482692732315 := by
  unfold tailWord_438732
  simp only [CollatzResearch.WordTrace]
  refine ⟨8000935323278184152635225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10667913764370912203513633 8000935323278184152635225)
  ·
    refine ⟨6000701492458638114476419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8000935323278184152635225 6000701492458638114476419)
    ·
      refine ⟨9001052238687957171714629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6000701492458638114476419 9001052238687957171714629)
      ·
        refine ⟨1687697294753991969696493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9001052238687957171714629 1687697294753991969696493)
        ·
          refine ⟨632886485532746988636185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1687697294753991969696493 632886485532746988636185)
          ·
            refine ⟨474664864149560241477139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 632886485532746988636185 474664864149560241477139)
            ·
              refine ⟨711997296224340362215709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 474664864149560241477139 711997296224340362215709)
              ·
                refine ⟨266998986084127635830891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 711997296224340362215709 266998986084127635830891)
                ·
                  refine ⟨400498479126191453746337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 266998986084127635830891 400498479126191453746337)
                  ·
                    refine ⟨300373859344643590309753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 400498479126191453746337 300373859344643590309753)
                    ·
                      refine ⟨225280394508482692732315, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 300373859344643590309753 225280394508482692732315)
                      ·
                        rfl

theorem cell23_438732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 3, 2, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 3, 2, 1, 3, 1, 2, 2].length) (baseStart_438732 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_438732 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_438732 prefixEnd_438732 := by exact prefixLift 438732
  have htrace : WordTrace (prefixWord ++ tailWord_438732) baseStart_438732 baseEnd_438732 := by
    simpa [prefixWord, tailWord_438732, baseEnd_438732] using wordTrace_append hprefix tailTrace_438732
  have hstable : (prefixWord ++ tailWord_438732).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_438732).length < 2 ^ (prefixWord ++ tailWord_438732).sum := by decide
  have hdescent : baseEnd_438732 < baseStart_438732 := by decide
  rcases family_descends (prefixWord ++ tailWord_438732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_438765 : List Nat := [1, 5, 1, 3, 1, 1, 4, 1, 2, 1, 3]
def baseStart_438765 : Nat := 118140960795 + 438765 * 2 ^ 59
def prefixEnd_438765 : Nat := 4983230072969 + 3 ^ 40 * 438765 * 2
def baseEnd_438765 : Nat := 225297339370081063619663

theorem tailTrace_438765 : CollatzResearch.WordTrace tailWord_438765 prefixEnd_438765 225297339370081063619663 := by
  unfold tailWord_438765
  simp only [CollatzResearch.WordTrace]
  refine ⟨16003074255436814941221749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10668716170291209960814499 16003074255436814941221749)
  ·
    refine ⟨1500288211447201400739539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 16003074255436814941221749 1500288211447201400739539)
    ·
      refine ⟨2250432317170802101109309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1500288211447201400739539 2250432317170802101109309)
      ·
        refine ⟨843912118939050787915991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2250432317170802101109309 843912118939050787915991)
        ·
          refine ⟨1265868178408576181873987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 843912118939050787915991 1265868178408576181873987)
          ·
            refine ⟨1898802267612864272810981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1265868178408576181873987 1898802267612864272810981)
            ·
              refine ⟨356025425177412051152059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1898802267612864272810981 356025425177412051152059)
              ·
                refine ⟨534038137766118076728089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 356025425177412051152059 534038137766118076728089)
                ·
                  refine ⟨400528603324588557546067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 534038137766118076728089 400528603324588557546067)
                  ·
                    refine ⟨600792904986882836319101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 400528603324588557546067 600792904986882836319101)
                    ·
                      refine ⟨225297339370081063619663, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 600792904986882836319101 225297339370081063619663)
                      ·
                        rfl

theorem cell23_438765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 1, 4, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 1, 4, 1, 2, 1, 3].length) (baseStart_438765 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_438765 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_438765 prefixEnd_438765 := by exact prefixLift 438765
  have htrace : WordTrace (prefixWord ++ tailWord_438765) baseStart_438765 baseEnd_438765 := by
    simpa [prefixWord, tailWord_438765, baseEnd_438765] using wordTrace_append hprefix tailTrace_438765
  have hstable : (prefixWord ++ tailWord_438765).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_438765).length < 2 ^ (prefixWord ++ tailWord_438765).sum := by decide
  have hdescent : baseEnd_438765 < baseStart_438765 := by decide
  rcases family_descends (prefixWord ++ tailWord_438765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_438767 : List Nat := [1, 1, 2, 1, 4, 1, 1, 3, 1, 4, 4]
def baseStart_438767 : Nat := 118140960795 + 438767 * 2 ^ 59
def prefixEnd_438767 : Nat := 4983230072969 + 3 ^ 40 * 438767 * 2
def baseEnd_438767 : Nat := 225298366331390055794653

theorem tailTrace_438767 : CollatzResearch.WordTrace tailWord_438767 prefixEnd_438767 225298366331390055794653 := by
  unfold tailWord_438767
  simp only [CollatzResearch.WordTrace]
  refine ⟨16003147201429569282794555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10668764800953046188529703 16003147201429569282794555)
  ·
    refine ⟨24004720802144353924191833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16003147201429569282794555 24004720802144353924191833)
    ·
      refine ⟨18003540601608265443143875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24004720802144353924191833 18003540601608265443143875)
      ·
        refine ⟨27005310902412398164715813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18003540601608265443143875 27005310902412398164715813)
        ·
          refine ⟨5063495794202324655884215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 27005310902412398164715813 5063495794202324655884215)
          ·
            refine ⟨7595243691303486983826323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5063495794202324655884215 7595243691303486983826323)
            ·
              refine ⟨11392865536955230475739485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7595243691303486983826323 11392865536955230475739485)
              ·
                refine ⟨4272324576358211428402307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11392865536955230475739485 4272324576358211428402307)
                ·
                  refine ⟨6408486864537317142603461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4272324576358211428402307 6408486864537317142603461)
                  ·
                    refine ⟨1201591287100746964238149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6408486864537317142603461 1201591287100746964238149)
                    ·
                      refine ⟨225298366331390055794653, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1201591287100746964238149 225298366331390055794653)
                      ·
                        rfl

theorem cell23_438767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 1, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 1, 3, 1, 4, 4].length) (baseStart_438767 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_438767 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_438767 prefixEnd_438767 := by exact prefixLift 438767
  have htrace : WordTrace (prefixWord ++ tailWord_438767) baseStart_438767 baseEnd_438767 := by
    simpa [prefixWord, tailWord_438767, baseEnd_438767] using wordTrace_append hprefix tailTrace_438767
  have hstable : (prefixWord ++ tailWord_438767).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_438767).length < 2 ^ (prefixWord ++ tailWord_438767).sum := by decide
  have hdescent : baseEnd_438767 < baseStart_438767 := by decide
  rcases family_descends (prefixWord ++ tailWord_438767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_438774 : List Nat := [5, 1, 1, 1, 2, 1, 1, 1, 4, 1, 5]
def baseStart_438774 : Nat := 118140960795 + 438774 * 2 ^ 59
def prefixEnd_438774 : Nat := 4983230072969 + 3 ^ 40 * 438774 * 2
def baseEnd_438774 : Nat := 225301960695971528407121

theorem tailTrace_438774 : CollatzResearch.WordTrace tailWord_438774 prefixEnd_438774 225301960695971528407121 := by
  unfold tailWord_438774
  simp only [CollatzResearch.WordTrace]
  refine ⟨1000212657025263092393711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 10668935008269472985532917 1000212657025263092393711)
  ·
    refine ⟨1500318985537894638590567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1000212657025263092393711 1500318985537894638590567)
    ·
      refine ⟨2250478478306841957885851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1500318985537894638590567 2250478478306841957885851)
      ·
        refine ⟨3375717717460262936828777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2250478478306841957885851 3375717717460262936828777)
        ·
          refine ⟨2531788288095197202621583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3375717717460262936828777 2531788288095197202621583)
          ·
            refine ⟨3797682432142795803932375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2531788288095197202621583 3797682432142795803932375)
            ·
              refine ⟨5696523648214193705898563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3797682432142795803932375 5696523648214193705898563)
              ·
                refine ⟨8544785472321290558847845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5696523648214193705898563 8544785472321290558847845)
                ·
                  refine ⟨1602147276060241979783971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8544785472321290558847845 1602147276060241979783971)
                  ·
                    refine ⟨2403220914090362969675957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1602147276060241979783971 2403220914090362969675957)
                    ·
                      refine ⟨225301960695971528407121, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 2403220914090362969675957 225301960695971528407121)
                      ·
                        rfl

theorem cell23_438774_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 1, 1, 4, 1, 5].length) (baseStart_438774 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_438774 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_438774 prefixEnd_438774 := by exact prefixLift 438774
  have htrace : WordTrace (prefixWord ++ tailWord_438774) baseStart_438774 baseEnd_438774 := by
    simpa [prefixWord, tailWord_438774, baseEnd_438774] using wordTrace_append hprefix tailTrace_438774
  have hstable : (prefixWord ++ tailWord_438774).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_438774).length < 2 ^ (prefixWord ++ tailWord_438774).sum := by decide
  have hdescent : baseEnd_438774 < baseStart_438774 := by decide
  rcases family_descends (prefixWord ++ tailWord_438774) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_438777 : List Nat := [1, 2, 1, 3, 1, 2, 2, 4, 7]
def baseStart_438777 : Nat := 118140960795 + 438777 * 2 ^ 59
def prefixEnd_438777 : Nat := 4983230072969 + 3 ^ 40 * 438777 * 2
def baseEnd_438777 : Nat := 25033722348659446296623

theorem tailTrace_438777 : CollatzResearch.WordTrace tailWord_438777 prefixEnd_438777 25033722348659446296623 := by
  unfold tailWord_438777
  simp only [CollatzResearch.WordTrace]
  refine ⟨16003511931393340990658585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10669007954262227327105723 16003511931393340990658585)
  ·
    refine ⟨12002633948545005742993939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16003511931393340990658585 12002633948545005742993939)
    ·
      refine ⟨18003950922817508614490909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12002633948545005742993939 18003950922817508614490909)
      ·
        refine ⟨6751481596056565730434091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18003950922817508614490909 6751481596056565730434091)
        ·
          refine ⟨10127222394084848595651137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6751481596056565730434091 10127222394084848595651137)
          ·
            refine ⟨7595416795563636446738353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10127222394084848595651137 7595416795563636446738353)
            ·
              refine ⟨5696562596672727335053765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7595416795563636446738353 5696562596672727335053765)
              ·
                refine ⟨1068105486876136375322581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5696562596672727335053765 1068105486876136375322581)
                ·
                  refine ⟨25033722348659446296623, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1068105486876136375322581 25033722348659446296623)
                  ·
                    rfl

theorem cell23_438777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 2, 4, 7].length) (baseStart_438777 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_438777 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_438777 prefixEnd_438777 := by exact prefixLift 438777
  have htrace : WordTrace (prefixWord ++ tailWord_438777) baseStart_438777 baseEnd_438777 := by
    simpa [prefixWord, tailWord_438777, baseEnd_438777] using wordTrace_append hprefix tailTrace_438777
  have hstable : (prefixWord ++ tailWord_438777).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_438777).length < 2 ^ (prefixWord ++ tailWord_438777).sum := by decide
  have hdescent : baseEnd_438777 < baseStart_438777 := by decide
  rcases family_descends (prefixWord ++ tailWord_438777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_438788 : List Nat := [2, 3, 2, 3, 1, 2, 1, 2, 1, 4, 2]
def baseStart_438788 : Nat := 118140960795 + 438788 * 2 ^ 59
def prefixEnd_438788 : Nat := 4983230072969 + 3 ^ 40 * 438788 * 2
def baseEnd_438788 : Nat := 225309149425134473632057

theorem tailTrace_438788 : CollatzResearch.WordTrace tailWord_438788 prefixEnd_438788 225309149425134473632057 := by
  unfold tailWord_438788
  simp only [CollatzResearch.WordTrace]
  refine ⟨8001956567176744934654509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10669275422902326579539345 8001956567176744934654509)
  ·
    refine ⟨3000733712691279350495441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8001956567176744934654509 3000733712691279350495441)
    ·
      refine ⟨2250550284518459512871581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3000733712691279350495441 2250550284518459512871581)
      ·
        refine ⟨843956356694422317326843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2250550284518459512871581 843956356694422317326843)
        ·
          refine ⟨1265934535041633475990265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 843956356694422317326843 1265934535041633475990265)
          ·
            refine ⟨949450901281225106992699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1265934535041633475990265 949450901281225106992699)
            ·
              refine ⟨1424176351921837660489049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 949450901281225106992699 1424176351921837660489049)
              ·
                refine ⟨1068132263941378245366787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1424176351921837660489049 1068132263941378245366787)
                ·
                  refine ⟨1602198395912067368050181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1068132263941378245366787 1602198395912067368050181)
                  ·
                    refine ⟨300412199233512631509409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1602198395912067368050181 300412199233512631509409)
                    ·
                      refine ⟨225309149425134473632057, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 300412199233512631509409 225309149425134473632057)
                      ·
                        rfl

theorem cell23_438788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 2, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 2, 1, 2, 1, 4, 2].length) (baseStart_438788 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_438788 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_438788 prefixEnd_438788 := by exact prefixLift 438788
  have htrace : WordTrace (prefixWord ++ tailWord_438788) baseStart_438788 baseEnd_438788 := by
    simpa [prefixWord, tailWord_438788, baseEnd_438788] using wordTrace_append hprefix tailTrace_438788
  have hstable : (prefixWord ++ tailWord_438788).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_438788).length < 2 ^ (prefixWord ++ tailWord_438788).sum := by decide
  have hdescent : baseEnd_438788 < baseStart_438788 := by decide
  rcases family_descends (prefixWord ++ tailWord_438788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_438871 : List Nat := [1, 1, 3, 2, 2, 2, 4, 1, 3, 4]
def baseStart_438871 : Nat := 118140960795 + 438871 * 2 ^ 59
def prefixEnd_438871 : Nat := 4983230072969 + 3 ^ 40 * 438871 * 2
def baseEnd_438871 : Nat := 75117256106485882964725

theorem tailTrace_438871 : CollatzResearch.WordTrace tailWord_438871 prefixEnd_438871 75117256106485882964725 := by
  unfold tailWord_438871
  simp only [CollatzResearch.WordTrace]
  refine ⟨16006940393052795044580467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10671293595368530029720311 16006940393052795044580467)
  ·
    refine ⟨24010410589579192566870701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16006940393052795044580467 24010410589579192566870701)
    ·
      refine ⟨9003903971092197212576513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24010410589579192566870701 9003903971092197212576513)
      ·
        refine ⟨6752927978319147909432385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9003903971092197212576513 6752927978319147909432385)
        ·
          refine ⟨5064695983739360932074289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6752927978319147909432385 5064695983739360932074289)
          ·
            refine ⟨3798521987804520699055717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5064695983739360932074289 3798521987804520699055717)
            ·
              refine ⟨712222872713347631072947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3798521987804520699055717 712222872713347631072947)
              ·
                refine ⟨1068334309070021446609421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 712222872713347631072947 1068334309070021446609421)
                ·
                  refine ⟨400625365901258042478533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1068334309070021446609421 400625365901258042478533)
                  ·
                    refine ⟨75117256106485882964725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 400625365901258042478533 75117256106485882964725)
                    ·
                      rfl

theorem cell23_438871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 4, 1, 3, 4].length) (baseStart_438871 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_438871 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_438871 prefixEnd_438871 := by exact prefixLift 438871
  have htrace : WordTrace (prefixWord ++ tailWord_438871) baseStart_438871 baseEnd_438871 := by
    simpa [prefixWord, tailWord_438871, baseEnd_438871] using wordTrace_append hprefix tailTrace_438871
  have hstable : (prefixWord ++ tailWord_438871).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_438871).length < 2 ^ (prefixWord ++ tailWord_438871).sum := by decide
  have hdescent : baseEnd_438871 < baseStart_438871 := by decide
  rcases family_descends (prefixWord ++ tailWord_438871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_438905 : List Nat := [1, 2, 1, 3, 3, 4, 1, 3, 1, 4]
def baseStart_438905 : Nat := 118140960795 + 438905 * 2 ^ 59
def prefixEnd_438905 : Nat := 4983230072969 + 3 ^ 40 * 438905 * 2
def baseEnd_438905 : Nat := 75123075553903505289673

theorem tailTrace_438905 : CollatzResearch.WordTrace tailWord_438905 prefixEnd_438905 75123075553903505289673 := by
  unfold tailWord_438905
  simp only [CollatzResearch.WordTrace]
  refine ⟨16008180474929618851318169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10672120316619745900878779 16008180474929618851318169)
  ·
    refine ⟨12006135356197214138488627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16008180474929618851318169 12006135356197214138488627)
    ·
      refine ⟨18009203034295821207732941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12006135356197214138488627 18009203034295821207732941)
      ·
        refine ⟨6753451137860932952899853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18009203034295821207732941 6753451137860932952899853)
        ·
          refine ⟨2532544176697849857337445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6753451137860932952899853 2532544176697849857337445)
          ·
            refine ⟨474852033130846848250771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2532544176697849857337445 474852033130846848250771)
            ·
              refine ⟨712278049696270272376157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 474852033130846848250771 712278049696270272376157)
              ·
                refine ⟨267104268636101352141059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 712278049696270272376157 267104268636101352141059)
                ·
                  refine ⟨400656402954152028211589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 267104268636101352141059 400656402954152028211589)
                  ·
                    refine ⟨75123075553903505289673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 400656402954152028211589 75123075553903505289673)
                    ·
                      rfl

theorem cell23_438905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 4, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 4, 1, 3, 1, 4].length) (baseStart_438905 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_438905 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_438905 prefixEnd_438905 := by exact prefixLift 438905
  have htrace : WordTrace (prefixWord ++ tailWord_438905) baseStart_438905 baseEnd_438905 := by
    simpa [prefixWord, tailWord_438905, baseEnd_438905] using wordTrace_append hprefix tailTrace_438905
  have hstable : (prefixWord ++ tailWord_438905).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_438905).length < 2 ^ (prefixWord ++ tailWord_438905).sum := by decide
  have hdescent : baseEnd_438905 < baseStart_438905 := by decide
  rcases family_descends (prefixWord ++ tailWord_438905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_438922 : List Nat := [3, 1, 2, 3, 3, 1, 3, 2, 1, 4]
def baseStart_438922 : Nat := 118140960795 + 438922 * 2 ^ 59
def prefixEnd_438922 : Nat := 4983230072969 + 3 ^ 40 * 438922 * 2
def baseEnd_438922 : Nat := 75125985277612316452147

theorem tailTrace_438922 : CollatzResearch.WordTrace tailWord_438922 prefixEnd_438922 75125985277612316452147 := by
  unfold tailWord_438922
  simp only [CollatzResearch.WordTrace]
  refine ⟨4002200128967007688671755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10672533677245353836458013 4002200128967007688671755)
  ·
    refine ⟨6003300193450511533007633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4002200128967007688671755 6003300193450511533007633)
    ·
      refine ⟨4502475145087883649755725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6003300193450511533007633 4502475145087883649755725)
      ·
        refine ⟨1688428179407956368658397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4502475145087883649755725 1688428179407956368658397)
        ·
          refine ⟨633160567277983638246899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1688428179407956368658397 633160567277983638246899)
          ·
            refine ⟨949740850916975457370349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 633160567277983638246899 949740850916975457370349)
            ·
              refine ⟨356152819093865796513881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 949740850916975457370349 356152819093865796513881)
              ·
                refine ⟨267114614320399347385411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 356152819093865796513881 267114614320399347385411)
                ·
                  refine ⟨400671921480599021078117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 267114614320399347385411 400671921480599021078117)
                  ·
                    refine ⟨75125985277612316452147, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 400671921480599021078117 75125985277612316452147)
                    ·
                      rfl

theorem cell23_438922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 3, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 3, 1, 3, 2, 1, 4].length) (baseStart_438922 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_438922 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_438922 prefixEnd_438922 := by exact prefixLift 438922
  have htrace : WordTrace (prefixWord ++ tailWord_438922) baseStart_438922 baseEnd_438922 := by
    simpa [prefixWord, tailWord_438922, baseEnd_438922] using wordTrace_append hprefix tailTrace_438922
  have hstable : (prefixWord ++ tailWord_438922).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_438922).length < 2 ^ (prefixWord ++ tailWord_438922).sum := by decide
  have hdescent : baseEnd_438922 < baseStart_438922 := by decide
  rcases family_descends (prefixWord ++ tailWord_438922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_438965 : List Nat := [1, 3, 3, 3, 1, 2, 3, 1, 1, 5]
def baseStart_438965 : Nat := 118140960795 + 438965 * 2 ^ 59
def prefixEnd_438965 : Nat := 4983230072969 + 3 ^ 40 * 438965 * 2
def baseEnd_438965 : Nat := 75133345166993427039581

theorem tailTrace_438965 : CollatzResearch.WordTrace tailWord_438965 prefixEnd_438965 75133345166993427039581 := by
  unfold tailWord_438965
  simp only [CollatzResearch.WordTrace]
  refine ⟨16010368854712249098502349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10673579236474832732334899 16010368854712249098502349)
  ·
    refine ⟨6003888320517093411938381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16010368854712249098502349 6003888320517093411938381)
    ·
      refine ⟨2251458120193910029476893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6003888320517093411938381 2251458120193910029476893)
      ·
        refine ⟨844296795072716261053835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2251458120193910029476893 844296795072716261053835)
        ·
          refine ⟨1266445192609074391580753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 844296795072716261053835 1266445192609074391580753)
          ·
            refine ⟨949833894456805793685565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1266445192609074391580753 949833894456805793685565)
            ·
              refine ⟨356187710421302172632087, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 949833894456805793685565 356187710421302172632087)
              ·
                refine ⟨534281565631953258948131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 356187710421302172632087 534281565631953258948131)
                ·
                  refine ⟨801422348447929888422197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 534281565631953258948131 801422348447929888422197)
                  ·
                    refine ⟨75133345166993427039581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 801422348447929888422197 75133345166993427039581)
                    ·
                      rfl

theorem cell23_438965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 2, 3, 1, 1, 5].length) (baseStart_438965 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_438965 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_438965 prefixEnd_438965 := by exact prefixLift 438965
  have htrace : WordTrace (prefixWord ++ tailWord_438965) baseStart_438965 baseEnd_438965 := by
    simpa [prefixWord, tailWord_438965, baseEnd_438965] using wordTrace_append hprefix tailTrace_438965
  have hstable : (prefixWord ++ tailWord_438965).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_438965).length < 2 ^ (prefixWord ++ tailWord_438965).sum := by decide
  have hdescent : baseEnd_438965 < baseStart_438965 := by decide
  rcases family_descends (prefixWord ++ tailWord_438965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_438988 : List Nat := [2, 2, 1, 5, 1, 1, 1, 2, 3, 2, 3]
def baseStart_438988 : Nat := 118140960795 + 438988 * 2 ^ 59
def prefixEnd_438988 : Nat := 4983230072969 + 3 ^ 40 * 438988 * 2
def baseEnd_438988 : Nat := 225411845556033691131137

theorem tailTrace_438988 : CollatzResearch.WordTrace tailWord_438988 prefixEnd_438988 225411845556033691131137 := by
  unfold tailWord_438988
  simp only [CollatzResearch.WordTrace]
  refine ⟨8005603866814462013294809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10674138489085949351059745 8005603866814462013294809)
  ·
    refine ⟨6004202900110846509971107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8005603866814462013294809 6004202900110846509971107)
    ·
      refine ⟨9006304350166269764956661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6004202900110846509971107 9006304350166269764956661)
      ·
        refine ⟨844341032828087790464687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 9006304350166269764956661 844341032828087790464687)
        ·
          refine ⟨1266511549242131685697031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 844341032828087790464687 1266511549242131685697031)
          ·
            refine ⟨1899767323863197528545547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1266511549242131685697031 1899767323863197528545547)
            ·
              refine ⟨2849650985794796292818321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1899767323863197528545547 2849650985794796292818321)
              ·
                refine ⟨2137238239346097219613741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2849650985794796292818321 2137238239346097219613741)
                ·
                  refine ⟨801464339754786457355153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2137238239346097219613741 801464339754786457355153)
                  ·
                    refine ⟨601098254816089843016365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 801464339754786457355153 601098254816089843016365)
                    ·
                      refine ⟨225411845556033691131137, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 601098254816089843016365 225411845556033691131137)
                      ·
                        rfl

theorem cell23_438988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 1, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 1, 1, 2, 3, 2, 3].length) (baseStart_438988 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_438988 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_438988 prefixEnd_438988 := by exact prefixLift 438988
  have htrace : WordTrace (prefixWord ++ tailWord_438988) baseStart_438988 baseEnd_438988 := by
    simpa [prefixWord, tailWord_438988, baseEnd_438988] using wordTrace_append hprefix tailTrace_438988
  have hstable : (prefixWord ++ tailWord_438988).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_438988).length < 2 ^ (prefixWord ++ tailWord_438988).sum := by decide
  have hdescent : baseEnd_438988 < baseStart_438988 := by decide
  rcases family_descends (prefixWord ++ tailWord_438988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_439018 : List Nat := [3, 1, 3, 1, 1, 1, 1, 4, 4, 1, 3]
def baseStart_439018 : Nat := 118140960795 + 439018 * 2 ^ 59
def prefixEnd_439018 : Nat := 4983230072969 + 3 ^ 40 * 439018 * 2
def baseEnd_439018 : Nat := 225427249975668573755999

theorem tailTrace_439018 : CollatzResearch.WordTrace tailWord_439018 prefixEnd_439018 225427249975668573755999 := by
  unfold tailWord_439018
  simp only [CollatzResearch.WordTrace]
  refine ⟨4003075480880059787545427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10674867949013492766787805 4003075480880059787545427)
  ·
    refine ⟨6004613221320089681318141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4003075480880059787545427 6004613221320089681318141)
    ·
      refine ⟨2251729957995033630494303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6004613221320089681318141 2251729957995033630494303)
      ·
        refine ⟨3377594936992550445741455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2251729957995033630494303 3377594936992550445741455)
        ·
          refine ⟨5066392405488825668612183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3377594936992550445741455 5066392405488825668612183)
          ·
            refine ⟨7599588608233238502918275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5066392405488825668612183 7599588608233238502918275)
            ·
              refine ⟨11399382912349857754377413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7599588608233238502918275 11399382912349857754377413)
              ·
                refine ⟨2137384296065598328945765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11399382912349857754377413 2137384296065598328945765)
                ·
                  refine ⟨400759555512299686677331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2137384296065598328945765 400759555512299686677331)
                  ·
                    refine ⟨601139333268449530015997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 400759555512299686677331 601139333268449530015997)
                    ·
                      refine ⟨225427249975668573755999, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 601139333268449530015997 225427249975668573755999)
                      ·
                        rfl

theorem cell23_439018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 1, 4, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 1, 4, 4, 1, 3].length) (baseStart_439018 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_439018 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_439018 prefixEnd_439018 := by exact prefixLift 439018
  have htrace : WordTrace (prefixWord ++ tailWord_439018) baseStart_439018 baseEnd_439018 := by
    simpa [prefixWord, tailWord_439018, baseEnd_439018] using wordTrace_append hprefix tailTrace_439018
  have hstable : (prefixWord ++ tailWord_439018).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_439018).length < 2 ^ (prefixWord ++ tailWord_439018).sum := by decide
  have hdescent : baseEnd_439018 < baseStart_439018 := by decide
  rcases family_descends (prefixWord ++ tailWord_439018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_439022 : List Nat := [4, 1, 2, 1, 1, 5, 2, 1, 1, 2, 3]
def baseStart_439022 : Nat := 118140960795 + 439022 * 2 ^ 59
def prefixEnd_439022 : Nat := 4983230072969 + 3 ^ 40 * 439022 * 2
def baseEnd_439022 : Nat := 225429303898286558105981

theorem tailTrace_439022 : CollatzResearch.WordTrace tailWord_439022 prefixEnd_439022 225429303898286558105981 := by
  unfold tailWord_439022
  simp only [CollatzResearch.WordTrace]
  refine ⟨2001555976938218479165915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 10674965210337165222218213 2001555976938218479165915)
  ·
    refine ⟨3002333965407327718748873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2001555976938218479165915 3002333965407327718748873)
    ·
      refine ⟨2251750474055495789061655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3002333965407327718748873 2251750474055495789061655)
      ·
        refine ⟨3377625711083243683592483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2251750474055495789061655 3377625711083243683592483)
        ·
          refine ⟨5066438566624865525388725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3377625711083243683592483 5066438566624865525388725)
          ·
            refine ⟨474978615621081143005193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 5066438566624865525388725 474978615621081143005193)
            ·
              refine ⟨356233961715810857253895, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 474978615621081143005193 356233961715810857253895)
              ·
                refine ⟨534350942573716285880843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 356233961715810857253895 534350942573716285880843)
                ·
                  refine ⟨801526413860574428821265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 534350942573716285880843 801526413860574428821265)
                  ·
                    refine ⟨601144810395430821615949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 801526413860574428821265 601144810395430821615949)
                    ·
                      refine ⟨225429303898286558105981, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 601144810395430821615949 225429303898286558105981)
                      ·
                        rfl

theorem cell23_439022_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 5, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 5, 2, 1, 1, 2, 3].length) (baseStart_439022 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_439022 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_439022 prefixEnd_439022 := by exact prefixLift 439022
  have htrace : WordTrace (prefixWord ++ tailWord_439022) baseStart_439022 baseEnd_439022 := by
    simpa [prefixWord, tailWord_439022, baseEnd_439022] using wordTrace_append hprefix tailTrace_439022
  have hstable : (prefixWord ++ tailWord_439022).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_439022).length < 2 ^ (prefixWord ++ tailWord_439022).sum := by decide
  have hdescent : baseEnd_439022 < baseStart_439022 := by decide
  rcases family_descends (prefixWord ++ tailWord_439022) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_439061 : List Nat := [1, 3, 2, 1, 2, 2, 2, 2, 2, 1, 5]
def baseStart_439061 : Nat := 118140960795 + 439061 * 2 ^ 59
def prefixEnd_439061 : Nat := 4983230072969 + 3 ^ 40 * 439061 * 2
def baseEnd_439061 : Nat := 225449329643811905518301

theorem tailTrace_439061 : CollatzResearch.WordTrace tailWord_439061 prefixEnd_439061 225449329643811905518301 := by
  unfold tailWord_439061
  simp only [CollatzResearch.WordTrace]
  refine ⟨16013870262364457493997037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10675913508242971662664691 16013870262364457493997037)
  ·
    refine ⟨6005201348386671560248889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16013870262364457493997037 6005201348386671560248889)
    ·
      refine ⟨4503901011290003670186667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6005201348386671560248889 4503901011290003670186667)
      ·
        refine ⟨6755851516935005505280001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4503901011290003670186667 6755851516935005505280001)
        ·
          refine ⟨5066888637701254128960001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6755851516935005505280001 5066888637701254128960001)
          ·
            refine ⟨3800166478275940596720001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5066888637701254128960001 3800166478275940596720001)
            ·
              refine ⟨2850124858706955447540001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3800166478275940596720001 2850124858706955447540001)
              ·
                refine ⟨2137593644030216585655001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2850124858706955447540001 2137593644030216585655001)
                ·
                  refine ⟨1603195233022662439241251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2137593644030216585655001 1603195233022662439241251)
                  ·
                    refine ⟨2404792849533993658861877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1603195233022662439241251 2404792849533993658861877)
                    ·
                      refine ⟨225449329643811905518301, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 2404792849533993658861877 225449329643811905518301)
                      ·
                        rfl

theorem cell23_439061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 2, 2, 2, 1, 5].length) (baseStart_439061 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_439061 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_439061 prefixEnd_439061 := by exact prefixLift 439061
  have htrace : WordTrace (prefixWord ++ tailWord_439061) baseStart_439061 baseEnd_439061 := by
    simpa [prefixWord, tailWord_439061, baseEnd_439061] using wordTrace_append hprefix tailTrace_439061
  have hstable : (prefixWord ++ tailWord_439061).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_439061).length < 2 ^ (prefixWord ++ tailWord_439061).sum := by decide
  have hdescent : baseEnd_439061 < baseStart_439061 := by decide
  rcases family_descends (prefixWord ++ tailWord_439061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_439111 : List Nat := [1, 1, 4, 1, 2, 1, 1, 1, 6, 5]
def baseStart_439111 : Nat := 118140960795 + 439111 * 2 ^ 59
def prefixEnd_439111 : Nat := 4983230072969 + 3 ^ 40 * 439111 * 2
def baseEnd_439111 : Nat := 75158334558845569964357

theorem tailTrace_439111 : CollatzResearch.WordTrace tailWord_439111 prefixEnd_439111 75158334558845569964357 := by
  unfold tailWord_439111
  simp only [CollatzResearch.WordTrace]
  refine ⟨16015693912183316033317187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10677129274788877355544791 16015693912183316033317187)
  ·
    refine ⟨24023540868274974049975781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16015693912183316033317187 24023540868274974049975781)
    ·
      refine ⟨4504413912801557634370459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 24023540868274974049975781 4504413912801557634370459)
      ·
        refine ⟨6756620869202336451555689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4504413912801557634370459 6756620869202336451555689)
        ·
          refine ⟨5067465651901752338666767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6756620869202336451555689 5067465651901752338666767)
          ·
            refine ⟨7601198477852628508000151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5067465651901752338666767 7601198477852628508000151)
            ·
              refine ⟨11401797716778942762000227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7601198477852628508000151 11401797716778942762000227)
              ·
                refine ⟨17102696575168414143000341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11401797716778942762000227 17102696575168414143000341)
                ·
                  refine ⟨801688901961019412953141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 17102696575168414143000341 801688901961019412953141)
                  ·
                    refine ⟨75158334558845569964357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 801688901961019412953141 75158334558845569964357)
                    ·
                      rfl

theorem cell23_439111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 1, 1, 6, 5].length) (baseStart_439111 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_439111 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_439111 prefixEnd_439111 := by exact prefixLift 439111
  have htrace : WordTrace (prefixWord ++ tailWord_439111) baseStart_439111 baseEnd_439111 := by
    simpa [prefixWord, tailWord_439111, baseEnd_439111] using wordTrace_append hprefix tailTrace_439111
  have hstable : (prefixWord ++ tailWord_439111).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_439111).length < 2 ^ (prefixWord ++ tailWord_439111).sum := by decide
  have hdescent : baseEnd_439111 < baseStart_439111 := by decide
  rcases family_descends (prefixWord ++ tailWord_439111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_439148 : List Nat := [2, 2, 1, 1, 4, 1, 1, 4, 2, 1, 4]
def baseStart_439148 : Nat := 118140960795 + 439148 * 2 ^ 59
def prefixEnd_439148 : Nat := 4983230072969 + 3 ^ 40 * 439148 * 2
def baseEnd_439148 : Nat := 225494002460753065130401

theorem tailTrace_439148 : CollatzResearch.WordTrace tailWord_439148 prefixEnd_439148 225494002460753065130401 := by
  unfold tailWord_439148
  simp only [CollatzResearch.WordTrace]
  refine ⟨8008521706524635676207049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10678028942032847568276065 8008521706524635676207049)
  ·
    refine ⟨6006391279893476757155287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8008521706524635676207049 6006391279893476757155287)
    ·
      refine ⟨9009586919840215135732931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6006391279893476757155287 9009586919840215135732931)
      ·
        refine ⟨13514380379760322703599397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9009586919840215135732931 13514380379760322703599397)
        ·
          refine ⟨2533946321205060506924887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13514380379760322703599397 2533946321205060506924887)
          ·
            refine ⟨3800919481807590760387331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2533946321205060506924887 3800919481807590760387331)
            ·
              refine ⟨5701379222711386140580997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3800919481807590760387331 5701379222711386140580997)
              ·
                refine ⟨1069008604258384901358937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5701379222711386140580997 1069008604258384901358937)
                ·
                  refine ⟨801756453193788676019203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1069008604258384901358937 801756453193788676019203)
                  ·
                    refine ⟨1202634679790683014028805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 801756453193788676019203 1202634679790683014028805)
                    ·
                      refine ⟨225494002460753065130401, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1202634679790683014028805 225494002460753065130401)
                      ·
                        rfl

theorem cell23_439148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 2, 1, 4].length) (baseStart_439148 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_439148 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_439148 prefixEnd_439148 := by exact prefixLift 439148
  have htrace : WordTrace (prefixWord ++ tailWord_439148) baseStart_439148 baseEnd_439148 := by
    simpa [prefixWord, tailWord_439148, baseEnd_439148] using wordTrace_append hprefix tailTrace_439148
  have hstable : (prefixWord ++ tailWord_439148).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_439148).length < 2 ^ (prefixWord ++ tailWord_439148).sum := by decide
  have hdescent : baseEnd_439148 < baseStart_439148 := by decide
  rcases family_descends (prefixWord ++ tailWord_439148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_439175 : List Nat := [1, 1, 4, 2, 3, 2, 1, 2, 3, 4]
def baseStart_439175 : Nat := 118140960795 + 439175 * 2 ^ 59
def prefixEnd_439175 : Nat := 4983230072969 + 3 ^ 40 * 439175 * 2
def baseEnd_439175 : Nat := 75169288812808153164259

theorem tailTrace_439175 : CollatzResearch.WordTrace tailWord_439175 prefixEnd_439175 75169288812808153164259 := by
  unfold tailWord_439175
  simp only [CollatzResearch.WordTrace]
  refine ⟨16018028183951454963646979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10678685455967636642431319 16018028183951454963646979)
  ·
    refine ⟨24027042275927182445470469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16018028183951454963646979 24027042275927182445470469)
    ·
      refine ⟨4505070426736346708525713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 24027042275927182445470469 4505070426736346708525713)
      ·
        refine ⟨3378802820052260031394285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4505070426736346708525713 3378802820052260031394285)
        ·
          refine ⟨1267051057519597511772857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3378802820052260031394285 1267051057519597511772857)
          ·
            refine ⟨950288293139698133829643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1267051057519597511772857 950288293139698133829643)
            ·
              refine ⟨1425432439709547200744465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 950288293139698133829643 1425432439709547200744465)
              ·
                refine ⟨1069074329782160400558349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1425432439709547200744465 1069074329782160400558349)
                ·
                  refine ⟨400902873668310150209381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1069074329782160400558349 400902873668310150209381)
                  ·
                    refine ⟨75169288812808153164259, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 400902873668310150209381 75169288812808153164259)
                    ·
                      rfl

theorem cell23_439175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 2, 1, 2, 3, 4].length) (baseStart_439175 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_439175 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_439175 prefixEnd_439175 := by exact prefixLift 439175
  have htrace : WordTrace (prefixWord ++ tailWord_439175) baseStart_439175 baseEnd_439175 := by
    simpa [prefixWord, tailWord_439175, baseEnd_439175] using wordTrace_append hprefix tailTrace_439175
  have hstable : (prefixWord ++ tailWord_439175).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_439175).length < 2 ^ (prefixWord ++ tailWord_439175).sum := by decide
  have hdescent : baseEnd_439175 < baseStart_439175 := by decide
  rcases family_descends (prefixWord ++ tailWord_439175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_439188 : List Nat := [2, 4, 2, 1, 1, 1, 2, 2, 8]
def baseStart_439188 : Nat := 118140960795 + 439188 * 2 ^ 59
def prefixEnd_439188 : Nat := 4983230072969 + 3 ^ 40 * 439188 * 2
def baseEnd_439188 : Nat := 25057171298548100958913

theorem tailTrace_439188 : CollatzResearch.WordTrace tailWord_439188 prefixEnd_439188 25057171298548100958913 := by
  unfold tailWord_439188
  simp only [CollatzResearch.WordTrace]
  refine ⟨8009251166452179091935109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10679001555269572122580145 8009251166452179091935109)
  ·
    refine ⟨1501734593709783579737833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 8009251166452179091935109 1501734593709783579737833)
    ·
      refine ⟨1126300945282337684803375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1501734593709783579737833 1126300945282337684803375)
      ·
        refine ⟨1689451417923506527205063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1126300945282337684803375 1689451417923506527205063)
        ·
          refine ⟨2534177126885259790807595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1689451417923506527205063 2534177126885259790807595)
          ·
            refine ⟨3801265690327889686211393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2534177126885259790807595 3801265690327889686211393)
            ·
              refine ⟨2850949267745917264658545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3801265690327889686211393 2850949267745917264658545)
              ·
                refine ⟨2138211950809437948493909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2850949267745917264658545 2138211950809437948493909)
                ·
                  refine ⟨25057171298548100958913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 2138211950809437948493909 25057171298548100958913)
                  ·
                    rfl

theorem cell23_439188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 2, 2, 8].length) (baseStart_439188 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_439188 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_439188 prefixEnd_439188 := by exact prefixLift 439188
  have htrace : WordTrace (prefixWord ++ tailWord_439188) baseStart_439188 baseEnd_439188 := by
    simpa [prefixWord, tailWord_439188, baseEnd_439188] using wordTrace_append hprefix tailTrace_439188
  have hstable : (prefixWord ++ tailWord_439188).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_439188).length < 2 ^ (prefixWord ++ tailWord_439188).sum := by decide
  have hdescent : baseEnd_439188 < baseStart_439188 := by decide
  rcases family_descends (prefixWord ++ tailWord_439188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_439211 : List Nat := [1, 1, 1, 1, 2, 1, 1, 4, 2, 4, 5]
def baseStart_439211 : Nat := 118140960795 + 439211 * 2 ^ 59
def prefixEnd_439211 : Nat := 4983230072969 + 3 ^ 40 * 439211 * 2
def baseEnd_439211 : Nat := 225526351741986318642611

theorem tailTrace_439211 : CollatzResearch.WordTrace tailWord_439211 prefixEnd_439211 225526351741986318642611 := by
  unfold tailWord_439211
  simp only [CollatzResearch.WordTrace]
  refine ⟨16019341211821033111957487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10679560807880688741304991 16019341211821033111957487)
  ·
    refine ⟨24029011817731549667936231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16019341211821033111957487 24029011817731549667936231)
    ·
      refine ⟨36043517726597324501904347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24029011817731549667936231 36043517726597324501904347)
      ·
        refine ⟨54065276589895986752856521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36043517726597324501904347 54065276589895986752856521)
        ·
          refine ⟨40548957442421990064642391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54065276589895986752856521 40548957442421990064642391)
          ·
            refine ⟨60823436163632985096963587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40548957442421990064642391 60823436163632985096963587)
            ·
              refine ⟨91235154245449477645445381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60823436163632985096963587 91235154245449477645445381)
              ·
                refine ⟨17106591421021777058521009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 91235154245449477645445381 17106591421021777058521009)
                ·
                  refine ⟨12829943565766332793890757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17106591421021777058521009 12829943565766332793890757)
                  ·
                    refine ⟨2405614418581187398854517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12829943565766332793890757 2405614418581187398854517)
                    ·
                      refine ⟨225526351741986318642611, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 2405614418581187398854517 225526351741986318642611)
                      ·
                        rfl

theorem cell23_439211_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 4, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 4, 2, 4, 5].length) (baseStart_439211 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_439211 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_439211 prefixEnd_439211 := by exact prefixLift 439211
  have htrace : WordTrace (prefixWord ++ tailWord_439211) baseStart_439211 baseEnd_439211 := by
    simpa [prefixWord, tailWord_439211, baseEnd_439211] using wordTrace_append hprefix tailTrace_439211
  have hstable : (prefixWord ++ tailWord_439211).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_439211).length < 2 ^ (prefixWord ++ tailWord_439211).sum := by decide
  have hdescent : baseEnd_439211 < baseStart_439211 := by decide
  rcases family_descends (prefixWord ++ tailWord_439211) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_439225 : List Nat := [1, 2, 1, 4, 2, 2, 1, 2, 1, 5, 2]
def baseStart_439225 : Nat := 118140960795 + 439225 * 2 ^ 59
def prefixEnd_439225 : Nat := 4983230072969 + 3 ^ 40 * 439225 * 2
def baseEnd_439225 : Nat := 225533540471149263867547

theorem tailTrace_439225 : CollatzResearch.WordTrace tailWord_439225 prefixEnd_439225 225533540471149263867547 := by
  unfold tailWord_439225
  simp only [CollatzResearch.WordTrace]
  refine ⟨16019851833770313502967129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10679901222513542335311419 16019851833770313502967129)
  ·
    refine ⟨12014888875327735127225347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16019851833770313502967129 12014888875327735127225347)
    ·
      refine ⟨18022333312991602690838021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12014888875327735127225347 18022333312991602690838021)
      ·
        refine ⟨3379187496185925504532129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 18022333312991602690838021 3379187496185925504532129)
        ·
          refine ⟨2534390622139444128399097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3379187496185925504532129 2534390622139444128399097)
          ·
            refine ⟨1900792966604583096299323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2534390622139444128399097 1900792966604583096299323)
            ·
              refine ⟨2851189449906874644448985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1900792966604583096299323 2851189449906874644448985)
              ·
                refine ⟨2138392087430155983336739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2851189449906874644448985 2138392087430155983336739)
                ·
                  refine ⟨3207588131145233975005109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2138392087430155983336739 3207588131145233975005109)
                  ·
                    refine ⟨300711387294865685156729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3207588131145233975005109 300711387294865685156729)
                    ·
                      refine ⟨225533540471149263867547, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 300711387294865685156729 225533540471149263867547)
                      ·
                        rfl

theorem cell23_439225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 2, 1, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 2, 1, 2, 1, 5, 2].length) (baseStart_439225 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_439225 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_439225 prefixEnd_439225 := by exact prefixLift 439225
  have htrace : WordTrace (prefixWord ++ tailWord_439225) baseStart_439225 baseEnd_439225 := by
    simpa [prefixWord, tailWord_439225, baseEnd_439225] using wordTrace_append hprefix tailTrace_439225
  have hstable : (prefixWord ++ tailWord_439225).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_439225).length < 2 ^ (prefixWord ++ tailWord_439225).sum := by decide
  have hdescent : baseEnd_439225 < baseStart_439225 := by decide
  rcases family_descends (prefixWord ++ tailWord_439225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_439265 : List Nat := [1, 2, 3, 1, 2, 1, 1, 6, 2, 4]
def baseStart_439265 : Nat := 118140960795 + 439265 * 2 ^ 59
def prefixEnd_439265 : Nat := 4983230072969 + 3 ^ 40 * 439265 * 2
def baseEnd_439265 : Nat := 75184693232443035789121

theorem tailTrace_439265 : CollatzResearch.WordTrace tailWord_439265 prefixEnd_439265 75184693232443035789121 := by
  unfold tailWord_439265
  simp only [CollatzResearch.WordTrace]
  refine ⟨16021310753625400334423249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10680873835750266889615499 16021310753625400334423249)
  ·
    refine ⟨12015983065219050250817437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16021310753625400334423249 12015983065219050250817437)
    ·
      refine ⟨4505993649457143844056539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12015983065219050250817437 4505993649457143844056539)
      ·
        refine ⟨6758990474185715766084809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4505993649457143844056539 6758990474185715766084809)
        ·
          refine ⟨5069242855639286824563607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6758990474185715766084809 5069242855639286824563607)
          ·
            refine ⟨7603864283458930236845411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5069242855639286824563607 7603864283458930236845411)
            ·
              refine ⟨11405796425188395355268117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7603864283458930236845411 11405796425188395355268117)
              ·
                refine ⟨534646707430706032278193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 11405796425188395355268117 534646707430706032278193)
                ·
                  refine ⟨400985030573029524208645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 534646707430706032278193 400985030573029524208645)
                  ·
                    refine ⟨75184693232443035789121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 400985030573029524208645 75184693232443035789121)
                    ·
                      rfl

theorem cell23_439265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 1, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 1, 6, 2, 4].length) (baseStart_439265 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_439265 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_439265 prefixEnd_439265 := by exact prefixLift 439265
  have htrace : WordTrace (prefixWord ++ tailWord_439265) baseStart_439265 baseEnd_439265 := by
    simpa [prefixWord, tailWord_439265, baseEnd_439265] using wordTrace_append hprefix tailTrace_439265
  have hstable : (prefixWord ++ tailWord_439265).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_439265).length < 2 ^ (prefixWord ++ tailWord_439265).sum := by decide
  have hdescent : baseEnd_439265 < baseStart_439265 := by decide
  rcases family_descends (prefixWord ++ tailWord_439265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_439266 : List Nat := [3, 3, 3, 1, 1, 3, 1, 1, 3, 1, 3]
def baseStart_439266 : Nat := 118140960795 + 439266 * 2 ^ 59
def prefixEnd_439266 : Nat := 4983230072969 + 3 ^ 40 * 439266 * 2
def baseEnd_439266 : Nat := 225554593177983603454859

theorem tailTrace_439266 : CollatzResearch.WordTrace tailWord_439266 prefixEnd_439266 225554593177983603454859 := by
  unfold tailWord_439266
  simp only [CollatzResearch.WordTrace]
  refine ⟨4005336806655444376302413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10680898151081185003473101 4005336806655444376302413)
  ·
    refine ⟨1502001302495791641113405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4005336806655444376302413 1502001302495791641113405)
    ·
      refine ⟨563250488435921865417527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1502001302495791641113405 563250488435921865417527)
      ·
        refine ⟨844875732653882798126291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 563250488435921865417527 844875732653882798126291)
        ·
          refine ⟨1267313598980824197189437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 844875732653882798126291 1267313598980824197189437)
          ·
            refine ⟨475242599617809073946039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1267313598980824197189437 475242599617809073946039)
            ·
              refine ⟨712863899426713610919059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 475242599617809073946039 712863899426713610919059)
              ·
                refine ⟨1069295849140070416378589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 712863899426713610919059 1069295849140070416378589)
                ·
                  refine ⟨400985943427526406141971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1069295849140070416378589 400985943427526406141971)
                  ·
                    refine ⟨601478915141289609212957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 400985943427526406141971 601478915141289609212957)
                    ·
                      refine ⟨225554593177983603454859, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 601478915141289609212957 225554593177983603454859)
                      ·
                        rfl

theorem cell23_439266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 3, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 3, 1, 1, 3, 1, 3].length) (baseStart_439266 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_439266 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_439266 prefixEnd_439266 := by exact prefixLift 439266
  have htrace : WordTrace (prefixWord ++ tailWord_439266) baseStart_439266 baseEnd_439266 := by
    simpa [prefixWord, tailWord_439266, baseEnd_439266] using wordTrace_append hprefix tailTrace_439266
  have hstable : (prefixWord ++ tailWord_439266).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_439266).length < 2 ^ (prefixWord ++ tailWord_439266).sum := by decide
  have hdescent : baseEnd_439266 < baseStart_439266 := by decide
  rcases family_descends (prefixWord ++ tailWord_439266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_439268 : List Nat := [2, 3, 1, 1, 1, 1, 2, 1, 5, 2, 4]
def baseStart_439268 : Nat := 118140960795 + 439268 * 2 ^ 59
def prefixEnd_439268 : Nat := 4983230072969 + 3 ^ 40 * 439268 * 2
def baseEnd_439268 : Nat := 225555620139292595629849

theorem tailTrace_439268 : CollatzResearch.WordTrace tailWord_439268 prefixEnd_439268 225555620139292595629849 := by
  unfold tailWord_439268
  simp only [CollatzResearch.WordTrace]
  refine ⟨8010710086307265923391229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10680946781743021231188305 8010710086307265923391229)
  ·
    refine ⟨3004016282365224721271711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8010710086307265923391229 3004016282365224721271711)
    ·
      refine ⟨4506024423547837081907567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3004016282365224721271711 4506024423547837081907567)
      ·
        refine ⟨6759036635321755622861351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4506024423547837081907567 6759036635321755622861351)
        ·
          refine ⟨10138554952982633434292027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6759036635321755622861351 10138554952982633434292027)
          ·
            refine ⟨15207832429473950151438041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10138554952982633434292027 15207832429473950151438041)
            ·
              refine ⟨11405874322105462613578531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15207832429473950151438041 11405874322105462613578531)
              ·
                refine ⟨17108811483158193920367797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11405874322105462613578531 17108811483158193920367797)
                ·
                  refine ⟨1603951076546080680034481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 17108811483158193920367797 1603951076546080680034481)
                  ·
                    refine ⟨1202963307409560510025861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1603951076546080680034481 1202963307409560510025861)
                    ·
                      refine ⟨225555620139292595629849, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1202963307409560510025861 225555620139292595629849)
                      ·
                        rfl

theorem cell23_439268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 2, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 2, 1, 5, 2, 4].length) (baseStart_439268 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_439268 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_439268 prefixEnd_439268 := by exact prefixLift 439268
  have htrace : WordTrace (prefixWord ++ tailWord_439268) baseStart_439268 baseEnd_439268 := by
    simpa [prefixWord, tailWord_439268, baseEnd_439268] using wordTrace_append hprefix tailTrace_439268
  have hstable : (prefixWord ++ tailWord_439268).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_439268).length < 2 ^ (prefixWord ++ tailWord_439268).sum := by decide
  have hdescent : baseEnd_439268 < baseStart_439268 := by decide
  rcases family_descends (prefixWord ++ tailWord_439268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_439292 : List Nat := [2, 2, 2, 1, 2, 3, 3, 2, 1, 2, 3]
def baseStart_439292 : Nat := 118140960795 + 439292 * 2 ^ 59
def prefixEnd_439292 : Nat := 4983230072969 + 3 ^ 40 * 439292 * 2
def baseEnd_439292 : Nat := 225567943675000501729739

theorem tailTrace_439292 : CollatzResearch.WordTrace tailWord_439292 prefixEnd_439292 225567943675000501729739 := by
  unfold tailWord_439292
  simp only [CollatzResearch.WordTrace]
  refine ⟨8011147762263791972828065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10681530349685055963770753 8011147762263791972828065)
  ·
    refine ⟨6008360821697843979621049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8011147762263791972828065 6008360821697843979621049)
    ·
      refine ⟨4506270616273382984715787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6008360821697843979621049 4506270616273382984715787)
      ·
        refine ⟨6759405924410074477073681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4506270616273382984715787 6759405924410074477073681)
        ·
          refine ⟨5069554443307555857805261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6759405924410074477073681 5069554443307555857805261)
          ·
            refine ⟨1901082916240333446676973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5069554443307555857805261 1901082916240333446676973)
            ·
              refine ⟨712906093590125042503865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1901082916240333446676973 712906093590125042503865)
              ·
                refine ⟨534679570192593781877899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 712906093590125042503865 534679570192593781877899)
                ·
                  refine ⟨802019355288890672816849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 534679570192593781877899 802019355288890672816849)
                  ·
                    refine ⟨601514516466668004612637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 802019355288890672816849 601514516466668004612637)
                    ·
                      refine ⟨225567943675000501729739, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 601514516466668004612637 225567943675000501729739)
                      ·
                        rfl

theorem cell23_439292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 3, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 3, 3, 2, 1, 2, 3].length) (baseStart_439292 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_439292 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_439292 prefixEnd_439292 := by exact prefixLift 439292
  have htrace : WordTrace (prefixWord ++ tailWord_439292) baseStart_439292 baseEnd_439292 := by
    simpa [prefixWord, tailWord_439292, baseEnd_439292] using wordTrace_append hprefix tailTrace_439292
  have hstable : (prefixWord ++ tailWord_439292).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_439292).length < 2 ^ (prefixWord ++ tailWord_439292).sum := by decide
  have hdescent : baseEnd_439292 < baseStart_439292 := by decide
  rcases family_descends (prefixWord ++ tailWord_439292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_439305 : List Nat := [1, 2, 1, 1, 3, 1, 1, 3, 6, 1, 3]
def baseStart_439305 : Nat := 118140960795 + 439305 * 2 ^ 59
def prefixEnd_439305 : Nat := 4983230072969 + 3 ^ 40 * 439305 * 2
def baseEnd_439305 : Nat := 225574618923508950867179

theorem tailTrace_439305 : CollatzResearch.WordTrace tailWord_439305 prefixEnd_439305 225574618923508950867179 := by
  unfold tailWord_439305
  simp only [CollatzResearch.WordTrace]
  refine ⟨16022769673480487165879369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10681846448986991443919579 16022769673480487165879369)
  ·
    refine ⟨12017077255110365374409527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16022769673480487165879369 12017077255110365374409527)
    ·
      refine ⟨18025615882665548061614291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12017077255110365374409527 18025615882665548061614291)
      ·
        refine ⟨27038423823998322092421437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18025615882665548061614291 27038423823998322092421437)
        ·
          refine ⟨10139408933999370784658039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27038423823998322092421437 10139408933999370784658039)
          ·
            refine ⟨15209113400999056176987059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10139408933999370784658039 15209113400999056176987059)
            ·
              refine ⟨22813670101498584265480589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15209113400999056176987059 22813670101498584265480589)
              ·
                refine ⟨8555126288061969099555221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22813670101498584265480589 8555126288061969099555221)
                ·
                  refine ⟨401021544752904801541651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8555126288061969099555221 401021544752904801541651)
                  ·
                    refine ⟨601532317129357202312477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 401021544752904801541651 601532317129357202312477)
                    ·
                      refine ⟨225574618923508950867179, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 601532317129357202312477 225574618923508950867179)
                      ·
                        rfl

theorem cell23_439305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 1, 3, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 1, 3, 6, 1, 3].length) (baseStart_439305 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_439305 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_439305 prefixEnd_439305 := by exact prefixLift 439305
  have htrace : WordTrace (prefixWord ++ tailWord_439305) baseStart_439305 baseEnd_439305 := by
    simpa [prefixWord, tailWord_439305, baseEnd_439305] using wordTrace_append hprefix tailTrace_439305
  have hstable : (prefixWord ++ tailWord_439305).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_439305).length < 2 ^ (prefixWord ++ tailWord_439305).sum := by decide
  have hdescent : baseEnd_439305 < baseStart_439305 := by decide
  rcases family_descends (prefixWord ++ tailWord_439305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_439368 : List Nat := [2, 1, 3, 1, 1, 1, 3, 2, 9]
def baseStart_439368 : Nat := 118140960795 + 439368 * 2 ^ 59
def prefixEnd_439368 : Nat := 4983230072969 + 3 ^ 40 * 439368 * 2
def baseEnd_439368 : Nat := 25067440911638022708821

theorem tailTrace_439368 : CollatzResearch.WordTrace tailWord_439368 prefixEnd_439368 25067440911638022708821 := by
  unfold tailWord_439368
  simp only [CollatzResearch.WordTrace]
  refine ⟨8012533736126124462711379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10683378314834832616948505 8012533736126124462711379)
  ·
    refine ⟨12018800604189186694067069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8012533736126124462711379 12018800604189186694067069)
    ·
      refine ⟨4507050226570945010275151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12018800604189186694067069 4507050226570945010275151)
      ·
        refine ⟨6760575339856417515412727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4507050226570945010275151 6760575339856417515412727)
        ·
          refine ⟨10140863009784626273119091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6760575339856417515412727 10140863009784626273119091)
          ·
            refine ⟨15211294514676939409678637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10140863009784626273119091 15211294514676939409678637)
            ·
              refine ⟨5704235443003852278629489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15211294514676939409678637 5704235443003852278629489)
              ·
                refine ⟨4278176582252889208972117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5704235443003852278629489 4278176582252889208972117)
                ·
                  refine ⟨25067440911638022708821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 4278176582252889208972117 25067440911638022708821)
                  ·
                    rfl

theorem cell23_439368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 3, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 3, 2, 9].length) (baseStart_439368 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_439368 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_439368 prefixEnd_439368 := by exact prefixLift 439368
  have htrace : WordTrace (prefixWord ++ tailWord_439368) baseStart_439368 baseEnd_439368 := by
    simpa [prefixWord, tailWord_439368, baseEnd_439368] using wordTrace_append hprefix tailTrace_439368
  have hstable : (prefixWord ++ tailWord_439368).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_439368).length < 2 ^ (prefixWord ++ tailWord_439368).sum := by decide
  have hdescent : baseEnd_439368 < baseStart_439368 := by decide
  rcases family_descends (prefixWord ++ tailWord_439368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_439390 : List Nat := [4, 4, 1, 1, 1, 2, 3, 1, 2, 1, 3]
def baseStart_439390 : Nat := 118140960795 + 439390 * 2 ^ 59
def prefixEnd_439390 : Nat := 4983230072969 + 3 ^ 40 * 439390 * 2
def baseEnd_439390 : Nat := 225618264779141118304289

theorem tailTrace_439390 : CollatzResearch.WordTrace tailWord_439390 prefixEnd_439390 225618264779141118304289 := by
  unfold tailWord_439390
  simp only [CollatzResearch.WordTrace]
  refine ⟨2003233734771568335340453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 10683913252115031121815749 2003233734771568335340453)
  ·
    refine ⟨375606325269669062876335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2003233734771568335340453 375606325269669062876335)
    ·
      refine ⟨563409487904503594314503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 375606325269669062876335 563409487904503594314503)
      ·
        refine ⟨845114231856755391471755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 563409487904503594314503 845114231856755391471755)
        ·
          refine ⟨1267671347785133087207633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 845114231856755391471755 1267671347785133087207633)
          ·
            refine ⟨950753510838849815405725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1267671347785133087207633 950753510838849815405725)
            ·
              refine ⟨356532566564568680777147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 950753510838849815405725 356532566564568680777147)
              ·
                refine ⟨534798849846853021165721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 356532566564568680777147 534798849846853021165721)
                ·
                  refine ⟨401099137385139765874291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 534798849846853021165721 401099137385139765874291)
                  ·
                    refine ⟨601648706077709648811437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 401099137385139765874291 601648706077709648811437)
                    ·
                      refine ⟨225618264779141118304289, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 601648706077709648811437 225618264779141118304289)
                      ·
                        rfl

theorem cell23_439390_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 2, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 2, 3, 1, 2, 1, 3].length) (baseStart_439390 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_439390 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_439390 prefixEnd_439390 := by exact prefixLift 439390
  have htrace : WordTrace (prefixWord ++ tailWord_439390) baseStart_439390 baseEnd_439390 := by
    simpa [prefixWord, tailWord_439390, baseEnd_439390] using wordTrace_append hprefix tailTrace_439390
  have hstable : (prefixWord ++ tailWord_439390).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_439390).length < 2 ^ (prefixWord ++ tailWord_439390).sum := by decide
  have hdescent : baseEnd_439390 < baseStart_439390 := by decide
  rcases family_descends (prefixWord ++ tailWord_439390) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_439415 : List Nat := [1, 1, 3, 1, 1, 4, 2, 3, 2, 5]
def baseStart_439415 : Nat := 118140960795 + 439415 * 2 ^ 59
def prefixEnd_439415 : Nat := 4983230072969 + 3 ^ 40 * 439415 * 2
def baseEnd_439415 : Nat := 75210367265167840163891

theorem tailTrace_439415 : CollatzResearch.WordTrace tailWord_439415 prefixEnd_439415 75210367265167840163891 := by
  unfold tailWord_439415
  simp only [CollatzResearch.WordTrace]
  refine ⟨16026781703081975952383699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10684521135387983968255799 16026781703081975952383699)
  ·
    refine ⟨24040172554622963928575549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16026781703081975952383699 24040172554622963928575549)
    ·
      refine ⟨9015064707983611473215831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24040172554622963928575549 9015064707983611473215831)
      ·
        refine ⟨13522597061975417209823747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9015064707983611473215831 13522597061975417209823747)
        ·
          refine ⟨20283895592963125814735621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13522597061975417209823747 20283895592963125814735621)
          ·
            refine ⟨3803230423680586090262929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 20283895592963125814735621 3803230423680586090262929)
            ·
              refine ⟨2852422817760439567697197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3803230423680586090262929 2852422817760439567697197)
              ·
                refine ⟨1069658556660164837886449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2852422817760439567697197 1069658556660164837886449)
                ·
                  refine ⟨802243917495123628414837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1069658556660164837886449 802243917495123628414837)
                  ·
                    refine ⟨75210367265167840163891, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 802243917495123628414837 75210367265167840163891)
                    ·
                      rfl

theorem cell23_439415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 2, 3, 2, 5].length) (baseStart_439415 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_439415 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_439415 prefixEnd_439415 := by exact prefixLift 439415
  have htrace : WordTrace (prefixWord ++ tailWord_439415) baseStart_439415 baseEnd_439415 := by
    simpa [prefixWord, tailWord_439415, baseEnd_439415] using wordTrace_append hprefix tailTrace_439415
  have hstable : (prefixWord ++ tailWord_439415).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_439415).length < 2 ^ (prefixWord ++ tailWord_439415).sum := by decide
  have hdescent : baseEnd_439415 < baseStart_439415 := by decide
  rcases family_descends (prefixWord ++ tailWord_439415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_439442 : List Nat := [3, 2, 3, 1, 1, 3, 1, 1, 1, 2, 5]
def baseStart_439442 : Nat := 118140960795 + 439442 * 2 ^ 59
def prefixEnd_439442 : Nat := 4983230072969 + 3 ^ 40 * 439442 * 2
def baseEnd_439442 : Nat := 225644965773174914854049

theorem tailTrace_439442 : CollatzResearch.WordTrace tailWord_439442 prefixEnd_439442 225644965773174914854049 := by
  unfold tailWord_439442
  simp only [CollatzResearch.WordTrace]
  refine ⟨4006941618496039890904145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10685177649322773042411053 4006941618496039890904145)
  ·
    refine ⟨3005206213872029918178109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4006941618496039890904145 3005206213872029918178109)
    ·
      refine ⟨1126952330202011219316791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3005206213872029918178109 1126952330202011219316791)
      ·
        refine ⟨1690428495303016828975187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1126952330202011219316791 1690428495303016828975187)
        ·
          refine ⟨2535642742954525243462781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1690428495303016828975187 2535642742954525243462781)
          ·
            refine ⟨950866028607946966298543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2535642742954525243462781 950866028607946966298543)
            ·
              refine ⟨1426299042911920449447815, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 950866028607946966298543 1426299042911920449447815)
              ·
                refine ⟨2139448564367880674171723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1426299042911920449447815 2139448564367880674171723)
                ·
                  refine ⟨3209172846551821011257585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2139448564367880674171723 3209172846551821011257585)
                  ·
                    refine ⟨2406879634913865758443189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3209172846551821011257585 2406879634913865758443189)
                    ·
                      refine ⟨225644965773174914854049, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 2406879634913865758443189 225644965773174914854049)
                      ·
                        rfl

theorem cell23_439442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 3, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 3, 1, 1, 1, 2, 5].length) (baseStart_439442 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_439442 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_439442 prefixEnd_439442 := by exact prefixLift 439442
  have htrace : WordTrace (prefixWord ++ tailWord_439442) baseStart_439442 baseEnd_439442 := by
    simpa [prefixWord, tailWord_439442, baseEnd_439442] using wordTrace_append hprefix tailTrace_439442
  have hstable : (prefixWord ++ tailWord_439442).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_439442).length < 2 ^ (prefixWord ++ tailWord_439442).sum := by decide
  have hdescent : baseEnd_439442 < baseStart_439442 := by decide
  rcases family_descends (prefixWord ++ tailWord_439442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_439479 : List Nat := [1, 1, 3, 1, 4, 1, 2, 5, 1, 4]
def baseStart_439479 : Nat := 118140960795 + 439479 * 2 ^ 59
def prefixEnd_439479 : Nat := 4983230072969 + 3 ^ 40 * 439479 * 2
def baseEnd_439479 : Nat := 75221321519130423363793

theorem tailTrace_439479 : CollatzResearch.WordTrace tailWord_439479 prefixEnd_439479 75221321519130423363793 := by
  unfold tailWord_439479
  simp only [CollatzResearch.WordTrace]
  refine ⟨16029115974850114882713491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10686077316566743255142327 16029115974850114882713491)
  ·
    refine ⟨24043673962275172324070237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16029115974850114882713491 24043673962275172324070237)
    ·
      refine ⟨9016377735853189621526339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24043673962275172324070237 9016377735853189621526339)
      ·
        refine ⟨13524566603779784432289509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9016377735853189621526339 13524566603779784432289509)
        ·
          refine ⟨2535856238208709581054283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13524566603779784432289509 2535856238208709581054283)
          ·
            refine ⟨3803784357313064371581425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2535856238208709581054283 3803784357313064371581425)
            ·
              refine ⟨2852838267984798278686069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3803784357313064371581425 2852838267984798278686069)
              ·
                refine ⟨267453587623574838626819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 2852838267984798278686069 267453587623574838626819)
                ·
                  refine ⟨401180381435362257940229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 267453587623574838626819 401180381435362257940229)
                  ·
                    refine ⟨75221321519130423363793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 401180381435362257940229 75221321519130423363793)
                    ·
                      rfl

theorem cell23_439479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 2, 5, 1, 4].length) (baseStart_439479 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_439479 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_439479 prefixEnd_439479 := by exact prefixLift 439479
  have htrace : WordTrace (prefixWord ++ tailWord_439479) baseStart_439479 baseEnd_439479 := by
    simpa [prefixWord, tailWord_439479, baseEnd_439479] using wordTrace_append hprefix tailTrace_439479
  have hstable : (prefixWord ++ tailWord_439479).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_439479).length < 2 ^ (prefixWord ++ tailWord_439479).sum := by decide
  have hdescent : baseEnd_439479 < baseStart_439479 := by decide
  rcases family_descends (prefixWord ++ tailWord_439479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_439496 : List Nat := [2, 1, 3, 1, 2, 1, 6, 2, 1, 4]
def baseStart_439496 : Nat := 118140960795 + 439496 * 2 ^ 59
def prefixEnd_439496 : Nat := 4983230072969 + 3 ^ 40 * 439496 * 2
def baseEnd_439496 : Nat := 75224231242839234526267

theorem tailTrace_439496 : CollatzResearch.WordTrace tailWord_439496 prefixEnd_439496 75224231242839234526267 := by
  unfold tailWord_439496
  simp only [CollatzResearch.WordTrace]
  refine ⟨8014868007894263393041171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10686490677192351190721561 8014868007894263393041171)
  ·
    refine ⟨12022302011841395089561757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8014868007894263393041171 12022302011841395089561757)
    ·
      refine ⟨4508363254440523158585659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12022302011841395089561757 4508363254440523158585659)
      ·
        refine ⟨6762544881660784737878489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4508363254440523158585659 6762544881660784737878489)
        ·
          refine ⟨5071908661245588553408867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6762544881660784737878489 5071908661245588553408867)
          ·
            refine ⟨7607862991868382830113301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5071908661245588553408867 7607862991868382830113301)
            ·
              refine ⟨356618577743830445161561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 7607862991868382830113301 356618577743830445161561)
              ·
                refine ⟨267463933307872833871171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 356618577743830445161561 267463933307872833871171)
                ·
                  refine ⟨401195899961809250806757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 267463933307872833871171 401195899961809250806757)
                  ·
                    refine ⟨75224231242839234526267, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 401195899961809250806757 75224231242839234526267)
                    ·
                      rfl

theorem cell23_439496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 6, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 6, 2, 1, 4].length) (baseStart_439496 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_439496 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_439496 prefixEnd_439496 := by exact prefixLift 439496
  have htrace : WordTrace (prefixWord ++ tailWord_439496) baseStart_439496 baseEnd_439496 := by
    simpa [prefixWord, tailWord_439496, baseEnd_439496] using wordTrace_append hprefix tailTrace_439496
  have hstable : (prefixWord ++ tailWord_439496).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_439496).length < 2 ^ (prefixWord ++ tailWord_439496).sum := by decide
  have hdescent : baseEnd_439496 < baseStart_439496 := by decide
  rcases family_descends (prefixWord ++ tailWord_439496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_439539 : List Nat := [1, 1, 1, 2, 2, 5, 4, 1, 1, 5]
def baseStart_439539 : Nat := 118140960795 + 439539 * 2 ^ 59
def prefixEnd_439539 : Nat := 4983230072969 + 3 ^ 40 * 439539 * 2
def baseEnd_439539 : Nat := 75231591132220345113701

theorem tailTrace_439539 : CollatzResearch.WordTrace tailWord_439539 prefixEnd_439539 75231591132220345113701 := by
  unfold tailWord_439539
  simp only [CollatzResearch.WordTrace]
  refine ⟨16031304354632745129897671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10687536236421830086598447 16031304354632745129897671)
  ·
    refine ⟨24046956531949117694846507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16031304354632745129897671 24046956531949117694846507)
    ·
      refine ⟨36070434797923676542269761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24046956531949117694846507 36070434797923676542269761)
      ·
        refine ⟨27052826098442757406702321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36070434797923676542269761 27052826098442757406702321)
        ·
          refine ⟨20289619573832068055026741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27052826098442757406702321 20289619573832068055026741)
          ·
            refine ⟨1902151835046756380158757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 20289619573832068055026741 1902151835046756380158757)
            ·
              refine ⟨356653469071266821279767, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1902151835046756380158757 356653469071266821279767)
              ·
                refine ⟨534980203606900231919651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 356653469071266821279767 534980203606900231919651)
                ·
                  refine ⟨802470305410350347879477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 534980203606900231919651 802470305410350347879477)
                  ·
                    refine ⟨75231591132220345113701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 802470305410350347879477 75231591132220345113701)
                    ·
                      rfl

theorem cell23_439539_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 5, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 5, 4, 1, 1, 5].length) (baseStart_439539 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_439539 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_439539 prefixEnd_439539 := by exact prefixLift 439539
  have htrace : WordTrace (prefixWord ++ tailWord_439539) baseStart_439539 baseEnd_439539 := by
    simpa [prefixWord, tailWord_439539, baseEnd_439539] using wordTrace_append hprefix tailTrace_439539
  have hstable : (prefixWord ++ tailWord_439539).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_439539).length < 2 ^ (prefixWord ++ tailWord_439539).sum := by decide
  have hdescent : baseEnd_439539 < baseStart_439539 := by decide
  rcases family_descends (prefixWord ++ tailWord_439539) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
