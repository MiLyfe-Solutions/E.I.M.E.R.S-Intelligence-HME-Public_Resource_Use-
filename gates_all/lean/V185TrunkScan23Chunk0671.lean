import V185TrunkScan23Chunk0670

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_3967097 : List Nat := [1, 2, 1, 3, 4, 1, 2, 4, 5]
def baseStart_3967097 : Nat := 118140960795 + 3967097 * 2 ^ 59
def prefixEnd_3967097 : Nat := 4983230072969 + 3 ^ 40 * 3967097 * 2
def baseEnd_3967097 : Nat := 226336396001063383160351

theorem tailTrace_3967097 : CollatzResearch.WordTrace tailWord_3967097 prefixEnd_3967097 226336396001063383160351 := by
  unfold tailWord_3967097
  simp only [CollatzResearch.WordTrace]
  refine ⟨144691914508892570072091545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96461276339261713381394363 144691914508892570072091545)
  ·
    refine ⟨108518935881669427554068659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 144691914508892570072091545 108518935881669427554068659)
    ·
      refine ⟨162778403822504141331102989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108518935881669427554068659 162778403822504141331102989)
      ·
        refine ⟨61041901433439052999163621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 162778403822504141331102989 61041901433439052999163621)
        ·
          refine ⟨11445356518769822437343179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 61041901433439052999163621 11445356518769822437343179)
          ·
            refine ⟨17168034778154733656014769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11445356518769822437343179 17168034778154733656014769)
            ·
              refine ⟨12876026083616050242011077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17168034778154733656014769 12876026083616050242011077)
              ·
                refine ⟨2414254890678009420377077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12876026083616050242011077 2414254890678009420377077)
                ·
                  refine ⟨226336396001063383160351, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2414254890678009420377077 226336396001063383160351)
                  ·
                    rfl

theorem cell23_3967097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 1, 2, 4, 5].length) (baseStart_3967097 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3967097 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3967097 prefixEnd_3967097 := by exact prefixLift 3967097
  have htrace : WordTrace (prefixWord ++ tailWord_3967097) baseStart_3967097 baseEnd_3967097 := by
    simpa [prefixWord, tailWord_3967097, baseEnd_3967097] using wordTrace_append hprefix tailTrace_3967097
  have hstable : (prefixWord ++ tailWord_3967097).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3967097).length < 2 ^ (prefixWord ++ tailWord_3967097).sum := by decide
  have hdescent : baseEnd_3967097 < baseStart_3967097 := by decide
  rcases family_descends (prefixWord ++ tailWord_3967097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3967123 : List Nat := [1, 1, 1, 2, 1, 2, 3, 1, 1, 10]
def baseStart_3967123 : Nat := 118140960795 + 3967123 * 2 ^ 59
def prefixEnd_3967123 : Nat := 4983230072969 + 3 ^ 40 * 3967123 * 2
def baseEnd_3967123 : Nat := 679013638168862448906013

theorem tailTrace_3967123 : CollatzResearch.WordTrace tailWord_3967123 prefixEnd_3967123 679013638168862448906013 := by
  unfold tailWord_3967123
  simp only [CollatzResearch.WordTrace]
  refine ⟨144692862806798376512538023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96461908537865584341692015 144692862806798376512538023)
  ·
    refine ⟨217039294210197564768807035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144692862806798376512538023 217039294210197564768807035)
    ·
      refine ⟨325558941315296347153210553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 217039294210197564768807035 325558941315296347153210553)
      ·
        refine ⟨244169205986472260364907915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 325558941315296347153210553 244169205986472260364907915)
        ·
          refine ⟨366253808979708390547361873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 244169205986472260364907915 366253808979708390547361873)
          ·
            refine ⟨274690356734781292910521405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 366253808979708390547361873 274690356734781292910521405)
            ·
              refine ⟨103008883775542984841445527, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 274690356734781292910521405 103008883775542984841445527)
              ·
                refine ⟨154513325663314477262168291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 103008883775542984841445527 154513325663314477262168291)
                ·
                  refine ⟨231769988494971715893252437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 154513325663314477262168291 231769988494971715893252437)
                  ·
                    refine ⟨679013638168862448906013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 231769988494971715893252437 679013638168862448906013)
                    ·
                      rfl

theorem cell23_3967123_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 3, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 3, 1, 1, 10].length) (baseStart_3967123 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3967123 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3967123 prefixEnd_3967123 := by exact prefixLift 3967123
  have htrace : WordTrace (prefixWord ++ tailWord_3967123) baseStart_3967123 baseEnd_3967123 := by
    simpa [prefixWord, tailWord_3967123, baseEnd_3967123] using wordTrace_append hprefix tailTrace_3967123
  have hstable : (prefixWord ++ tailWord_3967123).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3967123).length < 2 ^ (prefixWord ++ tailWord_3967123).sum := by decide
  have hdescent : baseEnd_3967123 < baseStart_3967123 := by decide
  rcases family_descends (prefixWord ++ tailWord_3967123) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3967208 : List Nat := [2, 1, 4, 1, 2, 4, 2, 2, 1, 4]
def baseStart_3967208 : Nat := 118140960795 + 3967208 * 2 ^ 59
def prefixEnd_3967208 : Nat := 4983230072969 + 3 ^ 40 * 3967208 * 2
def baseEnd_3967208 : Nat := 679028186787406504718383

theorem tailTrace_3967208 : CollatzResearch.WordTrace tailWord_3967208 prefixEnd_3967208 679028186787406504718383 := by
  unfold tailWord_3967208
  simp only [CollatzResearch.WordTrace]
  refine ⟨72347981505745218014691139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96463975340993624019588185 72347981505745218014691139)
  ·
    refine ⟨108521972258617827022036709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72347981505745218014691139 108521972258617827022036709)
    ·
      refine ⟨20347869798490842566631883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 108521972258617827022036709 20347869798490842566631883)
      ·
        refine ⟨30521804697736263849947825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20347869798490842566631883 30521804697736263849947825)
        ·
          refine ⟨22891353523302197887460869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30521804697736263849947825 22891353523302197887460869)
          ·
            refine ⟨4292128785619162103898913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 22891353523302197887460869 4292128785619162103898913)
            ·
              refine ⟨3219096589214371577924185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4292128785619162103898913 3219096589214371577924185)
              ·
                refine ⟨2414322441910778683443139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3219096589214371577924185 2414322441910778683443139)
                ·
                  refine ⟨3621483662866168025164709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2414322441910778683443139 3621483662866168025164709)
                  ·
                    refine ⟨679028186787406504718383, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3621483662866168025164709 679028186787406504718383)
                    ·
                      rfl

theorem cell23_3967208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 4, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 4, 2, 2, 1, 4].length) (baseStart_3967208 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3967208 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3967208 prefixEnd_3967208 := by exact prefixLift 3967208
  have htrace : WordTrace (prefixWord ++ tailWord_3967208) baseStart_3967208 baseEnd_3967208 := by
    simpa [prefixWord, tailWord_3967208, baseEnd_3967208] using wordTrace_append hprefix tailTrace_3967208
  have hstable : (prefixWord ++ tailWord_3967208).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3967208).length < 2 ^ (prefixWord ++ tailWord_3967208).sum := by decide
  have hdescent : baseEnd_3967208 < baseStart_3967208 := by decide
  rcases family_descends (prefixWord ++ tailWord_3967208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3967214 : List Nat := [4, 1, 2, 1, 1, 1, 1, 5, 3, 1, 3]
def baseStart_3967214 : Nat := 118140960795 + 3967214 * 2 ^ 59
def prefixEnd_3967214 : Nat := 4983230072969 + 3 ^ 40 * 3967214 * 2
def baseEnd_3967214 : Nat := 2037087641246146490680121

theorem tailTrace_3967214 : CollatzResearch.WordTrace tailWord_3967214 prefixEnd_3967214 2037087641246146490680121 := by
  unfold tailWord_3967214
  simp only [CollatzResearch.WordTrace]
  refine ⟨18087022731183587381762587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 96464121232979132702733797 18087022731183587381762587)
  ·
    refine ⟨27130534096775381072643881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18087022731183587381762587 27130534096775381072643881)
    ·
      refine ⟨20347900572581535804482911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27130534096775381072643881 20347900572581535804482911)
      ·
        refine ⟨30521850858872303706724367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20347900572581535804482911 30521850858872303706724367)
        ·
          refine ⟨45782776288308455560086551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30521850858872303706724367 45782776288308455560086551)
          ·
            refine ⟨68674164432462683340129827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45782776288308455560086551 68674164432462683340129827)
            ·
              refine ⟨103011246648694025010194741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68674164432462683340129827 103011246648694025010194741)
              ·
                refine ⟨9657304373315064844705757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 103011246648694025010194741 9657304373315064844705757)
                ·
                  refine ⟨3621489139993149316764659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9657304373315064844705757 3621489139993149316764659)
                  ·
                    refine ⟨5432233709989723975146989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3621489139993149316764659 5432233709989723975146989)
                    ·
                      refine ⟨2037087641246146490680121, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5432233709989723975146989 2037087641246146490680121)
                      ·
                        rfl

theorem cell23_3967214_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 1, 5, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 1, 5, 3, 1, 3].length) (baseStart_3967214 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3967214 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3967214 prefixEnd_3967214 := by exact prefixLift 3967214
  have htrace : WordTrace (prefixWord ++ tailWord_3967214) baseStart_3967214 baseEnd_3967214 := by
    simpa [prefixWord, tailWord_3967214, baseEnd_3967214] using wordTrace_append hprefix tailTrace_3967214
  have hstable : (prefixWord ++ tailWord_3967214).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3967214).length < 2 ^ (prefixWord ++ tailWord_3967214).sum := by decide
  have hdescent : baseEnd_3967214 < baseStart_3967214 := by decide
  rcases family_descends (prefixWord ++ tailWord_3967214) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3967234 : List Nat := [3, 4, 1, 1, 2, 1, 2, 1, 3, 5]
def baseStart_3967234 : Nat := 118140960795 + 3967234 * 2 ^ 59
def prefixEnd_3967234 : Nat := 4983230072969 + 3 ^ 40 * 3967234 * 2
def baseEnd_3967234 : Nat := 679032636953078804143343

theorem tailTrace_3967234 : CollatzResearch.WordTrace tailWord_3967234 prefixEnd_3967234 679032636953078804143343 := by
  unfold tailWord_3967234
  simp only [CollatzResearch.WordTrace]
  refine ⟨36174227827349060617457189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 96464607539597494979885837 36174227827349060617457189)
  ·
    refine ⟨6782667717627948865773223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 36174227827349060617457189 6782667717627948865773223)
    ·
      refine ⟨10174001576441923298659835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6782667717627948865773223 10174001576441923298659835)
      ·
        refine ⟨15261002364662884947989753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10174001576441923298659835 15261002364662884947989753)
        ·
          refine ⟨11445751773497163710992315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15261002364662884947989753 11445751773497163710992315)
          ·
            refine ⟨17168627660245745566488473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11445751773497163710992315 17168627660245745566488473)
            ·
              refine ⟨12876470745184309174866355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17168627660245745566488473 12876470745184309174866355)
              ·
                refine ⟨19314706117776463762299533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12876470745184309174866355 19314706117776463762299533)
                ·
                  refine ⟨7243014794166173910862325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19314706117776463762299533 7243014794166173910862325)
                  ·
                    refine ⟨679032636953078804143343, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7243014794166173910862325 679032636953078804143343)
                    ·
                      rfl

theorem cell23_3967234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 1, 2, 1, 3, 5].length) (baseStart_3967234 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3967234 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3967234 prefixEnd_3967234 := by exact prefixLift 3967234
  have htrace : WordTrace (prefixWord ++ tailWord_3967234) baseStart_3967234 baseEnd_3967234 := by
    simpa [prefixWord, tailWord_3967234, baseEnd_3967234] using wordTrace_append hprefix tailTrace_3967234
  have hstable : (prefixWord ++ tailWord_3967234).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3967234).length < 2 ^ (prefixWord ++ tailWord_3967234).sum := by decide
  have hdescent : baseEnd_3967234 < baseStart_3967234 := by decide
  rcases family_descends (prefixWord ++ tailWord_3967234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3967237 : List Nat := [1, 3, 1, 1, 2, 1, 2, 1, 1, 8, 2]
def baseStart_3967237 : Nat := 118140960795 + 3967237 * 2 ^ 59
def prefixEnd_3967237 : Nat := 4983230072969 + 3 ^ 40 * 3967237 * 2
def baseEnd_3967237 : Nat := 2037099451301199900692515

theorem tailTrace_3967237 : CollatzResearch.WordTrace tailWord_3967237 prefixEnd_3967237 2037099451301199900692515 := by
  unfold tailWord_3967237
  simp only [CollatzResearch.WordTrace]
  refine ⟨144697020728385373982187965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96464680485590249321458643 144697020728385373982187965)
  ·
    refine ⟨54261382773144515243320487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 144697020728385373982187965 54261382773144515243320487)
    ·
      refine ⟨81392074159716772864980731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54261382773144515243320487 81392074159716772864980731)
      ·
        refine ⟨122088111239575159297471097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81392074159716772864980731 122088111239575159297471097)
        ·
          refine ⟨91566083429681369473103323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 122088111239575159297471097 91566083429681369473103323)
          ·
            refine ⟨137349125144522054209654985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91566083429681369473103323 137349125144522054209654985)
            ·
              refine ⟨103011843858391540657241239, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 137349125144522054209654985 103011843858391540657241239)
              ·
                refine ⟨154517765787587310985861859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 103011843858391540657241239 154517765787587310985861859)
                ·
                  refine ⟨231776648681380966478792789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 154517765787587310985861859 231776648681380966478792789)
                  ·
                    refine ⟨2716132601734933200923353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 231776648681380966478792789 2716132601734933200923353)
                    ·
                      refine ⟨2037099451301199900692515, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2716132601734933200923353 2037099451301199900692515)
                      ·
                        rfl

theorem cell23_3967237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 2, 1, 1, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 2, 1, 1, 8, 2].length) (baseStart_3967237 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3967237 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3967237 prefixEnd_3967237 := by exact prefixLift 3967237
  have htrace : WordTrace (prefixWord ++ tailWord_3967237) baseStart_3967237 baseEnd_3967237 := by
    simpa [prefixWord, tailWord_3967237, baseEnd_3967237] using wordTrace_append hprefix tailTrace_3967237
  have hstable : (prefixWord ++ tailWord_3967237).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3967237).length < 2 ^ (prefixWord ++ tailWord_3967237).sum := by decide
  have hdescent : baseEnd_3967237 < baseStart_3967237 := by decide
  rcases family_descends (prefixWord ++ tailWord_3967237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3967241 : List Nat := [1, 2, 1, 1, 3, 6, 1, 1, 2, 3, 2]
def baseStart_3967241 : Nat := 118140960795 + 3967241 * 2 ^ 59
def prefixEnd_3967241 : Nat := 4983230072969 + 3 ^ 40 * 3967241 * 2
def baseEnd_3967241 : Nat := 2037101505223817885042497

theorem tailTrace_3967241 : CollatzResearch.WordTrace tailWord_3967241 prefixEnd_3967241 2037101505223817885042497 := by
  unfold tailWord_3967241
  simp only [CollatzResearch.WordTrace]
  refine ⟨144697166620370882665333577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96464777746913921776889051 144697166620370882665333577)
  ·
    refine ⟨108522874965278161999000183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 144697166620370882665333577 108522874965278161999000183)
    ·
      refine ⟨162784312447917242998500275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108522874965278161999000183 162784312447917242998500275)
      ·
        refine ⟨244176468671875864497750413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 162784312447917242998500275 244176468671875864497750413)
        ·
          refine ⟨91566175751953449186656405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 244176468671875864497750413 91566175751953449186656405)
          ·
            refine ⟨4292164488372817930624519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 91566175751953449186656405 4292164488372817930624519)
            ·
              refine ⟨6438246732559226895936779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4292164488372817930624519 6438246732559226895936779)
              ·
                refine ⟨9657370098838840343905169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6438246732559226895936779 9657370098838840343905169)
                ·
                  refine ⟨7243027574129130257928877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9657370098838840343905169 7243027574129130257928877)
                  ·
                    refine ⟨2716135340298423846723329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7243027574129130257928877 2716135340298423846723329)
                    ·
                      refine ⟨2037101505223817885042497, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2716135340298423846723329 2037101505223817885042497)
                      ·
                        rfl

theorem cell23_3967241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 6, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 6, 1, 1, 2, 3, 2].length) (baseStart_3967241 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3967241 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3967241 prefixEnd_3967241 := by exact prefixLift 3967241
  have htrace : WordTrace (prefixWord ++ tailWord_3967241) baseStart_3967241 baseEnd_3967241 := by
    simpa [prefixWord, tailWord_3967241, baseEnd_3967241] using wordTrace_append hprefix tailTrace_3967241
  have hstable : (prefixWord ++ tailWord_3967241).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3967241).length < 2 ^ (prefixWord ++ tailWord_3967241).sum := by decide
  have hdescent : baseEnd_3967241 < baseStart_3967241 := by decide
  rcases family_descends (prefixWord ++ tailWord_3967241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3967264 : List Nat := [2, 1, 1, 5, 2, 2, 1, 1, 4, 4]
def baseStart_3967264 : Nat := 118140960795 + 3967264 * 2 ^ 59
def prefixEnd_3967264 : Nat := 4983230072969 + 3 ^ 40 * 3967264 * 2
def baseEnd_3967264 : Nat := 679037771759623765018297

theorem tailTrace_3967264 : CollatzResearch.WordTrace tailWord_3967264 prefixEnd_3967264 679037771759623765018297 := by
  unfold tailWord_3967264
  simp only [CollatzResearch.WordTrace]
  refine ⟨72349002749643778796710423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96465336999525038395613897 72349002749643778796710423)
  ·
    refine ⟨108523504124465668195065635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72349002749643778796710423 108523504124465668195065635)
    ·
      refine ⟨162785256186698502292598453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108523504124465668195065635 162785256186698502292598453)
      ·
        refine ⟨15261117767502984589931105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 162785256186698502292598453 15261117767502984589931105)
        ·
          refine ⟨11445838325627238442448329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15261117767502984589931105 11445838325627238442448329)
          ·
            refine ⟨8584378744220428831836247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11445838325627238442448329 8584378744220428831836247)
            ·
              refine ⟨12876568116330643247754371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8584378744220428831836247 12876568116330643247754371)
              ·
                refine ⟨19314852174495964871631557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12876568116330643247754371 19314852174495964871631557)
                ·
                  refine ⟨3621534782717993413430917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19314852174495964871631557 3621534782717993413430917)
                  ·
                    refine ⟨679037771759623765018297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3621534782717993413430917 679037771759623765018297)
                    ·
                      rfl

theorem cell23_3967264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 2, 1, 1, 4, 4].length) (baseStart_3967264 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3967264 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3967264 prefixEnd_3967264 := by exact prefixLift 3967264
  have htrace : WordTrace (prefixWord ++ tailWord_3967264) baseStart_3967264 baseEnd_3967264 := by
    simpa [prefixWord, tailWord_3967264, baseEnd_3967264] using wordTrace_append hprefix tailTrace_3967264
  have hstable : (prefixWord ++ tailWord_3967264).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3967264).length < 2 ^ (prefixWord ++ tailWord_3967264).sum := by decide
  have hdescent : baseEnd_3967264 < baseStart_3967264 := by decide
  rcases family_descends (prefixWord ++ tailWord_3967264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3967280 : List Nat := [2, 1, 1, 1, 2, 2, 2, 1, 1, 4, 6]
def baseStart_3967280 : Nat := 118140960795 + 3967280 * 2 ^ 59
def prefixEnd_3967280 : Nat := 4983230072969 + 3 ^ 40 * 3967280 * 2
def baseEnd_3967280 : Nat := 2037121530969343232454817

theorem tailTrace_3967280 : CollatzResearch.WordTrace tailWord_3967280 prefixEnd_3967280 2037121530969343232454817 := by
  unfold tailWord_3967280
  simp only [CollatzResearch.WordTrace]
  refine ⟨72349294533614796163001647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96465726044819728217335529 72349294533614796163001647)
  ·
    refine ⟨108523941800422194244502471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72349294533614796163001647 108523941800422194244502471)
    ·
      refine ⟨162785912700633291366753707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108523941800422194244502471 162785912700633291366753707)
      ·
        refine ⟨244178869050949937050130561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 162785912700633291366753707 244178869050949937050130561)
        ·
          refine ⟨183134151788212452787597921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 244178869050949937050130561 183134151788212452787597921)
          ·
            refine ⟨137350613841159339590698441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 183134151788212452787597921 137350613841159339590698441)
            ·
              refine ⟨103012960380869504693023831, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 137350613841159339590698441 103012960380869504693023831)
              ·
                refine ⟨154519440571304257039535747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 103012960380869504693023831 154519440571304257039535747)
                ·
                  refine ⟨231779160856956385559303621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 154519440571304257039535747 231779160856956385559303621)
                  ·
                    refine ⟨43458592660679322292369429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 231779160856956385559303621 43458592660679322292369429)
                    ·
                      refine ⟨2037121530969343232454817, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 43458592660679322292369429 2037121530969343232454817)
                      ·
                        rfl

theorem cell23_3967280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 2, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 2, 1, 1, 4, 6].length) (baseStart_3967280 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3967280 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3967280 prefixEnd_3967280 := by exact prefixLift 3967280
  have htrace : WordTrace (prefixWord ++ tailWord_3967280) baseStart_3967280 baseEnd_3967280 := by
    simpa [prefixWord, tailWord_3967280, baseEnd_3967280] using wordTrace_append hprefix tailTrace_3967280
  have hstable : (prefixWord ++ tailWord_3967280).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3967280).length < 2 ^ (prefixWord ++ tailWord_3967280).sum := by decide
  have hdescent : baseEnd_3967280 < baseStart_3967280 := by decide
  rcases family_descends (prefixWord ++ tailWord_3967280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3967281 : List Nat := [1, 2, 2, 3, 5, 1, 1, 1, 1, 6]
def baseStart_3967281 : Nat := 118140960795 + 3967281 * 2 ^ 59
def prefixEnd_3967281 : Nat := 4983230072969 + 3 ^ 40 * 3967281 * 2
def baseEnd_3967281 : Nat := 679040681483332576180771

theorem tailTrace_3967281 : CollatzResearch.WordTrace tailWord_3967281 prefixEnd_3967281 679040681483332576180771 := by
  unfold tailWord_3967281
  simp only [CollatzResearch.WordTrace]
  refine ⟨144698625540225969496789697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96465750360150646331193131 144698625540225969496789697)
  ·
    refine ⟨108523969155169477122592273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 144698625540225969496789697 108523969155169477122592273)
    ·
      refine ⟨81392976866377107841944205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 108523969155169477122592273 81392976866377107841944205)
      ·
        refine ⟨30522366324891415440729077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 81392976866377107841944205 30522366324891415440729077)
        ·
          refine ⟨2861471842958570197568351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 30522366324891415440729077 2861471842958570197568351)
          ·
            refine ⟨4292207764437855296352527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2861471842958570197568351 4292207764437855296352527)
            ·
              refine ⟨6438311646656782944528791, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4292207764437855296352527 6438311646656782944528791)
              ·
                refine ⟨9657467469985174416793187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6438311646656782944528791 9657467469985174416793187)
                ·
                  refine ⟨14486201204977761625189781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9657467469985174416793187 14486201204977761625189781)
                  ·
                    refine ⟨679040681483332576180771, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14486201204977761625189781 679040681483332576180771)
                    ·
                      rfl

theorem cell23_3967281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 5, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 5, 1, 1, 1, 1, 6].length) (baseStart_3967281 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3967281 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3967281 prefixEnd_3967281 := by exact prefixLift 3967281
  have htrace : WordTrace (prefixWord ++ tailWord_3967281) baseStart_3967281 baseEnd_3967281 := by
    simpa [prefixWord, tailWord_3967281, baseEnd_3967281] using wordTrace_append hprefix tailTrace_3967281
  have hstable : (prefixWord ++ tailWord_3967281).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3967281).length < 2 ^ (prefixWord ++ tailWord_3967281).sum := by decide
  have hdescent : baseEnd_3967281 < baseStart_3967281 := by decide
  rcases family_descends (prefixWord ++ tailWord_3967281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3967284 : List Nat := [2, 5, 1, 1, 1, 3, 1, 1, 1, 1, 6]
def baseStart_3967284 : Nat := 118140960795 + 3967284 * 2 ^ 59
def prefixEnd_3967284 : Nat := 4983230072969 + 3 ^ 40 * 3967284 * 2
def baseEnd_3967284 : Nat := 2037123584891961216804799

theorem tailTrace_3967284 : CollatzResearch.WordTrace tailWord_3967284 prefixEnd_3967284 2037123584891961216804799 := by
  unfold tailWord_3967284
  simp only [CollatzResearch.WordTrace]
  refine ⟨72349367479607550504574453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96465823306143400672765937 72349367479607550504574453)
  ·
    refine ⟨6782753201213207859803855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 72349367479607550504574453 6782753201213207859803855)
    ·
      refine ⟨10174129801819811789705783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6782753201213207859803855 10174129801819811789705783)
      ·
        refine ⟨15261194702729717684558675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10174129801819811789705783 15261194702729717684558675)
        ·
          refine ⟨22891792054094576526838013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15261194702729717684558675 22891792054094576526838013)
          ·
            refine ⟨8584422020285466197564255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22891792054094576526838013 8584422020285466197564255)
            ·
              refine ⟨12876633030428199296346383, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8584422020285466197564255 12876633030428199296346383)
              ·
                refine ⟨19314949545642298944519575, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12876633030428199296346383 19314949545642298944519575)
                ·
                  refine ⟨28972424318463448416779363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19314949545642298944519575 28972424318463448416779363)
                  ·
                    refine ⟨43458636477695172625169045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 28972424318463448416779363 43458636477695172625169045)
                    ·
                      refine ⟨2037123584891961216804799, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 43458636477695172625169045 2037123584891961216804799)
                      ·
                        rfl

theorem cell23_3967284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 3, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 3, 1, 1, 1, 1, 6].length) (baseStart_3967284 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3967284 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3967284 prefixEnd_3967284 := by exact prefixLift 3967284
  have htrace : WordTrace (prefixWord ++ tailWord_3967284) baseStart_3967284 baseEnd_3967284 := by
    simpa [prefixWord, tailWord_3967284, baseEnd_3967284] using wordTrace_append hprefix tailTrace_3967284
  have hstable : (prefixWord ++ tailWord_3967284).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3967284).length < 2 ^ (prefixWord ++ tailWord_3967284).sum := by decide
  have hdescent : baseEnd_3967284 < baseStart_3967284 := by decide
  rcases family_descends (prefixWord ++ tailWord_3967284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3967294 : List Nat := [4, 2, 1, 2, 1, 2, 4, 7]
def baseStart_3967294 : Nat := 118140960795 + 3967294 * 2 ^ 59
def prefixEnd_3967294 : Nat := 4983230072969 + 3 ^ 40 * 3967294 * 2
def baseEnd_3967294 : Nat := 75449211840685413988139

theorem tailTrace_3967294 : CollatzResearch.WordTrace tailWord_3967294 prefixEnd_3967294 75449211840685413988139 := by
  unfold tailWord_3967294
  simp only [CollatzResearch.WordTrace]
  refine ⟨18087387461147359089626617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 96466066459452581811341957 18087387461147359089626617)
  ·
    refine ⟨13565540595860519317219963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18087387461147359089626617 13565540595860519317219963)
    ·
      refine ⟨20348310893790778975829945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13565540595860519317219963 20348310893790778975829945)
      ·
        refine ⟨15261233170343084231872459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20348310893790778975829945 15261233170343084231872459)
        ·
          refine ⟨22891849755514626347808689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15261233170343084231872459 22891849755514626347808689)
          ·
            refine ⟨17168887316635969760856517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22891849755514626347808689 17168887316635969760856517)
            ·
              refine ⟨3219166371869244330160597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17168887316635969760856517 3219166371869244330160597)
              ·
                refine ⟨75449211840685413988139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3219166371869244330160597 75449211840685413988139)
                ·
                  rfl

theorem cell23_3967294_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 2, 4, 7].length) (baseStart_3967294 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3967294 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3967294 prefixEnd_3967294 := by exact prefixLift 3967294
  have htrace : WordTrace (prefixWord ++ tailWord_3967294) baseStart_3967294 baseEnd_3967294 := by
    simpa [prefixWord, tailWord_3967294, baseEnd_3967294] using wordTrace_append hprefix tailTrace_3967294
  have hstable : (prefixWord ++ tailWord_3967294).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3967294).length < 2 ^ (prefixWord ++ tailWord_3967294).sum := by decide
  have hdescent : baseEnd_3967294 < baseStart_3967294 := by decide
  rcases family_descends (prefixWord ++ tailWord_3967294) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3967304 : List Nat := [2, 1, 3, 1, 1, 2, 3, 2, 4, 1, 3]
def baseStart_3967304 : Nat := 118140960795 + 3967304 * 2 ^ 59
def prefixEnd_3967304 : Nat := 4983230072969 + 3 ^ 40 * 3967304 * 2
def baseEnd_3967304 : Nat := 2037133854505051138554707

theorem tailTrace_3967304 : CollatzResearch.WordTrace tailWord_3967304 prefixEnd_3967304 2037133854505051138554707 := by
  unfold tailWord_3967304
  simp only [CollatzResearch.WordTrace]
  refine ⟨72349732209571322212438483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96466309612761762949917977 72349732209571322212438483)
  ·
    refine ⟨108524598314356983318657725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72349732209571322212438483 108524598314356983318657725)
    ·
      refine ⟨40696724367883868744496647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 108524598314356983318657725 40696724367883868744496647)
      ·
        refine ⟨61045086551825803116744971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40696724367883868744496647 61045086551825803116744971)
        ·
          refine ⟨91567629827738704675117457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61045086551825803116744971 91567629827738704675117457)
          ·
            refine ⟨68675722370804028506338093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 91567629827738704675117457 68675722370804028506338093)
            ·
              refine ⟨25753395889051510689876785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 68675722370804028506338093 25753395889051510689876785)
              ·
                refine ⟨19315046916788633017407589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25753395889051510689876785 19315046916788633017407589)
                ·
                  refine ⟨3621571296897868690763923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19315046916788633017407589 3621571296897868690763923)
                  ·
                    refine ⟨5432356945346803036145885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3621571296897868690763923 5432356945346803036145885)
                    ·
                      refine ⟨2037133854505051138554707, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5432356945346803036145885 2037133854505051138554707)
                      ·
                        rfl

theorem cell23_3967304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 3, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 3, 2, 4, 1, 3].length) (baseStart_3967304 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3967304 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3967304 prefixEnd_3967304 := by exact prefixLift 3967304
  have htrace : WordTrace (prefixWord ++ tailWord_3967304) baseStart_3967304 baseEnd_3967304 := by
    simpa [prefixWord, tailWord_3967304, baseEnd_3967304] using wordTrace_append hprefix tailTrace_3967304
  have hstable : (prefixWord ++ tailWord_3967304).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3967304).length < 2 ^ (prefixWord ++ tailWord_3967304).sum := by decide
  have hdescent : baseEnd_3967304 < baseStart_3967304 := by decide
  rcases family_descends (prefixWord ++ tailWord_3967304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3967338 : List Nat := [3, 1, 3, 3, 1, 2, 1, 3, 2, 1, 3]
def baseStart_3967338 : Nat := 118140960795 + 3967338 * 2 ^ 59
def prefixEnd_3967338 : Nat := 4983230072969 + 3 ^ 40 * 3967338 * 2
def baseEnd_3967338 : Nat := 2037151312847304005529551

theorem tailTrace_3967338 : CollatzResearch.WordTrace tailWord_3967338 prefixEnd_3967338 2037151312847304005529551 := by
  unfold tailWord_3967338
  simp only [CollatzResearch.WordTrace]
  refine ⟨36175176125254867057903667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 96467136334012978821076445 36175176125254867057903667)
  ·
    refine ⟨54262764187882300586855501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36175176125254867057903667 54262764187882300586855501)
    ·
      refine ⟨20348536570455862720070813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 54262764187882300586855501 20348536570455862720070813)
      ·
        refine ⟨7630701213920948520026555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20348536570455862720070813 7630701213920948520026555)
        ·
          refine ⟨11446051820881422780039833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7630701213920948520026555 11446051820881422780039833)
          ·
            refine ⟨8584538865661067085029875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11446051820881422780039833 8584538865661067085029875)
            ·
              refine ⟨12876808298491600627544813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8584538865661067085029875 12876808298491600627544813)
              ·
                refine ⟨4828803111934350235329305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12876808298491600627544813 4828803111934350235329305)
                ·
                  refine ⟨3621602333950762676496979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4828803111934350235329305 3621602333950762676496979)
                  ·
                    refine ⟨5432403500926144014745469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3621602333950762676496979 5432403500926144014745469)
                    ·
                      refine ⟨2037151312847304005529551, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5432403500926144014745469 2037151312847304005529551)
                      ·
                        rfl

theorem cell23_3967338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 2, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 2, 1, 3, 2, 1, 3].length) (baseStart_3967338 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3967338 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3967338 prefixEnd_3967338 := by exact prefixLift 3967338
  have htrace : WordTrace (prefixWord ++ tailWord_3967338) baseStart_3967338 baseEnd_3967338 := by
    simpa [prefixWord, tailWord_3967338, baseEnd_3967338] using wordTrace_append hprefix tailTrace_3967338
  have hstable : (prefixWord ++ tailWord_3967338).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3967338).length < 2 ^ (prefixWord ++ tailWord_3967338).sum := by decide
  have hdescent : baseEnd_3967338 < baseStart_3967338 := by decide
  rcases family_descends (prefixWord ++ tailWord_3967338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3967347 : List Nat := [1, 1, 1, 2, 2, 1, 2, 4, 2, 4, 3]
def baseStart_3967347 : Nat := 118140960795 + 3967347 * 2 ^ 59
def prefixEnd_3967347 : Nat := 4983230072969 + 3 ^ 40 * 3967347 * 2
def baseEnd_3967347 : Nat := 2037155934173194470317009

theorem tailTrace_3967347 : CollatzResearch.WordTrace tailWord_3967347 prefixEnd_3967347 2037155934173194470317009 := by
  unfold tailWord_3967347
  simp only [CollatzResearch.WordTrace]
  refine ⟨144701032757986862768692295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96467355171991241845794863 144701032757986862768692295)
  ·
    refine ⟨217051549136980294153038443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144701032757986862768692295 217051549136980294153038443)
    ·
      refine ⟨325577323705470441229557665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 217051549136980294153038443 325577323705470441229557665)
      ·
        refine ⟨244182992779102830922168249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 325577323705470441229557665 244182992779102830922168249)
        ·
          refine ⟨183137244584327123191626187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 244182992779102830922168249 183137244584327123191626187)
          ·
            refine ⟨274705866876490684787439281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 183137244584327123191626187 274705866876490684787439281)
            ·
              refine ⟨206029400157368013590579461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 274705866876490684787439281 206029400157368013590579461)
              ·
                refine ⟨38630512529506502548233649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 206029400157368013590579461 38630512529506502548233649)
                ·
                  refine ⟨28972884397129876911175237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38630512529506502548233649 28972884397129876911175237)
                  ·
                    refine ⟨5432415824461851920845357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28972884397129876911175237 5432415824461851920845357)
                    ·
                      refine ⟨2037155934173194470317009, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5432415824461851920845357 2037155934173194470317009)
                      ·
                        rfl

theorem cell23_3967347_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 2, 4, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 2, 4, 2, 4, 3].length) (baseStart_3967347 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3967347 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3967347 prefixEnd_3967347 := by exact prefixLift 3967347
  have htrace : WordTrace (prefixWord ++ tailWord_3967347) baseStart_3967347 baseEnd_3967347 := by
    simpa [prefixWord, tailWord_3967347, baseEnd_3967347] using wordTrace_append hprefix tailTrace_3967347
  have hstable : (prefixWord ++ tailWord_3967347).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3967347).length < 2 ^ (prefixWord ++ tailWord_3967347).sum := by decide
  have hdescent : baseEnd_3967347 < baseStart_3967347 := by decide
  rcases family_descends (prefixWord ++ tailWord_3967347) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3967361 : List Nat := [1, 2, 4, 3, 1, 1, 1, 1, 3, 4, 2]
def baseStart_3967361 : Nat := 118140960795 + 3967361 * 2 ^ 59
def prefixEnd_3967361 : Nat := 4983230072969 + 3 ^ 40 * 3967361 * 2
def baseEnd_3967361 : Nat := 2037163122902357415541945

theorem tailTrace_3967361 : CollatzResearch.WordTrace tailWord_3967361 prefixEnd_3967361 2037163122902357415541945 := by
  unfold tailWord_3967361
  simp only [CollatzResearch.WordTrace]
  refine ⟨144701543379936143159701937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96467695586624095439801291 144701543379936143159701937)
  ·
    refine ⟨108526157534952107369776453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 144701543379936143159701937 108526157534952107369776453)
    ·
      refine ⟨20348654537803520131833085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 108526157534952107369776453 20348654537803520131833085)
      ·
        refine ⟨7630745451676320049437407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20348654537803520131833085 7630745451676320049437407)
        ·
          refine ⟨11446118177514480074156111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7630745451676320049437407 11446118177514480074156111)
          ·
            refine ⟨17169177266271720111234167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11446118177514480074156111 17169177266271720111234167)
            ·
              refine ⟨25753765899407580166851251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17169177266271720111234167 25753765899407580166851251)
              ·
                refine ⟨38630648849111370250276877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25753765899407580166851251 38630648849111370250276877)
                ·
                  refine ⟨14486493318416763843853829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38630648849111370250276877 14486493318416763843853829)
                  ·
                    refine ⟨2716217497203143220722593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 14486493318416763843853829 2716217497203143220722593)
                    ·
                      refine ⟨2037163122902357415541945, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2716217497203143220722593 2037163122902357415541945)
                      ·
                        rfl

theorem cell23_3967361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 1, 1, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 1, 1, 1, 3, 4, 2].length) (baseStart_3967361 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3967361 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3967361 prefixEnd_3967361 := by exact prefixLift 3967361
  have htrace : WordTrace (prefixWord ++ tailWord_3967361) baseStart_3967361 baseEnd_3967361 := by
    simpa [prefixWord, tailWord_3967361, baseEnd_3967361] using wordTrace_append hprefix tailTrace_3967361
  have hstable : (prefixWord ++ tailWord_3967361).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3967361).length < 2 ^ (prefixWord ++ tailWord_3967361).sum := by decide
  have hdescent : baseEnd_3967361 < baseStart_3967361 := by decide
  rcases family_descends (prefixWord ++ tailWord_3967361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3967397 : List Nat := [1, 3, 1, 2, 1, 1, 4, 2, 1, 7]
def baseStart_3967397 : Nat := 118140960795 + 3967397 * 2 ^ 59
def prefixEnd_3967397 : Nat := 4983230072969 + 3 ^ 40 * 3967397 * 2
def baseEnd_3967397 : Nat := 679060536068639758230593

theorem tailTrace_3967397 : CollatzResearch.WordTrace tailWord_3967397 prefixEnd_3967397 679060536068639758230593 := by
  unfold tailWord_3967397
  simp only [CollatzResearch.WordTrace]
  refine ⟨144702856407805721308012445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96468570938537147538674963 144702856407805721308012445)
  ·
    refine ⟨54263571152927145490504667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 144702856407805721308012445 54263571152927145490504667)
    ·
      refine ⟨81395356729390718235757001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54263571152927145490504667 81395356729390718235757001)
      ·
        refine ⟨61046517547043038676817751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81395356729390718235757001 61046517547043038676817751)
        ·
          refine ⟨91569776320564558015226627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61046517547043038676817751 91569776320564558015226627)
          ·
            refine ⟨137354664480846837022839941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91569776320564558015226627 137354664480846837022839941)
            ·
              refine ⟨25753999590158781941782489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 137354664480846837022839941 25753999590158781941782489)
              ·
                refine ⟨19315499692619086456336867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25753999590158781941782489 19315499692619086456336867)
                ·
                  refine ⟨28973249538928629684505301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19315499692619086456336867 28973249538928629684505301)
                  ·
                    refine ⟨679060536068639758230593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 28973249538928629684505301 679060536068639758230593)
                    ·
                      rfl

theorem cell23_3967397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 4, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 4, 2, 1, 7].length) (baseStart_3967397 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3967397 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3967397 prefixEnd_3967397 := by exact prefixLift 3967397
  have htrace : WordTrace (prefixWord ++ tailWord_3967397) baseStart_3967397 baseEnd_3967397 := by
    simpa [prefixWord, tailWord_3967397, baseEnd_3967397] using wordTrace_append hprefix tailTrace_3967397
  have hstable : (prefixWord ++ tailWord_3967397).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3967397).length < 2 ^ (prefixWord ++ tailWord_3967397).sum := by decide
  have hdescent : baseEnd_3967397 < baseStart_3967397 := by decide
  rcases family_descends (prefixWord ++ tailWord_3967397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3967404 : List Nat := [2, 2, 1, 1, 1, 1, 3, 1, 4, 5, 2]
def baseStart_3967404 : Nat := 118140960795 + 3967404 * 2 ^ 59
def prefixEnd_3967404 : Nat := 4983230072969 + 3 ^ 40 * 3967404 * 2
def baseEnd_3967404 : Nat := 2037185202570500747304247

theorem tailTrace_3967404 : CollatzResearch.WordTrace tailWord_3967404 prefixEnd_3967404 2037185202570500747304247 := by
  unfold tailWord_3967404
  simp only [CollatzResearch.WordTrace]
  refine ⟨72351555859390180751758633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96468741145853574335678177 72351555859390180751758633)
  ·
    refine ⟨54263666894542635563818975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72351555859390180751758633 54263666894542635563818975)
    ·
      refine ⟨81395500341813953345728463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54263666894542635563818975 81395500341813953345728463)
      ·
        refine ⟨122093250512720930018592695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81395500341813953345728463 122093250512720930018592695)
        ·
          refine ⟨183139875769081395027889043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 122093250512720930018592695 183139875769081395027889043)
          ·
            refine ⟨274709813653622092541833565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 183139875769081395027889043 274709813653622092541833565)
            ·
              refine ⟨103016180120108284703187587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 274709813653622092541833565 103016180120108284703187587)
              ·
                refine ⟨154524270180162427054781381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 103016180120108284703187587 154524270180162427054781381)
                ·
                  refine ⟨28973300658780455072771509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 154524270180162427054781381 28973300658780455072771509)
                  ·
                    refine ⟨2716246936760667663072329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 28973300658780455072771509 2716246936760667663072329)
                    ·
                      refine ⟨2037185202570500747304247, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2716246936760667663072329 2037185202570500747304247)
                      ·
                        rfl

theorem cell23_3967404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 5, 2].length) (baseStart_3967404 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3967404 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3967404 prefixEnd_3967404 := by exact prefixLift 3967404
  have htrace : WordTrace (prefixWord ++ tailWord_3967404) baseStart_3967404 baseEnd_3967404 := by
    simpa [prefixWord, tailWord_3967404, baseEnd_3967404] using wordTrace_append hprefix tailTrace_3967404
  have hstable : (prefixWord ++ tailWord_3967404).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3967404).length < 2 ^ (prefixWord ++ tailWord_3967404).sum := by decide
  have hdescent : baseEnd_3967404 < baseStart_3967404 := by decide
  rcases family_descends (prefixWord ++ tailWord_3967404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3967434 : List Nat := [3, 1, 2, 1, 2, 2, 2, 1, 4, 1, 4]
def baseStart_3967434 : Nat := 118140960795 + 3967434 * 2 ^ 59
def prefixEnd_3967434 : Nat := 4983230072969 + 3 ^ 40 * 3967434 * 2
def baseEnd_3967434 : Nat := 2037200606990135629929109

theorem tailTrace_3967434 : CollatzResearch.WordTrace tailWord_3967434 prefixEnd_3967434 2037200606990135629929109 := by
  unfold tailWord_3967434
  simp only [CollatzResearch.WordTrace]
  refine ⟨36176051477167919156777339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 96469470605781117751406237 36176051477167919156777339)
  ·
    refine ⟨54264077215751878735166009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36176051477167919156777339 54264077215751878735166009)
    ·
      refine ⟨40698057911813909051374507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54264077215751878735166009 40698057911813909051374507)
      ·
        refine ⟨61047086867720863577061761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40698057911813909051374507 61047086867720863577061761)
        ·
          refine ⟨45785315150790647682796321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61047086867720863577061761 45785315150790647682796321)
          ·
            refine ⟨34338986363092985762097241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45785315150790647682796321 34338986363092985762097241)
            ·
              refine ⟨25754239772319739321572931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34338986363092985762097241 25754239772319739321572931)
              ·
                refine ⟨38631359658479608982359397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25754239772319739321572931 38631359658479608982359397)
                ·
                  refine ⟨7243379935964926684192387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 38631359658479608982359397 7243379935964926684192387)
                  ·
                    refine ⟨10865069903947390026288581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7243379935964926684192387 10865069903947390026288581)
                    ·
                      refine ⟨2037200606990135629929109, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10865069903947390026288581 2037200606990135629929109)
                      ·
                        rfl

theorem cell23_3967434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 2, 1, 4, 1, 4].length) (baseStart_3967434 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3967434 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3967434 prefixEnd_3967434 := by exact prefixLift 3967434
  have htrace : WordTrace (prefixWord ++ tailWord_3967434) baseStart_3967434 baseEnd_3967434 := by
    simpa [prefixWord, tailWord_3967434, baseEnd_3967434] using wordTrace_append hprefix tailTrace_3967434
  have hstable : (prefixWord ++ tailWord_3967434).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3967434).length < 2 ^ (prefixWord ++ tailWord_3967434).sum := by decide
  have hdescent : baseEnd_3967434 < baseStart_3967434 := by decide
  rcases family_descends (prefixWord ++ tailWord_3967434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3967495 : List Nat := [1, 1, 4, 3, 4, 1, 1, 1, 3, 4]
def baseStart_3967495 : Nat := 118140960795 + 3967495 * 2 ^ 59
def prefixEnd_3967495 : Nat := 4983230072969 + 3 ^ 40 * 3967495 * 2
def baseEnd_3967495 : Nat := 679077309770019963755443

theorem tailTrace_3967495 : CollatzResearch.WordTrace tailWord_3967495 prefixEnd_3967495 679077309770019963755443 := by
  unfold tailWord_3967495
  simp only [CollatzResearch.WordTrace]
  refine ⟨144706430761450684045079939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96470953840967122696719959 144706430761450684045079939)
  ·
    refine ⟨217059646142176026067619909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144706430761450684045079939 217059646142176026067619909)
    ·
      refine ⟨40698683651658004887678733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 217059646142176026067619909 40698683651658004887678733)
      ·
        refine ⟨15262006369371751832879525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40698683651658004887678733 15262006369371751832879525)
        ·
          refine ⟨2861626194257203468664911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15262006369371751832879525 2861626194257203468664911)
          ·
            refine ⟨4292439291385805202997367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2861626194257203468664911 4292439291385805202997367)
            ·
              refine ⟨6438658937078707804496051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4292439291385805202997367 6438658937078707804496051)
              ·
                refine ⟨9657988405618061706744077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6438658937078707804496051 9657988405618061706744077)
                ·
                  refine ⟨3621745652106773140029029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9657988405618061706744077 3621745652106773140029029)
                  ·
                    refine ⟨679077309770019963755443, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3621745652106773140029029 679077309770019963755443)
                    ·
                      rfl

theorem cell23_3967495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 4, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 4, 1, 1, 1, 3, 4].length) (baseStart_3967495 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3967495 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3967495 prefixEnd_3967495 := by exact prefixLift 3967495
  have htrace : WordTrace (prefixWord ++ tailWord_3967495) baseStart_3967495 baseEnd_3967495 := by
    simpa [prefixWord, tailWord_3967495, baseEnd_3967495] using wordTrace_append hprefix tailTrace_3967495
  have hstable : (prefixWord ++ tailWord_3967495).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3967495).length < 2 ^ (prefixWord ++ tailWord_3967495).sum := by decide
  have hdescent : baseEnd_3967495 < baseStart_3967495 := by decide
  rcases family_descends (prefixWord ++ tailWord_3967495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3967508 : List Nat := [2, 4, 3, 1, 1, 2, 1, 3, 6]
def baseStart_3967508 : Nat := 118140960795 + 3967508 * 2 ^ 59
def prefixEnd_3967508 : Nat := 4983230072969 + 3 ^ 40 * 3967508 * 2
def baseEnd_3967508 : Nat := 226359844950952037822641

theorem tailTrace_3967508 : CollatzResearch.WordTrace tailWord_3967508 prefixEnd_3967508 226359844950952037822641 := by
  unfold tailWord_3967508
  simp only [CollatzResearch.WordTrace]
  refine ⟨72353452455201793632651589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96471269940269058176868785 72353452455201793632651589)
  ·
    refine ⟨13566272335350336306122173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 72353452455201793632651589 13566272335350336306122173)
    ·
      refine ⟨5087352125756376114795815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13566272335350336306122173 5087352125756376114795815)
      ·
        refine ⟨7631028188634564172193723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5087352125756376114795815 7631028188634564172193723)
        ·
          refine ⟨11446542282951846258290585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7631028188634564172193723 11446542282951846258290585)
          ·
            refine ⟨8584906712213884693717939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11446542282951846258290585 8584906712213884693717939)
            ·
              refine ⟨12877360068320827040576909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8584906712213884693717939 12877360068320827040576909)
              ·
                refine ⟨4829010025620310140216341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12877360068320827040576909 4829010025620310140216341)
                ·
                  refine ⟨226359844950952037822641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4829010025620310140216341 226359844950952037822641)
                  ·
                    rfl

theorem cell23_3967508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 2, 1, 3, 6].length) (baseStart_3967508 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3967508 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3967508 prefixEnd_3967508 := by exact prefixLift 3967508
  have htrace : WordTrace (prefixWord ++ tailWord_3967508) baseStart_3967508 baseEnd_3967508 := by
    simpa [prefixWord, tailWord_3967508, baseEnd_3967508] using wordTrace_append hprefix tailTrace_3967508
  have hstable : (prefixWord ++ tailWord_3967508).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3967508).length < 2 ^ (prefixWord ++ tailWord_3967508).sum := by decide
  have hdescent : baseEnd_3967508 < baseStart_3967508 := by decide
  rcases family_descends (prefixWord ++ tailWord_3967508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3967592 : List Nat := [2, 1, 4, 3, 2, 2, 2, 1, 1, 1, 4]
def baseStart_3967592 : Nat := 118140960795 + 3967592 * 2 ^ 59
def prefixEnd_3967592 : Nat := 4983230072969 + 3 ^ 40 * 3967592 * 2
def baseEnd_3967592 : Nat := 2037281736933546011753383

theorem tailTrace_3967592 : CollatzResearch.WordTrace tailWord_3967592 prefixEnd_3967592 2037281736933546011753383 := by
  unfold tailWord_3967592
  simp only [CollatzResearch.WordTrace]
  refine ⟨72354984321049634805680515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96473312428066179740907353 72354984321049634805680515)
  ·
    refine ⟨108532476481574452208520773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72354984321049634805680515 108532476481574452208520773)
    ·
      refine ⟨20349839340295209789097645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 108532476481574452208520773 20349839340295209789097645)
      ·
        refine ⟨7631189752610703670911617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20349839340295209789097645 7631189752610703670911617)
        ·
          refine ⟨5723392314458027753183713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7631189752610703670911617 5723392314458027753183713)
          ·
            refine ⟨4292544235843520814887785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5723392314458027753183713 4292544235843520814887785)
            ·
              refine ⟨3219408176882640611165839, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4292544235843520814887785 3219408176882640611165839)
              ·
                refine ⟨4829112265323960916748759, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3219408176882640611165839 4829112265323960916748759)
                ·
                  refine ⟨7243668397985941375123139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4829112265323960916748759 7243668397985941375123139)
                  ·
                    refine ⟨10865502596978912062684709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7243668397985941375123139 10865502596978912062684709)
                    ·
                      refine ⟨2037281736933546011753383, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10865502596978912062684709 2037281736933546011753383)
                      ·
                        rfl

theorem cell23_3967592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 2, 2, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 2, 2, 2, 1, 1, 1, 4].length) (baseStart_3967592 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3967592 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3967592 prefixEnd_3967592 := by exact prefixLift 3967592
  have htrace : WordTrace (prefixWord ++ tailWord_3967592) baseStart_3967592 baseEnd_3967592 := by
    simpa [prefixWord, tailWord_3967592, baseEnd_3967592] using wordTrace_append hprefix tailTrace_3967592
  have hstable : (prefixWord ++ tailWord_3967592).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3967592).length < 2 ^ (prefixWord ++ tailWord_3967592).sum := by decide
  have hdescent : baseEnd_3967592 < baseStart_3967592 := by decide
  rcases family_descends (prefixWord ++ tailWord_3967592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3967602 : List Nat := [3, 2, 1, 2, 5, 1, 1, 2, 2, 4]
def baseStart_3967602 : Nat := 118140960795 + 3967602 * 2 ^ 59
def prefixEnd_3967602 : Nat := 4983230072969 + 3 ^ 40 * 3967602 * 2
def baseEnd_3967602 : Nat := 679095623913363657542779

theorem tailTrace_3967602 : CollatzResearch.WordTrace tailWord_3967602 prefixEnd_3967602 679095623913363657542779 := by
  unfold tailWord_3967602
  simp only [CollatzResearch.WordTrace]
  refine ⟨36177583343015760329806265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 96473555581375360879483373 36177583343015760329806265)
  ·
    refine ⟨27133187507261820247354699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36177583343015760329806265 27133187507261820247354699)
    ·
      refine ⟨40699781260892730371032049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27133187507261820247354699 40699781260892730371032049)
      ·
        refine ⟨30524835945669547778274037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40699781260892730371032049 30524835945669547778274037)
        ·
          refine ⟨2861703369906520104213191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 30524835945669547778274037 2861703369906520104213191)
          ·
            refine ⟨4292555054859780156319787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2861703369906520104213191 4292555054859780156319787)
            ·
              refine ⟨6438832582289670234479681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4292555054859780156319787 6438832582289670234479681)
              ·
                refine ⟨4829124436717252675859761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6438832582289670234479681 4829124436717252675859761)
                ·
                  refine ⟨3621843327537939506894821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4829124436717252675859761 3621843327537939506894821)
                  ·
                    refine ⟨679095623913363657542779, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3621843327537939506894821 679095623913363657542779)
                    ·
                      rfl

theorem cell23_3967602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 5, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 5, 1, 1, 2, 2, 4].length) (baseStart_3967602 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3967602 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3967602 prefixEnd_3967602 := by exact prefixLift 3967602
  have htrace : WordTrace (prefixWord ++ tailWord_3967602) baseStart_3967602 baseEnd_3967602 := by
    simpa [prefixWord, tailWord_3967602, baseEnd_3967602] using wordTrace_append hprefix tailTrace_3967602
  have hstable : (prefixWord ++ tailWord_3967602).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3967602).length < 2 ^ (prefixWord ++ tailWord_3967602).sum := by decide
  have hdescent : baseEnd_3967602 < baseStart_3967602 := by decide
  rcases family_descends (prefixWord ++ tailWord_3967602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3967664 : List Nat := [2, 1, 1, 1, 2, 1, 3, 1, 1, 1, 9]
def baseStart_3967664 : Nat := 118140960795 + 3967664 * 2 ^ 59
def prefixEnd_3967664 : Nat := 4983230072969 + 3 ^ 40 * 3967664 * 2
def baseEnd_3967664 : Nat := 2037318707540669730053051

theorem tailTrace_3967664 : CollatzResearch.WordTrace tailWord_3967664 prefixEnd_3967664 2037318707540669730053051 := by
  unfold tailWord_3967664
  simp only [CollatzResearch.WordTrace]
  refine ⟨72356297348919212953991023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96475063131892283938654697 72356297348919212953991023)
  ·
    refine ⟨108534446023378819430986535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72356297348919212953991023 108534446023378819430986535)
    ·
      refine ⟨162801669035068229146479803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108534446023378819430986535 162801669035068229146479803)
      ·
        refine ⟨244202503552602343719719705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 162801669035068229146479803 244202503552602343719719705)
        ·
          refine ⟨183151877664451757789789779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 244202503552602343719719705 183151877664451757789789779)
          ·
            refine ⟨274727816496677636684684669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 183151877664451757789789779 274727816496677636684684669)
            ·
              refine ⟨103022931186254113756756751, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 274727816496677636684684669 103022931186254113756756751)
              ·
                refine ⟨154534396779381170635135127, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 103022931186254113756756751 154534396779381170635135127)
                ·
                  refine ⟨231801595169071755952702691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 154534396779381170635135127 231801595169071755952702691)
                  ·
                    refine ⟨347702392753607633929054037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 231801595169071755952702691 347702392753607633929054037)
                    ·
                      refine ⟨2037318707540669730053051, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 347702392753607633929054037 2037318707540669730053051)
                      ·
                        rfl

theorem cell23_3967664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 3, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 3, 1, 1, 1, 9].length) (baseStart_3967664 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3967664 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3967664 prefixEnd_3967664 := by exact prefixLift 3967664
  have htrace : WordTrace (prefixWord ++ tailWord_3967664) baseStart_3967664 baseEnd_3967664 := by
    simpa [prefixWord, tailWord_3967664, baseEnd_3967664] using wordTrace_append hprefix tailTrace_3967664
  have hstable : (prefixWord ++ tailWord_3967664).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3967664).length < 2 ^ (prefixWord ++ tailWord_3967664).sum := by decide
  have hdescent : baseEnd_3967664 < baseStart_3967664 := by decide
  rcases family_descends (prefixWord ++ tailWord_3967664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3967711 : List Nat := [1, 1, 2, 3, 2, 3, 1, 2, 1, 2, 5]
def baseStart_3967711 : Nat := 118140960795 + 3967711 * 2 ^ 59
def prefixEnd_3967711 : Nat := 4983230072969 + 3 ^ 40 * 3967711 * 2
def baseEnd_3967711 : Nat := 2037342841131431046165335

theorem tailTrace_3967711 : CollatzResearch.WordTrace tailWord_3967711 prefixEnd_3967711 2037342841131431046165335 := by
  unfold tailWord_3967711
  simp only [CollatzResearch.WordTrace]
  refine ⟨144714308928668152934942987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96476205952445435289961991 144714308928668152934942987)
  ·
    refine ⟨217071463393002229402414481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144714308928668152934942987 217071463393002229402414481)
    ·
      refine ⟨162803597544751672051810861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 217071463393002229402414481 162803597544751672051810861)
      ·
        refine ⟨61051349079281877019429073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 162803597544751672051810861 61051349079281877019429073)
        ·
          refine ⟨45788511809461407764571805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61051349079281877019429073 45788511809461407764571805)
          ·
            refine ⟨17170691928548027911714427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45788511809461407764571805 17170691928548027911714427)
            ·
              refine ⟨25756037892822041867571641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17170691928548027911714427 25756037892822041867571641)
              ·
                refine ⟨19317028419616531400678731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25756037892822041867571641 19317028419616531400678731)
                ·
                  refine ⟨28975542629424797101018097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19317028419616531400678731 28975542629424797101018097)
                  ·
                    refine ⟨21731656972068597825763573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 28975542629424797101018097 21731656972068597825763573)
                    ·
                      refine ⟨2037342841131431046165335, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 21731656972068597825763573 2037342841131431046165335)
                      ·
                        rfl

theorem cell23_3967711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 3, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 3, 1, 2, 1, 2, 5].length) (baseStart_3967711 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3967711 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3967711 prefixEnd_3967711 := by exact prefixLift 3967711
  have htrace : WordTrace (prefixWord ++ tailWord_3967711) baseStart_3967711 baseEnd_3967711 := by
    simpa [prefixWord, tailWord_3967711, baseEnd_3967711] using wordTrace_append hprefix tailTrace_3967711
  have hstable : (prefixWord ++ tailWord_3967711).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3967711).length < 2 ^ (prefixWord ++ tailWord_3967711).sum := by decide
  have hdescent : baseEnd_3967711 < baseStart_3967711 := by decide
  rcases family_descends (prefixWord ++ tailWord_3967711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3967738 : List Nat := [3, 1, 1, 1, 1, 3, 3, 1, 1, 6, 2]
def baseStart_3967738 : Nat := 118140960795 + 3967738 * 2 ^ 59
def prefixEnd_3967738 : Nat := 4983230072969 + 3 ^ 40 * 3967738 * 2
def baseEnd_3967738 : Nat := 2037356705109102440527711

theorem tailTrace_3967738 : CollatzResearch.WordTrace tailWord_3967738 prefixEnd_3967738 2037356705109102440527711 := by
  unfold tailWord_3967738
  simp only [CollatzResearch.WordTrace]
  refine ⟨36178823424892584136543967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 96476862466380224364117245 36178823424892584136543967)
  ·
    refine ⟨54268235137338876204815951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36178823424892584136543967 54268235137338876204815951)
    ·
      refine ⟨81402352706008314307223927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54268235137338876204815951 81402352706008314307223927)
      ·
        refine ⟨122103529059012471460835891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81402352706008314307223927 122103529059012471460835891)
        ·
          refine ⟨183155293588518707191253837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 122103529059012471460835891 183155293588518707191253837)
          ·
            refine ⟨68683235095694515196720189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 183155293588518707191253837 68683235095694515196720189)
            ·
              refine ⟨25756213160885443198770071, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 68683235095694515196720189 25756213160885443198770071)
              ·
                refine ⟨38634319741328164798155107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25756213160885443198770071 38634319741328164798155107)
                ·
                  refine ⟨57951479611992247197232661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38634319741328164798155107 57951479611992247197232661)
                  ·
                    refine ⟨2716475606812136587370281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 57951479611992247197232661 2716475606812136587370281)
                    ·
                      refine ⟨2037356705109102440527711, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2716475606812136587370281 2037356705109102440527711)
                      ·
                        rfl

theorem cell23_3967738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 3, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 3, 1, 1, 6, 2].length) (baseStart_3967738 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3967738 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3967738 prefixEnd_3967738 := by exact prefixLift 3967738
  have htrace : WordTrace (prefixWord ++ tailWord_3967738) baseStart_3967738 baseEnd_3967738 := by
    simpa [prefixWord, tailWord_3967738, baseEnd_3967738] using wordTrace_append hprefix tailTrace_3967738
  have hstable : (prefixWord ++ tailWord_3967738).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3967738).length < 2 ^ (prefixWord ++ tailWord_3967738).sum := by decide
  have hdescent : baseEnd_3967738 < baseStart_3967738 := by decide
  rcases family_descends (prefixWord ++ tailWord_3967738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3967778 : List Nat := [3, 3, 1, 1, 2, 3, 1, 1, 8]
def baseStart_3967778 : Nat := 118140960795 + 3967778 * 2 ^ 59
def prefixEnd_3967778 : Nat := 4983230072969 + 3 ^ 40 * 3967778 * 2
def baseEnd_3967778 : Nat := 226375249370586920447503

theorem tailTrace_3967778 : CollatzResearch.WordTrace tailWord_3967778 prefixEnd_3967778 226375249370586920447503 := by
  unfold tailWord_3967778
  simp only [CollatzResearch.WordTrace]
  refine ⟨36179188154856355844407997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 96477835079616948918421325 36179188154856355844407997)
  ·
    refine ⟨13567195558071133441652999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36179188154856355844407997 13567195558071133441652999)
    ·
      refine ⟨20350793337106700162479499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13567195558071133441652999 20350793337106700162479499)
      ·
        refine ⟨30526190005660050243719249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20350793337106700162479499 30526190005660050243719249)
        ·
          refine ⟨22894642504245037682789437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30526190005660050243719249 22894642504245037682789437)
          ·
            refine ⟨8585490939091889131046039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22894642504245037682789437 8585490939091889131046039)
            ·
              refine ⟨12878236408637833696569059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8585490939091889131046039 12878236408637833696569059)
              ·
                refine ⟨19317354612956750544853589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12878236408637833696569059 19317354612956750544853589)
                ·
                  refine ⟨226375249370586920447503, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 19317354612956750544853589 226375249370586920447503)
                  ·
                    rfl

theorem cell23_3967778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 3, 1, 1, 8].length) (baseStart_3967778 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3967778 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3967778 prefixEnd_3967778 := by exact prefixLift 3967778
  have htrace : WordTrace (prefixWord ++ tailWord_3967778) baseStart_3967778 baseEnd_3967778 := by
    simpa [prefixWord, tailWord_3967778, baseEnd_3967778] using wordTrace_append hprefix tailTrace_3967778
  have hstable : (prefixWord ++ tailWord_3967778).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3967778).length < 2 ^ (prefixWord ++ tailWord_3967778).sum := by decide
  have hdescent : baseEnd_3967778 < baseStart_3967778 := by decide
  rcases family_descends (prefixWord ++ tailWord_3967778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3967781 : List Nat := [1, 3, 1, 2, 3, 1, 1, 1, 1, 1, 8]
def baseStart_3967781 : Nat := 118140960795 + 3967781 * 2 ^ 59
def prefixEnd_3967781 : Nat := 4983230072969 + 3 ^ 40 * 3967781 * 2
def baseEnd_3967781 : Nat := 2037378784777245772290013

theorem tailTrace_3967781 : CollatzResearch.WordTrace tailWord_3967781 prefixEnd_3967781 2037378784777245772290013 := by
  unfold tailWord_3967781
  simp only [CollatzResearch.WordTrace]
  refine ⟨144716862038414554889991197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96477908025609703259994131 144716862038414554889991197)
  ·
    refine ⟨54268823264405458083746699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 144716862038414554889991197 54268823264405458083746699)
    ·
      refine ⟨81403234896608187125620049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54268823264405458083746699 81403234896608187125620049)
      ·
        refine ⟨61052426172456140344215037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81403234896608187125620049 61052426172456140344215037)
        ·
          refine ⟨22894659814671052629080639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 61052426172456140344215037 22894659814671052629080639)
          ·
            refine ⟨34341989722006578943620959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22894659814671052629080639 34341989722006578943620959)
            ·
              refine ⟨51512984583009868415431439, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34341989722006578943620959 51512984583009868415431439)
              ·
                refine ⟨77269476874514802623147159, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51512984583009868415431439 77269476874514802623147159)
                ·
                  refine ⟨115904215311772203934720739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 77269476874514802623147159 115904215311772203934720739)
                  ·
                    refine ⟨173856322967658305902081109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 115904215311772203934720739 173856322967658305902081109)
                    ·
                      refine ⟨2037378784777245772290013, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 173856322967658305902081109 2037378784777245772290013)
                      ·
                        rfl

theorem cell23_3967781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 1, 1, 1, 1, 8].length) (baseStart_3967781 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3967781 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3967781 prefixEnd_3967781 := by exact prefixLift 3967781
  have htrace : WordTrace (prefixWord ++ tailWord_3967781) baseStart_3967781 baseEnd_3967781 := by
    simpa [prefixWord, tailWord_3967781, baseEnd_3967781] using wordTrace_append hprefix tailTrace_3967781
  have hstable : (prefixWord ++ tailWord_3967781).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3967781).length < 2 ^ (prefixWord ++ tailWord_3967781).sum := by decide
  have hdescent : baseEnd_3967781 < baseStart_3967781 := by decide
  rcases family_descends (prefixWord ++ tailWord_3967781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3967795 : List Nat := [1, 1, 1, 2, 6, 2, 3, 1, 6]
def baseStart_3967795 : Nat := 118140960795 + 3967795 * 2 ^ 59
def prefixEnd_3967795 : Nat := 4983230072969 + 3 ^ 40 * 3967795 * 2
def baseEnd_3967795 : Nat := 226376219278489857501661

theorem tailTrace_3967795 : CollatzResearch.WordTrace tailWord_3967795 prefixEnd_3967795 226376219278489857501661 := by
  unfold tailWord_3967795
  simp only [CollatzResearch.WordTrace]
  refine ⟨144717372660363835281000839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96478248440242556854000559 144717372660363835281000839)
  ·
    refine ⟨217076058990545752921501259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144717372660363835281000839 217076058990545752921501259)
    ·
      refine ⟨325614088485818629382251889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 217076058990545752921501259 325614088485818629382251889)
      ·
        refine ⟨244210566364363972036688917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 325614088485818629382251889 244210566364363972036688917)
        ·
          refine ⟨11447370298329561189219793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 244210566364363972036688917 11447370298329561189219793)
          ·
            refine ⟨8585527723747170891914845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11447370298329561189219793 8585527723747170891914845)
            ·
              refine ⟨3219572896405189084468067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8585527723747170891914845 3219572896405189084468067)
              ·
                refine ⟨4829359344607783626702101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3219572896405189084468067 4829359344607783626702101)
                ·
                  refine ⟨226376219278489857501661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4829359344607783626702101 226376219278489857501661)
                  ·
                    rfl

theorem cell23_3967795_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 2, 3, 1, 6].length) (baseStart_3967795 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3967795 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3967795 prefixEnd_3967795 := by exact prefixLift 3967795
  have htrace : WordTrace (prefixWord ++ tailWord_3967795) baseStart_3967795 baseEnd_3967795 := by
    simpa [prefixWord, tailWord_3967795, baseEnd_3967795] using wordTrace_append hprefix tailTrace_3967795
  have hstable : (prefixWord ++ tailWord_3967795).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3967795).length < 2 ^ (prefixWord ++ tailWord_3967795).sum := by decide
  have hdescent : baseEnd_3967795 < baseStart_3967795 := by decide
  rcases family_descends (prefixWord ++ tailWord_3967795) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3967815 : List Nat := [1, 1, 4, 1, 2, 1, 1, 5, 2, 3, 2]
def baseStart_3967815 : Nat := 118140960795 + 3967815 * 2 ^ 59
def prefixEnd_3967815 : Nat := 4983230072969 + 3 ^ 40 * 3967815 * 2
def baseEnd_3967815 : Nat := 2037396243119498639264857

theorem tailTrace_3967815 : CollatzResearch.WordTrace tailWord_3967815 prefixEnd_3967815 2037396243119498639264857 := by
  unfold tailWord_3967815
  simp only [CollatzResearch.WordTrace]
  refine ⟨144718102120291378696728899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96478734746860919131152599 144718102120291378696728899)
  ·
    refine ⟨217077153180437068045093349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144718102120291378696728899 217077153180437068045093349)
    ·
      refine ⟨40701966221331950258455003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 217077153180437068045093349 40701966221331950258455003)
      ·
        refine ⟨61052949331997925387682505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40701966221331950258455003 61052949331997925387682505)
        ·
          refine ⟨45789711998998444040761879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61052949331997925387682505 45789711998998444040761879)
          ·
            refine ⟨68684567998497666061142819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45789711998998444040761879 68684567998497666061142819)
            ·
              refine ⟨103026851997746499091714229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68684567998497666061142819 103026851997746499091714229)
              ·
                refine ⟨9658767374788734289848209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 103026851997746499091714229 9658767374788734289848209)
                ·
                  refine ⟨7244075531091550717386157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9658767374788734289848209 7244075531091550717386157)
                  ·
                    refine ⟨2716528324159331519019809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7244075531091550717386157 2716528324159331519019809)
                    ·
                      refine ⟨2037396243119498639264857, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2716528324159331519019809 2037396243119498639264857)
                      ·
                        rfl

theorem cell23_3967815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 1, 5, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 1, 5, 2, 3, 2].length) (baseStart_3967815 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3967815 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3967815 prefixEnd_3967815 := by exact prefixLift 3967815
  have htrace : WordTrace (prefixWord ++ tailWord_3967815) baseStart_3967815 baseEnd_3967815 := by
    simpa [prefixWord, tailWord_3967815, baseEnd_3967815] using wordTrace_append hprefix tailTrace_3967815
  have hstable : (prefixWord ++ tailWord_3967815).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3967815).length < 2 ^ (prefixWord ++ tailWord_3967815).sum := by decide
  have hdescent : baseEnd_3967815 < baseStart_3967815 := by decide
  rcases family_descends (prefixWord ++ tailWord_3967815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3967839 : List Nat := [1, 1, 2, 3, 1, 3, 5, 2, 1, 1, 3]
def baseStart_3967839 : Nat := 118140960795 + 3967839 * 2 ^ 59
def prefixEnd_3967839 : Nat := 4983230072969 + 3 ^ 40 * 3967839 * 2
def baseEnd_3967839 : Nat := 2037408566655206545364747

theorem tailTrace_3967839 : CollatzResearch.WordTrace tailWord_3967839 prefixEnd_3967839 2037408566655206545364747 := by
  unfold tailWord_3967839
  simp only [CollatzResearch.WordTrace]
  refine ⟨144718977472204430795602571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96479318314802953863735047 144718977472204430795602571)
  ·
    refine ⟨217078466208306646193403857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144718977472204430795602571 217078466208306646193403857)
    ·
      refine ⟨162808849656229984645052893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 217078466208306646193403857 162808849656229984645052893)
      ·
        refine ⟨61053318621086244241894835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 162808849656229984645052893 61053318621086244241894835)
        ·
          refine ⟨91579977931629366362842253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61053318621086244241894835 91579977931629366362842253)
          ·
            refine ⟨34342491724361012386065845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 91579977931629366362842253 34342491724361012386065845)
            ·
              refine ⟨3219608599158844911193673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 34342491724361012386065845 3219608599158844911193673)
              ·
                refine ⟨2414706449369133683395255, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3219608599158844911193673 2414706449369133683395255)
                ·
                  refine ⟨3622059674053700525092883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2414706449369133683395255 3622059674053700525092883)
                  ·
                    refine ⟨5433089511080550787639325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3622059674053700525092883 5433089511080550787639325)
                    ·
                      refine ⟨2037408566655206545364747, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5433089511080550787639325 2037408566655206545364747)
                      ·
                        rfl

theorem cell23_3967839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 5, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 5, 2, 1, 1, 3].length) (baseStart_3967839 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3967839 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3967839 prefixEnd_3967839 := by exact prefixLift 3967839
  have htrace : WordTrace (prefixWord ++ tailWord_3967839) baseStart_3967839 baseEnd_3967839 := by
    simpa [prefixWord, tailWord_3967839, baseEnd_3967839] using wordTrace_append hprefix tailTrace_3967839
  have hstable : (prefixWord ++ tailWord_3967839).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3967839).length < 2 ^ (prefixWord ++ tailWord_3967839).sum := by decide
  have hdescent : baseEnd_3967839 < baseStart_3967839 := by decide
  rcases family_descends (prefixWord ++ tailWord_3967839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3967851 : List Nat := [1, 1, 1, 1, 2, 2, 5, 10]
def baseStart_3967851 : Nat := 118140960795 + 3967851 * 2 ^ 59
def prefixEnd_3967851 : Nat := 4983230072969 + 3 ^ 40 * 3967851 * 2
def baseEnd_3967851 : Nat := 75459804756409648089433

theorem tailTrace_3967851 : CollatzResearch.WordTrace tailWord_3967851 prefixEnd_3967851 75459804756409648089433 := by
  unfold tailWord_3967851
  simp only [CollatzResearch.WordTrace]
  refine ⟨144719415148160956845039407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96479610098773971230026271 144719415148160956845039407)
  ·
    refine ⟨217079122722241435267559111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144719415148160956845039407 217079122722241435267559111)
    ·
      refine ⟨325618684083362152901338667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 217079122722241435267559111 325618684083362152901338667)
      ·
        refine ⟨488428026125043229352008001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 325618684083362152901338667 488428026125043229352008001)
        ·
          refine ⟨366321019593782422014006001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 488428026125043229352008001 366321019593782422014006001)
          ·
            refine ⟨274740764695336816510504501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 366321019593782422014006001 274740764695336816510504501)
            ·
              refine ⟨25756946690187826547859797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 274740764695336816510504501 25756946690187826547859797)
              ·
                refine ⟨75459804756409648089433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 25756946690187826547859797 75459804756409648089433)
                ·
                  rfl

theorem cell23_3967851_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 5, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 5, 10].length) (baseStart_3967851 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3967851 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3967851 prefixEnd_3967851 := by exact prefixLift 3967851
  have htrace : WordTrace (prefixWord ++ tailWord_3967851) baseStart_3967851 baseEnd_3967851 := by
    simpa [prefixWord, tailWord_3967851, baseEnd_3967851] using wordTrace_append hprefix tailTrace_3967851
  have hstable : (prefixWord ++ tailWord_3967851).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3967851).length < 2 ^ (prefixWord ++ tailWord_3967851).sum := by decide
  have hdescent : baseEnd_3967851 < baseStart_3967851 := by decide
  rcases family_descends (prefixWord ++ tailWord_3967851) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3967858 : List Nat := [3, 2, 1, 2, 1, 1, 4, 1, 1, 1, 6]
def baseStart_3967858 : Nat := 118140960795 + 3967858 * 2 ^ 59
def prefixEnd_3967858 : Nat := 4983230072969 + 3 ^ 40 * 3967858 * 2
def baseEnd_3967858 : Nat := 2037418322787641971027159

theorem tailTrace_3967858 : CollatzResearch.WordTrace tailWord_3967858 prefixEnd_3967858 2037418322787641971027159 := by
  unfold tailWord_3967858
  simp only [CollatzResearch.WordTrace]
  refine ⟨36179917614783899260136057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 96479780306090398027029485 36179917614783899260136057)
  ·
    refine ⟨27134938211087924445102043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36179917614783899260136057 27134938211087924445102043)
    ·
      refine ⟨40702407316631886667653065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27134938211087924445102043 40702407316631886667653065)
      ·
        refine ⟨30526805487473915000739799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40702407316631886667653065 30526805487473915000739799)
        ·
          refine ⟨45790208231210872501109699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30526805487473915000739799 45790208231210872501109699)
          ·
            refine ⟨68685312346816308751664549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45790208231210872501109699 68685312346816308751664549)
            ·
              refine ⟨12878496065028057890937103, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 68685312346816308751664549 12878496065028057890937103)
              ·
                refine ⟨19317744097542086836405655, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12878496065028057890937103 19317744097542086836405655)
                ·
                  refine ⟨28976616146313130254608483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19317744097542086836405655 28976616146313130254608483)
                  ·
                    refine ⟨43464924219469695381912725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 28976616146313130254608483 43464924219469695381912725)
                    ·
                      refine ⟨2037418322787641971027159, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 43464924219469695381912725 2037418322787641971027159)
                      ·
                        rfl

theorem cell23_3967858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 4, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 4, 1, 1, 1, 6].length) (baseStart_3967858 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3967858 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3967858 prefixEnd_3967858 := by exact prefixLift 3967858
  have htrace : WordTrace (prefixWord ++ tailWord_3967858) baseStart_3967858 baseEnd_3967858 := by
    simpa [prefixWord, tailWord_3967858, baseEnd_3967858] using wordTrace_append hprefix tailTrace_3967858
  have hstable : (prefixWord ++ tailWord_3967858).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3967858).length < 2 ^ (prefixWord ++ tailWord_3967858).sum := by decide
  have hdescent : baseEnd_3967858 < baseStart_3967858 := by decide
  rcases family_descends (prefixWord ++ tailWord_3967858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3967862 : List Nat := [5, 1, 1, 3, 1, 2, 1, 1, 3, 1, 4]
def baseStart_3967862 : Nat := 118140960795 + 3967862 * 2 ^ 59
def prefixEnd_3967862 : Nat := 4983230072969 + 3 ^ 40 * 3967862 * 2
def baseEnd_3967862 : Nat := 2037420376710259955377141

theorem tailTrace_3967862 : CollatzResearch.WordTrace tailWord_3967862 prefixEnd_3967862 2037420376710259955377141 := by
  unfold tailWord_3967862
  simp only [CollatzResearch.WordTrace]
  refine ⟨9044988521945069107730615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 96479877567414070482459893 9044988521945069107730615)
  ·
    refine ⟨13567482782917603661595923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9044988521945069107730615 13567482782917603661595923)
    ·
      refine ⟨20351224174376405492393885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13567482782917603661595923 20351224174376405492393885)
      ·
        refine ⟨7631709065391152059647707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20351224174376405492393885 7631709065391152059647707)
        ·
          refine ⟨11447563598086728089471561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7631709065391152059647707 11447563598086728089471561)
          ·
            refine ⟨8585672698565046067103671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11447563598086728089471561 8585672698565046067103671)
            ·
              refine ⟨12878509047847569100655507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8585672698565046067103671 12878509047847569100655507)
              ·
                refine ⟨19317763571771353650983261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12878509047847569100655507 19317763571771353650983261)
                ·
                  refine ⟨7244161339414257619118723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19317763571771353650983261 7244161339414257619118723)
                  ·
                    refine ⟨10866242009121386428678085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7244161339414257619118723 10866242009121386428678085)
                    ·
                      refine ⟨2037420376710259955377141, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10866242009121386428678085 2037420376710259955377141)
                      ·
                        rfl

theorem cell23_3967862_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 2, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 2, 1, 1, 3, 1, 4].length) (baseStart_3967862 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3967862 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3967862 prefixEnd_3967862 := by exact prefixLift 3967862
  have htrace : WordTrace (prefixWord ++ tailWord_3967862) baseStart_3967862 baseEnd_3967862 := by
    simpa [prefixWord, tailWord_3967862, baseEnd_3967862] using wordTrace_append hprefix tailTrace_3967862
  have hstable : (prefixWord ++ tailWord_3967862).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3967862).length < 2 ^ (prefixWord ++ tailWord_3967862).sum := by decide
  have hdescent : baseEnd_3967862 < baseStart_3967862 := by decide
  rcases family_descends (prefixWord ++ tailWord_3967862) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3967865 : List Nat := [1, 2, 1, 3, 2, 4, 1, 1, 3, 2, 3]
def baseStart_3967865 : Nat := 118140960795 + 3967865 * 2 ^ 59
def prefixEnd_3967865 : Nat := 4983230072969 + 3 ^ 40 * 3967865 * 2
def baseEnd_3967865 : Nat := 2037421917152223443639627

theorem tailTrace_3967865 : CollatzResearch.WordTrace tailWord_3967865 prefixEnd_3967865 2037421917152223443639627 := by
  unfold tailWord_3967865
  simp only [CollatzResearch.WordTrace]
  refine ⟨144719925770110237236049049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96479950513406824824032699 144719925770110237236049049)
  ·
    refine ⟨108539944327582677927036787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 144719925770110237236049049 108539944327582677927036787)
    ·
      refine ⟨162809916491374016890555181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108539944327582677927036787 162809916491374016890555181)
      ·
        refine ⟨61053718684265256333958193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 162809916491374016890555181 61053718684265256333958193)
        ·
          refine ⟨45790289013198942250468645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61053718684265256333958193 45790289013198942250468645)
          ·
            refine ⟨8585679189974801671962871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 45790289013198942250468645 8585679189974801671962871)
            ·
              refine ⟨12878518784962202507944307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8585679189974801671962871 12878518784962202507944307)
              ·
                refine ⟨19317778177443303761916461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12878518784962202507944307 19317778177443303761916461)
                ·
                  refine ⟨7244166816541238910718673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19317778177443303761916461 7244166816541238910718673)
                  ·
                    refine ⟨5433125112405929183039005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7244166816541238910718673 5433125112405929183039005)
                    ·
                      refine ⟨2037421917152223443639627, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5433125112405929183039005 2037421917152223443639627)
                      ·
                        rfl

theorem cell23_3967865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 4, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 4, 1, 1, 3, 2, 3].length) (baseStart_3967865 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3967865 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3967865 prefixEnd_3967865 := by exact prefixLift 3967865
  have htrace : WordTrace (prefixWord ++ tailWord_3967865) baseStart_3967865 baseEnd_3967865 := by
    simpa [prefixWord, tailWord_3967865, baseEnd_3967865] using wordTrace_append hprefix tailTrace_3967865
  have hstable : (prefixWord ++ tailWord_3967865).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3967865).length < 2 ^ (prefixWord ++ tailWord_3967865).sum := by decide
  have hdescent : baseEnd_3967865 < baseStart_3967865 := by decide
  rcases family_descends (prefixWord ++ tailWord_3967865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3967882 : List Nat := [3, 1, 2, 4, 1, 3, 1, 1, 1, 1, 5]
def baseStart_3967882 : Nat := 118140960795 + 3967882 * 2 ^ 59
def prefixEnd_3967882 : Nat := 4983230072969 + 3 ^ 40 * 3967882 * 2
def baseEnd_3967882 : Nat := 2037430646323349877127049

theorem tailTrace_3967882 : CollatzResearch.WordTrace tailWord_3967882 prefixEnd_3967882 2037430646323349877127049 := by
  unfold tailWord_3967882
  simp only [CollatzResearch.WordTrace]
  refine ⟨36180136452762162284854475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 96480363874032432759611933 36180136452762162284854475)
  ·
    refine ⟨54270204679143243427281713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36180136452762162284854475 54270204679143243427281713)
    ·
      refine ⟨40702653509357432570461285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54270204679143243427281713 40702653509357432570461285)
      ·
        refine ⟨7631747533004518606961491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 40702653509357432570461285 7631747533004518606961491)
        ·
          refine ⟨11447621299506777910442237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7631747533004518606961491 11447621299506777910442237)
          ·
            refine ⟨4292857987315041716415839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11447621299506777910442237 4292857987315041716415839)
            ·
              refine ⟨6439286980972562574623759, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4292857987315041716415839 6439286980972562574623759)
              ·
                refine ⟨9658930471458843861935639, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6439286980972562574623759 9658930471458843861935639)
                ·
                  refine ⟨14488395707188265792903459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9658930471458843861935639 14488395707188265792903459)
                  ·
                    refine ⟨21732593560782398689355189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14488395707188265792903459 21732593560782398689355189)
                    ·
                      refine ⟨2037430646323349877127049, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 21732593560782398689355189 2037430646323349877127049)
                      ·
                        rfl

theorem cell23_3967882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 3, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 3, 1, 1, 1, 1, 5].length) (baseStart_3967882 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3967882 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3967882 prefixEnd_3967882 := by exact prefixLift 3967882
  have htrace : WordTrace (prefixWord ++ tailWord_3967882) baseStart_3967882 baseEnd_3967882 := by
    simpa [prefixWord, tailWord_3967882, baseEnd_3967882] using wordTrace_append hprefix tailTrace_3967882
  have hstable : (prefixWord ++ tailWord_3967882).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3967882).length < 2 ^ (prefixWord ++ tailWord_3967882).sum := by decide
  have hdescent : baseEnd_3967882 < baseStart_3967882 := by decide
  rcases family_descends (prefixWord ++ tailWord_3967882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3967890 : List Nat := [3, 2, 3, 2, 3, 1, 2, 2, 1, 1, 3]
def baseStart_3967890 : Nat := 118140960795 + 3967890 * 2 ^ 59
def prefixEnd_3967890 : Nat := 4983230072969 + 3 ^ 40 * 3967890 * 2
def baseEnd_3967890 : Nat := 2037434754168585845827013

theorem tailTrace_3967890 : CollatzResearch.WordTrace tailWord_3967890 prefixEnd_3967890 2037434754168585845827013 := by
  unfold tailWord_3967890
  simp only [CollatzResearch.WordTrace]
  refine ⟨36180209398754916626427281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 96480558396679777670472749 36180209398754916626427281)
  ·
    refine ⟨27135157049066187469820461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36180209398754916626427281 27135157049066187469820461)
    ·
      refine ⟨10175683893399820301182673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27135157049066187469820461 10175683893399820301182673)
      ·
        refine ⟨7631762920049865225887005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10175683893399820301182673 7631762920049865225887005)
        ·
          refine ⟨2861911095018699459707627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7631762920049865225887005 2861911095018699459707627)
          ·
            refine ⟨4292866642528049189561441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2861911095018699459707627 4292866642528049189561441)
            ·
              refine ⟨3219649981896036892171081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4292866642528049189561441 3219649981896036892171081)
              ·
                refine ⟨2414737486422027669128311, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3219649981896036892171081 2414737486422027669128311)
                ·
                  refine ⟨3622106229633041503692467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2414737486422027669128311 3622106229633041503692467)
                  ·
                    refine ⟨5433159344449562255538701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3622106229633041503692467 5433159344449562255538701)
                    ·
                      refine ⟨2037434754168585845827013, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5433159344449562255538701 2037434754168585845827013)
                      ·
                        rfl

theorem cell23_3967890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 3, 1, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 3, 1, 2, 2, 1, 1, 3].length) (baseStart_3967890 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3967890 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3967890 prefixEnd_3967890 := by exact prefixLift 3967890
  have htrace : WordTrace (prefixWord ++ tailWord_3967890) baseStart_3967890 baseEnd_3967890 := by
    simpa [prefixWord, tailWord_3967890, baseEnd_3967890] using wordTrace_append hprefix tailTrace_3967890
  have hstable : (prefixWord ++ tailWord_3967890).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3967890).length < 2 ^ (prefixWord ++ tailWord_3967890).sum := by decide
  have hdescent : baseEnd_3967890 < baseStart_3967890 := by decide
  rcases family_descends (prefixWord ++ tailWord_3967890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3967935 : List Nat := [1, 1, 2, 2, 2, 1, 2, 3, 3, 4, 2]
def baseStart_3967935 : Nat := 118140960795 + 3967935 * 2 ^ 59
def prefixEnd_3967935 : Nat := 4983230072969 + 3 ^ 40 * 3967935 * 2
def baseEnd_3967935 : Nat := 2037457860798038169764305

theorem tailTrace_3967935 : CollatzResearch.WordTrace tailWord_3967935 prefixEnd_3967935 2037457860798038169764305 := by
  unfold tailWord_3967935
  simp only [CollatzResearch.WordTrace]
  refine ⟨144722478879856639191097259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96481652586571092794064839 144722478879856639191097259)
  ·
    refine ⟨217083718319784958786645889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144722478879856639191097259 217083718319784958786645889)
    ·
      refine ⟨162812788739838719089984417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 217083718319784958786645889 162812788739838719089984417)
      ·
        refine ⟨122109591554879039317488313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 162812788739838719089984417 122109591554879039317488313)
        ·
          refine ⟨91582193666159279488116235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 122109591554879039317488313 91582193666159279488116235)
          ·
            refine ⟨137373290499238919232174353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91582193666159279488116235 137373290499238919232174353)
            ·
              refine ⟨103029967874429189424130765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 137373290499238919232174353 103029967874429189424130765)
              ·
                refine ⟨38636237952910946034049037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 103029967874429189424130765 38636237952910946034049037)
                ·
                  refine ⟨14488589232341604762768389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38636237952910946034049037 14488589232341604762768389)
                  ·
                    refine ⟨2716610481064050893019073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 14488589232341604762768389 2716610481064050893019073)
                    ·
                      refine ⟨2037457860798038169764305, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2716610481064050893019073 2037457860798038169764305)
                      ·
                        rfl

theorem cell23_3967935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 2, 3, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 2, 3, 3, 4, 2].length) (baseStart_3967935 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3967935 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3967935 prefixEnd_3967935 := by exact prefixLift 3967935
  have htrace : WordTrace (prefixWord ++ tailWord_3967935) baseStart_3967935 baseEnd_3967935 := by
    simpa [prefixWord, tailWord_3967935, baseEnd_3967935] using wordTrace_append hprefix tailTrace_3967935
  have hstable : (prefixWord ++ tailWord_3967935).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3967935).length < 2 ^ (prefixWord ++ tailWord_3967935).sum := by decide
  have hdescent : baseEnd_3967935 < baseStart_3967935 := by decide
  rcases family_descends (prefixWord ++ tailWord_3967935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3967975 : List Nat := [1, 1, 5, 2, 2, 1, 2, 2, 7]
def baseStart_3967975 : Nat := 118140960795 + 3967975 * 2 ^ 59
def prefixEnd_3967975 : Nat := 4983230072969 + 3 ^ 40 * 3967975 * 2
def baseEnd_3967975 : Nat := 226386488891579779251569

theorem tailTrace_3967975 : CollatzResearch.WordTrace tailWord_3967975 prefixEnd_3967975 226386488891579779251569 := by
  unfold tailWord_3967975
  simp only [CollatzResearch.WordTrace]
  refine ⟨144723937799711726022553379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96482625199807817348368919 144723937799711726022553379)
  ·
    refine ⟨217085906699567589033830069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144723937799711726022553379 217085906699567589033830069)
    ·
      refine ⟨20351803753084461471921569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 217085906699567589033830069 20351803753084461471921569)
      ·
        refine ⟨15263852814813346103941177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20351803753084461471921569 15263852814813346103941177)
        ·
          refine ⟨11447889611110009577955883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15263852814813346103941177 11447889611110009577955883)
          ·
            refine ⟨17171834416665014366933825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11447889611110009577955883 17171834416665014366933825)
            ·
              refine ⟨12878875812498760775200369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17171834416665014366933825 12878875812498760775200369)
              ·
                refine ⟨9659156859374070581400277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12878875812498760775200369 9659156859374070581400277)
                ·
                  refine ⟨226386488891579779251569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9659156859374070581400277 226386488891579779251569)
                  ·
                    rfl

theorem cell23_3967975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 1, 2, 2, 7].length) (baseStart_3967975 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3967975 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3967975 prefixEnd_3967975 := by exact prefixLift 3967975
  have htrace : WordTrace (prefixWord ++ tailWord_3967975) baseStart_3967975 baseEnd_3967975 := by
    simpa [prefixWord, tailWord_3967975, baseEnd_3967975] using wordTrace_append hprefix tailTrace_3967975
  have hstable : (prefixWord ++ tailWord_3967975).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3967975).length < 2 ^ (prefixWord ++ tailWord_3967975).sum := by decide
  have hdescent : baseEnd_3967975 < baseStart_3967975 := by decide
  rcases family_descends (prefixWord ++ tailWord_3967975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3967989 : List Nat := [1, 3, 5, 2, 1, 1, 1, 1, 2, 1, 5]
def baseStart_3967989 : Nat := 118140960795 + 3967989 * 2 ^ 59
def prefixEnd_3967989 : Nat := 4983230072969 + 3 ^ 40 * 3967989 * 2
def baseEnd_3967989 : Nat := 2037485588753380958489057

theorem tailTrace_3967989 : CollatzResearch.WordTrace tailWord_3967989 prefixEnd_3967989 2037485588753380958489057 := by
  unfold tailWord_3967989
  simp only [CollatzResearch.WordTrace]
  refine ⟨144724448421661006413563021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96482965614440670942375347 144724448421661006413563021)
  ·
    refine ⟨54271668158122877405086133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 144724448421661006413563021 54271668158122877405086133)
    ·
      refine ⟨5087968889824019756726825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 54271668158122877405086133 5087968889824019756726825)
      ·
        refine ⟨3815976667368014817545119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5087968889824019756726825 3815976667368014817545119)
        ·
          refine ⟨5723965001052022226317679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3815976667368014817545119 5723965001052022226317679)
          ·
            refine ⟨8585947501578033339476519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5723965001052022226317679 8585947501578033339476519)
            ·
              refine ⟨12878921252367050009214779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8585947501578033339476519 12878921252367050009214779)
              ·
                refine ⟨19318381878550575013822169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12878921252367050009214779 19318381878550575013822169)
                ·
                  refine ⟨14488786408912931260366627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19318381878550575013822169 14488786408912931260366627)
                  ·
                    refine ⟨21733179613369396890549941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14488786408912931260366627 21733179613369396890549941)
                    ·
                      refine ⟨2037485588753380958489057, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 21733179613369396890549941 2037485588753380958489057)
                      ·
                        rfl

theorem cell23_3967989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 1, 1, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 1, 1, 1, 1, 2, 1, 5].length) (baseStart_3967989 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3967989 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3967989 prefixEnd_3967989 := by exact prefixLift 3967989
  have htrace : WordTrace (prefixWord ++ tailWord_3967989) baseStart_3967989 baseEnd_3967989 := by
    simpa [prefixWord, tailWord_3967989, baseEnd_3967989] using wordTrace_append hprefix tailTrace_3967989
  have hstable : (prefixWord ++ tailWord_3967989).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3967989).length < 2 ^ (prefixWord ++ tailWord_3967989).sum := by decide
  have hdescent : baseEnd_3967989 < baseStart_3967989 := by decide
  rcases family_descends (prefixWord ++ tailWord_3967989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3967995 : List Nat := [1, 1, 1, 1, 1, 3, 3, 2, 1, 7, 2]
def baseStart_3967995 : Nat := 118140960795 + 3967995 * 2 ^ 59
def prefixEnd_3967995 : Nat := 4983230072969 + 3 ^ 40 * 3967995 * 2
def baseEnd_3967995 : Nat := 2037488669637307935014029

theorem tailTrace_3967995 : CollatzResearch.WordTrace tailWord_3967995 prefixEnd_3967995 2037488669637307935014029 := by
  unfold tailWord_3967995
  simp only [CollatzResearch.WordTrace]
  refine ⟨144724667259639269438281439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96483111506426179625520959 144724667259639269438281439)
  ·
    refine ⟨217087000889458904157422159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144724667259639269438281439 217087000889458904157422159)
    ·
      refine ⟨325630501334188356236133239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 217087000889458904157422159 325630501334188356236133239)
      ·
        refine ⟨488445752001282534354199859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 325630501334188356236133239 488445752001282534354199859)
        ·
          refine ⟨732668628001923801531299789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 488445752001282534354199859 732668628001923801531299789)
          ·
            refine ⟨274750735500721425574237421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 732668628001923801531299789 274750735500721425574237421)
            ·
              refine ⟨103031525812770534590339033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 274750735500721425574237421 103031525812770534590339033)
              ·
                refine ⟨77273644359577900942754275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 103031525812770534590339033 77273644359577900942754275)
                ·
                  refine ⟨115910466539366851414131413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 77273644359577900942754275 115910466539366851414131413)
                  ·
                    refine ⟨2716651559516410580018705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 115910466539366851414131413 2716651559516410580018705)
                    ·
                      refine ⟨2037488669637307935014029, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2716651559516410580018705 2037488669637307935014029)
                      ·
                        rfl

theorem cell23_3967995_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 3, 2, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 3, 2, 1, 7, 2].length) (baseStart_3967995 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3967995 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3967995 prefixEnd_3967995 := by exact prefixLift 3967995
  have htrace : WordTrace (prefixWord ++ tailWord_3967995) baseStart_3967995 baseEnd_3967995 := by
    simpa [prefixWord, tailWord_3967995, baseEnd_3967995] using wordTrace_append hprefix tailTrace_3967995
  have hstable : (prefixWord ++ tailWord_3967995).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3967995).length < 2 ^ (prefixWord ++ tailWord_3967995).sum := by decide
  have hdescent : baseEnd_3967995 < baseStart_3967995 := by decide
  rcases family_descends (prefixWord ++ tailWord_3967995) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3968005 : List Nat := [1, 3, 1, 1, 2, 3, 3, 2, 2, 5]
def baseStart_3968005 : Nat := 118140960795 + 3968005 * 2 ^ 59
def prefixEnd_3968005 : Nat := 4983230072969 + 3 ^ 40 * 3968005 * 2
def baseEnd_3968005 : Nat := 679164601481284298629661

theorem tailTrace_3968005 : CollatzResearch.WordTrace tailWord_3968005 prefixEnd_3968005 679164601481284298629661 := by
  unfold tailWord_3968005
  simp only [CollatzResearch.WordTrace]
  refine ⟨144725031989603041146145469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96483354659735360764096979 144725031989603041146145469)
  ·
    refine ⟨54271886996101140429804551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 144725031989603041146145469 54271886996101140429804551)
    ·
      refine ⟨81407830494151710644706827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54271886996101140429804551 81407830494151710644706827)
      ·
        refine ⟨122111745741227565967060241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81407830494151710644706827 122111745741227565967060241)
        ·
          refine ⟨91583809305920674475295181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 122111745741227565967060241 91583809305920674475295181)
          ·
            refine ⟨34343928489720252928235693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 91583809305920674475295181 34343928489720252928235693)
            ·
              refine ⟨12878973183645094848088385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34343928489720252928235693 12878973183645094848088385)
              ·
                refine ⟨9659229887733821136066289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12878973183645094848088385 9659229887733821136066289)
                ·
                  refine ⟨7244422415800365852049717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9659229887733821136066289 7244422415800365852049717)
                  ·
                    refine ⟨679164601481284298629661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7244422415800365852049717 679164601481284298629661)
                    ·
                      rfl

theorem cell23_3968005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 3, 2, 2, 5].length) (baseStart_3968005 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3968005 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3968005 prefixEnd_3968005 := by exact prefixLift 3968005
  have htrace : WordTrace (prefixWord ++ tailWord_3968005) baseStart_3968005 baseEnd_3968005 := by
    simpa [prefixWord, tailWord_3968005, baseEnd_3968005] using wordTrace_append hprefix tailTrace_3968005
  have hstable : (prefixWord ++ tailWord_3968005).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3968005).length < 2 ^ (prefixWord ++ tailWord_3968005).sum := by decide
  have hdescent : baseEnd_3968005 < baseStart_3968005 := by decide
  rcases family_descends (prefixWord ++ tailWord_3968005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3968039 : List Nat := [1, 1, 7, 1, 1, 2, 2, 1, 2, 5]
def baseStart_3968039 : Nat := 118140960795 + 3968039 * 2 ^ 59
def prefixEnd_3968039 : Nat := 4983230072969 + 3 ^ 40 * 3968039 * 2
def baseEnd_3968039 : Nat := 679170420928701920954609

theorem tailTrace_3968039 : CollatzResearch.WordTrace tailWord_3968039 prefixEnd_3968039 679170420928701920954609 := by
  unfold tailWord_3968039
  simp only [CollatzResearch.WordTrace]
  refine ⟨144726272071479864952883171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96484181380986576635255447 144726272071479864952883171)
  ·
    refine ⟨217089408107219797429324757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144726272071479864952883171 217089408107219797429324757)
    ·
      refine ⟨5088033002512964002249799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 217089408107219797429324757 5088033002512964002249799)
      ·
        refine ⟨7632049503769446003374699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5088033002512964002249799 7632049503769446003374699)
        ·
          refine ⟨11448074255654169005062049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7632049503769446003374699 11448074255654169005062049)
          ·
            refine ⟨8586055691740626753796537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11448074255654169005062049 8586055691740626753796537)
            ·
              refine ⟨6439541768805470065347403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8586055691740626753796537 6439541768805470065347403)
              ·
                refine ⟨9659312653208205098021105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6439541768805470065347403 9659312653208205098021105)
                ·
                  refine ⟨7244484489906153823515829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9659312653208205098021105 7244484489906153823515829)
                  ·
                    refine ⟨679170420928701920954609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7244484489906153823515829 679170420928701920954609)
                    ·
                      rfl

theorem cell23_3968039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 2, 2, 1, 2, 5].length) (baseStart_3968039 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3968039 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3968039 prefixEnd_3968039 := by exact prefixLift 3968039
  have htrace : WordTrace (prefixWord ++ tailWord_3968039) baseStart_3968039 baseEnd_3968039 := by
    simpa [prefixWord, tailWord_3968039, baseEnd_3968039] using wordTrace_append hprefix tailTrace_3968039
  have hstable : (prefixWord ++ tailWord_3968039).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3968039).length < 2 ^ (prefixWord ++ tailWord_3968039).sum := by decide
  have hdescent : baseEnd_3968039 < baseStart_3968039 := by decide
  rcases family_descends (prefixWord ++ tailWord_3968039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3968082 : List Nat := [3, 2, 2, 1, 3, 1, 2, 3, 6]
def baseStart_3968082 : Nat := 118140960795 + 3968082 * 2 ^ 59
def prefixEnd_3968082 : Nat := 4983230072969 + 3 ^ 40 * 3968082 * 2
def baseEnd_3968082 : Nat := 226392593606027677180681

theorem tailTrace_3968082 : CollatzResearch.WordTrace tailWord_3968082 prefixEnd_3968082 226392593606027677180681 := by
  unfold tailWord_3968082
  simp only [CollatzResearch.WordTrace]
  refine ⟨36181960102581020824174625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 96485226940216055531132333 36181960102581020824174625)
  ·
    refine ⟨27136470076935765618130969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36181960102581020824174625 27136470076935765618130969)
    ·
      refine ⟨20352352557701824213598227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27136470076935765618130969 20352352557701824213598227)
      ·
        refine ⟨30528528836552736320397341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20352352557701824213598227 30528528836552736320397341)
        ·
          refine ⟨11448198313707276120149003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30528528836552736320397341 11448198313707276120149003)
          ·
            refine ⟨17172297470560914180223505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11448198313707276120149003 17172297470560914180223505)
            ·
              refine ⟨12879223102920685635167629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17172297470560914180223505 12879223102920685635167629)
              ·
                refine ⟨4829708663595257113187861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12879223102920685635167629 4829708663595257113187861)
                ·
                  refine ⟨226392593606027677180681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4829708663595257113187861 226392593606027677180681)
                  ·
                    rfl

theorem cell23_3968082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 1, 2, 3, 6].length) (baseStart_3968082 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3968082 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3968082 prefixEnd_3968082 := by exact prefixLift 3968082
  have htrace : WordTrace (prefixWord ++ tailWord_3968082) baseStart_3968082 baseEnd_3968082 := by
    simpa [prefixWord, tailWord_3968082, baseEnd_3968082] using wordTrace_append hprefix tailTrace_3968082
  have hstable : (prefixWord ++ tailWord_3968082).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3968082).length < 2 ^ (prefixWord ++ tailWord_3968082).sum := by decide
  have hdescent : baseEnd_3968082 < baseStart_3968082 := by decide
  rcases family_descends (prefixWord ++ tailWord_3968082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3968093 : List Nat := [1, 4, 4, 1, 3, 1, 1, 1, 2, 1, 4]
def baseStart_3968093 : Nat := 118140960795 + 3968093 * 2 ^ 59
def prefixEnd_3968093 : Nat := 4983230072969 + 3 ^ 40 * 3968093 * 2
def baseEnd_3968093 : Nat := 2037538990741448551588579

theorem tailTrace_3968093 : CollatzResearch.WordTrace tailWord_3968093 prefixEnd_3968093 2037538990741448551588579 := by
  unfold tailWord_3968093
  simp only [CollatzResearch.WordTrace]
  refine ⟨144728241613284232175348933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96485494408856154783565955 144728241613284232175348933)
  ·
    refine ⟨27136545302490793532877925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 144728241613284232175348933 27136545302490793532877925)
    ·
      refine ⟨5088102244217023787414611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 27136545302490793532877925 5088102244217023787414611)
      ·
        refine ⟨7632153366325535681121917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5088102244217023787414611 7632153366325535681121917)
        ·
          refine ⟨2862057512372075880420719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7632153366325535681121917 2862057512372075880420719)
          ·
            refine ⟨4293086268558113820631079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2862057512372075880420719 4293086268558113820631079)
            ·
              refine ⟨6439629402837170730946619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4293086268558113820631079 6439629402837170730946619)
              ·
                refine ⟨9659444104255756096419929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6439629402837170730946619 9659444104255756096419929)
                ·
                  refine ⟨7244583078191817072314947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9659444104255756096419929 7244583078191817072314947)
                  ·
                    refine ⟨10866874617287725608472421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7244583078191817072314947 10866874617287725608472421)
                    ·
                      refine ⟨2037538990741448551588579, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10866874617287725608472421 2037538990741448551588579)
                      ·
                        rfl

theorem cell23_3968093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 3, 1, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 3, 1, 1, 1, 2, 1, 4].length) (baseStart_3968093 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3968093 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3968093 prefixEnd_3968093 := by exact prefixLift 3968093
  have htrace : WordTrace (prefixWord ++ tailWord_3968093) baseStart_3968093 baseEnd_3968093 := by
    simpa [prefixWord, tailWord_3968093, baseEnd_3968093] using wordTrace_append hprefix tailTrace_3968093
  have hstable : (prefixWord ++ tailWord_3968093).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3968093).length < 2 ^ (prefixWord ++ tailWord_3968093).sum := by decide
  have hdescent : baseEnd_3968093 < baseStart_3968093 := by decide
  rcases family_descends (prefixWord ++ tailWord_3968093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3968095 : List Nat := [1, 1, 2, 3, 1, 1, 3, 3, 3, 5]
def baseStart_3968095 : Nat := 118140960795 + 3968095 * 2 ^ 59
def prefixEnd_3968095 : Nat := 4983230072969 + 3 ^ 40 * 3968095 * 2
def baseEnd_3968095 : Nat := 679180005900919181254523

theorem tailTrace_3968095 : CollatzResearch.WordTrace tailWord_3968095 prefixEnd_3968095 679180005900919181254523 := by
  unfold tailWord_3968095
  simp only [CollatzResearch.WordTrace]
  refine ⟨144728314559276986516921739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96485543039517991011281159 144728314559276986516921739)
  ·
    refine ⟨217092471838915479775382609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144728314559276986516921739 217092471838915479775382609)
    ·
      refine ⟨162819353879186609831536957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 217092471838915479775382609 162819353879186609831536957)
      ·
        refine ⟨61057257704694978686826359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 162819353879186609831536957 61057257704694978686826359)
        ·
          refine ⟨91585886557042468030239539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61057257704694978686826359 91585886557042468030239539)
          ·
            refine ⟨137378829835563702045359309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91585886557042468030239539 137378829835563702045359309)
            ·
              refine ⟨51517061188336388267009741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 137378829835563702045359309 51517061188336388267009741)
              ·
                refine ⟨19318897945626145600128653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 51517061188336388267009741 19318897945626145600128653)
                ·
                  refine ⟨7244586729609804600048245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19318897945626145600128653 7244586729609804600048245)
                  ·
                    refine ⟨679180005900919181254523, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7244586729609804600048245 679180005900919181254523)
                    ·
                      rfl

theorem cell23_3968095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 3, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 3, 3, 3, 5].length) (baseStart_3968095 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3968095 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3968095 prefixEnd_3968095 := by exact prefixLift 3968095
  have htrace : WordTrace (prefixWord ++ tailWord_3968095) baseStart_3968095 baseEnd_3968095 := by
    simpa [prefixWord, tailWord_3968095, baseEnd_3968095] using wordTrace_append hprefix tailTrace_3968095
  have hstable : (prefixWord ++ tailWord_3968095).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3968095).length < 2 ^ (prefixWord ++ tailWord_3968095).sum := by decide
  have hdescent : baseEnd_3968095 < baseStart_3968095 := by decide
  rcases family_descends (prefixWord ++ tailWord_3968095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3968112 : List Nat := [2, 1, 1, 1, 5, 1, 3, 3, 1, 5]
def baseStart_3968112 : Nat := 118140960795 + 3968112 * 2 ^ 59
def prefixEnd_3968112 : Nat := 4983230072969 + 3 ^ 40 * 3968112 * 2
def baseEnd_3968112 : Nat := 679182915624627992416997

theorem tailTrace_3968112 : CollatzResearch.WordTrace tailWord_3968112 prefixEnd_3968112 679182915624627992416997 := by
  unfold tailWord_3968112
  simp only [CollatzResearch.WordTrace]
  refine ⟨72364467300107699210145295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96485956400143598946860393 72364467300107699210145295)
  ·
    refine ⟨108546700950161548815217943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72364467300107699210145295 108546700950161548815217943)
    ·
      refine ⟨162820051425242323222826915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108546700950161548815217943 162820051425242323222826915)
      ·
        refine ⟨244230077137863484834240373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 162820051425242323222826915 244230077137863484834240373)
        ·
          refine ⟨22896569731674701703210035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 244230077137863484834240373 22896569731674701703210035)
          ·
            refine ⟨34344854597512052554815053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22896569731674701703210035 34344854597512052554815053)
            ·
              refine ⟨12879320474067019708055645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34344854597512052554815053 12879320474067019708055645)
              ·
                refine ⟨4829745177775132390520867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12879320474067019708055645 4829745177775132390520867)
                ·
                  refine ⟨7244617766662698585781301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4829745177775132390520867 7244617766662698585781301)
                  ·
                    refine ⟨679182915624627992416997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7244617766662698585781301 679182915624627992416997)
                    ·
                      rfl

theorem cell23_3968112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 3, 3, 1, 5].length) (baseStart_3968112 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3968112 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3968112 prefixEnd_3968112 := by exact prefixLift 3968112
  have htrace : WordTrace (prefixWord ++ tailWord_3968112) baseStart_3968112 baseEnd_3968112 := by
    simpa [prefixWord, tailWord_3968112, baseEnd_3968112] using wordTrace_append hprefix tailTrace_3968112
  have hstable : (prefixWord ++ tailWord_3968112).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3968112).length < 2 ^ (prefixWord ++ tailWord_3968112).sum := by decide
  have hdescent : baseEnd_3968112 < baseStart_3968112 := by decide
  rcases family_descends (prefixWord ++ tailWord_3968112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3968149 : List Nat := [1, 3, 2, 1, 1, 1, 2, 3, 5, 2, 2]
def baseStart_3968149 : Nat := 118140960795 + 3968149 * 2 ^ 59
def prefixEnd_3968149 : Nat := 4983230072969 + 3 ^ 40 * 3968149 * 2
def baseEnd_3968149 : Nat := 2037567745658100332488321

theorem tailTrace_3968149 : CollatzResearch.WordTrace tailWord_3968149 prefixEnd_3968149 2037567745658100332488321 := by
  unfold tailWord_3968149
  simp only [CollatzResearch.WordTrace]
  refine ⟨144730284101081353739387501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96486856067387569159591667 144730284101081353739387501)
  ·
    refine ⟨54273856537905507652270313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 144730284101081353739387501 54273856537905507652270313)
    ·
      refine ⟨40705392403429130739202735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54273856537905507652270313 40705392403429130739202735)
      ·
        refine ⟨61058088605143696108804103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40705392403429130739202735 61058088605143696108804103)
        ·
          refine ⟨91587132907715544163206155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61058088605143696108804103 91587132907715544163206155)
          ·
            refine ⟨137380699361573316244809233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91587132907715544163206155 137380699361573316244809233)
            ·
              refine ⟨103035524521179987183606925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 137380699361573316244809233 103035524521179987183606925)
              ·
                refine ⟨38638321695442495193852597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 103035524521179987183606925 38638321695442495193852597)
                ·
                  refine ⟨3622342658947733924423681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 38638321695442495193852597 3622342658947733924423681)
                  ·
                    refine ⟨2716756994210800443317761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3622342658947733924423681 2716756994210800443317761)
                    ·
                      refine ⟨2037567745658100332488321, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2716756994210800443317761 2037567745658100332488321)
                      ·
                        rfl

theorem cell23_3968149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 2, 3, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 2, 3, 5, 2, 2].length) (baseStart_3968149 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3968149 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3968149 prefixEnd_3968149 := by exact prefixLift 3968149
  have htrace : WordTrace (prefixWord ++ tailWord_3968149) baseStart_3968149 baseEnd_3968149 := by
    simpa [prefixWord, tailWord_3968149, baseEnd_3968149] using wordTrace_append hprefix tailTrace_3968149
  have hstable : (prefixWord ++ tailWord_3968149).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3968149).length < 2 ^ (prefixWord ++ tailWord_3968149).sum := by decide
  have hdescent : baseEnd_3968149 < baseStart_3968149 := by decide
  rcases family_descends (prefixWord ++ tailWord_3968149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3968193 : List Nat := [1, 2, 6, 1, 1, 1, 4, 1, 2, 4]
def baseStart_3968193 : Nat := 118140960795 + 3968193 * 2 ^ 59
def prefixEnd_3968193 : Nat := 4983230072969 + 3 ^ 40 * 3968193 * 2
def baseEnd_3968193 : Nat := 679196779602299386779373

theorem tailTrace_3968193 : CollatzResearch.WordTrace tailWord_3968193 prefixEnd_3968193 679196779602299386779373 := by
  unfold tailWord_3968193
  simp only [CollatzResearch.WordTrace]
  refine ⟨144731888912921949253989233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96487925941947966169326155 144731888912921949253989233)
  ·
    refine ⟨108548916684691461940491925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 144731888912921949253989233 108548916684691461940491925)
    ·
      refine ⟨5088230469594912278460559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 108548916684691461940491925 5088230469594912278460559)
      ·
        refine ⟨7632345704392368417690839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5088230469594912278460559 7632345704392368417690839)
        ·
          refine ⟨11448518556588552626536259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7632345704392368417690839 11448518556588552626536259)
          ·
            refine ⟨17172777834882828939804389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11448518556588552626536259 17172777834882828939804389)
            ·
              refine ⟨3219895844040530426213323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17172777834882828939804389 3219895844040530426213323)
              ·
                refine ⟨4829843766060795639319985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3219895844040530426213323 4829843766060795639319985)
                ·
                  refine ⟨3622382824545596729489989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4829843766060795639319985 3622382824545596729489989)
                  ·
                    refine ⟨679196779602299386779373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3622382824545596729489989 679196779602299386779373)
                    ·
                      rfl

theorem cell23_3968193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 1, 4, 1, 2, 4].length) (baseStart_3968193 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3968193 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3968193 prefixEnd_3968193 := by exact prefixLift 3968193
  have htrace : WordTrace (prefixWord ++ tailWord_3968193) baseStart_3968193 baseEnd_3968193 := by
    simpa [prefixWord, tailWord_3968193, baseEnd_3968193] using wordTrace_append hprefix tailTrace_3968193
  have hstable : (prefixWord ++ tailWord_3968193).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3968193).length < 2 ^ (prefixWord ++ tailWord_3968193).sum := by decide
  have hdescent : baseEnd_3968193 < baseStart_3968193 := by decide
  rcases family_descends (prefixWord ++ tailWord_3968193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3968195 : List Nat := [1, 1, 1, 3, 1, 1, 1, 4, 1, 4, 5]
def baseStart_3968195 : Nat := 118140960795 + 3968195 * 2 ^ 59
def prefixEnd_3968195 : Nat := 4983230072969 + 3 ^ 40 * 3968195 * 2
def baseEnd_3968195 : Nat := 2037591365768207152513109

theorem tailTrace_3968195 : CollatzResearch.WordTrace tailWord_3968195 prefixEnd_3968195 2037591365768207152513109 := by
  unfold tailWord_3968195
  simp only [CollatzResearch.WordTrace]
  refine ⟨144731961858914703595562039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96487974572609802397041359 144731961858914703595562039)
  ·
    refine ⟨217097942788372055393343059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144731961858914703595562039 217097942788372055393343059)
    ·
      refine ⟨325646914182558083090014589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 217097942788372055393343059 325646914182558083090014589)
      ·
        refine ⟨122117592818459281158755471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 325646914182558083090014589 122117592818459281158755471)
        ·
          refine ⟨183176389227688921738133207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 122117592818459281158755471 183176389227688921738133207)
          ·
            refine ⟨274764583841533382607199811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 183176389227688921738133207 274764583841533382607199811)
            ·
              refine ⟨412146875762300073910799717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 274764583841533382607199811 412146875762300073910799717)
              ·
                refine ⟨77277539205431263858274947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 412146875762300073910799717 77277539205431263858274947)
                ·
                  refine ⟨115916308808146895787412421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 77277539205431263858274947 115916308808146895787412421)
                  ·
                    refine ⟨21734307901527542960139829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 115916308808146895787412421 21734307901527542960139829)
                    ·
                      refine ⟨2037591365768207152513109, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 21734307901527542960139829 2037591365768207152513109)
                      ·
                        rfl

theorem cell23_3968195_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 4, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 4, 1, 4, 5].length) (baseStart_3968195 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3968195 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3968195 prefixEnd_3968195 := by exact prefixLift 3968195
  have htrace : WordTrace (prefixWord ++ tailWord_3968195) baseStart_3968195 baseEnd_3968195 := by
    simpa [prefixWord, tailWord_3968195, baseEnd_3968195] using wordTrace_append hprefix tailTrace_3968195
  have hstable : (prefixWord ++ tailWord_3968195).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3968195).length < 2 ^ (prefixWord ++ tailWord_3968195).sum := by decide
  have hdescent : baseEnd_3968195 < baseStart_3968195 := by decide
  rcases family_descends (prefixWord ++ tailWord_3968195) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3968232 : List Nat := [2, 1, 4, 1, 2, 1, 2, 2, 2, 6]
def baseStart_3968232 : Nat := 118140960795 + 3968232 * 2 ^ 59
def prefixEnd_3968232 : Nat := 4983230072969 + 3 ^ 40 * 3968232 * 2
def baseEnd_3968232 : Nat := 679203454850807835916813

theorem tailTrace_3968232 : CollatzResearch.WordTrace tailWord_3968232 prefixEnd_3968232 679203454850807835916813 := by
  unfold tailWord_3968232
  simp only [CollatzResearch.WordTrace]
  refine ⟨72366655679890329457329475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96488874239853772609772633 72366655679890329457329475)
  ·
    refine ⟨108549983519835494185994213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72366655679890329457329475 108549983519835494185994213)
    ·
      refine ⟨20353121909969155159873915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 108549983519835494185994213 20353121909969155159873915)
      ·
        refine ⟨30529682864953732739810873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20353121909969155159873915 30529682864953732739810873)
        ·
          refine ⟨22897262148715299554858155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30529682864953732739810873 22897262148715299554858155)
          ·
            refine ⟨34345893223072949332287233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22897262148715299554858155 34345893223072949332287233)
            ·
              refine ⟨25759419917304711999215425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34345893223072949332287233 25759419917304711999215425)
              ·
                refine ⟨19319564937978533999411569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25759419917304711999215425 19319564937978533999411569)
                ·
                  refine ⟨14489673703483900499558677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19319564937978533999411569 14489673703483900499558677)
                  ·
                    refine ⟨679203454850807835916813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14489673703483900499558677 679203454850807835916813)
                    ·
                      rfl

theorem cell23_3968232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 2, 2, 2, 6].length) (baseStart_3968232 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3968232 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3968232 prefixEnd_3968232 := by exact prefixLift 3968232
  have htrace : WordTrace (prefixWord ++ tailWord_3968232) baseStart_3968232 baseEnd_3968232 := by
    simpa [prefixWord, tailWord_3968232, baseEnd_3968232] using wordTrace_append hprefix tailTrace_3968232
  have hstable : (prefixWord ++ tailWord_3968232).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3968232).length < 2 ^ (prefixWord ++ tailWord_3968232).sum := by decide
  have hdescent : baseEnd_3968232 < baseStart_3968232 := by decide
  rcases family_descends (prefixWord ++ tailWord_3968232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3968296 : List Nat := [2, 1, 5, 1, 2, 1, 2, 4, 5]
def baseStart_3968296 : Nat := 118140960795 + 3968296 * 2 ^ 59
def prefixEnd_3968296 : Nat := 4983230072969 + 3 ^ 40 * 3968296 * 2
def baseEnd_3968296 : Nat := 226404803034923473038905

theorem tailTrace_3968296 : CollatzResearch.WordTrace tailWord_3968296 prefixEnd_3968296 226404803034923473038905 := by
  unfold tailWord_3968296
  simp only [CollatzResearch.WordTrace]
  refine ⟨72367822815774398922494371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96490430421032531896659161 72367822815774398922494371)
  ·
    refine ⟨108551734223661598383741557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72367822815774398922494371 108551734223661598383741557)
    ·
      refine ⟨10176725083468274848475771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 108551734223661598383741557 10176725083468274848475771)
      ·
        refine ⟨15265087625202412272713657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10176725083468274848475771 15265087625202412272713657)
        ·
          refine ⟨11448815718901809204535243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15265087625202412272713657 11448815718901809204535243)
          ·
            refine ⟨17173223578352713806802865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11448815718901809204535243 17173223578352713806802865)
            ·
              refine ⟨12879917683764535355102149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17173223578352713806802865 12879917683764535355102149)
              ·
                refine ⟨2414984565705850379081653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12879917683764535355102149 2414984565705850379081653)
                ·
                  refine ⟨226404803034923473038905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2414984565705850379081653 226404803034923473038905)
                  ·
                    rfl

theorem cell23_3968296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 1, 2, 4, 5].length) (baseStart_3968296 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3968296 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3968296 prefixEnd_3968296 := by exact prefixLift 3968296
  have htrace : WordTrace (prefixWord ++ tailWord_3968296) baseStart_3968296 baseEnd_3968296 := by
    simpa [prefixWord, tailWord_3968296, baseEnd_3968296] using wordTrace_append hprefix tailTrace_3968296
  have hstable : (prefixWord ++ tailWord_3968296).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3968296).length < 2 ^ (prefixWord ++ tailWord_3968296).sum := by decide
  have hdescent : baseEnd_3968296 < baseStart_3968296 := by decide
  rcases family_descends (prefixWord ++ tailWord_3968296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3968329 : List Nat := [1, 2, 1, 1, 2, 3, 2, 2, 1, 6, 2]
def baseStart_3968329 : Nat := 118140960795 + 3968329 * 2 ^ 59
def prefixEnd_3968329 : Nat := 4983230072969 + 3 ^ 40 * 3968329 * 2
def baseEnd_3968329 : Nat := 2037660172175909628237493

theorem tailTrace_3968329 : CollatzResearch.WordTrace tailWord_3968329 prefixEnd_3968329 2037660172175909628237493 := by
  unfold tailWord_3968329
  simp only [CollatzResearch.WordTrace]
  refine ⟨144736849240429244480940041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96491232826952829653960027 144736849240429244480940041)
  ·
    refine ⟨108552636930321933360705031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 144736849240429244480940041 108552636930321933360705031)
    ·
      refine ⟨162828955395482900041057547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108552636930321933360705031 162828955395482900041057547)
      ·
        refine ⟨244243433093224350061586321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 162828955395482900041057547 244243433093224350061586321)
        ·
          refine ⟨183182574819918262546189741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 244243433093224350061586321 183182574819918262546189741)
          ·
            refine ⟨68693465557469348454821153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 183182574819918262546189741 68693465557469348454821153)
            ·
              refine ⟨51520099168102011341115865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 68693465557469348454821153 51520099168102011341115865)
              ·
                refine ⟨38640074376076508505836899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51520099168102011341115865 38640074376076508505836899)
                ·
                  refine ⟨57960111564114762758755349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38640074376076508505836899 57960111564114762758755349)
                  ·
                    refine ⟨2716880229567879504316657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 57960111564114762758755349 2716880229567879504316657)
                    ·
                      refine ⟨2037660172175909628237493, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2716880229567879504316657 2037660172175909628237493)
                      ·
                        rfl

theorem cell23_3968329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 2, 2, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 2, 2, 1, 6, 2].length) (baseStart_3968329 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3968329 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3968329 prefixEnd_3968329 := by exact prefixLift 3968329
  have htrace : WordTrace (prefixWord ++ tailWord_3968329) baseStart_3968329 baseEnd_3968329 := by
    simpa [prefixWord, tailWord_3968329, baseEnd_3968329] using wordTrace_append hprefix tailTrace_3968329
  have hstable : (prefixWord ++ tailWord_3968329).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3968329).length < 2 ^ (prefixWord ++ tailWord_3968329).sum := by decide
  have hdescent : baseEnd_3968329 < baseStart_3968329 := by decide
  rcases family_descends (prefixWord ++ tailWord_3968329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3968356 : List Nat := [2, 3, 1, 1, 3, 2, 3, 1, 3, 4]
def baseStart_3968356 : Nat := 118140960795 + 3968356 * 2 ^ 59
def prefixEnd_3968356 : Nat := 4983230072969 + 3 ^ 40 * 3968356 * 2
def baseEnd_3968356 : Nat := 679224678717860340866623

theorem tailTrace_3968356 : CollatzResearch.WordTrace tailWord_3968356 prefixEnd_3968356 679224678717860340866623 := by
  unfold tailWord_3968356
  simp only [CollatzResearch.WordTrace]
  refine ⟨72368917005665714046086461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96491889340887618728115281 72368917005665714046086461)
  ·
    refine ⟨27138343877124642767282423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 72368917005665714046086461 27138343877124642767282423)
    ·
      refine ⟨40707515815686964150923635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27138343877124642767282423 40707515815686964150923635)
      ·
        refine ⟨61061273723530446226385453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40707515815686964150923635 61061273723530446226385453)
        ·
          refine ⟨22897977646323917334894545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 61061273723530446226385453 22897977646323917334894545)
          ·
            refine ⟨17173483234742938001170909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22897977646323917334894545 17173483234742938001170909)
            ·
              refine ⟨6440056213028601750439091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17173483234742938001170909 6440056213028601750439091)
              ·
                refine ⟨9660084319542902625658637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6440056213028601750439091 9660084319542902625658637)
                ·
                  refine ⟨3622531619828588484621989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9660084319542902625658637 3622531619828588484621989)
                  ·
                    refine ⟨679224678717860340866623, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3622531619828588484621989 679224678717860340866623)
                    ·
                      rfl

theorem cell23_3968356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 2, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 2, 3, 1, 3, 4].length) (baseStart_3968356 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3968356 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3968356 prefixEnd_3968356 := by exact prefixLift 3968356
  have htrace : WordTrace (prefixWord ++ tailWord_3968356) baseStart_3968356 baseEnd_3968356 := by
    simpa [prefixWord, tailWord_3968356, baseEnd_3968356] using wordTrace_append hprefix tailTrace_3968356
  have hstable : (prefixWord ++ tailWord_3968356).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3968356).length < 2 ^ (prefixWord ++ tailWord_3968356).sum := by decide
  have hdescent : baseEnd_3968356 < baseStart_3968356 := by decide
  rcases family_descends (prefixWord ++ tailWord_3968356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3968419 : List Nat := [1, 1, 1, 4, 1, 3, 1, 1, 5, 1, 4]
def baseStart_3968419 : Nat := 118140960795 + 3968419 * 2 ^ 59
def prefixEnd_3968419 : Nat := 4983230072969 + 3 ^ 40 * 3968419 * 2
def baseEnd_3968419 : Nat := 2037706385434814276112079

theorem tailTrace_3968419 : CollatzResearch.WordTrace tailWord_3968419 prefixEnd_3968419 2037706385434814276112079 := by
  unfold tailWord_3968419
  simp only [CollatzResearch.WordTrace]
  refine ⟨144740131810103189851716311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96493421206735459901144207 144740131810103189851716311)
  ·
    refine ⟨217110197715154784777574467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144740131810103189851716311 217110197715154784777574467)
    ·
      refine ⟨325665296572732177166361701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 217110197715154784777574467 325665296572732177166361701)
      ·
        refine ⟨61062243107387283218692819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 325665296572732177166361701 61062243107387283218692819)
        ·
          refine ⟨91593364661080924828039229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61062243107387283218692819 91593364661080924828039229)
          ·
            refine ⟨34347511747905346810514711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 91593364661080924828039229 34347511747905346810514711)
            ·
              refine ⟨51521267621858020215772067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34347511747905346810514711 51521267621858020215772067)
              ·
                refine ⟨77281901432787030323658101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51521267621858020215772067 77281901432787030323658101)
                ·
                  refine ⟨7245178259323784092842947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 77281901432787030323658101 7245178259323784092842947)
                  ·
                    refine ⟨10867767388985676139264421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7245178259323784092842947 10867767388985676139264421)
                    ·
                      refine ⟨2037706385434814276112079, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10867767388985676139264421 2037706385434814276112079)
                      ·
                        rfl

theorem cell23_3968419_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 1, 1, 5, 1, 4].length) (baseStart_3968419 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3968419 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3968419 prefixEnd_3968419 := by exact prefixLift 3968419
  have htrace : WordTrace (prefixWord ++ tailWord_3968419) baseStart_3968419 baseEnd_3968419 := by
    simpa [prefixWord, tailWord_3968419, baseEnd_3968419] using wordTrace_append hprefix tailTrace_3968419
  have hstable : (prefixWord ++ tailWord_3968419).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3968419).length < 2 ^ (prefixWord ++ tailWord_3968419).sum := by decide
  have hdescent : baseEnd_3968419 < baseStart_3968419 := by decide
  rcases family_descends (prefixWord ++ tailWord_3968419) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3968446 : List Nat := [4, 2, 1, 1, 1, 1, 1, 4, 4, 4]
def baseStart_3968446 : Nat := 118140960795 + 3968446 * 2 ^ 59
def prefixEnd_3968446 : Nat := 4983230072969 + 3 ^ 40 * 3968446 * 2
def baseEnd_3968446 : Nat := 679240083137495223491485

theorem tailTrace_3968446 : CollatzResearch.WordTrace tailWord_3968446 prefixEnd_3968446 679240083137495223491485 := by
  unfold tailWord_3968446
  simp only [CollatzResearch.WordTrace]
  refine ⟨18092639572625671682868649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 96494077720670248975299461 18092639572625671682868649)
  ·
    refine ⟨13569479679469253762151487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18092639572625671682868649 13569479679469253762151487)
    ·
      refine ⟨20354219519203880643227231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13569479679469253762151487 20354219519203880643227231)
      ·
        refine ⟨30531329278805820964840847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20354219519203880643227231 30531329278805820964840847)
        ·
          refine ⟨45796993918208731447261271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30531329278805820964840847 45796993918208731447261271)
          ·
            refine ⟨68695490877313097170891907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45796993918208731447261271 68695490877313097170891907)
            ·
              refine ⟨103043236315969645756337861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68695490877313097170891907 103043236315969645756337861)
              ·
                refine ⟨19320606809244308579313349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 103043236315969645756337861 19320606809244308579313349)
                ·
                  refine ⟨3622613776733307858621253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19320606809244308579313349 3622613776733307858621253)
                  ·
                    refine ⟨679240083137495223491485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3622613776733307858621253 679240083137495223491485)
                    ·
                      rfl

theorem cell23_3968446_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 1, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 1, 4, 4, 4].length) (baseStart_3968446 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3968446 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3968446 prefixEnd_3968446 := by exact prefixLift 3968446
  have htrace : WordTrace (prefixWord ++ tailWord_3968446) baseStart_3968446 baseEnd_3968446 := by
    simpa [prefixWord, tailWord_3968446, baseEnd_3968446] using wordTrace_append hprefix tailTrace_3968446
  have hstable : (prefixWord ++ tailWord_3968446).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3968446).length < 2 ^ (prefixWord ++ tailWord_3968446).sum := by decide
  have hdescent : baseEnd_3968446 < baseStart_3968446 := by decide
  rcases family_descends (prefixWord ++ tailWord_3968446) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3968483 : List Nat := [1, 1, 1, 6, 2, 3, 1, 1, 1, 2, 4]
def baseStart_3968483 : Nat := 118140960795 + 3968483 * 2 ^ 59
def prefixEnd_3968483 : Nat := 4983230072969 + 3 ^ 40 * 3968483 * 2
def baseEnd_3968483 : Nat := 2037739248196702025711785

theorem tailTrace_3968483 : CollatzResearch.WordTrace tailWord_3968483 prefixEnd_3968483 2037739248196702025711785 := by
  unfold tailWord_3968483
  simp only [CollatzResearch.WordTrace]
  refine ⟨144742466081871328782046103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96494977387914219188030735 144742466081871328782046103)
  ·
    refine ⟨217113699122806993173069155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144742466081871328782046103 217113699122806993173069155)
    ·
      refine ⟨325670548684210489759603733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 217113699122806993173069155 325670548684210489759603733)
      ·
        refine ⟨15265806969572366707481425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 325670548684210489759603733 15265806969572366707481425)
        ·
          refine ⟨11449355227179275030611069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15265806969572366707481425 11449355227179275030611069)
          ·
            refine ⟨4293508210192228136479151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11449355227179275030611069 4293508210192228136479151)
            ·
              refine ⟨6440262315288342204718727, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4293508210192228136479151 6440262315288342204718727)
              ·
                refine ⟨9660393472932513307078091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6440262315288342204718727 9660393472932513307078091)
                ·
                  refine ⟨14490590209398769960617137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9660393472932513307078091 14490590209398769960617137)
                  ·
                    refine ⟨10867942657049077470462853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14490590209398769960617137 10867942657049077470462853)
                    ·
                      refine ⟨2037739248196702025711785, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10867942657049077470462853 2037739248196702025711785)
                      ·
                        rfl

theorem cell23_3968483_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 3, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 3, 1, 1, 1, 2, 4].length) (baseStart_3968483 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3968483 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3968483 prefixEnd_3968483 := by exact prefixLift 3968483
  have htrace : WordTrace (prefixWord ++ tailWord_3968483) baseStart_3968483 baseEnd_3968483 := by
    simpa [prefixWord, tailWord_3968483, baseEnd_3968483] using wordTrace_append hprefix tailTrace_3968483
  have hstable : (prefixWord ++ tailWord_3968483).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3968483).length < 2 ^ (prefixWord ++ tailWord_3968483).sum := by decide
  have hdescent : baseEnd_3968483 < baseStart_3968483 := by decide
  rcases family_descends (prefixWord ++ tailWord_3968483) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3968490 : List Nat := [3, 1, 3, 1, 4, 1, 2, 2, 1, 2, 3]
def baseStart_3968490 : Nat := 118140960795 + 3968490 * 2 ^ 59
def prefixEnd_3968490 : Nat := 4983230072969 + 3 ^ 40 * 3968490 * 2
def baseEnd_3968490 : Nat := 2037742842561283498324253

theorem tailTrace_3968490 : CollatzResearch.WordTrace tailWord_3968490 prefixEnd_3968490 2037742842561283498324253 := by
  unfold tailWord_3968490
  simp only [CollatzResearch.WordTrace]
  refine ⟨36185680348211492244387731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 96495147595230645985033949 36185680348211492244387731)
  ·
    refine ⟨54278520522317238366581597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36185680348211492244387731 54278520522317238366581597)
    ·
      refine ⟨20354445195868964387468099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 54278520522317238366581597 20354445195868964387468099)
      ·
        refine ⟨30531667793803446581202149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20354445195868964387468099 30531667793803446581202149)
        ·
          refine ⟨5724687711338146233975403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 30531667793803446581202149 5724687711338146233975403)
          ·
            refine ⟨8587031567007219350963105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5724687711338146233975403 8587031567007219350963105)
            ·
              refine ⟨6440273675255414513222329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8587031567007219350963105 6440273675255414513222329)
              ·
                refine ⟨4830205256441560884916747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6440273675255414513222329 4830205256441560884916747)
                ·
                  refine ⟨7245307884662341327375121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4830205256441560884916747 7245307884662341327375121)
                  ·
                    refine ⟨5433980913496755995531341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7245307884662341327375121 5433980913496755995531341)
                    ·
                      refine ⟨2037742842561283498324253, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5433980913496755995531341 2037742842561283498324253)
                      ·
                        rfl

theorem cell23_3968490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 4, 1, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 4, 1, 2, 2, 1, 2, 3].length) (baseStart_3968490 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3968490 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3968490 prefixEnd_3968490 := by exact prefixLift 3968490
  have htrace : WordTrace (prefixWord ++ tailWord_3968490) baseStart_3968490 baseEnd_3968490 := by
    simpa [prefixWord, tailWord_3968490, baseEnd_3968490] using wordTrace_append hprefix tailTrace_3968490
  have hstable : (prefixWord ++ tailWord_3968490).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3968490).length < 2 ^ (prefixWord ++ tailWord_3968490).sum := by decide
  have hdescent : baseEnd_3968490 < baseStart_3968490 := by decide
  rcases family_descends (prefixWord ++ tailWord_3968490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3968510 : List Nat := [4, 2, 2, 3, 2, 1, 9]
def baseStart_3968510 : Nat := 118140960795 + 3968510 * 2 ^ 59
def prefixEnd_3968510 : Nat := 4983230072969 + 3 ^ 40 * 3968510 * 2
def baseEnd_3968510 : Nat := 25157445829313252099681

theorem tailTrace_3968510 : CollatzResearch.WordTrace tailWord_3968510 prefixEnd_3968510 25157445829313252099681 := by
  unfold tailWord_3968510
  simp only [CollatzResearch.WordTrace]
  refine ⟨18092931356596689049159873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 96495633901849008262185989 18092931356596689049159873)
  ·
    refine ⟨13569698517447516786869905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18092931356596689049159873 13569698517447516786869905)
    ·
      refine ⟨10177273888085637590152429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13569698517447516786869905 10177273888085637590152429)
      ·
        refine ⟨3816477708032114096307161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10177273888085637590152429 3816477708032114096307161)
        ·
          refine ⟨2862358281024085572230371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3816477708032114096307161 2862358281024085572230371)
          ·
            refine ⟨4293537421536128358345557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2862358281024085572230371 4293537421536128358345557)
            ·
              refine ⟨25157445829313252099681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 4293537421536128358345557 25157445829313252099681)
              ·
                rfl

theorem cell23_3968510_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 2, 1, 9].length) (baseStart_3968510 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3968510 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3968510 prefixEnd_3968510 := by exact prefixLift 3968510
  have htrace : WordTrace (prefixWord ++ tailWord_3968510) baseStart_3968510 baseEnd_3968510 := by
    simpa [prefixWord, tailWord_3968510, baseEnd_3968510] using wordTrace_append hprefix tailTrace_3968510
  have hstable : (prefixWord ++ tailWord_3968510).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3968510).length < 2 ^ (prefixWord ++ tailWord_3968510).sum := by decide
  have hdescent : baseEnd_3968510 < baseStart_3968510 := by decide
  rcases family_descends (prefixWord ++ tailWord_3968510) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3968529 : List Nat := [1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 5]
def baseStart_3968529 : Nat := 118140960795 + 3968529 * 2 ^ 59
def prefixEnd_3968529 : Nat := 4983230072969 + 3 ^ 40 * 3968529 * 2
def baseEnd_3968529 : Nat := 2037762868306808845736573

theorem tailTrace_3968529 : CollatzResearch.WordTrace tailWord_3968529 prefixEnd_3968529 2037762868306808845736573 := by
  unfold tailWord_3968529
  simp only [CollatzResearch.WordTrace]
  refine ⟨144744143839704678638220641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96496095893136452425480427 144744143839704678638220641)
  ·
    refine ⟨108558107879778508978665481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 144744143839704678638220641 108558107879778508978665481)
    ·
      refine ⟨81418580909833881733999111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 108558107879778508978665481 81418580909833881733999111)
      ·
        refine ⟨122127871364750822600998667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81418580909833881733999111 122127871364750822600998667)
        ·
          refine ⟨183191807047126233901498001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 122127871364750822600998667 183191807047126233901498001)
          ·
            refine ⟨137393855285344675426123501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 183191807047126233901498001 137393855285344675426123501)
            ·
              refine ⟨51522695732004253284796313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 137393855285344675426123501 51522695732004253284796313)
              ·
                refine ⟨38642021799003189963597235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51522695732004253284796313 38642021799003189963597235)
                ·
                  refine ⟨57963032698504784945395853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38642021799003189963597235 57963032698504784945395853)
                  ·
                    refine ⟨21736137261939294354523445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 57963032698504784945395853 21736137261939294354523445)
                    ·
                      refine ⟨2037762868306808845736573, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 21736137261939294354523445 2037762868306808845736573)
                      ·
                        rfl

theorem cell23_3968529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 5].length) (baseStart_3968529 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3968529 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3968529 prefixEnd_3968529 := by exact prefixLift 3968529
  have htrace : WordTrace (prefixWord ++ tailWord_3968529) baseStart_3968529 baseEnd_3968529 := by
    simpa [prefixWord, tailWord_3968529, baseEnd_3968529] using wordTrace_append hprefix tailTrace_3968529
  have hstable : (prefixWord ++ tailWord_3968529).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3968529).length < 2 ^ (prefixWord ++ tailWord_3968529).sum := by decide
  have hdescent : baseEnd_3968529 < baseStart_3968529 := by decide
  rcases family_descends (prefixWord ++ tailWord_3968529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3968546 : List Nat := [3, 3, 1, 1, 1, 1, 3, 2, 2, 1, 5]
def baseStart_3968546 : Nat := 118140960795 + 3968546 * 2 ^ 59
def prefixEnd_3968546 : Nat := 4983230072969 + 3 ^ 40 * 3968546 * 2
def baseEnd_3968546 : Nat := 2037771597477935279223995

theorem tailTrace_3968546 : CollatzResearch.WordTrace tailWord_3968546 prefixEnd_3968546 2037771597477935279223995 := by
  unfold tailWord_3968546
  simp only [CollatzResearch.WordTrace]
  refine ⟨36186190970160772635397373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 96496509253762060361059661 36186190970160772635397373)
  ·
    refine ⟨13569821613810289738274015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36186190970160772635397373 13569821613810289738274015)
    ·
      refine ⟨20354732420715434607411023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13569821613810289738274015 20354732420715434607411023)
      ·
        refine ⟨30532098631073151911116535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20354732420715434607411023 30532098631073151911116535)
        ·
          refine ⟨45798147946609727866674803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30532098631073151911116535 45798147946609727866674803)
          ·
            refine ⟨68697221919914591800012205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45798147946609727866674803 68697221919914591800012205)
            ·
              refine ⟨25761458219967971925004577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 68697221919914591800012205 25761458219967971925004577)
              ·
                refine ⟨19321093664975978943753433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25761458219967971925004577 19321093664975978943753433)
                ·
                  refine ⟨14490820248731984207815075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19321093664975978943753433 14490820248731984207815075)
                  ·
                    refine ⟨21736230373097976311722613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14490820248731984207815075 21736230373097976311722613)
                    ·
                      refine ⟨2037771597477935279223995, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 21736230373097976311722613 2037771597477935279223995)
                      ·
                        rfl

theorem cell23_3968546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 3, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 3, 2, 2, 1, 5].length) (baseStart_3968546 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3968546 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3968546 prefixEnd_3968546 := by exact prefixLift 3968546
  have htrace : WordTrace (prefixWord ++ tailWord_3968546) baseStart_3968546 baseEnd_3968546 := by
    simpa [prefixWord, tailWord_3968546, baseEnd_3968546] using wordTrace_append hprefix tailTrace_3968546
  have hstable : (prefixWord ++ tailWord_3968546).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3968546).length < 2 ^ (prefixWord ++ tailWord_3968546).sum := by decide
  have hdescent : baseEnd_3968546 < baseStart_3968546 := by decide
  rcases family_descends (prefixWord ++ tailWord_3968546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3968547 : List Nat := [1, 1, 1, 4, 5, 2, 1, 2, 1, 3, 2]
def baseStart_3968547 : Nat := 118140960795 + 3968547 * 2 ^ 59
def prefixEnd_3968547 : Nat := 4983230072969 + 3 ^ 40 * 3968547 * 2
def baseEnd_3968547 : Nat := 2037772110958589775311491

theorem tailTrace_3968547 : CollatzResearch.WordTrace tailWord_3968547 prefixEnd_3968547 2037772110958589775311491 := by
  unfold tailWord_3968547
  simp only [CollatzResearch.WordTrace]
  refine ⟨144744800353639467712375895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96496533569092978474917263 144744800353639467712375895)
  ·
    refine ⟨217117200530459201568563843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144744800353639467712375895 217117200530459201568563843)
    ·
      refine ⟨325675800795688802352845765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 217117200530459201568563843 325675800795688802352845765)
      ·
        refine ⟨61064212649191650441158581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 325675800795688802352845765 61064212649191650441158581)
        ·
          refine ⟨5724769935861717228858617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 61064212649191650441158581 5724769935861717228858617)
          ·
            refine ⟨4293577451896287921643963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5724769935861717228858617 4293577451896287921643963)
            ·
              refine ⟨6440366177844431882465945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4293577451896287921643963 6440366177844431882465945)
              ·
                refine ⟨4830274633383323911849459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6440366177844431882465945 4830274633383323911849459)
                ·
                  refine ⟨7245411950074985867774189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4830274633383323911849459 7245411950074985867774189)
                  ·
                    refine ⟨2717029481278119700415321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7245411950074985867774189 2717029481278119700415321)
                    ·
                      refine ⟨2037772110958589775311491, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2717029481278119700415321 2037772110958589775311491)
                      ·
                        rfl

theorem cell23_3968547_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 5, 2, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 5, 2, 1, 2, 1, 3, 2].length) (baseStart_3968547 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3968547 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3968547 prefixEnd_3968547 := by exact prefixLift 3968547
  have htrace : WordTrace (prefixWord ++ tailWord_3968547) baseStart_3968547 baseEnd_3968547 := by
    simpa [prefixWord, tailWord_3968547, baseEnd_3968547] using wordTrace_append hprefix tailTrace_3968547
  have hstable : (prefixWord ++ tailWord_3968547).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3968547).length < 2 ^ (prefixWord ++ tailWord_3968547).sum := by decide
  have hdescent : baseEnd_3968547 < baseStart_3968547 := by decide
  rcases family_descends (prefixWord ++ tailWord_3968547) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3968549 : List Nat := [1, 3, 1, 2, 2, 1, 1, 3, 9]
def baseStart_3968549 : Nat := 118140960795 + 3968549 * 2 ^ 59
def prefixEnd_3968549 : Nat := 4983230072969 + 3 ^ 40 * 3968549 * 2
def baseEnd_3968549 : Nat := 226419237546655418609609

theorem tailTrace_3968549 : CollatzResearch.WordTrace tailWord_3968549 prefixEnd_3968549 226419237546655418609609 := by
  unfold tailWord_3968549
  simp only [CollatzResearch.WordTrace]
  refine ⟨144744873299632222053948701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96496582199754814702632467 144744873299632222053948701)
  ·
    refine ⟨54279327487362083270230763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 144744873299632222053948701 54279327487362083270230763)
    ·
      refine ⟨81418991231043124905346145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54279327487362083270230763 81418991231043124905346145)
      ·
        refine ⟨61064243423282343679009609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81418991231043124905346145 61064243423282343679009609)
        ·
          refine ⟨45798182567461757759257207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61064243423282343679009609 45798182567461757759257207)
          ·
            refine ⟨68697273851192636638885811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45798182567461757759257207 68697273851192636638885811)
            ·
              refine ⟨103045910776788954958328717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68697273851192636638885811 103045910776788954958328717)
              ·
                refine ⟨38642216541295858109373269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 103045910776788954958328717 38642216541295858109373269)
                ·
                  refine ⟨226419237546655418609609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 38642216541295858109373269 226419237546655418609609)
                  ·
                    rfl

theorem cell23_3968549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 1, 3, 9].length) (baseStart_3968549 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3968549 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3968549 prefixEnd_3968549 := by exact prefixLift 3968549
  have htrace : WordTrace (prefixWord ++ tailWord_3968549) baseStart_3968549 baseEnd_3968549 := by
    simpa [prefixWord, tailWord_3968549, baseEnd_3968549] using wordTrace_append hprefix tailTrace_3968549
  have hstable : (prefixWord ++ tailWord_3968549).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3968549).length < 2 ^ (prefixWord ++ tailWord_3968549).sum := by decide
  have hdescent : baseEnd_3968549 < baseStart_3968549 := by decide
  rcases family_descends (prefixWord ++ tailWord_3968549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3968576 : List Nat := [2, 1, 1, 2, 2, 2, 1, 4, 2, 3, 3]
def baseStart_3968576 : Nat := 118140960795 + 3968576 * 2 ^ 59
def prefixEnd_3968576 : Nat := 4983230072969 + 3 ^ 40 * 3968576 * 2
def baseEnd_3968576 : Nat := 2037787001897570161848857

theorem tailTrace_3968576 : CollatzResearch.WordTrace tailWord_3968576 prefixEnd_3968576 2037787001897570161848857 := by
  unfold tailWord_3968576
  simp only [CollatzResearch.WordTrace]
  refine ⟨72372929035267202832590791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96497238713689603776787721 72372929035267202832590791)
  ·
    refine ⟨108559393552900804248886187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72372929035267202832590791 108559393552900804248886187)
    ·
      refine ⟨162839090329351206373329281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108559393552900804248886187 162839090329351206373329281)
      ·
        refine ⟨122129317747013404779996961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 162839090329351206373329281 122129317747013404779996961)
        ·
          refine ⟨91596988310260053584997721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 122129317747013404779996961 91596988310260053584997721)
          ·
            refine ⟨68697741232695040188748291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 91596988310260053584997721 68697741232695040188748291)
            ·
              refine ⟨103046611849042560283122437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68697741232695040188748291 103046611849042560283122437)
              ·
                refine ⟨19321239721695480053085457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 103046611849042560283122437 19321239721695480053085457)
                ·
                  refine ⟨14490929791271610039814093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19321239721695480053085457 14490929791271610039814093)
                  ·
                    refine ⟨5434098671726853764930285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14490929791271610039814093 5434098671726853764930285)
                    ·
                      refine ⟨2037787001897570161848857, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5434098671726853764930285 2037787001897570161848857)
                      ·
                        rfl

theorem cell23_3968576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 1, 4, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 1, 4, 2, 3, 3].length) (baseStart_3968576 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3968576 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3968576 prefixEnd_3968576 := by exact prefixLift 3968576
  have htrace : WordTrace (prefixWord ++ tailWord_3968576) baseStart_3968576 baseEnd_3968576 := by
    simpa [prefixWord, tailWord_3968576, baseEnd_3968576] using wordTrace_append hprefix tailTrace_3968576
  have hstable : (prefixWord ++ tailWord_3968576).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3968576).length < 2 ^ (prefixWord ++ tailWord_3968576).sum := by decide
  have hdescent : baseEnd_3968576 < baseStart_3968576 := by decide
  rcases family_descends (prefixWord ++ tailWord_3968576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3968577 : List Nat := [1, 2, 5, 1, 1, 1, 4, 2, 2, 2, 2]
def baseStart_3968577 : Nat := 118140960795 + 3968577 * 2 ^ 59
def prefixEnd_3968577 : Nat := 4983230072969 + 3 ^ 40 * 3968577 * 2
def baseEnd_3968577 : Nat := 2037787515378224657936353

theorem tailTrace_3968577 : CollatzResearch.WordTrace tailWord_3968577 prefixEnd_3968577 2037787515378224657936353 := by
  unfold tailWord_3968577
  simp only [CollatzResearch.WordTrace]
  refine ⟨144745894543530782835967985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96497263029020521890645323 144745894543530782835967985)
  ·
    refine ⟨108559420907648087126975989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 144745894543530782835967985 108559420907648087126975989)
    ·
      refine ⟨10177445710092008168153999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 108559420907648087126975989 10177445710092008168153999)
      ·
        refine ⟨15266168565138012252230999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10177445710092008168153999 15266168565138012252230999)
        ·
          refine ⟨22899252847707018378346499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15266168565138012252230999 22899252847707018378346499)
          ·
            refine ⟨34348879271560527567519749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22899252847707018378346499 34348879271560527567519749)
            ·
              refine ⟨6440414863417598918909953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 34348879271560527567519749 6440414863417598918909953)
              ·
                refine ⟨4830311147563199189182465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6440414863417598918909953 4830311147563199189182465)
                ·
                  refine ⟨3622733360672399391886849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4830311147563199189182465 3622733360672399391886849)
                  ·
                    refine ⟨2717050020504299543915137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3622733360672399391886849 2717050020504299543915137)
                    ·
                      refine ⟨2037787515378224657936353, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2717050020504299543915137 2037787515378224657936353)
                      ·
                        rfl

theorem cell23_3968577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 4, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 4, 2, 2, 2, 2].length) (baseStart_3968577 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3968577 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3968577 prefixEnd_3968577 := by exact prefixLift 3968577
  have htrace : WordTrace (prefixWord ++ tailWord_3968577) baseStart_3968577 baseEnd_3968577 := by
    simpa [prefixWord, tailWord_3968577, baseEnd_3968577] using wordTrace_append hprefix tailTrace_3968577
  have hstable : (prefixWord ++ tailWord_3968577).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3968577).length < 2 ^ (prefixWord ++ tailWord_3968577).sum := by decide
  have hdescent : baseEnd_3968577 < baseStart_3968577 := by decide
  rcases family_descends (prefixWord ++ tailWord_3968577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3968579 : List Nat := [1, 1, 1, 3, 1, 2, 1, 1, 5, 7]
def baseStart_3968579 : Nat := 118140960795 + 3968579 * 2 ^ 59
def prefixEnd_3968579 : Nat := 4983230072969 + 3 ^ 40 * 3968579 * 2
def baseEnd_3968579 : Nat := 679262847446511216703781

theorem tailTrace_3968579 : CollatzResearch.WordTrace tailWord_3968579 prefixEnd_3968579 679262847446511216703781 := by
  unfold tailWord_3968579
  simp only [CollatzResearch.WordTrace]
  refine ⟨144745967489523537177540791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96497311659682358118360527 144745967489523537177540791)
  ·
    refine ⟨217118951234285305766311187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144745967489523537177540791 217118951234285305766311187)
    ·
      refine ⟨325678426851427958649466781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 217118951234285305766311187 325678426851427958649466781)
      ·
        refine ⟨122129410069285484493550043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 325678426851427958649466781 122129410069285484493550043)
        ·
          refine ⟨183194115103928226740325065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 122129410069285484493550043 183194115103928226740325065)
          ·
            refine ⟨137395586327946170055243799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 183194115103928226740325065 137395586327946170055243799)
            ·
              refine ⟨206093379491919255082865699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 137395586327946170055243799 206093379491919255082865699)
              ·
                refine ⟨309140069237878882624298549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 206093379491919255082865699 309140069237878882624298549)
                ·
                  refine ⟨28981881491051145246027989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 309140069237878882624298549 28981881491051145246027989)
                  ·
                    refine ⟨679262847446511216703781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 28981881491051145246027989 679262847446511216703781)
                    ·
                      rfl

theorem cell23_3968579_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 5, 7].length) (baseStart_3968579 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3968579 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3968579 prefixEnd_3968579 := by exact prefixLift 3968579
  have htrace : WordTrace (prefixWord ++ tailWord_3968579) baseStart_3968579 baseEnd_3968579 := by
    simpa [prefixWord, tailWord_3968579, baseEnd_3968579] using wordTrace_append hprefix tailTrace_3968579
  have hstable : (prefixWord ++ tailWord_3968579).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3968579).length < 2 ^ (prefixWord ++ tailWord_3968579).sum := by decide
  have hdescent : baseEnd_3968579 < baseStart_3968579 := by decide
  rcases family_descends (prefixWord ++ tailWord_3968579) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3968596 : List Nat := [2, 4, 1, 1, 1, 2, 2, 2, 1, 7]
def baseStart_3968596 : Nat := 118140960795 + 3968596 * 2 ^ 59
def prefixEnd_3968596 : Nat := 4983230072969 + 3 ^ 40 * 3968596 * 2
def baseEnd_3968596 : Nat := 679265757170220027866255

theorem tailTrace_3968596 : CollatzResearch.WordTrace tailWord_3968596 prefixEnd_3968596 679265757170220027866255 := by
  unfold tailWord_3968596
  simp only [CollatzResearch.WordTrace]
  refine ⟨72373293765230974540454821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96497725020307966053939761 72373293765230974540454821)
  ·
    refine ⟨13569992580980807726335279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 72373293765230974540454821 13569992580980807726335279)
    ·
      refine ⟨20354988871471211589502919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13569992580980807726335279 20354988871471211589502919)
      ·
        refine ⟨30532483307206817384254379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20354988871471211589502919 30532483307206817384254379)
        ·
          refine ⟨45798724960810226076381569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30532483307206817384254379 45798724960810226076381569)
          ·
            refine ⟨34349043720607669557286177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45798724960810226076381569 34349043720607669557286177)
            ·
              refine ⟨25761782790455752167964633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34349043720607669557286177 25761782790455752167964633)
              ·
                refine ⟨19321337092841814125973475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25761782790455752167964633 19321337092841814125973475)
                ·
                  refine ⟨28982005639262721188960213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19321337092841814125973475 28982005639262721188960213)
                  ·
                    refine ⟨679265757170220027866255, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 28982005639262721188960213 679265757170220027866255)
                    ·
                      rfl

theorem cell23_3968596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 2, 2, 1, 7].length) (baseStart_3968596 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3968596 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3968596 prefixEnd_3968596 := by exact prefixLift 3968596
  have htrace : WordTrace (prefixWord ++ tailWord_3968596) baseStart_3968596 baseEnd_3968596 := by
    simpa [prefixWord, tailWord_3968596, baseEnd_3968596] using wordTrace_append hprefix tailTrace_3968596
  have hstable : (prefixWord ++ tailWord_3968596).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3968596).length < 2 ^ (prefixWord ++ tailWord_3968596).sum := by decide
  have hdescent : baseEnd_3968596 < baseStart_3968596 := by decide
  rcases family_descends (prefixWord ++ tailWord_3968596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3968613 : List Nat := [1, 3, 1, 3, 3, 1, 3, 1, 2, 5]
def baseStart_3968613 : Nat := 118140960795 + 3968613 * 2 ^ 59
def prefixEnd_3968613 : Nat := 4983230072969 + 3 ^ 40 * 3968613 * 2
def baseEnd_3968613 : Nat := 679268666893928839028729

theorem tailTrace_3968613 : CollatzResearch.WordTrace tailWord_3968613 prefixEnd_3968613 679268666893928839028729 := by
  unfold tailWord_3968613
  simp only [CollatzResearch.WordTrace]
  refine ⟨144747207571400360984278493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96498138380933573989518995 144747207571400360984278493)
  ·
    refine ⟨54280202839275135369104435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 144747207571400360984278493 54280202839275135369104435)
    ·
      refine ⟨81420304258912703053656653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54280202839275135369104435 81420304258912703053656653)
      ·
        refine ⟨30532614097092263645121245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 81420304258912703053656653 30532614097092263645121245)
        ·
          refine ⟨11449730286409598866920467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30532614097092263645121245 11449730286409598866920467)
          ·
            refine ⟨17174595429614398300380701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11449730286409598866920467 17174595429614398300380701)
            ·
              refine ⟨6440473286105399362642763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17174595429614398300380701 6440473286105399362642763)
              ·
                refine ⟨9660709929158099043964145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6440473286105399362642763 9660709929158099043964145)
                ·
                  refine ⟨7245532446868574282973109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9660709929158099043964145 7245532446868574282973109)
                  ·
                    refine ⟨679268666893928839028729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7245532446868574282973109 679268666893928839028729)
                    ·
                      rfl

theorem cell23_3968613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 1, 3, 1, 2, 5].length) (baseStart_3968613 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3968613 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3968613 prefixEnd_3968613 := by exact prefixLift 3968613
  have htrace : WordTrace (prefixWord ++ tailWord_3968613) baseStart_3968613 baseEnd_3968613 := by
    simpa [prefixWord, tailWord_3968613, baseEnd_3968613] using wordTrace_append hprefix tailTrace_3968613
  have hstable : (prefixWord ++ tailWord_3968613).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3968613).length < 2 ^ (prefixWord ++ tailWord_3968613).sum := by decide
  have hdescent : baseEnd_3968613 < baseStart_3968613 := by decide
  rcases family_descends (prefixWord ++ tailWord_3968613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3968633 : List Nat := [1, 2, 1, 3, 3, 1, 1, 1, 4, 4, 2]
def baseStart_3968633 : Nat := 118140960795 + 3968633 * 2 ^ 59
def prefixEnd_3968633 : Nat := 4983230072969 + 3 ^ 40 * 3968633 * 2
def baseEnd_3968633 : Nat := 2037816270294876438836095

theorem tailTrace_3968633 : CollatzResearch.WordTrace tailWord_3968633 prefixEnd_3968633 2037816270294876438836095 := by
  unfold tailWord_3968633
  simp only [CollatzResearch.WordTrace]
  refine ⟨144747937031327904400006553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96498624687551936266671035 144747937031327904400006553)
  ·
    refine ⟨108560952773495928300004915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 144747937031327904400006553 108560952773495928300004915)
    ·
      refine ⟨162841429160243892450007373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108560952773495928300004915 162841429160243892450007373)
      ·
        refine ⟨61065535935091459668752765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 162841429160243892450007373 61065535935091459668752765)
        ·
          refine ⟨22899575975659297375782287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 61065535935091459668752765 22899575975659297375782287)
          ·
            refine ⟨34349363963488946063673431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22899575975659297375782287 34349363963488946063673431)
            ·
              refine ⟨51524045945233419095510147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34349363963488946063673431 51524045945233419095510147)
              ·
                refine ⟨77286068917850128643265221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51524045945233419095510147 77286068917850128643265221)
                ·
                  refine ⟨14491137922096899120612229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 77286068917850128643265221 14491137922096899120612229)
                  ·
                    refine ⟨2717088360393168585114793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 14491137922096899120612229 2717088360393168585114793)
                    ·
                      refine ⟨2037816270294876438836095, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2717088360393168585114793 2037816270294876438836095)
                      ·
                        rfl

theorem cell23_3968633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 1, 1, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 1, 1, 4, 4, 2].length) (baseStart_3968633 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3968633 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3968633 prefixEnd_3968633 := by exact prefixLift 3968633
  have htrace : WordTrace (prefixWord ++ tailWord_3968633) baseStart_3968633 baseEnd_3968633 := by
    simpa [prefixWord, tailWord_3968633, baseEnd_3968633] using wordTrace_append hprefix tailTrace_3968633
  have hstable : (prefixWord ++ tailWord_3968633).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3968633).length < 2 ^ (prefixWord ++ tailWord_3968633).sum := by decide
  have hdescent : baseEnd_3968633 < baseStart_3968633 := by decide
  rcases family_descends (prefixWord ++ tailWord_3968633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3968650 : List Nat := [3, 1, 2, 3, 2, 1, 2, 1, 2, 4, 2]
def baseStart_3968650 : Nat := 118140960795 + 3968650 * 2 ^ 59
def prefixEnd_3968650 : Nat := 4983230072969 + 3 ^ 40 * 3968650 * 2
def baseEnd_3968650 : Nat := 2037824999466002872323517

theorem tailTrace_3968650 : CollatzResearch.WordTrace tailWord_3968650 prefixEnd_3968650 2037824999466002872323517 := by
  unfold tailWord_3968650
  simp only [CollatzResearch.WordTrace]
  refine ⟨36187139268066579075843851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 96499038048177544202250269 36187139268066579075843851)
  ·
    refine ⟨54280708902099868613765777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36187139268066579075843851 54280708902099868613765777)
    ·
      refine ⟨40710531676574901460324333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54280708902099868613765777 40710531676574901460324333)
      ·
        refine ⟨15266449378715588047621625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40710531676574901460324333 15266449378715588047621625)
        ·
          refine ⟨11449837034036691035716219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15266449378715588047621625 11449837034036691035716219)
          ·
            refine ⟨17174755551055036553574329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11449837034036691035716219 17174755551055036553574329)
            ·
              refine ⟨12881066663291277415180747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17174755551055036553574329 12881066663291277415180747)
              ·
                refine ⟨19321599994936916122771121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12881066663291277415180747 19321599994936916122771121)
                ·
                  refine ⟨14491199996202687092078341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19321599994936916122771121 14491199996202687092078341)
                  ·
                    refine ⟨2717099999288003829764689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 14491199996202687092078341 2717099999288003829764689)
                    ·
                      refine ⟨2037824999466002872323517, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2717099999288003829764689 2037824999466002872323517)
                      ·
                        rfl

theorem cell23_3968650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 1, 2, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 1, 2, 1, 2, 4, 2].length) (baseStart_3968650 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3968650 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3968650 prefixEnd_3968650 := by exact prefixLift 3968650
  have htrace : WordTrace (prefixWord ++ tailWord_3968650) baseStart_3968650 baseEnd_3968650 := by
    simpa [prefixWord, tailWord_3968650, baseEnd_3968650] using wordTrace_append hprefix tailTrace_3968650
  have hstable : (prefixWord ++ tailWord_3968650).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3968650).length < 2 ^ (prefixWord ++ tailWord_3968650).sum := by decide
  have hdescent : baseEnd_3968650 < baseStart_3968650 := by decide
  rcases family_descends (prefixWord ++ tailWord_3968650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3968656 : List Nat := [2, 1, 1, 1, 1, 1, 3, 7, 6]
def baseStart_3968656 : Nat := 118140960795 + 3968656 * 2 ^ 59
def prefixEnd_3968656 : Nat := 4983230072969 + 3 ^ 40 * 3968656 * 2
def baseEnd_3968656 : Nat := 226425342261103316538721

theorem tailTrace_3968656 : CollatzResearch.WordTrace tailWord_3968656 prefixEnd_3968656 226425342261103316538721 := by
  unfold tailWord_3968656
  simp only [CollatzResearch.WordTrace]
  refine ⟨72374387955122289664046911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96499183940163052885395881 72374387955122289664046911)
  ·
    refine ⟨108561581932683434496070367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72374387955122289664046911 108561581932683434496070367)
    ·
      refine ⟨162842372899025151744105551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108561581932683434496070367 162842372899025151744105551)
      ·
        refine ⟨244263559348537727616158327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 162842372899025151744105551 244263559348537727616158327)
        ·
          refine ⟨366395339022806591424237491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 244263559348537727616158327 366395339022806591424237491)
          ·
            refine ⟨549593008534209887136356237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 366395339022806591424237491 549593008534209887136356237)
            ·
              refine ⟨206097378200328707676133589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 549593008534209887136356237 206097378200328707676133589)
              ·
                refine ⟨4830407301570204086159381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 206097378200328707676133589 4830407301570204086159381)
                ·
                  refine ⟨226425342261103316538721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4830407301570204086159381 226425342261103316538721)
                  ·
                    rfl

theorem cell23_3968656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 3, 7, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 3, 7, 6].length) (baseStart_3968656 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3968656 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3968656 prefixEnd_3968656 := by exact prefixLift 3968656
  have htrace : WordTrace (prefixWord ++ tailWord_3968656) baseStart_3968656 baseEnd_3968656 := by
    simpa [prefixWord, tailWord_3968656, baseEnd_3968656] using wordTrace_append hprefix tailTrace_3968656
  have hstable : (prefixWord ++ tailWord_3968656).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3968656).length < 2 ^ (prefixWord ++ tailWord_3968656).sum := by decide
  have hdescent : baseEnd_3968656 < baseStart_3968656 := by decide
  rcases family_descends (prefixWord ++ tailWord_3968656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3968670 : List Nat := [4, 3, 1, 1, 1, 2, 2, 1, 1, 4, 3]
def baseStart_3968670 : Nat := 118140960795 + 3968670 * 2 ^ 59
def prefixEnd_3968670 : Nat := 4983230072969 + 3 ^ 40 * 3968670 * 2
def baseEnd_3968670 : Nat := 2037835269079092794073425

theorem tailTrace_3968670 : CollatzResearch.WordTrace tailWord_3968670 prefixEnd_3968670 2037835269079092794073425 := by
  unfold tailWord_3968670
  simp only [CollatzResearch.WordTrace]
  refine ⟨18093660816524232464887933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 96499524354795906479402309 18093660816524232464887933)
  ·
    refine ⟨6785122806196587174332975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18093660816524232464887933 6785122806196587174332975)
    ·
      refine ⟨10177684209294880761499463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6785122806196587174332975 10177684209294880761499463)
      ·
        refine ⟨15266526313942321142249195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10177684209294880761499463 15266526313942321142249195)
        ·
          refine ⟨22899789470913481713373793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15266526313942321142249195 22899789470913481713373793)
          ·
            refine ⟨17174842103185111285030345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22899789470913481713373793 17174842103185111285030345)
            ·
              refine ⟨12881131577388833463772759, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17174842103185111285030345 12881131577388833463772759)
              ·
                refine ⟨19321697366083250195659139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12881131577388833463772759 19321697366083250195659139)
                ·
                  refine ⟨28982546049124875293488709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19321697366083250195659139 28982546049124875293488709)
                  ·
                    refine ⟨5434227384210914117529133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28982546049124875293488709 5434227384210914117529133)
                    ·
                      refine ⟨2037835269079092794073425, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5434227384210914117529133 2037835269079092794073425)
                      ·
                        rfl

theorem cell23_3968670_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 2, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 2, 2, 1, 1, 4, 3].length) (baseStart_3968670 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3968670 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3968670 prefixEnd_3968670 := by exact prefixLift 3968670
  have htrace : WordTrace (prefixWord ++ tailWord_3968670) baseStart_3968670 baseEnd_3968670 := by
    simpa [prefixWord, tailWord_3968670, baseEnd_3968670] using wordTrace_append hprefix tailTrace_3968670
  have hstable : (prefixWord ++ tailWord_3968670).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3968670).length < 2 ^ (prefixWord ++ tailWord_3968670).sum := by decide
  have hdescent : baseEnd_3968670 < baseStart_3968670 := by decide
  rcases family_descends (prefixWord ++ tailWord_3968670) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3968694 : List Nat := [5, 1, 3, 1, 1, 3, 1, 1, 3, 4]
def baseStart_3968694 : Nat := 118140960795 + 3968694 * 2 ^ 59
def prefixEnd_3968694 : Nat := 4983230072969 + 3 ^ 40 * 3968694 * 2
def baseEnd_3968694 : Nat := 679282530871600233391105

theorem tailTrace_3968694 : CollatzResearch.WordTrace tailWord_3968694 prefixEnd_3968694 679282530871600233391105 := by
  unfold tailWord_3968694
  simp only [CollatzResearch.WordTrace]
  refine ⟨9046885117756681988623571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 96500107922737941211984757 9046885117756681988623571)
  ·
    refine ⟨13570327676635022982935357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9046885117756681988623571 13570327676635022982935357)
    ·
      refine ⟨5088872878738133618600759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13570327676635022982935357 5088872878738133618600759)
      ·
        refine ⟨7633309318107200427901139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5088872878738133618600759 7633309318107200427901139)
        ·
          refine ⟨11449963977160800641851709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7633309318107200427901139 11449963977160800641851709)
          ·
            refine ⟨4293736491435300240694391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11449963977160800641851709 4293736491435300240694391)
            ·
              refine ⟨6440604737152950361041587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4293736491435300240694391 6440604737152950361041587)
              ·
                refine ⟨9660907105729425541562381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6440604737152950361041587 9660907105729425541562381)
                ·
                  refine ⟨3622840164648534578085893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9660907105729425541562381 3622840164648534578085893)
                  ·
                    refine ⟨679282530871600233391105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3622840164648534578085893 679282530871600233391105)
                    ·
                      rfl

theorem cell23_3968694_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 3, 1, 1, 3, 4].length) (baseStart_3968694 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3968694 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3968694 prefixEnd_3968694 := by exact prefixLift 3968694
  have htrace : WordTrace (prefixWord ++ tailWord_3968694) baseStart_3968694 baseEnd_3968694 := by
    simpa [prefixWord, tailWord_3968694, baseEnd_3968694] using wordTrace_append hprefix tailTrace_3968694
  have hstable : (prefixWord ++ tailWord_3968694).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3968694).length < 2 ^ (prefixWord ++ tailWord_3968694).sum := by decide
  have hdescent : baseEnd_3968694 < baseStart_3968694 := by decide
  rcases family_descends (prefixWord ++ tailWord_3968694) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3968737 : List Nat := [1, 2, 3, 1, 5, 1, 3, 1, 1, 5]
def baseStart_3968737 : Nat := 118140960795 + 3968737 * 2 ^ 59
def prefixEnd_3968737 : Nat := 4983230072969 + 3 ^ 40 * 3968737 * 2
def baseEnd_3968737 : Nat := 679289890760981343978539

theorem tailTrace_3968737 : CollatzResearch.WordTrace tailWord_3968737 prefixEnd_3968737 679289890760981343978539 := by
  unfold tailWord_3968737
  simp only [CollatzResearch.WordTrace]
  refine ⟨144751730222951130161792465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96501153481967420107861643 144751730222951130161792465)
  ·
    refine ⟨108563797667213347621344349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 144751730222951130161792465 108563797667213347621344349)
    ·
      refine ⟨40711424125205005358004131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 108563797667213347621344349 40711424125205005358004131)
      ·
        refine ⟨61067136187807508037006197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40711424125205005358004131 61067136187807508037006197)
        ·
          refine ⟨5725044017606953878469331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 61067136187807508037006197 5725044017606953878469331)
          ·
            refine ⟨8587566026410430817703997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5725044017606953878469331 8587566026410430817703997)
            ·
              refine ⟨3220337259903911556638999, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8587566026410430817703997 3220337259903911556638999)
              ·
                refine ⟨4830505889855867334958499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3220337259903911556638999 4830505889855867334958499)
                ·
                  refine ⟨7245758834783801002437749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4830505889855867334958499 7245758834783801002437749)
                  ·
                    refine ⟨679289890760981343978539, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7245758834783801002437749 679289890760981343978539)
                    ·
                      rfl

theorem cell23_3968737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 5, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 5, 1, 3, 1, 1, 5].length) (baseStart_3968737 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3968737 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3968737 prefixEnd_3968737 := by exact prefixLift 3968737
  have htrace : WordTrace (prefixWord ++ tailWord_3968737) baseStart_3968737 baseEnd_3968737 := by
    simpa [prefixWord, tailWord_3968737, baseEnd_3968737] using wordTrace_append hprefix tailTrace_3968737
  have hstable : (prefixWord ++ tailWord_3968737).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3968737).length < 2 ^ (prefixWord ++ tailWord_3968737).sum := by decide
  have hdescent : baseEnd_3968737 < baseStart_3968737 := by decide
  rcases family_descends (prefixWord ++ tailWord_3968737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3968788 : List Nat := [2, 4, 4, 1, 1, 2, 2, 1, 1, 5]
def baseStart_3968788 : Nat := 118140960795 + 3968788 * 2 ^ 59
def prefixEnd_3968788 : Nat := 4983230072969 + 3 ^ 40 * 3968788 * 2
def baseEnd_3968788 : Nat := 679298619932107777465961

theorem tailTrace_3968788 : CollatzResearch.WordTrace tailWord_3968788 prefixEnd_3968788 679298619932107777465961 := by
  unfold tailWord_3968788
  simp only [CollatzResearch.WordTrace]
  refine ⟨72376795172883182935949509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96502393563844243914599345 72376795172883182935949509)
  ·
    refine ⟨13570649094915596800490533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 72376795172883182935949509 13570649094915596800490533)
    ·
      refine ⟨2544496705296674400091975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 13570649094915596800490533 2544496705296674400091975)
      ·
        refine ⟨3816745057945011600137963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2544496705296674400091975 3816745057945011600137963)
        ·
          refine ⟨5725117586917517400206945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3816745057945011600137963 5725117586917517400206945)
          ·
            refine ⟨4293838190188138050155209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5725117586917517400206945 4293838190188138050155209)
            ·
              refine ⟨3220378642641103537616407, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4293838190188138050155209 3220378642641103537616407)
              ·
                refine ⟨4830567963961655306424611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3220378642641103537616407 4830567963961655306424611)
                ·
                  refine ⟨7245851945942482959636917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4830567963961655306424611 7245851945942482959636917)
                  ·
                    refine ⟨679298619932107777465961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7245851945942482959636917 679298619932107777465961)
                    ·
                      rfl

theorem cell23_3968788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 1, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 1, 2, 2, 1, 1, 5].length) (baseStart_3968788 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3968788 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3968788 prefixEnd_3968788 := by exact prefixLift 3968788
  have htrace : WordTrace (prefixWord ++ tailWord_3968788) baseStart_3968788 baseEnd_3968788 := by
    simpa [prefixWord, tailWord_3968788, baseEnd_3968788] using wordTrace_append hprefix tailTrace_3968788
  have hstable : (prefixWord ++ tailWord_3968788).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3968788).length < 2 ^ (prefixWord ++ tailWord_3968788).sum := by decide
  have hdescent : baseEnd_3968788 < baseStart_3968788 := by decide
  rcases family_descends (prefixWord ++ tailWord_3968788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3968791 : List Nat := [1, 1, 3, 4, 2, 2, 2, 3, 1, 2, 2]
def baseStart_3968791 : Nat := 118140960795 + 3968791 * 2 ^ 59
def prefixEnd_3968791 : Nat := 4983230072969 + 3 ^ 40 * 3968791 * 2
def baseEnd_3968791 : Nat := 2037897400238286820660369

theorem tailTrace_3968791 : CollatzResearch.WordTrace tailWord_3968791 prefixEnd_3968791 2037897400238286820660369 := by
  unfold tailWord_3968791
  simp only [CollatzResearch.WordTrace]
  refine ⟨144753699764755497384258227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96502466509836998256172151 144753699764755497384258227)
  ·
    refine ⟨217130549647133246076387341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144753699764755497384258227 217130549647133246076387341)
    ·
      refine ⟨81423956117674967278645253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 217130549647133246076387341 81423956117674967278645253)
      ·
        refine ⟨15266991772064056364745985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 81423956117674967278645253 15266991772064056364745985)
        ·
          refine ⟨11450243829048042273559489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15266991772064056364745985 11450243829048042273559489)
          ·
            refine ⟨8587682871786031705169617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11450243829048042273559489 8587682871786031705169617)
            ·
              refine ⟨6440762153839523778877213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8587682871786031705169617 6440762153839523778877213)
              ·
                refine ⟨2415285807689821417078955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6440762153839523778877213 2415285807689821417078955)
                ·
                  refine ⟨3622928711534732125618433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2415285807689821417078955 3622928711534732125618433)
                  ·
                    refine ⟨2717196533651049094213825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3622928711534732125618433 2717196533651049094213825)
                    ·
                      refine ⟨2037897400238286820660369, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2717196533651049094213825 2037897400238286820660369)
                      ·
                        rfl

theorem cell23_3968791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 2, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 2, 2, 3, 1, 2, 2].length) (baseStart_3968791 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3968791 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3968791 prefixEnd_3968791 := by exact prefixLift 3968791
  have htrace : WordTrace (prefixWord ++ tailWord_3968791) baseStart_3968791 baseEnd_3968791 := by
    simpa [prefixWord, tailWord_3968791, baseEnd_3968791] using wordTrace_append hprefix tailTrace_3968791
  have hstable : (prefixWord ++ tailWord_3968791).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3968791).length < 2 ^ (prefixWord ++ tailWord_3968791).sum := by decide
  have hdescent : baseEnd_3968791 < baseStart_3968791 := by decide
  rcases family_descends (prefixWord ++ tailWord_3968791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3968794 : List Nat := [3, 1, 1, 3, 2, 4, 2, 1, 1, 2, 3]
def baseStart_3968794 : Nat := 118140960795 + 3968794 * 2 ^ 59
def prefixEnd_3968794 : Nat := 4983230072969 + 3 ^ 40 * 3968794 * 2
def baseEnd_3968794 : Nat := 2037898940680250308922855

theorem tailTrace_3968794 : CollatzResearch.WordTrace tailWord_3968794 prefixEnd_3968794 2037898940680250308922855 := by
  unfold tailWord_3968794
  simp only [CollatzResearch.WordTrace]
  refine ⟨36188452295936157224154359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 96502539455829752597744957 36188452295936157224154359)
  ·
    refine ⟨54282678443904235836231539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36188452295936157224154359 54282678443904235836231539)
    ·
      refine ⟨81424017665856353754347309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54282678443904235836231539 81424017665856353754347309)
      ·
        refine ⟨30534006624696132657880241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 81424017665856353754347309 30534006624696132657880241)
        ·
          refine ⟨22900504968522099493410181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30534006624696132657880241 22900504968522099493410181)
          ·
            refine ⟨4293844681597893655014409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 22900504968522099493410181 4293844681597893655014409)
            ·
              refine ⟨3220383511198420241260807, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4293844681597893655014409 3220383511198420241260807)
              ·
                refine ⟨4830575266797630361891211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3220383511198420241260807 4830575266797630361891211)
                ·
                  refine ⟨7245862900196445542836817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4830575266797630361891211 7245862900196445542836817)
                  ·
                    refine ⟨5434397175147334157127613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7245862900196445542836817 5434397175147334157127613)
                    ·
                      refine ⟨2037898940680250308922855, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5434397175147334157127613 2037898940680250308922855)
                      ·
                        rfl

theorem cell23_3968794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 4, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 4, 2, 1, 1, 2, 3].length) (baseStart_3968794 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3968794 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3968794 prefixEnd_3968794 := by exact prefixLift 3968794
  have htrace : WordTrace (prefixWord ++ tailWord_3968794) baseStart_3968794 baseEnd_3968794 := by
    simpa [prefixWord, tailWord_3968794, baseEnd_3968794] using wordTrace_append hprefix tailTrace_3968794
  have hstable : (prefixWord ++ tailWord_3968794).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3968794).length < 2 ^ (prefixWord ++ tailWord_3968794).sum := by decide
  have hdescent : baseEnd_3968794 < baseStart_3968794 := by decide
  rcases family_descends (prefixWord ++ tailWord_3968794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3968824 : List Nat := [2, 1, 2, 1, 3, 4, 3, 1, 2, 1, 3]
def baseStart_3968824 : Nat := 118140960795 + 3968824 * 2 ^ 59
def prefixEnd_3968824 : Nat := 4983230072969 + 3 ^ 40 * 3968824 * 2
def baseEnd_3968824 : Nat := 2037914345099885191547717

theorem tailTrace_3968824 : CollatzResearch.WordTrace tailWord_3968824 prefixEnd_3968824 2037914345099885191547717 := by
  unfold tailWord_3968824
  simp only [CollatzResearch.WordTrace]
  refine ⟨72377451686817972010104763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96503268915757296013473017 72377451686817972010104763)
  ·
    refine ⟨108566177530226958015157145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72377451686817972010104763 108566177530226958015157145)
    ·
      refine ⟨81424633147670218511367859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 108566177530226958015157145 81424633147670218511367859)
      ·
        refine ⟨122136949721505327767051789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81424633147670218511367859 122136949721505327767051789)
        ·
          refine ⟨45801356145564497912644421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 122136949721505327767051789 45801356145564497912644421)
          ·
            refine ⟨8587754277293343358620829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 45801356145564497912644421 8587754277293343358620829)
            ·
              refine ⟨3220407853985003759482811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8587754277293343358620829 3220407853985003759482811)
              ·
                refine ⟨4830611780977505639224217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3220407853985003759482811 4830611780977505639224217)
                ·
                  refine ⟨3622958835733129229418163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4830611780977505639224217 3622958835733129229418163)
                  ·
                    refine ⟨5434438253599693844127245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3622958835733129229418163 5434438253599693844127245)
                    ·
                      refine ⟨2037914345099885191547717, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5434438253599693844127245 2037914345099885191547717)
                      ·
                        rfl

theorem cell23_3968824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 4, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 4, 3, 1, 2, 1, 3].length) (baseStart_3968824 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3968824 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3968824 prefixEnd_3968824 := by exact prefixLift 3968824
  have htrace : WordTrace (prefixWord ++ tailWord_3968824) baseStart_3968824 baseEnd_3968824 := by
    simpa [prefixWord, tailWord_3968824, baseEnd_3968824] using wordTrace_append hprefix tailTrace_3968824
  have hstable : (prefixWord ++ tailWord_3968824).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3968824).length < 2 ^ (prefixWord ++ tailWord_3968824).sum := by decide
  have hdescent : baseEnd_3968824 < baseStart_3968824 := by decide
  rcases family_descends (prefixWord ++ tailWord_3968824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3968850 : List Nat := [3, 2, 2, 1, 1, 4, 1, 1, 2, 1, 5]
def baseStart_3968850 : Nat := 118140960795 + 3968850 * 2 ^ 59
def prefixEnd_3968850 : Nat := 4983230072969 + 3 ^ 40 * 3968850 * 2
def baseEnd_3968850 : Nat := 2037927695596902089822597

theorem tailTrace_3968850 : CollatzResearch.WordTrace tailWord_3968850 prefixEnd_3968850 2037927695596902089822597 := by
  unfold tailWord_3968850
  simp only [CollatzResearch.WordTrace]
  refine ⟨36188962917885437615164001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 96503901114361166973770669 36188962917885437615164001)
  ·
    refine ⟨27141722188414078211373001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36188962917885437615164001 27141722188414078211373001)
    ·
      refine ⟨20356291641310558658529751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27141722188414078211373001 20356291641310558658529751)
      ·
        refine ⟨30534437461965837987794627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20356291641310558658529751 30534437461965837987794627)
        ·
          refine ⟨45801656192948756981691941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30534437461965837987794627 45801656192948756981691941)
          ·
            refine ⟨8587810536177891934067239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 45801656192948756981691941 8587810536177891934067239)
            ·
              refine ⟨12881715804266837901100859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8587810536177891934067239 12881715804266837901100859)
              ·
                refine ⟨19322573706400256851651289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12881715804266837901100859 19322573706400256851651289)
                ·
                  refine ⟨14491930279800192638738467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19322573706400256851651289 14491930279800192638738467)
                  ·
                    refine ⟨21737895419700288958107701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14491930279800192638738467 21737895419700288958107701)
                    ·
                      refine ⟨2037927695596902089822597, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 21737895419700288958107701 2037927695596902089822597)
                      ·
                        rfl

theorem cell23_3968850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 4, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 4, 1, 1, 2, 1, 5].length) (baseStart_3968850 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3968850 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3968850 prefixEnd_3968850 := by exact prefixLift 3968850
  have htrace : WordTrace (prefixWord ++ tailWord_3968850) baseStart_3968850 baseEnd_3968850 := by
    simpa [prefixWord, tailWord_3968850, baseEnd_3968850] using wordTrace_append hprefix tailTrace_3968850
  have hstable : (prefixWord ++ tailWord_3968850).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3968850).length < 2 ^ (prefixWord ++ tailWord_3968850).sum := by decide
  have hdescent : baseEnd_3968850 < baseStart_3968850 := by decide
  rcases family_descends (prefixWord ++ tailWord_3968850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3968883 : List Nat := [1, 1, 1, 2, 2, 1, 3, 1, 6, 5]
def baseStart_3968883 : Nat := 118140960795 + 3968883 * 2 ^ 59
def prefixEnd_3968883 : Nat := 4983230072969 + 3 ^ 40 * 3968883 * 2
def baseEnd_3968883 : Nat := 679314880152833486903315

theorem tailTrace_3968883 : CollatzResearch.WordTrace tailWord_3968883 prefixEnd_3968883 679314880152833486903315 := by
  unfold tailWord_3968883
  simp only [CollatzResearch.WordTrace]
  refine ⟨144757055280422197096607303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96504703520281464731071535 144757055280422197096607303)
  ·
    refine ⟨217135582920633295644910955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144757055280422197096607303 217135582920633295644910955)
    ·
      refine ⟨325703374380949943467366433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 217135582920633295644910955 325703374380949943467366433)
      ·
        refine ⟨244277530785712457600524825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 325703374380949943467366433 244277530785712457600524825)
        ·
          refine ⟨183208148089284343200393619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 244277530785712457600524825 183208148089284343200393619)
          ·
            refine ⟨274812222133926514800590429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 183208148089284343200393619 274812222133926514800590429)
            ·
              refine ⟨103054583300222443050221411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 274812222133926514800590429 103054583300222443050221411)
              ·
                refine ⟨154581874950333664575332117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 103054583300222443050221411 154581874950333664575332117)
                ·
                  refine ⟨7246025388296890526968693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 154581874950333664575332117 7246025388296890526968693)
                  ·
                    refine ⟨679314880152833486903315, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7246025388296890526968693 679314880152833486903315)
                    ·
                      rfl

theorem cell23_3968883_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 3, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 3, 1, 6, 5].length) (baseStart_3968883 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3968883 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3968883 prefixEnd_3968883 := by exact prefixLift 3968883
  have htrace : WordTrace (prefixWord ++ tailWord_3968883) baseStart_3968883 baseEnd_3968883 := by
    simpa [prefixWord, tailWord_3968883, baseEnd_3968883] using wordTrace_append hprefix tailTrace_3968883
  have hstable : (prefixWord ++ tailWord_3968883).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3968883).length < 2 ^ (prefixWord ++ tailWord_3968883).sum := by decide
  have hdescent : baseEnd_3968883 < baseStart_3968883 := by decide
  rcases family_descends (prefixWord ++ tailWord_3968883) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3968893 : List Nat := [1, 4, 1, 1, 2, 1, 1, 1, 3, 1, 7]
def baseStart_3968893 : Nat := 118140960795 + 3968893 * 2 ^ 59
def prefixEnd_3968893 : Nat := 4983230072969 + 3 ^ 40 * 3968893 * 2
def baseEnd_3968893 : Nat := 2037949775265045421584899

theorem tailTrace_3968893 : CollatzResearch.WordTrace tailWord_3968893 prefixEnd_3968893 2037949775265045421584899 := by
  unfold tailWord_3968893
  simp only [CollatzResearch.WordTrace]
  refine ⟨144757420010385968804471333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96504946673590645869647555 144757420010385968804471333)
  ·
    refine ⟨27142016251947369150838375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 144757420010385968804471333 27142016251947369150838375)
    ·
      refine ⟨40713024377921053726257563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27142016251947369150838375 40713024377921053726257563)
      ·
        refine ⟨61069536566881580589386345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40713024377921053726257563 61069536566881580589386345)
        ·
          refine ⟨45802152425161185442039759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61069536566881580589386345 45802152425161185442039759)
          ·
            refine ⟨68703228637741778163059639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45802152425161185442039759 68703228637741778163059639)
            ·
              refine ⟨103054842956612667244589459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68703228637741778163059639 103054842956612667244589459)
              ·
                refine ⟨154582264434919000866884189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 103054842956612667244589459 154582264434919000866884189)
                ·
                  refine ⟨57968349163094625325081571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 154582264434919000866884189 57968349163094625325081571)
                  ·
                    refine ⟨86952523744641937987622357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 57968349163094625325081571 86952523744641937987622357)
                    ·
                      refine ⟨2037949775265045421584899, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 86952523744641937987622357 2037949775265045421584899)
                      ·
                        rfl

theorem cell23_3968893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 1, 1, 3, 1, 7].length) (baseStart_3968893 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3968893 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3968893 prefixEnd_3968893 := by exact prefixLift 3968893
  have htrace : WordTrace (prefixWord ++ tailWord_3968893) baseStart_3968893 baseEnd_3968893 := by
    simpa [prefixWord, tailWord_3968893, baseEnd_3968893] using wordTrace_append hprefix tailTrace_3968893
  have hstable : (prefixWord ++ tailWord_3968893).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3968893).length < 2 ^ (prefixWord ++ tailWord_3968893).sum := by decide
  have hdescent : baseEnd_3968893 < baseStart_3968893 := by decide
  rcases family_descends (prefixWord ++ tailWord_3968893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3968900 : List Nat := [2, 3, 2, 1, 1, 1, 3, 3, 2, 5]
def baseStart_3968900 : Nat := 118140960795 + 3968900 * 2 ^ 59
def prefixEnd_3968900 : Nat := 4983230072969 + 3 ^ 40 * 3968900 * 2
def baseEnd_3968900 : Nat := 679317789876542298065789

theorem tailTrace_3968900 : CollatzResearch.WordTrace tailWord_3968900 prefixEnd_3968900 679317789876542298065789 := by
  unfold tailWord_3968900
  simp only [CollatzResearch.WordTrace]
  refine ⟨72378837660680304499988077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96505116880907072666650769 72378837660680304499988077)
  ·
    refine ⟨27142064122755114187495529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 72378837660680304499988077 27142064122755114187495529)
    ·
      refine ⟨20356548092066335640621647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27142064122755114187495529 20356548092066335640621647)
      ·
        refine ⟨30534822138099503460932471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20356548092066335640621647 30534822138099503460932471)
        ·
          refine ⟨45802233207149255191398707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30534822138099503460932471 45802233207149255191398707)
          ·
            refine ⟨68703349810723882787098061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45802233207149255191398707 68703349810723882787098061)
            ·
              refine ⟨25763756179021456045161773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 68703349810723882787098061 25763756179021456045161773)
              ·
                refine ⟨9661408567133046016935665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25763756179021456045161773 9661408567133046016935665)
                ·
                  refine ⟨7246056425349784512701749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9661408567133046016935665 7246056425349784512701749)
                  ·
                    refine ⟨679317789876542298065789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7246056425349784512701749 679317789876542298065789)
                    ·
                      rfl

theorem cell23_3968900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 3, 3, 2, 5].length) (baseStart_3968900 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3968900 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3968900 prefixEnd_3968900 := by exact prefixLift 3968900
  have htrace : WordTrace (prefixWord ++ tailWord_3968900) baseStart_3968900 baseEnd_3968900 := by
    simpa [prefixWord, tailWord_3968900, baseEnd_3968900] using wordTrace_append hprefix tailTrace_3968900
  have hstable : (prefixWord ++ tailWord_3968900).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3968900).length < 2 ^ (prefixWord ++ tailWord_3968900).sum := by decide
  have hdescent : baseEnd_3968900 < baseStart_3968900 := by decide
  rcases family_descends (prefixWord ++ tailWord_3968900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3968957 : List Nat := [1, 4, 1, 2, 3, 2, 1, 1, 1, 4, 3]
def baseStart_3968957 : Nat := 118140960795 + 3968957 * 2 ^ 59
def prefixEnd_3968957 : Nat := 4983230072969 + 3 ^ 40 * 3968957 * 2
def baseEnd_3968957 : Nat := 2037982638026933171184605

theorem tailTrace_3968957 : CollatzResearch.WordTrace tailWord_3968957 prefixEnd_3968957 2037982638026933171184605 := by
  unfold tailWord_3968957
  simp only [CollatzResearch.WordTrace]
  refine ⟨144759754282154107734801125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96506502854769405156534083 144759754282154107734801125)
  ·
    refine ⟨27142453927903895200275211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 144759754282154107734801125 27142453927903895200275211)
    ·
      refine ⟨40713680891855842800412817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27142453927903895200275211 40713680891855842800412817)
      ·
        refine ⟨30535260668891882100309613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40713680891855842800412817 30535260668891882100309613)
        ·
          refine ⟨11450722750834455787616105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30535260668891882100309613 11450722750834455787616105)
          ·
            refine ⟨8588042063125841840712079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11450722750834455787616105 8588042063125841840712079)
            ·
              refine ⟨12882063094688762761068119, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8588042063125841840712079 12882063094688762761068119)
              ·
                refine ⟨19323094642033144141602179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12882063094688762761068119 19323094642033144141602179)
                ·
                  refine ⟨28984641963049716212403269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19323094642033144141602179 28984641963049716212403269)
                  ·
                    refine ⟨5434620368071821789825613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28984641963049716212403269 5434620368071821789825613)
                    ·
                      refine ⟨2037982638026933171184605, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5434620368071821789825613 2037982638026933171184605)
                      ·
                        rfl

theorem cell23_3968957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 2, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 2, 1, 1, 1, 4, 3].length) (baseStart_3968957 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3968957 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3968957 prefixEnd_3968957 := by exact prefixLift 3968957
  have htrace : WordTrace (prefixWord ++ tailWord_3968957) baseStart_3968957 baseEnd_3968957 := by
    simpa [prefixWord, tailWord_3968957, baseEnd_3968957] using wordTrace_append hprefix tailTrace_3968957
  have hstable : (prefixWord ++ tailWord_3968957).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3968957).length < 2 ^ (prefixWord ++ tailWord_3968957).sum := by decide
  have hdescent : baseEnd_3968957 < baseStart_3968957 := by decide
  rcases family_descends (prefixWord ++ tailWord_3968957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3968963 : List Nat := [1, 1, 1, 3, 1, 1, 2, 1, 3, 1, 8]
def baseStart_3968963 : Nat := 118140960795 + 3968963 * 2 ^ 59
def prefixEnd_3968963 : Nat := 4983230072969 + 3 ^ 40 * 3968963 * 2
def baseEnd_3968963 : Nat := 2037985718910860147709577

theorem tailTrace_3968963 : CollatzResearch.WordTrace tailWord_3968963 prefixEnd_3968963 2037985718910860147709577 := by
  unfold tailWord_3968963
  simp only [CollatzResearch.WordTrace]
  refine ⟨144759973120132370759519543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96506648746754913839679695 144759973120132370759519543)
  ·
    refine ⟨217139959680198556139279315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144759973120132370759519543 217139959680198556139279315)
    ·
      refine ⟨325709939520297834208918973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 217139959680198556139279315 325709939520297834208918973)
      ·
        refine ⟨122141227320111687828344615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 325709939520297834208918973 122141227320111687828344615)
        ·
          refine ⟨183211840980167531742516923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 122141227320111687828344615 183211840980167531742516923)
          ·
            refine ⟨274817761470251297613775385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 183211840980167531742516923 274817761470251297613775385)
            ·
              refine ⟨206113321102688473210331539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 274817761470251297613775385 206113321102688473210331539)
              ·
                refine ⟨309169981654032709815497309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 206113321102688473210331539 309169981654032709815497309)
                ·
                  refine ⟨115938743120262266180811491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 309169981654032709815497309 115938743120262266180811491)
                  ·
                    refine ⟨173908114680393399271217237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 115938743120262266180811491 173908114680393399271217237)
                    ·
                      refine ⟨2037985718910860147709577, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 173908114680393399271217237 2037985718910860147709577)
                      ·
                        rfl

theorem cell23_3968963_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 1, 3, 1, 8].length) (baseStart_3968963 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3968963 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3968963 prefixEnd_3968963 := by exact prefixLift 3968963
  have htrace : WordTrace (prefixWord ++ tailWord_3968963) baseStart_3968963 baseEnd_3968963 := by
    simpa [prefixWord, tailWord_3968963, baseEnd_3968963] using wordTrace_append hprefix tailTrace_3968963
  have hstable : (prefixWord ++ tailWord_3968963).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3968963).length < 2 ^ (prefixWord ++ tailWord_3968963).sum := by decide
  have hdescent : baseEnd_3968963 < baseStart_3968963 := by decide
  rcases family_descends (prefixWord ++ tailWord_3968963) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3968980 : List Nat := [2, 4, 1, 2, 1, 1, 1, 1, 1, 1, 8]
def baseStart_3968980 : Nat := 118140960795 + 3968980 * 2 ^ 59
def prefixEnd_3968980 : Nat := 4983230072969 + 3 ^ 40 * 3968980 * 2
def baseEnd_3968980 : Nat := 2037994448081986581196999

theorem tailTrace_3968980 : CollatzResearch.WordTrace tailWord_3968980 prefixEnd_3968980 2037994448081986581196999 := by
  unfold tailWord_3968980
  simp only [CollatzResearch.WordTrace]
  refine ⟨72380296580535391331444197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96507062107380521775258929 72380296580535391331444197)
  ·
    refine ⟨13571305608850385874645787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 72380296580535391331444197 13571305608850385874645787)
    ·
      refine ⟨20356958413275578811968681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13571305608850385874645787 20356958413275578811968681)
      ·
        refine ⟨15267718809956684108976511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20356958413275578811968681 15267718809956684108976511)
        ·
          refine ⟨22901578214935026163464767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15267718809956684108976511 22901578214935026163464767)
          ·
            refine ⟨34352367322402539245197151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22901578214935026163464767 34352367322402539245197151)
            ·
              refine ⟨51528550983603808867795727, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34352367322402539245197151 51528550983603808867795727)
              ·
                refine ⟨77292826475405713301693591, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51528550983603808867795727 77292826475405713301693591)
                ·
                  refine ⟨115939239713108569952540387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 77292826475405713301693591 115939239713108569952540387)
                  ·
                    refine ⟨173908859569662854928810581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 115939239713108569952540387 173908859569662854928810581)
                    ·
                      refine ⟨2037994448081986581196999, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 173908859569662854928810581 2037994448081986581196999)
                      ·
                        rfl

theorem cell23_3968980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 1, 1, 1, 1, 8].length) (baseStart_3968980 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3968980 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3968980 prefixEnd_3968980 := by exact prefixLift 3968980
  have htrace : WordTrace (prefixWord ++ tailWord_3968980) baseStart_3968980 baseEnd_3968980 := by
    simpa [prefixWord, tailWord_3968980, baseEnd_3968980] using wordTrace_append hprefix tailTrace_3968980
  have hstable : (prefixWord ++ tailWord_3968980).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3968980).length < 2 ^ (prefixWord ++ tailWord_3968980).sum := by decide
  have hdescent : baseEnd_3968980 < baseStart_3968980 := by decide
  rcases family_descends (prefixWord ++ tailWord_3968980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3969007 : List Nat := [1, 1, 2, 1, 4, 2, 4, 2, 1, 5]
def baseStart_3969007 : Nat := 118140960795 + 3969007 * 2 ^ 59
def prefixEnd_3969007 : Nat := 4983230072969 + 3 ^ 40 * 3969007 * 2
def baseEnd_3969007 : Nat := 679336104019885991853125

theorem tailTrace_3969007 : CollatzResearch.WordTrace tailWord_3969007 prefixEnd_3969007 679336104019885991853125 := by
  unfold tailWord_3969007
  simp only [CollatzResearch.WordTrace]
  refine ⟨144761577931972966274121275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96507718621315310849414183 144761577931972966274121275)
  ·
    refine ⟨217142366897959449411181913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144761577931972966274121275 217142366897959449411181913)
    ·
      refine ⟨162856775173469587058386435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 217142366897959449411181913 162856775173469587058386435)
      ·
        refine ⟨244285162760204380587579653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 162856775173469587058386435 244285162760204380587579653)
        ·
          refine ⟨45803468017538321360171185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 244285162760204380587579653 45803468017538321360171185)
          ·
            refine ⟨34352601013153741020128389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45803468017538321360171185 34352601013153741020128389)
            ·
              refine ⟨6441112689966326441274073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 34352601013153741020128389 6441112689966326441274073)
              ·
                refine ⟨4830834517474744830955555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6441112689966326441274073 4830834517474744830955555)
                ·
                  refine ⟨7246251776212117246433333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4830834517474744830955555 7246251776212117246433333)
                  ·
                    refine ⟨679336104019885991853125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7246251776212117246433333 679336104019885991853125)
                    ·
                      rfl

theorem cell23_3969007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 4, 2, 1, 5].length) (baseStart_3969007 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3969007 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3969007 prefixEnd_3969007 := by exact prefixLift 3969007
  have htrace : WordTrace (prefixWord ++ tailWord_3969007) baseStart_3969007 baseEnd_3969007 := by
    simpa [prefixWord, tailWord_3969007, baseEnd_3969007] using wordTrace_append hprefix tailTrace_3969007
  have hstable : (prefixWord ++ tailWord_3969007).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3969007).length < 2 ^ (prefixWord ++ tailWord_3969007).sum := by decide
  have hdescent : baseEnd_3969007 < baseStart_3969007 := by decide
  rcases family_descends (prefixWord ++ tailWord_3969007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3969020 : List Nat := [2, 2, 2, 1, 2, 2, 2, 1, 3, 6]
def baseStart_3969020 : Nat := 118140960795 + 3969020 * 2 ^ 59
def prefixEnd_3969020 : Nat := 4983230072969 + 3 ^ 40 * 3969020 * 2
def baseEnd_3969020 : Nat := 679338329102722141565605

theorem tailTrace_3969020 : CollatzResearch.WordTrace tailWord_3969020 prefixEnd_3969020 679338329102722141565605 := by
  unfold tailWord_3969020
  simp only [CollatzResearch.WordTrace]
  refine ⟨72381026040462934747172257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96508034720617246329563009 72381026040462934747172257)
  ·
    refine ⟨54285769530347201060379193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72381026040462934747172257 54285769530347201060379193)
    ·
      refine ⟨40714327147760400795284395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54285769530347201060379193 40714327147760400795284395)
      ·
        refine ⟨61071490721640601192926593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40714327147760400795284395 61071490721640601192926593)
        ·
          refine ⟨45803618041230450894694945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61071490721640601192926593 45803618041230450894694945)
          ·
            refine ⟨34352713530922838171021209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45803618041230450894694945 34352713530922838171021209)
            ·
              refine ⟨25764535148192128628265907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34352713530922838171021209 25764535148192128628265907)
              ·
                refine ⟨38646802722288192942398861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25764535148192128628265907 38646802722288192942398861)
                ·
                  refine ⟨14492551020858072353399573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38646802722288192942398861 14492551020858072353399573)
                  ·
                    refine ⟨679338329102722141565605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14492551020858072353399573 679338329102722141565605)
                    ·
                      rfl

theorem cell23_3969020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 2, 1, 3, 6].length) (baseStart_3969020 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3969020 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3969020 prefixEnd_3969020 := by exact prefixLift 3969020
  have htrace : WordTrace (prefixWord ++ tailWord_3969020) baseStart_3969020 baseEnd_3969020 := by
    simpa [prefixWord, tailWord_3969020, baseEnd_3969020] using wordTrace_append hprefix tailTrace_3969020
  have hstable : (prefixWord ++ tailWord_3969020).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3969020).length < 2 ^ (prefixWord ++ tailWord_3969020).sum := by decide
  have hdescent : baseEnd_3969020 < baseStart_3969020 := by decide
  rcases family_descends (prefixWord ++ tailWord_3969020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3969021 : List Nat := [1, 4, 1, 1, 1, 2, 5, 3, 1, 1, 3]
def baseStart_3969021 : Nat := 118140960795 + 3969021 * 2 ^ 59
def prefixEnd_3969021 : Nat := 4983230072969 + 3 ^ 40 * 3969021 * 2
def baseEnd_3969021 : Nat := 2038015500788820920784311

theorem tailTrace_3969021 : CollatzResearch.WordTrace tailWord_3969021 prefixEnd_3969021 2038015500788820920784311 := by
  unfold tailWord_3969021
  simp only [CollatzResearch.WordTrace]
  refine ⟨144762088553922246665130917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96508059035948164443420611 144762088553922246665130917)
  ·
    refine ⟨27142891603860421249712047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 144762088553922246665130917 27142891603860421249712047)
    ·
      refine ⟨40714337405790631874568071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27142891603860421249712047 40714337405790631874568071)
      ·
        refine ⟨61071506108685947811852107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40714337405790631874568071 61071506108685947811852107)
        ·
          refine ⟨91607259163028921717778161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61071506108685947811852107 91607259163028921717778161)
          ·
            refine ⟨68705444372271691288333621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 91607259163028921717778161 68705444372271691288333621)
            ·
              refine ⟨6441135409900471058281277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 68705444372271691288333621 6441135409900471058281277)
              ·
                refine ⟨2415425778712676646855479, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6441135409900471058281277 2415425778712676646855479)
                ·
                  refine ⟨3623138668069014970283219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2415425778712676646855479 3623138668069014970283219)
                  ·
                    refine ⟨5434708002103522455424829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3623138668069014970283219 5434708002103522455424829)
                    ·
                      refine ⟨2038015500788820920784311, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5434708002103522455424829 2038015500788820920784311)
                      ·
                        rfl

theorem cell23_3969021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 5, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 5, 3, 1, 1, 3].length) (baseStart_3969021 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3969021 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3969021 prefixEnd_3969021 := by exact prefixLift 3969021
  have htrace : WordTrace (prefixWord ++ tailWord_3969021) baseStart_3969021 baseEnd_3969021 := by
    simpa [prefixWord, tailWord_3969021, baseEnd_3969021] using wordTrace_append hprefix tailTrace_3969021
  have hstable : (prefixWord ++ tailWord_3969021).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3969021).length < 2 ^ (prefixWord ++ tailWord_3969021).sum := by decide
  have hdescent : baseEnd_3969021 < baseStart_3969021 := by decide
  rcases family_descends (prefixWord ++ tailWord_3969021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3969038 : List Nat := [4, 1, 1, 2, 2, 1, 5, 2, 1, 1, 3]
def baseStart_3969038 : Nat := 118140960795 + 3969038 * 2 ^ 59
def prefixEnd_3969038 : Nat := 4983230072969 + 3 ^ 40 * 3969038 * 2
def baseEnd_3969038 : Nat := 2038024229959947354271733

theorem tailTrace_3969038 : CollatzResearch.WordTrace tailWord_3969038 prefixEnd_3969038 2038024229959947354271733 := by
  unfold tailWord_3969038
  simp only [CollatzResearch.WordTrace]
  refine ⟨18095338574357582321062471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 96508472396573772378999845 18095338574357582321062471)
  ·
    refine ⟨27143007861536373481593707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18095338574357582321062471 27143007861536373481593707)
    ·
      refine ⟨40714511792304560222390561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27143007861536373481593707 40714511792304560222390561)
      ·
        refine ⟨30535883844228420166792921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40714511792304560222390561 30535883844228420166792921)
        ·
          refine ⟨22901912883171315125094691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30535883844228420166792921 22901912883171315125094691)
          ·
            refine ⟨34352869324756972687642037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22901912883171315125094691 34352869324756972687642037)
            ·
              refine ⟨3220581499195966189466441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 34352869324756972687642037 3220581499195966189466441)
              ·
                refine ⟨2415436124396974642099831, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3220581499195966189466441 2415436124396974642099831)
                ·
                  refine ⟨3623154186595461963149747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2415436124396974642099831 3623154186595461963149747)
                  ·
                    refine ⟨5434731279893192944724621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3623154186595461963149747 5434731279893192944724621)
                    ·
                      refine ⟨2038024229959947354271733, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5434731279893192944724621 2038024229959947354271733)
                      ·
                        rfl

theorem cell23_3969038_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 5, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 5, 2, 1, 1, 3].length) (baseStart_3969038 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3969038 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3969038 prefixEnd_3969038 := by exact prefixLift 3969038
  have htrace : WordTrace (prefixWord ++ tailWord_3969038) baseStart_3969038 baseEnd_3969038 := by
    simpa [prefixWord, tailWord_3969038, baseEnd_3969038] using wordTrace_append hprefix tailTrace_3969038
  have hstable : (prefixWord ++ tailWord_3969038).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3969038).length < 2 ^ (prefixWord ++ tailWord_3969038).sum := by decide
  have hdescent : baseEnd_3969038 < baseStart_3969038 := by decide
  rcases family_descends (prefixWord ++ tailWord_3969038) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3969040 : List Nat := [2, 1, 1, 1, 1, 1, 1, 6, 3, 2, 4]
def baseStart_3969040 : Nat := 118140960795 + 3969040 * 2 ^ 59
def prefixEnd_3969040 : Nat := 4983230072969 + 3 ^ 40 * 3969040 * 2
def baseEnd_3969040 : Nat := 2038025256921256346446723

theorem tailTrace_3969040 : CollatzResearch.WordTrace tailWord_3969040 prefixEnd_3969040 2038025256921256346446723 := by
  unfold tailWord_3969040
  simp only [CollatzResearch.WordTrace]
  refine ⟨72381390770426706455036287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96508521027235608606715049 72381390770426706455036287)
  ·
    refine ⟨108572086155640059682554431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72381390770426706455036287 108572086155640059682554431)
    ·
      refine ⟨162858129233460089523831647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108572086155640059682554431 162858129233460089523831647)
      ·
        refine ⟨244287193850190134285747471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 162858129233460089523831647 244287193850190134285747471)
        ·
          refine ⟨366430790775285201428621207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 244287193850190134285747471 366430790775285201428621207)
          ·
            refine ⟨549646186162927802142931811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 366430790775285201428621207 549646186162927802142931811)
            ·
              refine ⟨824469279244391703214397717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 549646186162927802142931811 824469279244391703214397717)
              ·
                refine ⟨38646997464580861088174893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 824469279244391703214397717 38646997464580861088174893)
                ·
                  refine ⟨14492624049217822908065585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38646997464580861088174893 14492624049217822908065585)
                  ·
                    refine ⟨10869468036913367181049189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14492624049217822908065585 10869468036913367181049189)
                    ·
                      refine ⟨2038025256921256346446723, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10869468036913367181049189 2038025256921256346446723)
                      ·
                        rfl

theorem cell23_3969040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 6, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 6, 3, 2, 4].length) (baseStart_3969040 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3969040 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3969040 prefixEnd_3969040 := by exact prefixLift 3969040
  have htrace : WordTrace (prefixWord ++ tailWord_3969040) baseStart_3969040 baseEnd_3969040 := by
    simpa [prefixWord, tailWord_3969040, baseEnd_3969040] using wordTrace_append hprefix tailTrace_3969040
  have hstable : (prefixWord ++ tailWord_3969040).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3969040).length < 2 ^ (prefixWord ++ tailWord_3969040).sum := by decide
  have hdescent : baseEnd_3969040 < baseStart_3969040 := by decide
  rcases family_descends (prefixWord ++ tailWord_3969040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3969050 : List Nat := [3, 1, 1, 3, 1, 3, 1, 10]
def baseStart_3969050 : Nat := 118140960795 + 3969050 * 2 ^ 59
def prefixEnd_3969050 : Nat := 4983230072969 + 3 ^ 40 * 3969050 * 2
def baseEnd_3969050 : Nat := 75482607101029678048951

theorem tailTrace_3969050 : CollatzResearch.WordTrace tailWord_3969050 prefixEnd_3969050 75482607101029678048951 := by
  unfold tailWord_3969050
  simp only [CollatzResearch.WordTrace]
  refine ⟨36190786567704296154484151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 96508764180544789745291069 36190786567704296154484151)
  ·
    refine ⟨54286179851556444231726227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36190786567704296154484151 54286179851556444231726227)
    ·
      refine ⟨81429269777334666347589341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54286179851556444231726227 81429269777334666347589341)
      ·
        refine ⟨30535976166500499880346003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 81429269777334666347589341 30535976166500499880346003)
        ·
          refine ⟨45803964249750749820519005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30535976166500499880346003 45803964249750749820519005)
          ·
            refine ⟨17176486593656531182694627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45803964249750749820519005 17176486593656531182694627)
            ·
              refine ⟨25764729890484796774041941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17176486593656531182694627 25764729890484796774041941)
              ·
                refine ⟨75482607101029678048951, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 25764729890484796774041941 75482607101029678048951)
                ·
                  rfl

theorem cell23_3969050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 3, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 3, 1, 10].length) (baseStart_3969050 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3969050 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3969050 prefixEnd_3969050 := by exact prefixLift 3969050
  have htrace : WordTrace (prefixWord ++ tailWord_3969050) baseStart_3969050 baseEnd_3969050 := by
    simpa [prefixWord, tailWord_3969050, baseEnd_3969050] using wordTrace_append hprefix tailTrace_3969050
  have hstable : (prefixWord ++ tailWord_3969050).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3969050).length < 2 ^ (prefixWord ++ tailWord_3969050).sum := by decide
  have hdescent : baseEnd_3969050 < baseStart_3969050 := by decide
  rcases family_descends (prefixWord ++ tailWord_3969050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3969077 : List Nat := [1, 3, 3, 1, 1, 1, 3, 1, 3, 3, 3]
def baseStart_3969077 : Nat := 118140960795 + 3969077 * 2 ^ 59
def prefixEnd_3969077 : Nat := 4983230072969 + 3 ^ 40 * 3969077 * 2
def baseEnd_3969077 : Nat := 2038044255705472701684053

theorem tailTrace_3969077 : CollatzResearch.WordTrace tailWord_3969077 prefixEnd_3969077 2038044255705472701684053 := by
  unfold tailWord_3969077
  simp only [CollatzResearch.WordTrace]
  refine ⟨144764131041719368229169485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96509420694479578819446323 144764131041719368229169485)
  ·
    refine ⟨54286549140644763085938557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 144764131041719368229169485 54286549140644763085938557)
    ·
      refine ⟨20357455927741786157226959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 54286549140644763085938557 20357455927741786157226959)
      ·
        refine ⟨30536183891612679235840439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20357455927741786157226959 30536183891612679235840439)
        ·
          refine ⟨45804275837419018853760659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30536183891612679235840439 45804275837419018853760659)
          ·
            refine ⟨68706413756128528280640989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45804275837419018853760659 68706413756128528280640989)
            ·
              refine ⟨25764905158548198105240371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 68706413756128528280640989 25764905158548198105240371)
              ·
                refine ⟨38647357737822297157860557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25764905158548198105240371 38647357737822297157860557)
                ·
                  refine ⟨14492759151683361434197709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38647357737822297157860557 14492759151683361434197709)
                  ·
                    refine ⟨5434784681881260537824141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14492759151683361434197709 5434784681881260537824141)
                    ·
                      refine ⟨2038044255705472701684053, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5434784681881260537824141 2038044255705472701684053)
                      ·
                        rfl

theorem cell23_3969077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 3, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 3, 1, 3, 3, 3].length) (baseStart_3969077 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3969077 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3969077 prefixEnd_3969077 := by exact prefixLift 3969077
  have htrace : WordTrace (prefixWord ++ tailWord_3969077) baseStart_3969077 baseEnd_3969077 := by
    simpa [prefixWord, tailWord_3969077, baseEnd_3969077] using wordTrace_append hprefix tailTrace_3969077
  have hstable : (prefixWord ++ tailWord_3969077).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3969077).length < 2 ^ (prefixWord ++ tailWord_3969077).sum := by decide
  have hdescent : baseEnd_3969077 < baseStart_3969077 := by decide
  rcases family_descends (prefixWord ++ tailWord_3969077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3969081 : List Nat := [1, 2, 1, 5, 4, 1, 1, 1, 1, 1, 5]
def baseStart_3969081 : Nat := 118140960795 + 3969081 * 2 ^ 59
def prefixEnd_3969081 : Nat := 4983230072969 + 3 ^ 40 * 3969081 * 2
def baseEnd_3969081 : Nat := 2038046309628090686034035

theorem tailTrace_3969081 : CollatzResearch.WordTrace tailWord_3969081 prefixEnd_3969081 2038046309628090686034035 := by
  unfold tailWord_3969081
  simp only [CollatzResearch.WordTrace]
  refine ⟨144764276933704876912315097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96509517955803251274876731 144764276933704876912315097)
  ·
    refine ⟨108573207700278657684236323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 144764276933704876912315097 108573207700278657684236323)
    ·
      refine ⟨162859811550417986526354485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108573207700278657684236323 162859811550417986526354485)
      ·
        refine ⟨15268107332851686236845733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 162859811550417986526354485 15268107332851686236845733)
        ·
          refine ⟨2862770124909691169408575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15268107332851686236845733 2862770124909691169408575)
          ·
            refine ⟨4294155187364536754112863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2862770124909691169408575 4294155187364536754112863)
            ·
              refine ⟨6441232781046805131169295, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4294155187364536754112863 6441232781046805131169295)
              ·
                refine ⟨9661849171570207696753943, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6441232781046805131169295 9661849171570207696753943)
                ·
                  refine ⟨14492773757355311545130915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9661849171570207696753943 14492773757355311545130915)
                  ·
                    refine ⟨21739160636032967317696373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14492773757355311545130915 21739160636032967317696373)
                    ·
                      refine ⟨2038046309628090686034035, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 21739160636032967317696373 2038046309628090686034035)
                      ·
                        rfl

theorem cell23_3969081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 4, 1, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 4, 1, 1, 1, 1, 1, 5].length) (baseStart_3969081 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3969081 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3969081 prefixEnd_3969081 := by exact prefixLift 3969081
  have htrace : WordTrace (prefixWord ++ tailWord_3969081) baseStart_3969081 baseEnd_3969081 := by
    simpa [prefixWord, tailWord_3969081, baseEnd_3969081] using wordTrace_append hprefix tailTrace_3969081
  have hstable : (prefixWord ++ tailWord_3969081).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3969081).length < 2 ^ (prefixWord ++ tailWord_3969081).sum := by decide
  have hdescent : baseEnd_3969081 < baseStart_3969081 := by decide
  rcases family_descends (prefixWord ++ tailWord_3969081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3969118 : List Nat := [4, 4, 1, 1, 2, 1, 3, 7]
def baseStart_3969118 : Nat := 118140960795 + 3969118 * 2 ^ 59
def prefixEnd_3969118 : Nat := 4983230072969 + 3 ^ 40 * 3969118 * 2
def baseEnd_3969118 : Nat := 75483900311566927454495

theorem tailTrace_3969118 : CollatzResearch.WordTrace tailWord_3969118 prefixEnd_3969118 75483900311566927454495 := by
  unfold tailWord_3969118
  simp only [CollatzResearch.WordTrace]
  refine ⟨18095703304321354028926501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 96510417623047221487608005 18095703304321354028926501)
  ·
    refine ⟨3392944369560253880423719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 18095703304321354028926501 3392944369560253880423719)
    ·
      refine ⟨5089416554340380820635579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3392944369560253880423719 5089416554340380820635579)
      ·
        refine ⟨7634124831510571230953369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5089416554340380820635579 7634124831510571230953369)
        ·
          refine ⟨5725593623632928423215027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7634124831510571230953369 5725593623632928423215027)
          ·
            refine ⟨8588390435449392634822541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5725593623632928423215027 8588390435449392634822541)
            ·
              refine ⟨3220646413293522238058453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8588390435449392634822541 3220646413293522238058453)
              ·
                refine ⟨75483900311566927454495, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3220646413293522238058453 75483900311566927454495)
                ·
                  rfl

theorem cell23_3969118_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 2, 1, 3, 7].length) (baseStart_3969118 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3969118 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3969118 prefixEnd_3969118 := by exact prefixLift 3969118
  have htrace : WordTrace (prefixWord ++ tailWord_3969118) baseStart_3969118 baseEnd_3969118 := by
    simpa [prefixWord, tailWord_3969118, baseEnd_3969118] using wordTrace_append hprefix tailTrace_3969118
  have hstable : (prefixWord ++ tailWord_3969118).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3969118).length < 2 ^ (prefixWord ++ tailWord_3969118).sum := by decide
  have hdescent : baseEnd_3969118 < baseStart_3969118 := by decide
  rcases family_descends (prefixWord ++ tailWord_3969118) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3969138 : List Nat := [3, 2, 1, 2, 2, 2, 4, 1, 1, 3, 2]
def baseStart_3969138 : Nat := 118140960795 + 3969138 * 2 ^ 59
def prefixEnd_3969138 : Nat := 4983230072969 + 3 ^ 40 * 3969138 * 2
def baseEnd_3969138 : Nat := 2038075578025396963021273

theorem tailTrace_3969138 : CollatzResearch.WordTrace tailWord_3969138 prefixEnd_3969138 2038075578025396963021273 := by
  unfold tailWord_3969138
  simp only [CollatzResearch.WordTrace]
  refine ⟨36191588973624593911785017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 96510903929665583764760045 36191588973624593911785017)
  ·
    refine ⟨27143691730218445433838763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36191588973624593911785017 27143691730218445433838763)
    ·
      refine ⟨40715537595327668150758145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27143691730218445433838763 40715537595327668150758145)
      ·
        refine ⟨30536653196495751113068609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40715537595327668150758145 30536653196495751113068609)
        ·
          refine ⟨22902489897371813334801457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30536653196495751113068609 22902489897371813334801457)
          ·
            refine ⟨17176867423028860001101093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22902489897371813334801457 17176867423028860001101093)
            ·
              refine ⟨3220662641817911250206455, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17176867423028860001101093 3220662641817911250206455)
              ·
                refine ⟨4830993962726866875309683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3220662641817911250206455 4830993962726866875309683)
                ·
                  refine ⟨7246490944090300312964525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4830993962726866875309683 7246490944090300312964525)
                  ·
                    refine ⟨2717434104033862617361697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7246490944090300312964525 2717434104033862617361697)
                    ·
                      refine ⟨2038075578025396963021273, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2717434104033862617361697 2038075578025396963021273)
                      ·
                        rfl

theorem cell23_3969138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 2, 4, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 2, 4, 1, 1, 3, 2].length) (baseStart_3969138 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3969138 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3969138 prefixEnd_3969138 := by exact prefixLift 3969138
  have htrace : WordTrace (prefixWord ++ tailWord_3969138) baseStart_3969138 baseEnd_3969138 := by
    simpa [prefixWord, tailWord_3969138, baseEnd_3969138] using wordTrace_append hprefix tailTrace_3969138
  have hstable : (prefixWord ++ tailWord_3969138).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3969138).length < 2 ^ (prefixWord ++ tailWord_3969138).sum := by decide
  have hdescent : baseEnd_3969138 < baseStart_3969138 := by decide
  rcases family_descends (prefixWord ++ tailWord_3969138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3969157 : List Nat := [1, 3, 1, 1, 5, 1, 1, 3, 7]
def baseStart_3969157 : Nat := 118140960795 + 3969157 * 2 ^ 59
def prefixEnd_3969157 : Nat := 4983230072969 + 3 ^ 40 * 3969157 * 2
def baseEnd_3969157 : Nat := 226453926017536932075965

theorem tailTrace_3969157 : CollatzResearch.WordTrace tailWord_3969157 prefixEnd_3969157 226453926017536932075965 := by
  unfold tailWord_3969157
  simp only [CollatzResearch.WordTrace]
  refine ⟨144767048881429541892081725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96511365920953027928054483 144767048881429541892081725)
  ·
    refine ⟨54287643330536078209530647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 144767048881429541892081725 54287643330536078209530647)
    ·
      refine ⟨81431464995804117314295971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54287643330536078209530647 81431464995804117314295971)
      ·
        refine ⟨122147197493706175971443957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81431464995804117314295971 122147197493706175971443957)
        ·
          refine ⟨11451299765034953997322871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 122147197493706175971443957 11451299765034953997322871)
          ·
            refine ⟨17176949647552430995984307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11451299765034953997322871 17176949647552430995984307)
            ·
              refine ⟨25765424471328646493976461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17176949647552430995984307 25765424471328646493976461)
              ·
                refine ⟨9662034176748242435241173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25765424471328646493976461 9662034176748242435241173)
                ·
                  refine ⟨226453926017536932075965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9662034176748242435241173 226453926017536932075965)
                  ·
                    rfl

theorem cell23_3969157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 1, 1, 3, 7].length) (baseStart_3969157 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3969157 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3969157 prefixEnd_3969157 := by exact prefixLift 3969157
  have htrace : WordTrace (prefixWord ++ tailWord_3969157) baseStart_3969157 baseEnd_3969157 := by
    simpa [prefixWord, tailWord_3969157, baseEnd_3969157] using wordTrace_append hprefix tailTrace_3969157
  have hstable : (prefixWord ++ tailWord_3969157).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3969157).length < 2 ^ (prefixWord ++ tailWord_3969157).sum := by decide
  have hdescent : baseEnd_3969157 < baseStart_3969157 := by decide
  rcases family_descends (prefixWord ++ tailWord_3969157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3969168 : List Nat := [2, 1, 1, 1, 1, 1, 9, 1, 2, 2, 2]
def baseStart_3969168 : Nat := 118140960795 + 3969168 * 2 ^ 59
def prefixEnd_3969168 : Nat := 4983230072969 + 3 ^ 40 * 3969168 * 2
def baseEnd_3969168 : Nat := 2038090982445031845646135

theorem tailTrace_3969168 : CollatzResearch.WordTrace tailWord_3969168 prefixEnd_3969168 2038090982445031845646135 := by
  unfold tailWord_3969168
  simp only [CollatzResearch.WordTrace]
  refine ⟨72383725042194845385366079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96511633389593127180488105 72383725042194845385366079)
  ·
    refine ⟨108575587563292268078049119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72383725042194845385366079 108575587563292268078049119)
    ·
      refine ⟨162863381344938402117073679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108575587563292268078049119 162863381344938402117073679)
      ·
        refine ⟨244295072017407603175610519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 162863381344938402117073679 244295072017407603175610519)
        ·
          refine ⟨366442608026111404763415779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 244295072017407603175610519 366442608026111404763415779)
          ·
            refine ⟨549663912039167107145123669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 366442608026111404763415779 549663912039167107145123669)
            ·
              refine ⟨3220686984604494768428459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 549663912039167107145123669 3220686984604494768428459)
              ·
                refine ⟨4831030476906742152642689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3220686984604494768428459 4831030476906742152642689)
                ·
                  refine ⟨3623272857680056614482017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4831030476906742152642689 3623272857680056614482017)
                  ·
                    refine ⟨2717454643260042460861513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3623272857680056614482017 2717454643260042460861513)
                    ·
                      refine ⟨2038090982445031845646135, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2717454643260042460861513 2038090982445031845646135)
                      ·
                        rfl

theorem cell23_3969168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 9, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 9, 1, 2, 2, 2].length) (baseStart_3969168 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3969168 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3969168 prefixEnd_3969168 := by exact prefixLift 3969168
  have htrace : WordTrace (prefixWord ++ tailWord_3969168) baseStart_3969168 baseEnd_3969168 := by
    simpa [prefixWord, tailWord_3969168, baseEnd_3969168] using wordTrace_append hprefix tailTrace_3969168
  have hstable : (prefixWord ++ tailWord_3969168).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3969168).length < 2 ^ (prefixWord ++ tailWord_3969168).sum := by decide
  have hdescent : baseEnd_3969168 < baseStart_3969168 := by decide
  rcases family_descends (prefixWord ++ tailWord_3969168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3969224 : List Nat := [2, 1, 3, 1, 2, 1, 1, 3, 1, 6, 2]
def baseStart_3969224 : Nat := 118140960795 + 3969224 * 2 ^ 59
def prefixEnd_3969224 : Nat := 4983230072969 + 3 ^ 40 * 3969224 * 2
def baseEnd_3969224 : Nat := 2038119737361683626545877

theorem tailTrace_3969224 : CollatzResearch.WordTrace tailWord_3969224 prefixEnd_3969224 2038119737361683626545877 := by
  unfold tailWord_3969224
  simp only [CollatzResearch.WordTrace]
  refine ⟨72384746286093406167385363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96512995048124541556513817 72384746286093406167385363)
  ·
    refine ⟨108577119429140109251078045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72384746286093406167385363 108577119429140109251078045)
    ·
      refine ⟨40716419785927540969154267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 108577119429140109251078045 40716419785927540969154267)
      ·
        refine ⟨61074629678891311453731401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40716419785927540969154267 61074629678891311453731401)
        ·
          refine ⟨45805972259168483590298551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61074629678891311453731401 45805972259168483590298551)
          ·
            refine ⟨68708958388752725385447827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45805972259168483590298551 68708958388752725385447827)
            ·
              refine ⟨103063437583129088078171741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68708958388752725385447827 103063437583129088078171741)
              ·
                refine ⟨38648789093673408029314403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 103063437583129088078171741 38648789093673408029314403)
                ·
                  refine ⟨57973183640510112043971605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38648789093673408029314403 57973183640510112043971605)
                  ·
                    refine ⟨2717492983148911502061169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 57973183640510112043971605 2717492983148911502061169)
                    ·
                      refine ⟨2038119737361683626545877, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2717492983148911502061169 2038119737361683626545877)
                      ·
                        rfl

theorem cell23_3969224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 1, 3, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 1, 3, 1, 6, 2].length) (baseStart_3969224 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3969224 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3969224 prefixEnd_3969224 := by exact prefixLift 3969224
  have htrace : WordTrace (prefixWord ++ tailWord_3969224) baseStart_3969224 baseEnd_3969224 := by
    simpa [prefixWord, tailWord_3969224, baseEnd_3969224] using wordTrace_append hprefix tailTrace_3969224
  have hstable : (prefixWord ++ tailWord_3969224).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3969224).length < 2 ^ (prefixWord ++ tailWord_3969224).sum := by decide
  have hdescent : baseEnd_3969224 < baseStart_3969224 := by decide
  rcases family_descends (prefixWord ++ tailWord_3969224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3969238 : List Nat := [5, 2, 1, 2, 1, 2, 2, 1, 2, 5]
def baseStart_3969238 : Nat := 118140960795 + 3969238 * 2 ^ 59
def prefixEnd_3969238 : Nat := 4983230072969 + 3 ^ 40 * 3969238 * 2
def baseEnd_3969238 : Nat := 679375642030282190590271

theorem tailTrace_3969238 : CollatzResearch.WordTrace tailWord_3969238 prefixEnd_3969238 679375642030282190590271 := by
  unfold tailWord_3969238
  simp only [CollatzResearch.WordTrace]
  refine ⟨9048125199633505795361273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 96513335462757395150520245 9048125199633505795361273)
  ·
    refine ⟨6786093899725129346520955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9048125199633505795361273 6786093899725129346520955)
    ·
      refine ⟨10179140849587694019781433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6786093899725129346520955 10179140849587694019781433)
      ·
        refine ⟨7634355637190770514836075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10179140849587694019781433 7634355637190770514836075)
        ·
          refine ⟨11451533455786155772254113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7634355637190770514836075 11451533455786155772254113)
          ·
            refine ⟨8588650091839616829190585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11451533455786155772254113 8588650091839616829190585)
            ·
              refine ⟨6441487568879712621892939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8588650091839616829190585 6441487568879712621892939)
              ·
                refine ⟨9662231353319568932839409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6441487568879712621892939 9662231353319568932839409)
                ·
                  refine ⟨7246673514989676699629557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9662231353319568932839409 7246673514989676699629557)
                  ·
                    refine ⟨679375642030282190590271, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7246673514989676699629557 679375642030282190590271)
                    ·
                      rfl

theorem cell23_3969238_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 2, 2, 1, 2, 5].length) (baseStart_3969238 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3969238 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3969238 prefixEnd_3969238 := by exact prefixLift 3969238
  have htrace : WordTrace (prefixWord ++ tailWord_3969238) baseStart_3969238 baseEnd_3969238 := by
    simpa [prefixWord, tailWord_3969238, baseEnd_3969238] using wordTrace_append hprefix tailTrace_3969238
  have hstable : (prefixWord ++ tailWord_3969238).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3969238).length < 2 ^ (prefixWord ++ tailWord_3969238).sum := by decide
  have hdescent : baseEnd_3969238 < baseStart_3969238 := by decide
  rcases family_descends (prefixWord ++ tailWord_3969238) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3969267 : List Nat := [1, 1, 1, 2, 2, 4, 2, 1, 1, 2, 6]
def baseStart_3969267 : Nat := 118140960795 + 3969267 * 2 ^ 59
def prefixEnd_3969267 : Nat := 4983230072969 + 3 ^ 40 * 3969267 * 2
def baseEnd_3969267 : Nat := 2038141817029826958308179

theorem tailTrace_3969267 : CollatzResearch.WordTrace tailWord_3969267 prefixEnd_3969267 2038141817029826958308179 := by
  unfold tailWord_3969267
  simp only [CollatzResearch.WordTrace]
  refine ⟨144771060911031030678586055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96514040607354020452390703 144771060911031030678586055)
  ·
    refine ⟨217156591366546546017879083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144771060911031030678586055 217156591366546546017879083)
    ·
      refine ⟨325734887049819819026818625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 217156591366546546017879083 325734887049819819026818625)
      ·
        refine ⟨244301165287364864270113969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 325734887049819819026818625 244301165287364864270113969)
        ·
          refine ⟨183225873965523648202585477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 244301165287364864270113969 183225873965523648202585477)
          ·
            refine ⟨34354851368535684037984777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 183225873965523648202585477 34354851368535684037984777)
            ·
              refine ⟨25766138526401763028488583, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34354851368535684037984777 25766138526401763028488583)
              ·
                refine ⟨38649207789602644542732875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25766138526401763028488583 38649207789602644542732875)
                ·
                  refine ⟨57973811684403966814099313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38649207789602644542732875 57973811684403966814099313)
                  ·
                    refine ⟨43480358763302975110574485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 57973811684403966814099313 43480358763302975110574485)
                    ·
                      refine ⟨2038141817029826958308179, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 43480358763302975110574485 2038141817029826958308179)
                      ·
                        rfl

theorem cell23_3969267_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 2, 1, 1, 2, 6].length) (baseStart_3969267 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3969267 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3969267 prefixEnd_3969267 := by exact prefixLift 3969267
  have htrace : WordTrace (prefixWord ++ tailWord_3969267) baseStart_3969267 baseEnd_3969267 := by
    simpa [prefixWord, tailWord_3969267, baseEnd_3969267] using wordTrace_append hprefix tailTrace_3969267
  have hstable : (prefixWord ++ tailWord_3969267).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3969267).length < 2 ^ (prefixWord ++ tailWord_3969267).sum := by decide
  have hdescent : baseEnd_3969267 < baseStart_3969267 := by decide
  rcases family_descends (prefixWord ++ tailWord_3969267) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3969291 : List Nat := [1, 1, 1, 1, 5, 2, 3, 2, 3, 1, 3]
def baseStart_3969291 : Nat := 118140960795 + 3969291 * 2 ^ 59
def prefixEnd_3969291 : Nat := 4983230072969 + 3 ^ 40 * 3969291 * 2
def baseEnd_3969291 : Nat := 2038154140565534864408069

theorem tailTrace_3969291 : CollatzResearch.WordTrace tailWord_3969291 prefixEnd_3969291 2038154140565534864408069 := by
  unfold tailWord_3969291
  simp only [CollatzResearch.WordTrace]
  refine ⟨144771936262944082777459727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96514624175296055184973151 144771936262944082777459727)
  ·
    refine ⟨217157904394416124166189591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144771936262944082777459727 217157904394416124166189591)
    ·
      refine ⟨325736856591624186249284387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 217157904394416124166189591 325736856591624186249284387)
      ·
        refine ⟨488605284887436279373926581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 325736856591624186249284387 488605284887436279373926581)
        ·
          refine ⟨45806745458197151191305617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 488605284887436279373926581 45806745458197151191305617)
          ·
            refine ⟨34355059093647863393479213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45806745458197151191305617 34355059093647863393479213)
            ·
              refine ⟨12883147160117948772554705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34355059093647863393479213 12883147160117948772554705)
              ·
                refine ⟨9662360370088461579416029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12883147160117948772554705 9662360370088461579416029)
                ·
                  refine ⟨3623385138783173092281011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9662360370088461579416029 3623385138783173092281011)
                  ·
                    refine ⟨5435077708174759638421517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3623385138783173092281011 5435077708174759638421517)
                    ·
                      refine ⟨2038154140565534864408069, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5435077708174759638421517 2038154140565534864408069)
                      ·
                        rfl

theorem cell23_3969291_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 3, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 3, 2, 3, 1, 3].length) (baseStart_3969291 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3969291 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3969291 prefixEnd_3969291 := by exact prefixLift 3969291
  have htrace : WordTrace (prefixWord ++ tailWord_3969291) baseStart_3969291 baseEnd_3969291 := by
    simpa [prefixWord, tailWord_3969291, baseEnd_3969291] using wordTrace_append hprefix tailTrace_3969291
  have hstable : (prefixWord ++ tailWord_3969291).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3969291).length < 2 ^ (prefixWord ++ tailWord_3969291).sum := by decide
  have hdescent : baseEnd_3969291 < baseStart_3969291 := by decide
  rcases family_descends (prefixWord ++ tailWord_3969291) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3969294 : List Nat := [4, 1, 1, 2, 1, 2, 1, 3, 3, 5]
def baseStart_3969294 : Nat := 118140960795 + 3969294 * 2 ^ 59
def prefixEnd_3969294 : Nat := 4983230072969 + 3 ^ 40 * 3969294 * 2
def baseEnd_3969294 : Nat := 679385227002499450890185

theorem tailTrace_3969294 : CollatzResearch.WordTrace tailWord_3969294 prefixEnd_3969294 679385227002499450890185 := by
  unfold tailWord_3969294
  simp only [CollatzResearch.WordTrace]
  refine ⟨18096505710241651786227367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 96514697121288809526545957 18096505710241651786227367)
  ·
    refine ⟨27144758565362477679341051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18096505710241651786227367 27144758565362477679341051)
    ·
      refine ⟨40717137848043716519011577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27144758565362477679341051 40717137848043716519011577)
      ·
        refine ⟨30537853386032787389258683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40717137848043716519011577 30537853386032787389258683)
        ·
          refine ⟨45806780079049181083888025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30537853386032787389258683 45806780079049181083888025)
          ·
            refine ⟨34355085059286885812916019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45806780079049181083888025 34355085059286885812916019)
            ·
              refine ⟨51532627588930328719374029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34355085059286885812916019 51532627588930328719374029)
              ·
                refine ⟨19324735345848873269765261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 51532627588930328719374029 19324735345848873269765261)
                ·
                  refine ⟨7246775754693327476161973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19324735345848873269765261 7246775754693327476161973)
                  ·
                    refine ⟨679385227002499450890185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7246775754693327476161973 679385227002499450890185)
                    ·
                      rfl

theorem cell23_3969294_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 1, 3, 3, 5].length) (baseStart_3969294 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3969294 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3969294 prefixEnd_3969294 := by exact prefixLift 3969294
  have htrace : WordTrace (prefixWord ++ tailWord_3969294) baseStart_3969294 baseEnd_3969294 := by
    simpa [prefixWord, tailWord_3969294, baseEnd_3969294] using wordTrace_append hprefix tailTrace_3969294
  have hstable : (prefixWord ++ tailWord_3969294).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3969294).length < 2 ^ (prefixWord ++ tailWord_3969294).sum := by decide
  have hdescent : baseEnd_3969294 < baseStart_3969294 := by decide
  rcases family_descends (prefixWord ++ tailWord_3969294) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3969311 : List Nat := [1, 1, 2, 4, 3, 2, 1, 3, 1, 5]
def baseStart_3969311 : Nat := 118140960795 + 3969311 * 2 ^ 59
def prefixEnd_3969311 : Nat := 4983230072969 + 3 ^ 40 * 3969311 * 2
def baseEnd_3969311 : Nat := 679388136726208262052659

theorem tailTrace_3969311 : CollatzResearch.WordTrace tailWord_3969311 prefixEnd_3969311 679388136726208262052659 := by
  unfold tailWord_3969311
  simp only [CollatzResearch.WordTrace]
  refine ⟨144772665722871626193187787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96515110481914417462125191 144772665722871626193187787)
  ·
    refine ⟨217158998584307439289781681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144772665722871626193187787 217158998584307439289781681)
    ·
      refine ⟨162869248938230579467336261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 217158998584307439289781681 162869248938230579467336261)
      ·
        refine ⟨30537984175918233650125549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 162869248938230579467336261 30537984175918233650125549)
        ·
          refine ⟨11451744065969337618797081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30537984175918233650125549 11451744065969337618797081)
          ·
            refine ⟨8588808049477003214097811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11451744065969337618797081 8588808049477003214097811)
            ·
              refine ⟨12883212074215504821146717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8588808049477003214097811 12883212074215504821146717)
              ·
                refine ⟨4831204527830814307930019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12883212074215504821146717 4831204527830814307930019)
                ·
                  refine ⟨7246806791746221461895029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4831204527830814307930019 7246806791746221461895029)
                  ·
                    refine ⟨679388136726208262052659, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7246806791746221461895029 679388136726208262052659)
                    ·
                      rfl

theorem cell23_3969311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 2, 1, 3, 1, 5].length) (baseStart_3969311 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3969311 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3969311 prefixEnd_3969311 := by exact prefixLift 3969311
  have htrace : WordTrace (prefixWord ++ tailWord_3969311) baseStart_3969311 baseEnd_3969311 := by
    simpa [prefixWord, tailWord_3969311, baseEnd_3969311] using wordTrace_append hprefix tailTrace_3969311
  have hstable : (prefixWord ++ tailWord_3969311).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3969311).length < 2 ^ (prefixWord ++ tailWord_3969311).sum := by decide
  have hdescent : baseEnd_3969311 < baseStart_3969311 := by decide
  rcases family_descends (prefixWord ++ tailWord_3969311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3969344 : List Nat := [2, 1, 1, 2, 2, 1, 2, 5, 1, 2, 4]
def baseStart_3969344 : Nat := 118140960795 + 3969344 * 2 ^ 59
def prefixEnd_3969344 : Nat := 4983230072969 + 3 ^ 40 * 3969344 * 2
def baseEnd_3969344 : Nat := 2038181355040223157045325

theorem tailTrace_3969344 : CollatzResearch.WordTrace tailWord_3969344 prefixEnd_3969344 2038181355040223157045325 := by
  unfold tailWord_3969344
  simp only [CollatzResearch.WordTrace]
  refine ⟨72386934665876036414569543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96515912887834715219426057 72386934665876036414569543)
  ·
    refine ⟨108580401998814054621854315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72386934665876036414569543 108580401998814054621854315)
    ·
      refine ⟨162870602998221081932781473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108580401998814054621854315 162870602998221081932781473)
      ·
        refine ⟨122152952248665811449586105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 162870602998221081932781473 122152952248665811449586105)
        ·
          refine ⟨91614714186499358587189579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 122152952248665811449586105 91614714186499358587189579)
          ·
            refine ⟨137422071279749037880784369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91614714186499358587189579 137422071279749037880784369)
            ·
              refine ⟨103066553459811778410588277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 137422071279749037880784369 103066553459811778410588277)
              ·
                refine ⟨9662489386857354225992651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 103066553459811778410588277 9662489386857354225992651)
                ·
                  refine ⟨14493734080286031338988977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9662489386857354225992651 14493734080286031338988977)
                  ·
                    refine ⟨10870300560214523504241733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14493734080286031338988977 10870300560214523504241733)
                    ·
                      refine ⟨2038181355040223157045325, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10870300560214523504241733 2038181355040223157045325)
                      ·
                        rfl

theorem cell23_3969344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 2, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 2, 5, 1, 2, 4].length) (baseStart_3969344 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3969344 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3969344 prefixEnd_3969344 := by exact prefixLift 3969344
  have htrace : WordTrace (prefixWord ++ tailWord_3969344) baseStart_3969344 baseEnd_3969344 := by
    simpa [prefixWord, tailWord_3969344, baseEnd_3969344] using wordTrace_append hprefix tailTrace_3969344
  have hstable : (prefixWord ++ tailWord_3969344).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3969344).length < 2 ^ (prefixWord ++ tailWord_3969344).sum := by decide
  have hdescent : baseEnd_3969344 < baseStart_3969344 := by decide
  rcases family_descends (prefixWord ++ tailWord_3969344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3969404 : List Nat := [2, 2, 2, 1, 1, 1, 2, 1, 4, 3, 4]
def baseStart_3969404 : Nat := 118140960795 + 3969404 * 2 ^ 59
def prefixEnd_3969404 : Nat := 4983230072969 + 3 ^ 40 * 3969404 * 2
def baseEnd_3969404 : Nat := 2038212163879492922295049

theorem tailTrace_3969404 : CollatzResearch.WordTrace tailWord_3969404 prefixEnd_3969404 2038212163879492922295049 := by
  unfold tailWord_3969404
  simp only [CollatzResearch.WordTrace]
  refine ⟨72388028855767351538161633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96517371807689802050882177 72388028855767351538161633)
  ·
    refine ⟨54291021641825513653621225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72388028855767351538161633 54291021641825513653621225)
    ·
      refine ⟨40718266231369135240215919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54291021641825513653621225 40718266231369135240215919)
      ·
        refine ⟨61077399347053702860323879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40718266231369135240215919 61077399347053702860323879)
        ·
          refine ⟨91616099020580554290485819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61077399347053702860323879 91616099020580554290485819)
          ·
            refine ⟨137424148530870831435728729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91616099020580554290485819 137424148530870831435728729)
            ·
              refine ⟨103068111398153123576796547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 137424148530870831435728729 103068111398153123576796547)
              ·
                refine ⟨154602167097229685365194821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 103068111398153123576796547 154602167097229685365194821)
                ·
                  refine ⟨28987906330730566005974029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 154602167097229685365194821 28987906330730566005974029)
                  ·
                    refine ⟨10870464874023962252240261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 28987906330730566005974029 10870464874023962252240261)
                    ·
                      refine ⟨2038212163879492922295049, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10870464874023962252240261 2038212163879492922295049)
                      ·
                        rfl

theorem cell23_3969404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 2, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 2, 1, 4, 3, 4].length) (baseStart_3969404 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3969404 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3969404 prefixEnd_3969404 := by exact prefixLift 3969404
  have htrace : WordTrace (prefixWord ++ tailWord_3969404) baseStart_3969404 baseEnd_3969404 := by
    simpa [prefixWord, tailWord_3969404, baseEnd_3969404] using wordTrace_append hprefix tailTrace_3969404
  have hstable : (prefixWord ++ tailWord_3969404).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3969404).length < 2 ^ (prefixWord ++ tailWord_3969404).sum := by decide
  have hdescent : baseEnd_3969404 < baseStart_3969404 := by decide
  rcases family_descends (prefixWord ++ tailWord_3969404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3969438 : List Nat := [4, 3, 1, 2, 1, 1, 1, 1, 2, 3, 4]
def baseStart_3969438 : Nat := 118140960795 + 3969438 * 2 ^ 59
def prefixEnd_3969438 : Nat := 4983230072969 + 3 ^ 40 * 3969438 * 2
def baseEnd_3969438 : Nat := 2038229622221745789269893

theorem tailTrace_3969438 : CollatzResearch.WordTrace tailWord_3969438 prefixEnd_3969438 2038229622221745789269893 := by
  unfold tailWord_3969438
  simp only [CollatzResearch.WordTrace]
  refine ⟨18097162224176440860382621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 96518198528941017922040645 18097162224176440860382621)
  ·
    refine ⟨6786435834066165322643483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18097162224176440860382621 6786435834066165322643483)
    ·
      refine ⟨10179653751099247983965225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6786435834066165322643483 10179653751099247983965225)
      ·
        refine ⟨7634740313324435987973919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10179653751099247983965225 7634740313324435987973919)
        ·
          refine ⟨11452110469986653981960879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7634740313324435987973919 11452110469986653981960879)
          ·
            refine ⟨17178165704979980972941319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11452110469986653981960879 17178165704979980972941319)
            ·
              refine ⟨25767248557469971459411979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17178165704979980972941319 25767248557469971459411979)
              ·
                refine ⟨38650872836204957189117969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25767248557469971459411979 38650872836204957189117969)
                ·
                  refine ⟨28988154627153717891838477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38650872836204957189117969 28988154627153717891838477)
                  ·
                    refine ⟨10870557985182644209439429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 28988154627153717891838477 10870557985182644209439429)
                    ·
                      refine ⟨2038229622221745789269893, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10870557985182644209439429 2038229622221745789269893)
                      ·
                        rfl

theorem cell23_3969438_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 1, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 1, 1, 1, 2, 3, 4].length) (baseStart_3969438 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3969438 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3969438 prefixEnd_3969438 := by exact prefixLift 3969438
  have htrace : WordTrace (prefixWord ++ tailWord_3969438) baseStart_3969438 baseEnd_3969438 := by
    simpa [prefixWord, tailWord_3969438, baseEnd_3969438] using wordTrace_append hprefix tailTrace_3969438
  have hstable : (prefixWord ++ tailWord_3969438).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3969438).length < 2 ^ (prefixWord ++ tailWord_3969438).sum := by decide
  have hdescent : baseEnd_3969438 < baseStart_3969438 := by decide
  rcases family_descends (prefixWord ++ tailWord_3969438) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3969448 : List Nat := [2, 1, 6, 1, 1, 2, 1, 1, 2, 6]
def baseStart_3969448 : Nat := 118140960795 + 3969448 * 2 ^ 59
def prefixEnd_3969448 : Nat := 4983230072969 + 3 ^ 40 * 3969448 * 2
def baseEnd_3969448 : Nat := 679411585676096916714949

theorem tailTrace_3969448 : CollatzResearch.WordTrace tailWord_3969448 prefixEnd_3969448 679411585676096916714949 := by
  unfold tailWord_3969448
  simp only [CollatzResearch.WordTrace]
  refine ⟨72388831261687649295462499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96518441682250199060616665 72388831261687649295462499)
  ·
    refine ⟨108583246892531473943193749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72388831261687649295462499 108583246892531473943193749)
    ·
      refine ⟨5089839698087412841087207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 108583246892531473943193749 5089839698087412841087207)
      ·
        refine ⟨7634759547131119261630811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5089839698087412841087207 7634759547131119261630811)
        ·
          refine ⟨11452139320696678892446217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7634759547131119261630811 11452139320696678892446217)
          ·
            refine ⟨8589104490522509169334663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11452139320696678892446217 8589104490522509169334663)
            ·
              refine ⟨12883656735783763754001995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8589104490522509169334663 12883656735783763754001995)
              ·
                refine ⟨19325485103675645631002993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12883656735783763754001995 19325485103675645631002993)
                ·
                  refine ⟨14494113827756734223252245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19325485103675645631002993 14494113827756734223252245)
                  ·
                    refine ⟨679411585676096916714949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14494113827756734223252245 679411585676096916714949)
                    ·
                      rfl

theorem cell23_3969448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 2, 1, 1, 2, 6].length) (baseStart_3969448 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3969448 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3969448 prefixEnd_3969448 := by exact prefixLift 3969448
  have htrace : WordTrace (prefixWord ++ tailWord_3969448) baseStart_3969448 baseEnd_3969448 := by
    simpa [prefixWord, tailWord_3969448, baseEnd_3969448] using wordTrace_append hprefix tailTrace_3969448
  have hstable : (prefixWord ++ tailWord_3969448).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3969448).length < 2 ^ (prefixWord ++ tailWord_3969448).sum := by decide
  have hdescent : baseEnd_3969448 < baseStart_3969448 := by decide
  rcases family_descends (prefixWord ++ tailWord_3969448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3969476 : List Nat := [2, 3, 3, 2, 3, 1, 2, 1, 1, 3, 2]
def baseStart_3969476 : Nat := 118140960795 + 3969476 * 2 ^ 59
def prefixEnd_3969476 : Nat := 4983230072969 + 3 ^ 40 * 3969476 * 2
def baseEnd_3969476 : Nat := 2038249134486616640594719

theorem tailTrace_3969476 : CollatzResearch.WordTrace tailWord_3969476 prefixEnd_3969476 2038249134486616640594719 := by
  unfold tailWord_3969476
  simp only [CollatzResearch.WordTrace]
  refine ⟨72389341883636929686472141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96519122511515906248629521 72389341883636929686472141)
  ·
    refine ⟨27146003206363848632427053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 72389341883636929686472141 27146003206363848632427053)
    ·
      refine ⟨10179751202386443237160145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27146003206363848632427053 10179751202386443237160145)
      ·
        refine ⟨7634813401789832427870109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10179751202386443237160145 7634813401789832427870109)
        ·
          refine ⟨2863055025671187160451291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7634813401789832427870109 2863055025671187160451291)
          ·
            refine ⟨4294582538506780740676937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2863055025671187160451291 4294582538506780740676937)
            ·
              refine ⟨3220936903880085555507703, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4294582538506780740676937 3220936903880085555507703)
              ·
                refine ⟨4831405355820128333261555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3220936903880085555507703 4831405355820128333261555)
                ·
                  refine ⟨7247108033730192499892333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4831405355820128333261555 7247108033730192499892333)
                  ·
                    refine ⟨2717665512648822187459625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7247108033730192499892333 2717665512648822187459625)
                    ·
                      refine ⟨2038249134486616640594719, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2717665512648822187459625 2038249134486616640594719)
                      ·
                        rfl

theorem cell23_3969476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 3, 1, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 3, 1, 2, 1, 1, 3, 2].length) (baseStart_3969476 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3969476 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3969476 prefixEnd_3969476 := by exact prefixLift 3969476
  have htrace : WordTrace (prefixWord ++ tailWord_3969476) baseStart_3969476 baseEnd_3969476 := by
    simpa [prefixWord, tailWord_3969476, baseEnd_3969476] using wordTrace_append hprefix tailTrace_3969476
  have hstable : (prefixWord ++ tailWord_3969476).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3969476).length < 2 ^ (prefixWord ++ tailWord_3969476).sum := by decide
  have hdescent : baseEnd_3969476 < baseStart_3969476 := by decide
  rcases family_descends (prefixWord ++ tailWord_3969476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3969501 : List Nat := [1, 4, 3, 1, 1, 1, 2, 1, 1, 1, 7]
def baseStart_3969501 : Nat := 118140960795 + 3969501 * 2 ^ 59
def prefixEnd_3969501 : Nat := 4983230072969 + 3 ^ 40 * 3969501 * 2
def baseEnd_3969501 : Nat := 2038261971502979042782103

theorem tailTrace_3969501 : CollatzResearch.WordTrace tailWord_3969501 prefixEnd_3969501 2038261971502979042782103 := by
  unfold tailWord_3969501
  simp only [CollatzResearch.WordTrace]
  refine ⟨144779595592183288642604357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96519730394788859095069571 144779595592183288642604357)
  ·
    refine ⟨27146174173534366620488317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 144779595592183288642604357 27146174173534366620488317)
    ·
      refine ⟨10179815315075387482683119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27146174173534366620488317 10179815315075387482683119)
      ·
        refine ⟨15269722972613081224024679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10179815315075387482683119 15269722972613081224024679)
        ·
          refine ⟨22904584458919621836037019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15269722972613081224024679 22904584458919621836037019)
          ·
            refine ⟨34356876688379432754055529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22904584458919621836037019 34356876688379432754055529)
            ·
              refine ⟨25767657516284574565541647, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34356876688379432754055529 25767657516284574565541647)
              ·
                refine ⟨38651486274426861848312471, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25767657516284574565541647 38651486274426861848312471)
                ·
                  refine ⟨57977229411640292772468707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38651486274426861848312471 57977229411640292772468707)
                  ·
                    refine ⟨86965844117460439158703061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 57977229411640292772468707 86965844117460439158703061)
                    ·
                      refine ⟨2038261971502979042782103, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 86965844117460439158703061 2038261971502979042782103)
                      ·
                        rfl

theorem cell23_3969501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 2, 1, 1, 1, 7].length) (baseStart_3969501 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3969501 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3969501 prefixEnd_3969501 := by exact prefixLift 3969501
  have htrace : WordTrace (prefixWord ++ tailWord_3969501) baseStart_3969501 baseEnd_3969501 := by
    simpa [prefixWord, tailWord_3969501, baseEnd_3969501] using wordTrace_append hprefix tailTrace_3969501
  have hstable : (prefixWord ++ tailWord_3969501).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3969501).length < 2 ^ (prefixWord ++ tailWord_3969501).sum := by decide
  have hdescent : baseEnd_3969501 < baseStart_3969501 := by decide
  rcases family_descends (prefixWord ++ tailWord_3969501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3969506 : List Nat := [3, 3, 3, 2, 2, 1, 1, 1, 1, 4, 2]
def baseStart_3969506 : Nat := 118140960795 + 3969506 * 2 ^ 59
def prefixEnd_3969506 : Nat := 4983230072969 + 3 ^ 40 * 3969506 * 2
def baseEnd_3969506 : Nat := 2038264538906251523219581

theorem tailTrace_3969506 : CollatzResearch.WordTrace tailWord_3969506 prefixEnd_3969506 2038264538906251523219581 := by
  unfold tailWord_3969506
  simp only [CollatzResearch.WordTrace]
  refine ⟨36194944489291293624134093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 96519851971443449664357581 36194944489291293624134093)
  ·
    refine ⟨13573104183484235109050285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36194944489291293624134093 13573104183484235109050285)
    ·
      refine ⟨5089914068806588165893857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13573104183484235109050285 5089914068806588165893857)
      ·
        refine ⟨3817435551604941124420393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5089914068806588165893857 3817435551604941124420393)
        ·
          refine ⟨2863076663703705843315295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3817435551604941124420393 2863076663703705843315295)
          ·
            refine ⟨4294614995555558764972943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2863076663703705843315295 4294614995555558764972943)
            ·
              refine ⟨6441922493333338147459415, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4294614995555558764972943 6441922493333338147459415)
              ·
                refine ⟨9662883740000007221189123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6441922493333338147459415 9662883740000007221189123)
                ·
                  refine ⟨14494325610000010831783685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9662883740000007221189123 14494325610000010831783685)
                  ·
                    refine ⟨2717686051875002030959441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 14494325610000010831783685 2717686051875002030959441)
                    ·
                      refine ⟨2038264538906251523219581, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2717686051875002030959441 2038264538906251523219581)
                      ·
                        rfl

theorem cell23_3969506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 2, 1, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 2, 1, 1, 1, 1, 4, 2].length) (baseStart_3969506 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3969506 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3969506 prefixEnd_3969506 := by exact prefixLift 3969506
  have htrace : WordTrace (prefixWord ++ tailWord_3969506) baseStart_3969506 baseEnd_3969506 := by
    simpa [prefixWord, tailWord_3969506, baseEnd_3969506] using wordTrace_append hprefix tailTrace_3969506
  have hstable : (prefixWord ++ tailWord_3969506).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3969506).length < 2 ^ (prefixWord ++ tailWord_3969506).sum := by decide
  have hdescent : baseEnd_3969506 < baseStart_3969506 := by decide
  rcases family_descends (prefixWord ++ tailWord_3969506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3969511 : List Nat := [1, 1, 5, 2, 1, 1, 1, 1, 3, 3, 4]
def baseStart_3969511 : Nat := 118140960795 + 3969511 * 2 ^ 59
def prefixEnd_3969511 : Nat := 4983230072969 + 3 ^ 40 * 3969511 * 2
def baseEnd_3969511 : Nat := 2038267106309524003657057

theorem tailTrace_3969511 : CollatzResearch.WordTrace tailWord_3969511 prefixEnd_3969511 2038267106309524003657057 := by
  unfold tailWord_3969511
  simp only [CollatzResearch.WordTrace]
  refine ⟨144779960322147060350468387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96519973548098040233645591 144779960322147060350468387)
  ·
    refine ⟨217169940483220590525702581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144779960322147060350468387 217169940483220590525702581)
    ·
      refine ⟨20359681920301930361784617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 217169940483220590525702581 20359681920301930361784617)
      ·
        refine ⟨15269761440226447771338463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20359681920301930361784617 15269761440226447771338463)
        ·
          refine ⟨22904642160339671657007695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15269761440226447771338463 22904642160339671657007695)
          ·
            refine ⟨34356963240509507485511543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22904642160339671657007695 34356963240509507485511543)
            ·
              refine ⟨51535444860764261228267315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34356963240509507485511543 51535444860764261228267315)
              ·
                refine ⟨77303167291146391842400973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51535444860764261228267315 77303167291146391842400973)
                ·
                  refine ⟨28988687734179896940900365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 77303167291146391842400973 28988687734179896940900365)
                  ·
                    refine ⟨10870757900317461352837637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 28988687734179896940900365 10870757900317461352837637)
                    ·
                      refine ⟨2038267106309524003657057, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10870757900317461352837637 2038267106309524003657057)
                      ·
                        rfl

theorem cell23_3969511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 1, 1, 3, 3, 4].length) (baseStart_3969511 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3969511 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3969511 prefixEnd_3969511 := by exact prefixLift 3969511
  have htrace : WordTrace (prefixWord ++ tailWord_3969511) baseStart_3969511 baseEnd_3969511 := by
    simpa [prefixWord, tailWord_3969511, baseEnd_3969511] using wordTrace_append hprefix tailTrace_3969511
  have hstable : (prefixWord ++ tailWord_3969511).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3969511).length < 2 ^ (prefixWord ++ tailWord_3969511).sum := by decide
  have hdescent : baseEnd_3969511 < baseStart_3969511 := by decide
  rcases family_descends (prefixWord ++ tailWord_3969511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3969542 : List Nat := [6, 2, 1, 1, 1, 1, 1, 1, 4, 5]
def baseStart_3969542 : Nat := 118140960795 + 3969542 * 2 ^ 59
def prefixEnd_3969542 : Nat := 4983230072969 + 3 ^ 40 * 3969542 * 2
def baseEnd_3969542 : Nat := 679427674736604460789805

theorem tailTrace_3969542 : CollatzResearch.WordTrace tailWord_3969542 prefixEnd_3969542 679427674736604460789805 := by
  unfold tailWord_3969542
  simp only [CollatzResearch.WordTrace]
  refine ⟨4524409093282336020151465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 96520727323356501763231253 4524409093282336020151465)
  ·
    refine ⟨3393306819961752015113599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4524409093282336020151465 3393306819961752015113599)
    ·
      refine ⟨5089960229942628022670399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3393306819961752015113599 5089960229942628022670399)
      ·
        refine ⟨7634940344913942034005599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5089960229942628022670399 7634940344913942034005599)
        ·
          refine ⟨11452410517370913051008399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7634940344913942034005599 11452410517370913051008399)
          ·
            refine ⟨17178615776056369576512599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11452410517370913051008399 17178615776056369576512599)
            ·
              refine ⟨25767923664084554364768899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17178615776056369576512599 25767923664084554364768899)
              ·
                refine ⟨38651885496126831547153349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25767923664084554364768899 38651885496126831547153349)
                ·
                  refine ⟨7247228530523780915091253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 38651885496126831547153349 7247228530523780915091253)
                  ·
                    refine ⟨679427674736604460789805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7247228530523780915091253 679427674736604460789805)
                    ·
                      rfl

theorem cell23_3969542_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 1, 1, 1, 4, 5].length) (baseStart_3969542 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3969542 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3969542 prefixEnd_3969542 := by exact prefixLift 3969542
  have htrace : WordTrace (prefixWord ++ tailWord_3969542) baseStart_3969542 baseEnd_3969542 := by
    simpa [prefixWord, tailWord_3969542, baseEnd_3969542] using wordTrace_append hprefix tailTrace_3969542
  have hstable : (prefixWord ++ tailWord_3969542).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3969542).length < 2 ^ (prefixWord ++ tailWord_3969542).sum := by decide
  have hdescent : baseEnd_3969542 < baseStart_3969542 := by decide
  rcases family_descends (prefixWord ++ tailWord_3969542) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3969548 : List Nat := [2, 2, 1, 2, 4, 1, 1, 1, 4, 2, 3]
def baseStart_3969548 : Nat := 118140960795 + 3969548 * 2 ^ 59
def prefixEnd_3969548 : Nat := 4983230072969 + 3 ^ 40 * 3969548 * 2
def baseEnd_3969548 : Nat := 2038286105093740358894387

theorem tailTrace_3969548 : CollatzResearch.WordTrace tailWord_3969548 prefixEnd_3969548 2038286105093740358894387 := by
  unfold tailWord_3969548
  simp only [CollatzResearch.WordTrace]
  refine ⟨72390654911506507834782649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96520873215342010446376865 72390654911506507834782649)
  ·
    refine ⟨54292991183629880876086987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72390654911506507834782649 54292991183629880876086987)
    ·
      refine ⟨81439486775444821314130481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54292991183629880876086987 81439486775444821314130481)
      ·
        refine ⟨61079615081583615985597861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81439486775444821314130481 61079615081583615985597861)
        ·
          refine ⟨11452427827796927997299599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 61079615081583615985597861 11452427827796927997299599)
          ·
            refine ⟨17178641741695391995949399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11452427827796927997299599 17178641741695391995949399)
            ·
              refine ⟨25767962612543087993924099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17178641741695391995949399 25767962612543087993924099)
              ·
                refine ⟨38651943918814631990886149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25767962612543087993924099 38651943918814631990886149)
                ·
                  refine ⟨7247239484777743498291153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 38651943918814631990886149 7247239484777743498291153)
                  ·
                    refine ⟨5435429613583307623718365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7247239484777743498291153 5435429613583307623718365)
                    ·
                      refine ⟨2038286105093740358894387, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5435429613583307623718365 2038286105093740358894387)
                      ·
                        rfl

theorem cell23_3969548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 1, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 1, 1, 1, 4, 2, 3].length) (baseStart_3969548 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3969548 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3969548 prefixEnd_3969548 := by exact prefixLift 3969548
  have htrace : WordTrace (prefixWord ++ tailWord_3969548) baseStart_3969548 baseEnd_3969548 := by
    simpa [prefixWord, tailWord_3969548, baseEnd_3969548] using wordTrace_append hprefix tailTrace_3969548
  have hstable : (prefixWord ++ tailWord_3969548).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3969548).length < 2 ^ (prefixWord ++ tailWord_3969548).sum := by decide
  have hdescent : baseEnd_3969548 < baseStart_3969548 := by decide
  rcases family_descends (prefixWord ++ tailWord_3969548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3969582 : List Nat := [4, 1, 3, 1, 3, 1, 2, 1, 2, 2, 3]
def baseStart_3969582 : Nat := 118140960795 + 3969582 * 2 ^ 59
def prefixEnd_3969582 : Nat := 4983230072969 + 3 ^ 40 * 3969582 * 2
def baseEnd_3969582 : Nat := 2038303563435993225869231

theorem tailTrace_3969582 : CollatzResearch.WordTrace tailWord_3969582 prefixEnd_3969582 2038303563435993225869231 := by
  unfold tailWord_3969582
  simp only [CollatzResearch.WordTrace]
  refine ⟨18097818738111229934537875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 96521699936593226317535333 18097818738111229934537875)
  ·
    refine ⟨27146728107166844901806813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18097818738111229934537875 27146728107166844901806813)
    ·
      refine ⟨10180023040187566838177555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27146728107166844901806813 10180023040187566838177555)
      ·
        refine ⟨15270034560281350257266333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10180023040187566838177555 15270034560281350257266333)
        ·
          refine ⟨5726262960105506346474875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15270034560281350257266333 5726262960105506346474875)
          ·
            refine ⟨8589394440158259519712313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5726262960105506346474875 8589394440158259519712313)
            ·
              refine ⟨6442045830118694639784235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8589394440158259519712313 6442045830118694639784235)
              ·
                refine ⟨9663068745178041959676353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6442045830118694639784235 9663068745178041959676353)
                ·
                  refine ⟨7247301558883531469757265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9663068745178041959676353 7247301558883531469757265)
                  ·
                    refine ⟨5435476169162648602317949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7247301558883531469757265 5435476169162648602317949)
                    ·
                      refine ⟨2038303563435993225869231, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5435476169162648602317949 2038303563435993225869231)
                      ·
                        rfl

theorem cell23_3969582_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 3, 1, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 3, 1, 2, 1, 2, 2, 3].length) (baseStart_3969582 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3969582 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3969582 prefixEnd_3969582 := by exact prefixLift 3969582
  have htrace : WordTrace (prefixWord ++ tailWord_3969582) baseStart_3969582 baseEnd_3969582 := by
    simpa [prefixWord, tailWord_3969582, baseEnd_3969582] using wordTrace_append hprefix tailTrace_3969582
  have hstable : (prefixWord ++ tailWord_3969582).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3969582).length < 2 ^ (prefixWord ++ tailWord_3969582).sum := by decide
  have hdescent : baseEnd_3969582 < baseStart_3969582 := by decide
  rcases family_descends (prefixWord ++ tailWord_3969582) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3969605 : List Nat := [1, 3, 1, 1, 1, 5, 2, 2, 2, 3, 2]
def baseStart_3969605 : Nat := 118140960795 + 3969605 * 2 ^ 59
def prefixEnd_3969605 : Nat := 4983230072969 + 3 ^ 40 * 3969605 * 2
def baseEnd_3969605 : Nat := 2038315373491046635881625

theorem tailTrace_3969605 : CollatzResearch.WordTrace tailWord_3969605 prefixEnd_3969605 2038315373491046635881625 := by
  unfold tailWord_3969605
  simp only [CollatzResearch.WordTrace]
  refine ⟨144783388783806514404390269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96522259189204342936260179 144783388783806514404390269)
  ·
    refine ⟨54293770793927442901646351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 144783388783806514404390269 54293770793927442901646351)
    ·
      refine ⟨81440656190891164352469527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54293770793927442901646351 81440656190891164352469527)
      ·
        refine ⟨122160984286336746528704291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81440656190891164352469527 122160984286336746528704291)
        ·
          refine ⟨183241476429505119793056437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 122160984286336746528704291 183241476429505119793056437)
          ·
            refine ⟨17178888415266104980599041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 183241476429505119793056437 17178888415266104980599041)
            ·
              refine ⟨12884166311449578735449281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17178888415266104980599041 12884166311449578735449281)
              ·
                refine ⟨9663124733587184051586961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12884166311449578735449281 9663124733587184051586961)
                ·
                  refine ⟨7247343550190388038690221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9663124733587184051586961 7247343550190388038690221)
                  ·
                    refine ⟨2717753831321395514508833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7247343550190388038690221 2717753831321395514508833)
                    ·
                      refine ⟨2038315373491046635881625, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2717753831321395514508833 2038315373491046635881625)
                      ·
                        rfl

theorem cell23_3969605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 5, 2, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 5, 2, 2, 2, 3, 2].length) (baseStart_3969605 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3969605 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3969605 prefixEnd_3969605 := by exact prefixLift 3969605
  have htrace : WordTrace (prefixWord ++ tailWord_3969605) baseStart_3969605 baseEnd_3969605 := by
    simpa [prefixWord, tailWord_3969605, baseEnd_3969605] using wordTrace_append hprefix tailTrace_3969605
  have hstable : (prefixWord ++ tailWord_3969605).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3969605).length < 2 ^ (prefixWord ++ tailWord_3969605).sum := by decide
  have hdescent : baseEnd_3969605 < baseStart_3969605 := by decide
  rcases family_descends (prefixWord ++ tailWord_3969605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3969606 : List Nat := [6, 1, 1, 1, 2, 1, 4, 2, 1, 4]
def baseStart_3969606 : Nat := 118140960795 + 3969606 * 2 ^ 59
def prefixEnd_3969606 : Nat := 4983230072969 + 3 ^ 40 * 3969606 * 2
def baseEnd_3969606 : Nat := 679438628990567043989707

theorem tailTrace_3969606 : CollatzResearch.WordTrace tailWord_3969606 prefixEnd_3969606 679438628990567043989707 := by
  unfold tailWord_3969606
  simp only [CollatzResearch.WordTrace]
  refine ⟨4524482039275090361724271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 96522283504535261050117781 4524482039275090361724271)
  ·
    refine ⟨6786723058912635542586407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4524482039275090361724271 6786723058912635542586407)
    ·
      refine ⟨10180084588368953313879611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6786723058912635542586407 10180084588368953313879611)
      ·
        refine ⟨15270126882553429970819417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10180084588368953313879611 15270126882553429970819417)
        ·
          refine ⟨11452595161915072478114563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15270126882553429970819417 11452595161915072478114563)
          ·
            refine ⟨17178892742872608717171845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11452595161915072478114563 17178892742872608717171845)
            ·
              refine ⟨3221042389288614134469721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17178892742872608717171845 3221042389288614134469721)
              ·
                refine ⟨2415781791966460600852291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3221042389288614134469721 2415781791966460600852291)
                ·
                  refine ⟨3623672687949690901278437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2415781791966460600852291 3623672687949690901278437)
                  ·
                    refine ⟨679438628990567043989707, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3623672687949690901278437 679438628990567043989707)
                    ·
                      rfl

theorem cell23_3969606_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 1, 4, 2, 1, 4].length) (baseStart_3969606 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3969606 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3969606 prefixEnd_3969606 := by exact prefixLift 3969606
  have htrace : WordTrace (prefixWord ++ tailWord_3969606) baseStart_3969606 baseEnd_3969606 := by
    simpa [prefixWord, tailWord_3969606, baseEnd_3969606] using wordTrace_append hprefix tailTrace_3969606
  have hstable : (prefixWord ++ tailWord_3969606).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3969606).length < 2 ^ (prefixWord ++ tailWord_3969606).sum := by decide
  have hdescent : baseEnd_3969606 < baseStart_3969606 := by decide
  rcases family_descends (prefixWord ++ tailWord_3969606) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3969612 : List Nat := [2, 2, 1, 3, 1, 2, 3, 4, 1, 1, 3]
def baseStart_3969612 : Nat := 118140960795 + 3969612 * 2 ^ 59
def prefixEnd_3969612 : Nat := 4983230072969 + 3 ^ 40 * 3969612 * 2
def baseEnd_3969612 : Nat := 2038318967855628108494093

theorem tailTrace_3969612 : CollatzResearch.WordTrace tailWord_3969612 prefixEnd_3969612 2038318967855628108494093 := by
  unfold tailWord_3969612
  simp only [CollatzResearch.WordTrace]
  refine ⟨72391822047390577299947545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96522429396520769733263393 72391822047390577299947545)
  ·
    refine ⟨54293866535542932974960659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72391822047390577299947545 54293866535542932974960659)
    ·
      refine ⟨81440799803314399462440989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54293866535542932974960659 81440799803314399462440989)
      ·
        refine ⟨30540299926242899798415371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 81440799803314399462440989 30540299926242899798415371)
        ·
          refine ⟨45810449889364349697623057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30540299926242899798415371 45810449889364349697623057)
          ·
            refine ⟨34357837417023262273217293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45810449889364349697623057 34357837417023262273217293)
            ·
              refine ⟨12884189031383723352456485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34357837417023262273217293 12884189031383723352456485)
              ·
                refine ⟨2415785443384448128585591, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12884189031383723352456485 2415785443384448128585591)
                ·
                  refine ⟨3623678165076672192878387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2415785443384448128585591 3623678165076672192878387)
                  ·
                    refine ⟨5435517247615008289317581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3623678165076672192878387 5435517247615008289317581)
                    ·
                      refine ⟨2038318967855628108494093, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5435517247615008289317581 2038318967855628108494093)
                      ·
                        rfl

theorem cell23_3969612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 3, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 3, 4, 1, 1, 3].length) (baseStart_3969612 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3969612 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3969612 prefixEnd_3969612 := by exact prefixLift 3969612
  have htrace : WordTrace (prefixWord ++ tailWord_3969612) baseStart_3969612 baseEnd_3969612 := by
    simpa [prefixWord, tailWord_3969612, baseEnd_3969612] using wordTrace_append hprefix tailTrace_3969612
  have hstable : (prefixWord ++ tailWord_3969612).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3969612).length < 2 ^ (prefixWord ++ tailWord_3969612).sum := by decide
  have hdescent : baseEnd_3969612 < baseStart_3969612 := by decide
  rcases family_descends (prefixWord ++ tailWord_3969612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3969618 : List Nat := [3, 2, 2, 1, 2, 1, 1, 1, 5, 1, 4]
def baseStart_3969618 : Nat := 118140960795 + 3969618 * 2 ^ 59
def prefixEnd_3969618 : Nat := 4983230072969 + 3 ^ 40 * 3969618 * 2
def baseEnd_3969618 : Nat := 2038322048739555085019065

theorem tailTrace_3969618 : CollatzResearch.WordTrace tailWord_3969618 prefixEnd_3969618 2038322048739555085019065 := by
  unfold tailWord_3969618
  simp only [CollatzResearch.WordTrace]
  refine ⟨36195965733189854406153377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 96522575288506278416409005 36195965733189854406153377)
  ·
    refine ⟨27146974299892390804615033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36195965733189854406153377 27146974299892390804615033)
    ·
      refine ⟨20360230724919293103461275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27146974299892390804615033 20360230724919293103461275)
      ·
        refine ⟨30540346087378939655191913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20360230724919293103461275 30540346087378939655191913)
        ·
          refine ⟨22905259565534204741393935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30540346087378939655191913 22905259565534204741393935)
          ·
            refine ⟨34357889348301307112090903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22905259565534204741393935 34357889348301307112090903)
            ·
              refine ⟨51536834022451960668136355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34357889348301307112090903 51536834022451960668136355)
              ·
                refine ⟨77305251033677941002204533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51536834022451960668136355 77305251033677941002204533)
                ·
                  refine ⟨7247367284407306968956675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 77305251033677941002204533 7247367284407306968956675)
                  ·
                    refine ⟨10871050926610960453435013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7247367284407306968956675 10871050926610960453435013)
                    ·
                      refine ⟨2038322048739555085019065, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10871050926610960453435013 2038322048739555085019065)
                      ·
                        rfl

theorem cell23_3969618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 1, 1, 5, 1, 4].length) (baseStart_3969618 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3969618 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3969618 prefixEnd_3969618 := by exact prefixLift 3969618
  have htrace : WordTrace (prefixWord ++ tailWord_3969618) baseStart_3969618 baseEnd_3969618 := by
    simpa [prefixWord, tailWord_3969618, baseEnd_3969618] using wordTrace_append hprefix tailTrace_3969618
  have hstable : (prefixWord ++ tailWord_3969618).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3969618).length < 2 ^ (prefixWord ++ tailWord_3969618).sum := by decide
  have hdescent : baseEnd_3969618 < baseStart_3969618 := by decide
  rcases family_descends (prefixWord ++ tailWord_3969618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3969631 : List Nat := [1, 1, 2, 3, 1, 1, 1, 5, 1, 1, 6]
def baseStart_3969631 : Nat := 118140960795 + 3969631 * 2 ^ 59
def prefixEnd_3969631 : Nat := 4983230072969 + 3 ^ 40 * 3969631 * 2
def baseEnd_3969631 : Nat := 2038328723988063534156505

theorem tailTrace_3969631 : CollatzResearch.WordTrace tailWord_3969631 prefixEnd_3969631 2038328723988063534156505 := by
  unfold tailWord_3969631
  simp only [CollatzResearch.WordTrace]
  refine ⟨144784337081712320844836747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96522891387808213896557831 144784337081712320844836747)
  ·
    refine ⟨217176505622568481267255121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144784337081712320844836747 217176505622568481267255121)
    ·
      refine ⟨162882379216926360950441341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 217176505622568481267255121 162882379216926360950441341)
      ·
        refine ⟨61080892206347385356415503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 162882379216926360950441341 61080892206347385356415503)
        ·
          refine ⟨91621338309521078034623255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61080892206347385356415503 91621338309521078034623255)
          ·
            refine ⟨137432007464281617051934883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91621338309521078034623255 137432007464281617051934883)
            ·
              refine ⟨206148011196422425577902325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 137432007464281617051934883 206148011196422425577902325)
              ·
                refine ⟨19326376049664602397928343, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 206148011196422425577902325 19326376049664602397928343)
                ·
                  refine ⟨28989564074496903596892515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19326376049664602397928343 28989564074496903596892515)
                  ·
                    refine ⟨43484346111745355395338773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 28989564074496903596892515 43484346111745355395338773)
                    ·
                      refine ⟨2038328723988063534156505, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 43484346111745355395338773 2038328723988063534156505)
                      ·
                        rfl

theorem cell23_3969631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 1, 5, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 1, 5, 1, 1, 6].length) (baseStart_3969631 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3969631 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3969631 prefixEnd_3969631 := by exact prefixLift 3969631
  have htrace : WordTrace (prefixWord ++ tailWord_3969631) baseStart_3969631 baseEnd_3969631 := by
    simpa [prefixWord, tailWord_3969631, baseEnd_3969631] using wordTrace_append hprefix tailTrace_3969631
  have hstable : (prefixWord ++ tailWord_3969631).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3969631).length < 2 ^ (prefixWord ++ tailWord_3969631).sum := by decide
  have hdescent : baseEnd_3969631 < baseStart_3969631 := by decide
  rcases family_descends (prefixWord ++ tailWord_3969631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3969669 : List Nat := [1, 3, 1, 1, 4, 2, 2, 4, 1, 2, 2]
def baseStart_3969669 : Nat := 118140960795 + 3969669 * 2 ^ 59
def prefixEnd_3969669 : Nat := 4983230072969 + 3 ^ 40 * 3969669 * 2
def baseEnd_3969669 : Nat := 2038348236252934385481331

theorem tailTrace_3969669 : CollatzResearch.WordTrace tailWord_3969669 prefixEnd_3969669 2038348236252934385481331 := by
  unfold tailWord_3969669
  simp only [CollatzResearch.WordTrace]
  refine ⟨144785723055574653334720061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96523815370383102223146707 144785723055574653334720061)
  ·
    refine ⟨54294646145840495000520023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 144785723055574653334720061 54294646145840495000520023)
    ·
      refine ⟨81441969218760742500780035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54294646145840495000520023 81441969218760742500780035)
      ·
        refine ⟨122162953828141113751170053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81441969218760742500780035 122162953828141113751170053)
        ·
          refine ⟨22905553842776458828344385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 122162953828141113751170053 22905553842776458828344385)
          ·
            refine ⟨17179165382082344121258289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22905553842776458828344385 17179165382082344121258289)
            ·
              refine ⟨12884374036561758090943717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17179165382082344121258289 12884374036561758090943717)
              ·
                refine ⟨2415820131855329642051947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12884374036561758090943717 2415820131855329642051947)
                ·
                  refine ⟨3623730197782994463077921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2415820131855329642051947 3623730197782994463077921)
                  ·
                    refine ⟨2717797648337245847308441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3623730197782994463077921 2717797648337245847308441)
                    ·
                      refine ⟨2038348236252934385481331, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2717797648337245847308441 2038348236252934385481331)
                      ·
                        rfl

theorem cell23_3969669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 2, 2, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 2, 2, 4, 1, 2, 2].length) (baseStart_3969669 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3969669 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3969669 prefixEnd_3969669 := by exact prefixLift 3969669
  have htrace : WordTrace (prefixWord ++ tailWord_3969669) baseStart_3969669 baseEnd_3969669 := by
    simpa [prefixWord, tailWord_3969669, baseEnd_3969669] using wordTrace_append hprefix tailTrace_3969669
  have hstable : (prefixWord ++ tailWord_3969669).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3969669).length < 2 ^ (prefixWord ++ tailWord_3969669).sum := by decide
  have hdescent : baseEnd_3969669 < baseStart_3969669 := by decide
  rcases family_descends (prefixWord ++ tailWord_3969669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3969682 : List Nat := [3, 2, 3, 1, 2, 3, 1, 1, 1, 2, 4]
def baseStart_3969682 : Nat := 118140960795 + 3969682 * 2 ^ 59
def prefixEnd_3969682 : Nat := 4983230072969 + 3 ^ 40 * 3969682 * 2
def baseEnd_3969682 : Nat := 2038354911501442834618771

theorem tailTrace_3969682 : CollatzResearch.WordTrace tailWord_3969682 prefixEnd_3969682 2038354911501442834618771 := by
  unfold tailWord_3969682
  simp only [CollatzResearch.WordTrace]
  refine ⟨36196549301131889138735825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 96524131469685037703295533 36196549301131889138735825)
  ·
    refine ⟨27147411975848916854051869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36196549301131889138735825 27147411975848916854051869)
    ·
      refine ⟨10180279490943343820269451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27147411975848916854051869 10180279490943343820269451)
      ·
        refine ⟨15270419236415015730404177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10180279490943343820269451 15270419236415015730404177)
        ·
          refine ⟨11452814427311261797803133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15270419236415015730404177 11452814427311261797803133)
          ·
            refine ⟨4294805410241723174176175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11452814427311261797803133 4294805410241723174176175)
            ·
              refine ⟨6442208115362584761264263, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4294805410241723174176175 6442208115362584761264263)
              ·
                refine ⟨9663312173043877141896395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6442208115362584761264263 9663312173043877141896395)
                ·
                  refine ⟨14494968259565815712844593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9663312173043877141896395 14494968259565815712844593)
                  ·
                    refine ⟨10871226194674361784633445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14494968259565815712844593 10871226194674361784633445)
                    ·
                      refine ⟨2038354911501442834618771, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10871226194674361784633445 2038354911501442834618771)
                      ·
                        rfl

theorem cell23_3969682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 3, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 3, 1, 1, 1, 2, 4].length) (baseStart_3969682 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3969682 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3969682 prefixEnd_3969682 := by exact prefixLift 3969682
  have htrace : WordTrace (prefixWord ++ tailWord_3969682) baseStart_3969682 baseEnd_3969682 := by
    simpa [prefixWord, tailWord_3969682, baseEnd_3969682] using wordTrace_append hprefix tailTrace_3969682
  have hstable : (prefixWord ++ tailWord_3969682).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3969682).length < 2 ^ (prefixWord ++ tailWord_3969682).sum := by decide
  have hdescent : baseEnd_3969682 < baseStart_3969682 := by decide
  rcases family_descends (prefixWord ++ tailWord_3969682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3969746 : List Nat := [3, 2, 2, 2, 3, 2, 1, 2, 1, 3, 2]
def baseStart_3969746 : Nat := 118140960795 + 3969746 * 2 ^ 59
def prefixEnd_3969746 : Nat := 4983230072969 + 3 ^ 40 * 3969746 * 2
def baseEnd_3969746 : Nat := 2038387774263330584218477

theorem tailTrace_3969746 : CollatzResearch.WordTrace tailWord_3969746 prefixEnd_3969746 2038387774263330584218477 := by
  unfold tailWord_3969746
  simp only [CollatzResearch.WordTrace]
  refine ⟨36197132869073923871318273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 96525687650863796990182061 36197132869073923871318273)
  ·
    refine ⟨27147849651805442903488705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36197132869073923871318273 27147849651805442903488705)
    ·
      refine ⟨20360887238854082177616529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27147849651805442903488705 20360887238854082177616529)
      ·
        refine ⟨15270665429140561633212397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20360887238854082177616529 15270665429140561633212397)
        ·
          refine ⟨5726499535927710612454649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15270665429140561633212397 5726499535927710612454649)
          ·
            refine ⟨4294874651945782959340987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5726499535927710612454649 4294874651945782959340987)
            ·
              refine ⟨6442311977918674439011481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4294874651945782959340987 6442311977918674439011481)
              ·
                refine ⟨4831733983439005829258611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6442311977918674439011481 4831733983439005829258611)
                ·
                  refine ⟨7247600975158508743887917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4831733983439005829258611 7247600975158508743887917)
                  ·
                    refine ⟨2717850365684440778957969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7247600975158508743887917 2717850365684440778957969)
                    ·
                      refine ⟨2038387774263330584218477, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2717850365684440778957969 2038387774263330584218477)
                      ·
                        rfl

theorem cell23_3969746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 3, 2, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 3, 2, 1, 2, 1, 3, 2].length) (baseStart_3969746 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3969746 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3969746 prefixEnd_3969746 := by exact prefixLift 3969746
  have htrace : WordTrace (prefixWord ++ tailWord_3969746) baseStart_3969746 baseEnd_3969746 := by
    simpa [prefixWord, tailWord_3969746, baseEnd_3969746] using wordTrace_append hprefix tailTrace_3969746
  have hstable : (prefixWord ++ tailWord_3969746).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3969746).length < 2 ^ (prefixWord ++ tailWord_3969746).sum := by decide
  have hdescent : baseEnd_3969746 < baseStart_3969746 := by decide
  rcases family_descends (prefixWord ++ tailWord_3969746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3969782 : List Nat := [5, 1, 1, 1, 1, 2, 3, 4, 5]
def baseStart_3969782 : Nat := 118140960795 + 3969782 * 2 ^ 59
def prefixEnd_3969782 : Nat := 4983230072969 + 3 ^ 40 * 3969782 * 2
def baseEnd_3969782 : Nat := 226489584396321382596479

theorem tailTrace_3969782 : CollatzResearch.WordTrace tailWord_3969782 prefixEnd_3969782 226489584396321382596479 := by
  unfold tailWord_3969782
  simp only [CollatzResearch.WordTrace]
  refine ⟨9049365281510329602098975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 96526563002776849089055733 9049365281510329602098975)
  ·
    refine ⟨13574047922265494403148463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9049365281510329602098975 13574047922265494403148463)
    ·
      refine ⟨20361071883398241604722695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13574047922265494403148463 20361071883398241604722695)
      ·
        refine ⟨30541607825097362407084043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20361071883398241604722695 30541607825097362407084043)
        ·
          refine ⟨45812411737646043610626065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30541607825097362407084043 45812411737646043610626065)
          ·
            refine ⟨34359308803234532707969549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45812411737646043610626065 34359308803234532707969549)
            ·
              refine ⟨12884740801212949765488581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34359308803234532707969549 12884740801212949765488581)
              ·
                refine ⟨2415888900227428081029109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12884740801212949765488581 2415888900227428081029109)
                ·
                  refine ⟨226489584396321382596479, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2415888900227428081029109 226489584396321382596479)
                  ·
                    rfl

theorem cell23_3969782_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 3, 4, 5].length) (baseStart_3969782 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3969782 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3969782 prefixEnd_3969782 := by exact prefixLift 3969782
  have htrace : WordTrace (prefixWord ++ tailWord_3969782) baseStart_3969782 baseEnd_3969782 := by
    simpa [prefixWord, tailWord_3969782, baseEnd_3969782] using wordTrace_append hprefix tailTrace_3969782
  have hstable : (prefixWord ++ tailWord_3969782).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3969782).length < 2 ^ (prefixWord ++ tailWord_3969782).sum := by decide
  have hdescent : baseEnd_3969782 < baseStart_3969782 := by decide
  rcases family_descends (prefixWord ++ tailWord_3969782) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3969825 : List Nat := [1, 2, 3, 2, 1, 2, 1, 2, 5, 4]
def baseStart_3969825 : Nat := 118140960795 + 3969825 * 2 ^ 59
def prefixEnd_3969825 : Nat := 4983230072969 + 3 ^ 40 * 3969825 * 2
def baseEnd_3969825 : Nat := 679476113078345258376871

theorem tailTrace_3969825 : CollatzResearch.WordTrace tailWord_3969825 prefixEnd_3969825 679476113078345258376871 := by
  unfold tailWord_3969825
  simp only [CollatzResearch.WordTrace]
  refine ⟨144791412843009491977398929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96527608562006327984932619 144791412843009491977398929)
  ·
    refine ⟨108593559632257118983049197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 144791412843009491977398929 108593559632257118983049197)
    ·
      refine ⟨40722584862096419618643449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 108593559632257118983049197 40722584862096419618643449)
      ·
        refine ⟨30541938646572314713982587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40722584862096419618643449 30541938646572314713982587)
        ·
          refine ⟨45812907969858472070973881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30541938646572314713982587 45812907969858472070973881)
          ·
            refine ⟨34359680977393854053230411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45812907969858472070973881 34359680977393854053230411)
            ·
              refine ⟨51539521466090781079845617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34359680977393854053230411 51539521466090781079845617)
              ·
                refine ⟨38654641099568085809884213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51539521466090781079845617 38654641099568085809884213)
                ·
                  refine ⟨3623872603084508044676645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 38654641099568085809884213 3623872603084508044676645)
                  ·
                    refine ⟨679476113078345258376871, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3623872603084508044676645 679476113078345258376871)
                    ·
                      rfl

theorem cell23_3969825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 1, 2, 5, 4].length) (baseStart_3969825 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3969825 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3969825 prefixEnd_3969825 := by exact prefixLift 3969825
  have htrace : WordTrace (prefixWord ++ tailWord_3969825) baseStart_3969825 baseEnd_3969825 := by
    simpa [prefixWord, tailWord_3969825, baseEnd_3969825] using wordTrace_append hprefix tailTrace_3969825
  have hstable : (prefixWord ++ tailWord_3969825).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3969825).length < 2 ^ (prefixWord ++ tailWord_3969825).sum := by decide
  have hdescent : baseEnd_3969825 < baseStart_3969825 := by decide
  rcases family_descends (prefixWord ++ tailWord_3969825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3969832 : List Nat := [2, 1, 5, 1, 1, 1, 1, 1, 4, 4, 2]
def baseStart_3969832 : Nat := 118140960795 + 3969832 * 2 ^ 59
def prefixEnd_3969832 : Nat := 4983230072969 + 3 ^ 40 * 3969832 * 2
def baseEnd_3969832 : Nat := 2038431933599617247743081

theorem tailTrace_3969832 : CollatzResearch.WordTrace tailWord_3969832 prefixEnd_3969832 2038431933599617247743081 := by
  unfold tailWord_3969832
  simp only [CollatzResearch.WordTrace]
  refine ⟨72395834076992066086451875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96527778769322754781935833 72395834076992066086451875)
  ·
    refine ⟨108593751115488099129677813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72395834076992066086451875 108593751115488099129677813)
    ·
      refine ⟨10180664167077009293407295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 108593751115488099129677813 10180664167077009293407295)
      ·
        refine ⟨15270996250615513940110943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10180664167077009293407295 15270996250615513940110943)
        ·
          refine ⟨22906494375923270910166415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15270996250615513940110943 22906494375923270910166415)
          ·
            refine ⟨34359741563884906365249623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22906494375923270910166415 34359741563884906365249623)
            ·
              refine ⟨51539612345827359547874435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34359741563884906365249623 51539612345827359547874435)
              ·
                refine ⟨77309418518741039321811653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51539612345827359547874435 77309418518741039321811653)
                ·
                  refine ⟨14495515972263944872839685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 77309418518741039321811653 14495515972263944872839685)
                  ·
                    refine ⟨2717909244799489663657441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 14495515972263944872839685 2717909244799489663657441)
                    ·
                      refine ⟨2038431933599617247743081, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2717909244799489663657441 2038431933599617247743081)
                      ·
                        rfl

theorem cell23_3969832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 1, 1, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 1, 1, 4, 4, 2].length) (baseStart_3969832 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3969832 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3969832 prefixEnd_3969832 := by exact prefixLift 3969832
  have htrace : WordTrace (prefixWord ++ tailWord_3969832) baseStart_3969832 baseEnd_3969832 := by
    simpa [prefixWord, tailWord_3969832, baseEnd_3969832] using wordTrace_append hprefix tailTrace_3969832
  have hstable : (prefixWord ++ tailWord_3969832).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3969832).length < 2 ^ (prefixWord ++ tailWord_3969832).sum := by decide
  have hdescent : baseEnd_3969832 < baseStart_3969832 := by decide
  rcases family_descends (prefixWord ++ tailWord_3969832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3969842 : List Nat := [3, 2, 1, 1, 3, 1, 4, 1, 3, 4]
def baseStart_3969842 : Nat := 118140960795 + 3969842 * 2 ^ 59
def prefixEnd_3969842 : Nat := 4983230072969 + 3 ^ 40 * 3969842 * 2
def baseEnd_3969842 : Nat := 679479022802054069539345

theorem tailTrace_3969842 : CollatzResearch.WordTrace tailWord_3969842 prefixEnd_3969842 679479022802054069539345 := by
  unfold tailWord_3969842
  simp only [CollatzResearch.WordTrace]
  refine ⟨36198008220986975970191945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 96528021922631935920511853 36198008220986975970191945)
  ·
    refine ⟨27148506165740231977643959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36198008220986975970191945 27148506165740231977643959)
    ·
      refine ⟨40722759248610347966465939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27148506165740231977643959 40722759248610347966465939)
      ·
        refine ⟨61084138872915521949698909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40722759248610347966465939 61084138872915521949698909)
        ·
          refine ⟨22906552077343320731137091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 61084138872915521949698909 22906552077343320731137091)
          ·
            refine ⟨34359828116014981096705637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22906552077343320731137091 34359828116014981096705637)
            ·
              refine ⟨6442467771752808955632307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 34359828116014981096705637 6442467771752808955632307)
              ·
                refine ⟨9663701657629213433448461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6442467771752808955632307 9663701657629213433448461)
                ·
                  refine ⟨3623888121610955037543173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9663701657629213433448461 3623888121610955037543173)
                  ·
                    refine ⟨679479022802054069539345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3623888121610955037543173 679479022802054069539345)
                    ·
                      rfl

theorem cell23_3969842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 4, 1, 3, 4].length) (baseStart_3969842 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3969842 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3969842 prefixEnd_3969842 := by exact prefixLift 3969842
  have htrace : WordTrace (prefixWord ++ tailWord_3969842) baseStart_3969842 baseEnd_3969842 := by
    simpa [prefixWord, tailWord_3969842, baseEnd_3969842] using wordTrace_append hprefix tailTrace_3969842
  have hstable : (prefixWord ++ tailWord_3969842).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3969842).length < 2 ^ (prefixWord ++ tailWord_3969842).sum := by decide
  have hdescent : baseEnd_3969842 < baseStart_3969842 := by decide
  rcases family_descends (prefixWord ++ tailWord_3969842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3969899 : List Nat := [1, 1, 1, 1, 2, 2, 4, 6, 1, 1, 3]
def baseStart_3969899 : Nat := 118140960795 + 3969899 * 2 ^ 59
def prefixEnd_3969899 : Nat := 4983230072969 + 3 ^ 40 * 3969899 * 2
def baseEnd_3969899 : Nat := 2038466336803468485605273

theorem tailTrace_3969899 : CollatzResearch.WordTrace tailWord_3969899 prefixEnd_3969899 2038466336803468485605273 := by
  unfold tailWord_3969899
  simp only [CollatzResearch.WordTrace]
  refine ⟨144794111844741402615592751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96529407896494268410395167 144794111844741402615592751)
  ·
    refine ⟨217191167767112103923389127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144794111844741402615592751 217191167767112103923389127)
    ·
      refine ⟨325786751650668155885083691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 217191167767112103923389127 325786751650668155885083691)
      ·
        refine ⟨488680127476002233827625537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 325786751650668155885083691 488680127476002233827625537)
        ·
          refine ⟨366510095607001675370719153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 488680127476002233827625537 366510095607001675370719153)
          ·
            refine ⟨274882571705251256528039365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 366510095607001675370719153 274882571705251256528039365)
            ·
              refine ⟨51540482194734610599007381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 274882571705251256528039365 51540482194734610599007381)
              ·
                refine ⟨2415960102878184871828471, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 51540482194734610599007381 2415960102878184871828471)
                ·
                  refine ⟨3623940154317277307742707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2415960102878184871828471 3623940154317277307742707)
                  ·
                    refine ⟨5435910231475915961614061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3623940154317277307742707 5435910231475915961614061)
                    ·
                      refine ⟨2038466336803468485605273, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5435910231475915961614061 2038466336803468485605273)
                      ·
                        rfl

theorem cell23_3969899_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 4, 6, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 4, 6, 1, 1, 3].length) (baseStart_3969899 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3969899 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3969899 prefixEnd_3969899 := by exact prefixLift 3969899
  have htrace : WordTrace (prefixWord ++ tailWord_3969899) baseStart_3969899 baseEnd_3969899 := by
    simpa [prefixWord, tailWord_3969899, baseEnd_3969899] using wordTrace_append hprefix tailTrace_3969899
  have hstable : (prefixWord ++ tailWord_3969899).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3969899).length < 2 ^ (prefixWord ++ tailWord_3969899).sum := by decide
  have hdescent : baseEnd_3969899 < baseStart_3969899 := by decide
  rcases family_descends (prefixWord ++ tailWord_3969899) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3969949 : List Nat := [1, 4, 2, 1, 2, 1, 4, 2, 2, 4]
def baseStart_3969949 : Nat := 118140960795 + 3969949 * 2 ^ 59
def prefixEnd_3969949 : Nat := 4983230072969 + 3 ^ 40 * 3969949 * 2
def baseEnd_3969949 : Nat := 679497336945397763326681

theorem tailTrace_3969949 : CollatzResearch.WordTrace tailWord_3969949 prefixEnd_3969949 679497336945397763326681 := by
  unfold tailWord_3969949
  simp only [CollatzResearch.WordTrace]
  refine ⟨144795935494560261154912901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96530623663040174103275267 144795935494560261154912901)
  ·
    refine ⟨27149237905230048966546169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 144795935494560261154912901 27149237905230048966546169)
    ·
      refine ⟨20361928428922536724909627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27149237905230048966546169 20361928428922536724909627)
      ·
        refine ⟨30542892643383805087364441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20361928428922536724909627 30542892643383805087364441)
        ·
          refine ⟨22907169482537853815523331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30542892643383805087364441 22907169482537853815523331)
          ·
            refine ⟨34360754223806780723284997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22907169482537853815523331 34360754223806780723284997)
            ·
              refine ⟨6442641416963771385615937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 34360754223806780723284997 6442641416963771385615937)
              ·
                refine ⟨4831981062722828539211953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6442641416963771385615937 4831981062722828539211953)
                ·
                  refine ⟨3623985797042121404408965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4831981062722828539211953 3623985797042121404408965)
                  ·
                    refine ⟨679497336945397763326681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3623985797042121404408965 679497336945397763326681)
                    ·
                      rfl

theorem cell23_3969949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 4, 2, 2, 4].length) (baseStart_3969949 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3969949 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3969949 prefixEnd_3969949 := by exact prefixLift 3969949
  have htrace : WordTrace (prefixWord ++ tailWord_3969949) baseStart_3969949 baseEnd_3969949 := by
    simpa [prefixWord, tailWord_3969949, baseEnd_3969949] using wordTrace_append hprefix tailTrace_3969949
  have hstable : (prefixWord ++ tailWord_3969949).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3969949).length < 2 ^ (prefixWord ++ tailWord_3969949).sum := by decide
  have hdescent : baseEnd_3969949 < baseStart_3969949 := by decide
  rcases family_descends (prefixWord ++ tailWord_3969949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3969969 : List Nat := [1, 2, 2, 4, 3, 1, 2, 1, 1, 2, 4]
def baseStart_3969969 : Nat := 118140960795 + 3969969 * 2 ^ 59
def prefixEnd_3969969 : Nat := 4983230072969 + 3 ^ 40 * 3969969 * 2
def baseEnd_3969969 : Nat := 2038502280449283211729951

theorem tailTrace_3969969 : CollatzResearch.WordTrace tailWord_3969969 prefixEnd_3969969 2038502280449283211729951 := by
  unfold tailWord_3969969
  simp only [CollatzResearch.WordTrace]
  refine ⟨144796664954487804570640961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96531109969658536380427307 144796664954487804570640961)
  ·
    refine ⟨108597498715865853427980721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 144796664954487804570640961 108597498715865853427980721)
    ·
      refine ⟨81448124036899390070985541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 108597498715865853427980721 81448124036899390070985541)
      ·
        refine ⟨15271523256918635638309789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 81448124036899390070985541 15271523256918635638309789)
        ·
          refine ⟨5726821221344488364366171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15271523256918635638309789 5726821221344488364366171)
          ·
            refine ⟨8590231832016732546549257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5726821221344488364366171 8590231832016732546549257)
            ·
              refine ⟨6442673874012549409911943, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8590231832016732546549257 6442673874012549409911943)
              ·
                refine ⟨9664010811018824114867915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6442673874012549409911943 9664010811018824114867915)
                ·
                  refine ⟨14496016216528236172301873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9664010811018824114867915 14496016216528236172301873)
                  ·
                    refine ⟨10872012162396177129226405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14496016216528236172301873 10872012162396177129226405)
                    ·
                      refine ⟨2038502280449283211729951, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10872012162396177129226405 2038502280449283211729951)
                      ·
                        rfl

theorem cell23_3969969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 3, 1, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 3, 1, 2, 1, 1, 2, 4].length) (baseStart_3969969 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3969969 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3969969 prefixEnd_3969969 := by exact prefixLift 3969969
  have htrace : WordTrace (prefixWord ++ tailWord_3969969) baseStart_3969969 baseEnd_3969969 := by
    simpa [prefixWord, tailWord_3969969, baseEnd_3969969] using wordTrace_append hprefix tailTrace_3969969
  have hstable : (prefixWord ++ tailWord_3969969).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3969969).length < 2 ^ (prefixWord ++ tailWord_3969969).sum := by decide
  have hdescent : baseEnd_3969969 < baseStart_3969969 := by decide
  rcases family_descends (prefixWord ++ tailWord_3969969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3970023 : List Nat := [1, 1, 5, 2, 2, 2, 3, 1, 2, 1, 3]
def baseStart_3970023 : Nat := 118140960795 + 3970023 * 2 ^ 59
def prefixEnd_3970023 : Nat := 4983230072969 + 3 ^ 40 * 3970023 * 2
def baseEnd_3970023 : Nat := 2038530008404626000454703

theorem tailTrace_3970023 : CollatzResearch.WordTrace tailWord_3970023 prefixEnd_3970023 2038530008404626000454703 := by
  unfold tailWord_3970023
  simp only [CollatzResearch.WordTrace]
  refine ⟨144798634496292171793106723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96532422997528114528737815 144798634496292171793106723)
  ·
    refine ⟨217197951744438257689660085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144798634496292171793106723 217197951744438257689660085)
    ·
      refine ⟨20362307976041086658405633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 217197951744438257689660085 20362307976041086658405633)
      ·
        refine ⟨15271730982030814993804225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20362307976041086658405633 15271730982030814993804225)
        ·
          refine ⟨11453798236523111245353169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15271730982030814993804225 11453798236523111245353169)
          ·
            refine ⟨8590348677392333434014877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11453798236523111245353169 8590348677392333434014877)
            ·
              refine ⟨3221380754022125037755579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8590348677392333434014877 3221380754022125037755579)
              ·
                refine ⟨4832071131033187556633369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3221380754022125037755579 4832071131033187556633369)
                ·
                  refine ⟨3624053348274890667475027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4832071131033187556633369 3624053348274890667475027)
                  ·
                    refine ⟨5436080022412336001212541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3624053348274890667475027 5436080022412336001212541)
                    ·
                      refine ⟨2038530008404626000454703, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5436080022412336001212541 2038530008404626000454703)
                      ·
                        rfl

theorem cell23_3970023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 2, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 2, 3, 1, 2, 1, 3].length) (baseStart_3970023 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3970023 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3970023 prefixEnd_3970023 := by exact prefixLift 3970023
  have htrace : WordTrace (prefixWord ++ tailWord_3970023) baseStart_3970023 baseEnd_3970023 := by
    simpa [prefixWord, tailWord_3970023, baseEnd_3970023] using wordTrace_append hprefix tailTrace_3970023
  have hstable : (prefixWord ++ tailWord_3970023).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3970023).length < 2 ^ (prefixWord ++ tailWord_3970023).sum := by decide
  have hdescent : baseEnd_3970023 < baseStart_3970023 := by decide
  rcases family_descends (prefixWord ++ tailWord_3970023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3970069 : List Nat := [1, 3, 2, 1, 4, 3, 1, 1, 7]
def baseStart_3970069 : Nat := 118140960795 + 3970069 * 2 ^ 59
def prefixEnd_3970069 : Nat := 4983230072969 + 3 ^ 40 * 3970069 * 2
def baseEnd_3970069 : Nat := 226505958723859202275499

theorem tailTrace_3970069 : CollatzResearch.WordTrace tailWord_3970069 prefixEnd_3970069 226505958723859202275499 := by
  unfold tailWord_3970069
  simp only [CollatzResearch.WordTrace]
  refine ⟨144800312254125521649281261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96533541502750347766187507 144800312254125521649281261)
  ·
    refine ⟨54300117095297070618480473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 144800312254125521649281261 54300117095297070618480473)
    ·
      refine ⟨40725087821472802963860355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54300117095297070618480473 40725087821472802963860355)
      ·
        refine ⟨61087631732209204445790533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40725087821472802963860355 61087631732209204445790533)
        ·
          refine ⟨11453930949789225833585725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 61087631732209204445790533 11453930949789225833585725)
          ·
            refine ⟨4295224106170959687594647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11453930949789225833585725 4295224106170959687594647)
            ·
              refine ⟨6442836159256439531391971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4295224106170959687594647 6442836159256439531391971)
              ·
                refine ⟨9664254238884659297087957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6442836159256439531391971 9664254238884659297087957)
                ·
                  refine ⟨226505958723859202275499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9664254238884659297087957 226505958723859202275499)
                  ·
                    rfl

theorem cell23_3970069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 3, 1, 1, 7].length) (baseStart_3970069 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3970069 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3970069 prefixEnd_3970069 := by exact prefixLift 3970069
  have htrace : WordTrace (prefixWord ++ tailWord_3970069) baseStart_3970069 baseEnd_3970069 := by
    simpa [prefixWord, tailWord_3970069, baseEnd_3970069] using wordTrace_append hprefix tailTrace_3970069
  have hstable : (prefixWord ++ tailWord_3970069).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3970069).length < 2 ^ (prefixWord ++ tailWord_3970069).sum := by decide
  have hdescent : baseEnd_3970069 < baseStart_3970069 := by decide
  rcases family_descends (prefixWord ++ tailWord_3970069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3970080 : List Nat := [2, 1, 1, 7, 1, 1, 1, 3, 2, 2, 2]
def baseStart_3970080 : Nat := 118140960795 + 3970080 * 2 ^ 59
def prefixEnd_3970080 : Nat := 4983230072969 + 3 ^ 40 * 3970080 * 2
def baseEnd_3970080 : Nat := 2038559276801932277441941

theorem tailTrace_3970080 : CollatzResearch.WordTrace tailWord_3970080 prefixEnd_3970080 2038559276801932277441941 := by
  unfold tailWord_3970080
  simp only [CollatzResearch.WordTrace]
  refine ⟨72400356728542835263965847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96533808971390447018621129 72400356728542835263965847)
  ·
    refine ⟨108600535092814252895948771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72400356728542835263965847 108600535092814252895948771)
    ·
      refine ⟨162900802639221379343923157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108600535092814252895948771 162900802639221379343923157)
      ·
        refine ⟨3817987561856751078373199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 162900802639221379343923157 3817987561856751078373199)
        ·
          refine ⟨5726981342785126617559799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3817987561856751078373199 5726981342785126617559799)
          ·
            refine ⟨8590472014177689926339699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5726981342785126617559799 8590472014177689926339699)
            ·
              refine ⟨12885708021266534889509549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8590472014177689926339699 12885708021266534889509549)
              ·
                refine ⟨4832140507974950583566081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12885708021266534889509549 4832140507974950583566081)
                ·
                  refine ⟨3624105380981212937674561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4832140507974950583566081 3624105380981212937674561)
                  ·
                    refine ⟨2718079035735909703255921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3624105380981212937674561 2718079035735909703255921)
                    ·
                      refine ⟨2038559276801932277441941, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2718079035735909703255921 2038559276801932277441941)
                      ·
                        rfl

theorem cell23_3970080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 1, 1, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 1, 1, 1, 3, 2, 2, 2].length) (baseStart_3970080 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3970080 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3970080 prefixEnd_3970080 := by exact prefixLift 3970080
  have htrace : WordTrace (prefixWord ++ tailWord_3970080) baseStart_3970080 baseEnd_3970080 := by
    simpa [prefixWord, tailWord_3970080, baseEnd_3970080] using wordTrace_append hprefix tailTrace_3970080
  have hstable : (prefixWord ++ tailWord_3970080).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3970080).length < 2 ^ (prefixWord ++ tailWord_3970080).sum := by decide
  have hdescent : baseEnd_3970080 < baseStart_3970080 := by decide
  rcases family_descends (prefixWord ++ tailWord_3970080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3970119 : List Nat := [1, 1, 4, 1, 3, 2, 2, 2, 2, 1, 4]
def baseStart_3970119 : Nat := 118140960795 + 3970119 * 2 ^ 59
def prefixEnd_3970119 : Nat := 4983230072969 + 3 ^ 40 * 3970119 * 2
def baseEnd_3970119 : Nat := 2038579302547457624854261

theorem tailTrace_3970119 : CollatzResearch.WordTrace tailWord_3970119 prefixEnd_3970119 2038579302547457624854261 := by
  unfold tailWord_3970119
  simp only [CollatzResearch.WordTrace]
  refine ⟨144802135903944380188601411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96534757269296253459067607 144802135903944380188601411)
  ·
    refine ⟨217203203855916570282902117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144802135903944380188601411 217203203855916570282902117)
    ·
      refine ⟨40725600722984356928044147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 217203203855916570282902117 40725600722984356928044147)
      ·
        refine ⟨61088401084476535392066221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40725600722984356928044147 61088401084476535392066221)
        ·
          refine ⟨22908150406678700772024833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 61088401084476535392066221 22908150406678700772024833)
          ·
            refine ⟨17181112805009025579018625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22908150406678700772024833 17181112805009025579018625)
            ·
              refine ⟨12885834603756769184263969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17181112805009025579018625 12885834603756769184263969)
              ·
                refine ⟨9664375952817576888197977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12885834603756769184263969 9664375952817576888197977)
                ·
                  refine ⟨7248281964613182666148483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9664375952817576888197977 7248281964613182666148483)
                  ·
                    refine ⟨10872422946919773999222725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7248281964613182666148483 10872422946919773999222725)
                    ·
                      refine ⟨2038579302547457624854261, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10872422946919773999222725 2038579302547457624854261)
                      ·
                        rfl

theorem cell23_3970119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 2, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 2, 2, 2, 2, 1, 4].length) (baseStart_3970119 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3970119 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3970119 prefixEnd_3970119 := by exact prefixLift 3970119
  have htrace : WordTrace (prefixWord ++ tailWord_3970119) baseStart_3970119 baseEnd_3970119 := by
    simpa [prefixWord, tailWord_3970119, baseEnd_3970119] using wordTrace_append hprefix tailTrace_3970119
  have hstable : (prefixWord ++ tailWord_3970119).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3970119).length < 2 ^ (prefixWord ++ tailWord_3970119).sum := by decide
  have hdescent : baseEnd_3970119 < baseStart_3970119 := by decide
  rcases family_descends (prefixWord ++ tailWord_3970119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3970146 : List Nat := [3, 3, 2, 2, 1, 1, 1, 1, 5, 4]
def baseStart_3970146 : Nat := 118140960795 + 3970146 * 2 ^ 59
def prefixEnd_3970146 : Nat := 4983230072969 + 3 ^ 40 * 3970146 * 2
def baseEnd_3970146 : Nat := 679531055508376339738879

theorem tailTrace_3970146 : CollatzResearch.WordTrace tailWord_3970146 prefixEnd_3970146 679531055508376339738879 := by
  unfold tailWord_3970146
  simp only [CollatzResearch.WordTrace]
  refine ⟨36200780168711640949958573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 96535413783231042533222861 36200780168711640949958573)
  ·
    refine ⟨13575292563266865356234465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36200780168711640949958573 13575292563266865356234465)
    ·
      refine ⟨10181469422450149017175849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13575292563266865356234465 10181469422450149017175849)
      ·
        refine ⟨7636102066837611762881887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10181469422450149017175849 7636102066837611762881887)
        ·
          refine ⟨11454153100256417644322831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7636102066837611762881887 11454153100256417644322831)
          ·
            refine ⟨17181229650384626466484247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11454153100256417644322831 17181229650384626466484247)
            ·
              refine ⟨25771844475576939699726371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17181229650384626466484247 25771844475576939699726371)
              ·
                refine ⟨38657766713365409549589557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25771844475576939699726371 38657766713365409549589557)
                ·
                  refine ⟨3624165629378007145274021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 38657766713365409549589557 3624165629378007145274021)
                  ·
                    refine ⟨679531055508376339738879, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3624165629378007145274021 679531055508376339738879)
                    ·
                      rfl

theorem cell23_3970146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 1, 1, 1, 5, 4].length) (baseStart_3970146 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3970146 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3970146 prefixEnd_3970146 := by exact prefixLift 3970146
  have htrace : WordTrace (prefixWord ++ tailWord_3970146) baseStart_3970146 baseEnd_3970146 := by
    simpa [prefixWord, tailWord_3970146, baseEnd_3970146] using wordTrace_append hprefix tailTrace_3970146
  have hstable : (prefixWord ++ tailWord_3970146).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3970146).length < 2 ^ (prefixWord ++ tailWord_3970146).sum := by decide
  have hdescent : baseEnd_3970146 < baseStart_3970146 := by decide
  rcases family_descends (prefixWord ++ tailWord_3970146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3970192 : List Nat := [2, 1, 1, 1, 1, 1, 4, 1, 2, 5, 4]
def baseStart_3970192 : Nat := 118140960795 + 3970192 * 2 ^ 59
def prefixEnd_3970192 : Nat := 4983230072969 + 3 ^ 40 * 3970192 * 2
def baseEnd_3970192 : Nat := 2038616786635235839241425

theorem tailTrace_3970192 : CollatzResearch.WordTrace tailWord_3970192 prefixEnd_3970192 2038616786635235839241425 := by
  unfold tailWord_3970192
  simp only [CollatzResearch.WordTrace]
  refine ⟨72402399216339956828004415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96536532288453275770672553 72402399216339956828004415)
  ·
    refine ⟨108603598824509935242006623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72402399216339956828004415 108603598824509935242006623)
    ·
      refine ⟨162905398236764902863009935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108603598824509935242006623 162905398236764902863009935)
      ·
        refine ⟨244358097355147354294514903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 162905398236764902863009935 244358097355147354294514903)
        ·
          refine ⟨366537146032721031441772355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 244358097355147354294514903 366537146032721031441772355)
          ·
            refine ⟨549805719049081547162658533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 366537146032721031441772355 549805719049081547162658533)
            ·
              refine ⟨103088572321702790092998475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 549805719049081547162658533 103088572321702790092998475)
              ·
                refine ⟨154632858482554185139497713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 103088572321702790092998475 154632858482554185139497713)
                ·
                  refine ⟨115974643861915638854623285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 154632858482554185139497713 115974643861915638854623285)
                  ·
                    refine ⟨10872622862054591142620933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 115974643861915638854623285 10872622862054591142620933)
                    ·
                      refine ⟨2038616786635235839241425, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10872622862054591142620933 2038616786635235839241425)
                      ·
                        rfl

theorem cell23_3970192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 4, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 4, 1, 2, 5, 4].length) (baseStart_3970192 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3970192 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3970192 prefixEnd_3970192 := by exact prefixLift 3970192
  have htrace : WordTrace (prefixWord ++ tailWord_3970192) baseStart_3970192 baseEnd_3970192 := by
    simpa [prefixWord, tailWord_3970192, baseEnd_3970192] using wordTrace_append hprefix tailTrace_3970192
  have hstable : (prefixWord ++ tailWord_3970192).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3970192).length < 2 ^ (prefixWord ++ tailWord_3970192).sum := by decide
  have hdescent : baseEnd_3970192 < baseStart_3970192 := by decide
  rcases family_descends (prefixWord ++ tailWord_3970192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3970226 : List Nat := [3, 2, 1, 1, 1, 4, 2, 3, 1, 1, 4]
def baseStart_3970226 : Nat := 118140960795 + 3970226 * 2 ^ 59
def prefixEnd_3970226 : Nat := 4983230072969 + 3 ^ 40 * 3970226 * 2
def baseEnd_3970226 : Nat := 2038634244977488706216269

theorem tailTrace_3970226 : CollatzResearch.WordTrace tailWord_3970226 prefixEnd_3970226 2038634244977488706216269 := by
  unfold tailWord_3970226
  simp only [CollatzResearch.WordTrace]
  refine ⟨36201509628639184365686633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 96537359009704491641831021 36201509628639184365686633)
  ·
    refine ⟨27151132221479388274264975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36201509628639184365686633 27151132221479388274264975)
    ·
      refine ⟨40726698332219082411397463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27151132221479388274264975 40726698332219082411397463)
      ·
        refine ⟨61090047498328623617096195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40726698332219082411397463 61090047498328623617096195)
        ·
          refine ⟨91635071247492935425644293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61090047498328623617096195 91635071247492935425644293)
          ·
            refine ⟨17181575858904925392308305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 91635071247492935425644293 17181575858904925392308305)
            ·
              refine ⟨12886181894178694044231229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17181575858904925392308305 12886181894178694044231229)
              ·
                refine ⟨4832318210317010266586711, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12886181894178694044231229 4832318210317010266586711)
                ·
                  refine ⟨7248477315475515399880067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4832318210317010266586711 7248477315475515399880067)
                  ·
                    refine ⟨10872715973213273099820101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7248477315475515399880067 10872715973213273099820101)
                    ·
                      refine ⟨2038634244977488706216269, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10872715973213273099820101 2038634244977488706216269)
                      ·
                        rfl

theorem cell23_3970226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 4, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 4, 2, 3, 1, 1, 4].length) (baseStart_3970226 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3970226 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3970226 prefixEnd_3970226 := by exact prefixLift 3970226
  have htrace : WordTrace (prefixWord ++ tailWord_3970226) baseStart_3970226 baseEnd_3970226 := by
    simpa [prefixWord, tailWord_3970226, baseEnd_3970226] using wordTrace_append hprefix tailTrace_3970226
  have hstable : (prefixWord ++ tailWord_3970226).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3970226).length < 2 ^ (prefixWord ++ tailWord_3970226).sum := by decide
  have hdescent : baseEnd_3970226 < baseStart_3970226 := by decide
  rcases family_descends (prefixWord ++ tailWord_3970226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3970236 : List Nat := [2, 2, 2, 3, 2, 1, 2, 1, 4, 4]
def baseStart_3970236 : Nat := 118140960795 + 3970236 * 2 ^ 59
def prefixEnd_3970236 : Nat := 4983230072969 + 3 ^ 40 * 3970236 * 2
def baseEnd_3970236 : Nat := 679546459928011222363741

theorem tailTrace_3970236 : CollatzResearch.WordTrace tailWord_3970236 prefixEnd_3970236 679546459928011222363741 := by
  unfold tailWord_3970236
  simp only [CollatzResearch.WordTrace]
  refine ⟨72403201622260254585305281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96537602163013672780407041 72403201622260254585305281)
  ·
    refine ⟨54302401216695190938978961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72403201622260254585305281 54302401216695190938978961)
    ·
      refine ⟨40726800912521393204234221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54302401216695190938978961 40726800912521393204234221)
      ·
        refine ⟨15272550342195522451587833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40726800912521393204234221 15272550342195522451587833)
        ·
          refine ⟨11454412756646641838690875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15272550342195522451587833 11454412756646641838690875)
          ·
            refine ⟨17181619134969962758036313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11454412756646641838690875 17181619134969962758036313)
            ·
              refine ⟨12886214351227472068527235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17181619134969962758036313 12886214351227472068527235)
              ·
                refine ⟨19329321526841208102790853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12886214351227472068527235 19329321526841208102790853)
                ·
                  refine ⟨3624247786282726519273285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19329321526841208102790853 3624247786282726519273285)
                  ·
                    refine ⟨679546459928011222363741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3624247786282726519273285 679546459928011222363741)
                    ·
                      rfl

theorem cell23_3970236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 1, 2, 1, 4, 4].length) (baseStart_3970236 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3970236 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3970236 prefixEnd_3970236 := by exact prefixLift 3970236
  have htrace : WordTrace (prefixWord ++ tailWord_3970236) baseStart_3970236 baseEnd_3970236 := by
    simpa [prefixWord, tailWord_3970236, baseEnd_3970236] using wordTrace_append hprefix tailTrace_3970236
  have hstable : (prefixWord ++ tailWord_3970236).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3970236).length < 2 ^ (prefixWord ++ tailWord_3970236).sum := by decide
  have hdescent : baseEnd_3970236 < baseStart_3970236 := by decide
  rcases family_descends (prefixWord ++ tailWord_3970236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3970276 : List Nat := [2, 3, 1, 1, 1, 2, 2, 1, 6, 1, 3]
def baseStart_3970276 : Nat := 118140960795 + 3970276 * 2 ^ 59
def prefixEnd_3970276 : Nat := 4983230072969 + 3 ^ 40 * 3970276 * 2
def baseEnd_3970276 : Nat := 2038659919010213510591039

theorem tailTrace_3970276 : CollatzResearch.WordTrace tailWord_3970276 prefixEnd_3970276 2038659919010213510591039 := by
  unfold tailWord_3970276
  simp only [CollatzResearch.WordTrace]
  refine ⟨72403931082187798001033341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96538574776250397334711121 72403931082187798001033341)
  ·
    refine ⟨27151474155820424250387503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 72403931082187798001033341 27151474155820424250387503)
    ·
      refine ⟨40727211233730636375581255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27151474155820424250387503 40727211233730636375581255)
      ·
        refine ⟨61090816850595954563371883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40727211233730636375581255 61090816850595954563371883)
        ·
          refine ⟨91636225275893931845057825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61090816850595954563371883 91636225275893931845057825)
          ·
            refine ⟨68727168956920448883793369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 91636225275893931845057825 68727168956920448883793369)
            ·
              refine ⟨51545376717690336662845027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 68727168956920448883793369 51545376717690336662845027)
              ·
                refine ⟨77318065076535504994267541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51545376717690336662845027 77318065076535504994267541)
                ·
                  refine ⟨3624284300462601796606291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 77318065076535504994267541 3624284300462601796606291)
                  ·
                    refine ⟨5436426450693902694909437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3624284300462601796606291 5436426450693902694909437)
                    ·
                      refine ⟨2038659919010213510591039, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5436426450693902694909437 2038659919010213510591039)
                      ·
                        rfl

theorem cell23_3970276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 2, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 2, 1, 6, 1, 3].length) (baseStart_3970276 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3970276 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3970276 prefixEnd_3970276 := by exact prefixLift 3970276
  have htrace : WordTrace (prefixWord ++ tailWord_3970276) baseStart_3970276 baseEnd_3970276 := by
    simpa [prefixWord, tailWord_3970276, baseEnd_3970276] using wordTrace_append hprefix tailTrace_3970276
  have hstable : (prefixWord ++ tailWord_3970276).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3970276).length < 2 ^ (prefixWord ++ tailWord_3970276).sum := by decide
  have hdescent : baseEnd_3970276 < baseStart_3970276 := by decide
  rcases family_descends (prefixWord ++ tailWord_3970276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3970309 : List Nat := [1, 3, 1, 1, 2, 1, 5, 1, 2, 6]
def baseStart_3970309 : Nat := 118140960795 + 3970309 * 2 ^ 59
def prefixEnd_3970309 : Nat := 4983230072969 + 3 ^ 40 * 3970309 * 2
def baseEnd_3970309 : Nat := 679558954623937293826129

theorem tailTrace_3970309 : CollatzResearch.WordTrace tailWord_3970309 prefixEnd_3970309 679558954623937293826129 := by
  unfold tailWord_3970309
  simp only [CollatzResearch.WordTrace]
  refine ⟨144809065773256042638017981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96539377182170695092011987 144809065773256042638017981)
  ·
    refine ⟨54303399664971015989256743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 144809065773256042638017981 54303399664971015989256743)
    ·
      refine ⟨81455099497456523983885115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54303399664971015989256743 81455099497456523983885115)
      ·
        refine ⟨122182649246184785975827673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81455099497456523983885115 122182649246184785975827673)
        ·
          refine ⟨91636986934638589481870755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 122182649246184785975827673 91636986934638589481870755)
          ·
            refine ⟨137455480401957884222806133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91636986934638589481870755 137455480401957884222806133)
            ·
              refine ⟨12886451287683551645888075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 137455480401957884222806133 12886451287683551645888075)
              ·
                refine ⟨19329676931525327468832113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12886451287683551645888075 19329676931525327468832113)
                ·
                  refine ⟨14497257698643995601624085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19329676931525327468832113 14497257698643995601624085)
                  ·
                    refine ⟨679558954623937293826129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14497257698643995601624085 679558954623937293826129)
                    ·
                      rfl

theorem cell23_3970309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 5, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 5, 1, 2, 6].length) (baseStart_3970309 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3970309 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3970309 prefixEnd_3970309 := by exact prefixLift 3970309
  have htrace : WordTrace (prefixWord ++ tailWord_3970309) baseStart_3970309 baseEnd_3970309 := by
    simpa [prefixWord, tailWord_3970309, baseEnd_3970309] using wordTrace_append hprefix tailTrace_3970309
  have hstable : (prefixWord ++ tailWord_3970309).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3970309).length < 2 ^ (prefixWord ++ tailWord_3970309).sum := by decide
  have hdescent : baseEnd_3970309 < baseStart_3970309 := by decide
  rcases family_descends (prefixWord ++ tailWord_3970309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3970367 : List Nat := [1, 1, 2, 2, 4, 3, 3, 1, 2, 2, 2]
def baseStart_3970367 : Nat := 118140960795 + 3970367 * 2 ^ 59
def prefixEnd_3970367 : Nat := 4983230072969 + 3 ^ 40 * 3970367 * 2
def baseEnd_3970367 : Nat := 2038706645749772654553121

theorem tailTrace_3970367 : CollatzResearch.WordTrace tailWord_3970367 prefixEnd_3970367 2038706645749772654553121 := by
  unfold tailWord_3970367
  simp only [CollatzResearch.WordTrace]
  refine ⟨144811181207045918543629355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96540787471363945695752903 144811181207045918543629355)
  ·
    refine ⟨217216771810568877815444033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144811181207045918543629355 217216771810568877815444033)
    ·
      refine ⟨162912578857926658361583025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 217216771810568877815444033 162912578857926658361583025)
      ·
        refine ⟨122184434143444993771187269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 162912578857926658361583025 122184434143444993771187269)
        ·
          refine ⟨22909581401895936332097613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 122184434143444993771187269 22909581401895936332097613)
          ·
            refine ⟨8591093025710976124536605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22909581401895936332097613 8591093025710976124536605)
            ·
              refine ⟨3221659884641616046701227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8591093025710976124536605 3221659884641616046701227)
              ·
                refine ⟨4832489826962424070051841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3221659884641616046701227 4832489826962424070051841)
                ·
                  refine ⟨3624367370221818052538881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4832489826962424070051841 3624367370221818052538881)
                  ·
                    refine ⟨2718275527666363539404161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3624367370221818052538881 2718275527666363539404161)
                    ·
                      refine ⟨2038706645749772654553121, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2718275527666363539404161 2038706645749772654553121)
                      ·
                        rfl

theorem cell23_3970367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 3, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 3, 3, 1, 2, 2, 2].length) (baseStart_3970367 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3970367 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3970367 prefixEnd_3970367 := by exact prefixLift 3970367
  have htrace : WordTrace (prefixWord ++ tailWord_3970367) baseStart_3970367 baseEnd_3970367 := by
    simpa [prefixWord, tailWord_3970367, baseEnd_3970367] using wordTrace_append hprefix tailTrace_3970367
  have hstable : (prefixWord ++ tailWord_3970367).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3970367).length < 2 ^ (prefixWord ++ tailWord_3970367).sum := by decide
  have hdescent : baseEnd_3970367 < baseStart_3970367 := by decide
  rcases family_descends (prefixWord ++ tailWord_3970367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3970386 : List Nat := [3, 2, 2, 1, 1, 1, 1, 5, 2, 5]
def baseStart_3970386 : Nat := 118140960795 + 3970386 * 2 ^ 59
def prefixEnd_3970386 : Nat := 4983230072969 + 3 ^ 40 * 3970386 * 2
def baseEnd_3970386 : Nat := 679572133960736026738511

theorem tailTrace_3970386 : CollatzResearch.WordTrace tailWord_3970386 prefixEnd_3970386 679572133960736026738511 := by
  unfold tailWord_3970386
  simp only [CollatzResearch.WordTrace]
  refine ⟨36202968548494271197142753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 96541249462651389859047341 36202968548494271197142753)
  ·
    refine ⟨27152226411370703397857065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36202968548494271197142753 27152226411370703397857065)
    ·
      refine ⟨20364169808528027548392799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27152226411370703397857065 20364169808528027548392799)
      ·
        refine ⟨30546254712792041322589199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20364169808528027548392799 30546254712792041322589199)
        ·
          refine ⟨45819382069188061983883799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30546254712792041322589199 45819382069188061983883799)
          ·
            refine ⟨68729073103782092975825699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45819382069188061983883799 68729073103782092975825699)
            ·
              refine ⟨103093609655673139463738549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68729073103782092975825699 103093609655673139463738549)
              ·
                refine ⟨9665025905219356824725489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 103093609655673139463738549 9665025905219356824725489)
                ·
                  refine ⟨7248769428914517618544117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9665025905219356824725489 7248769428914517618544117)
                  ·
                    refine ⟨679572133960736026738511, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7248769428914517618544117 679572133960736026738511)
                    ·
                      rfl

theorem cell23_3970386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 1, 5, 2, 5].length) (baseStart_3970386 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3970386 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3970386 prefixEnd_3970386 := by exact prefixLift 3970386
  have htrace : WordTrace (prefixWord ++ tailWord_3970386) baseStart_3970386 baseEnd_3970386 := by
    simpa [prefixWord, tailWord_3970386, baseEnd_3970386] using wordTrace_append hprefix tailTrace_3970386
  have hstable : (prefixWord ++ tailWord_3970386).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3970386).length < 2 ^ (prefixWord ++ tailWord_3970386).sum := by decide
  have hdescent : baseEnd_3970386 < baseStart_3970386 := by decide
  rcases family_descends (prefixWord ++ tailWord_3970386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3970409 : List Nat := [1, 2, 1, 1, 1, 3, 2, 1, 1, 5, 5]
def baseStart_3970409 : Nat := 118140960795 + 3970409 * 2 ^ 59
def prefixEnd_3970409 : Nat := 4983230072969 + 3 ^ 40 * 3970409 * 2
def baseEnd_3970409 : Nat := 2038728211937261490227927

theorem tailTrace_3970409 : CollatzResearch.WordTrace tailWord_3970409 prefixEnd_3970409 2038728211937261490227927 := by
  unfold tailWord_3970409
  simp only [CollatzResearch.WordTrace]
  refine ⟨144812713072893759716658281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96541808715262506477772187 144812713072893759716658281)
  ·
    refine ⟨108609534804670319787493711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 144812713072893759716658281 108609534804670319787493711)
    ·
      refine ⟨162914302207005479681240567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108609534804670319787493711 162914302207005479681240567)
      ·
        refine ⟨244371453310508219521860851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 162914302207005479681240567 244371453310508219521860851)
        ·
          refine ⟨366557179965762329282791277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 244371453310508219521860851 366557179965762329282791277)
          ·
            refine ⟨137458942487160873481046729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 366557179965762329282791277 137458942487160873481046729)
            ·
              refine ⟨103094206865370655110785047, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 137458942487160873481046729 103094206865370655110785047)
              ·
                refine ⟨154641310298055982666177571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 103094206865370655110785047 154641310298055982666177571)
                ·
                  refine ⟨231961965447083973999266357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 154641310298055982666177571 231961965447083973999266357)
                  ·
                    refine ⟨21746434260664122562431221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 231961965447083973999266357 21746434260664122562431221)
                    ·
                      refine ⟨2038728211937261490227927, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 21746434260664122562431221 2038728211937261490227927)
                      ·
                        rfl

theorem cell23_3970409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 2, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 2, 1, 1, 5, 5].length) (baseStart_3970409 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3970409 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3970409 prefixEnd_3970409 := by exact prefixLift 3970409
  have htrace : WordTrace (prefixWord ++ tailWord_3970409) baseStart_3970409 baseEnd_3970409 := by
    simpa [prefixWord, tailWord_3970409, baseEnd_3970409] using wordTrace_append hprefix tailTrace_3970409
  have hstable : (prefixWord ++ tailWord_3970409).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3970409).length < 2 ^ (prefixWord ++ tailWord_3970409).sum := by decide
  have hdescent : baseEnd_3970409 < baseStart_3970409 := by decide
  rcases family_descends (prefixWord ++ tailWord_3970409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3970443 : List Nat := [1, 1, 1, 1, 4, 3, 4, 1, 2, 2, 3]
def baseStart_3970443 : Nat := 118140960795 + 3970443 * 2 ^ 59
def prefixEnd_3970443 : Nat := 4983230072969 + 3 ^ 40 * 3970443 * 2
def baseEnd_3970443 : Nat := 2038745670279514357202771

theorem tailTrace_3970443 : CollatzResearch.WordTrace tailWord_3970443 prefixEnd_3970443 2038745670279514357202771 := by
  unfold tailWord_3970443
  simp only [CollatzResearch.WordTrace]
  refine ⟨144813953154770583523395983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96542635436513722348930655 144813953154770583523395983)
  ·
    refine ⟨217220929732155875285093975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144813953154770583523395983 217220929732155875285093975)
    ·
      refine ⟨325831394598233812927640963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 217220929732155875285093975 325831394598233812927640963)
      ·
        refine ⟨488747091897350719391461445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 325831394598233812927640963 488747091897350719391461445)
        ·
          refine ⟨91640079730753259885899021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 488747091897350719391461445 91640079730753259885899021)
          ·
            refine ⟨34365029899032472457212133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 91640079730753259885899021 34365029899032472457212133)
            ·
              refine ⟨6443443106068588585727275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 34365029899032472457212133 6443443106068588585727275)
              ·
                refine ⟨9665164659102882878590913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6443443106068588585727275 9665164659102882878590913)
                ·
                  refine ⟨7248873494327162158943185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9665164659102882878590913 7248873494327162158943185)
                  ·
                    refine ⟨5436655120745371619207389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7248873494327162158943185 5436655120745371619207389)
                    ·
                      refine ⟨2038745670279514357202771, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5436655120745371619207389 2038745670279514357202771)
                      ·
                        rfl

theorem cell23_3970443_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 4, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 4, 1, 2, 2, 3].length) (baseStart_3970443 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3970443 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3970443 prefixEnd_3970443 := by exact prefixLift 3970443
  have htrace : WordTrace (prefixWord ++ tailWord_3970443) baseStart_3970443 baseEnd_3970443 := by
    simpa [prefixWord, tailWord_3970443, baseEnd_3970443] using wordTrace_append hprefix tailTrace_3970443
  have hstable : (prefixWord ++ tailWord_3970443).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3970443).length < 2 ^ (prefixWord ++ tailWord_3970443).sum := by decide
  have hdescent : baseEnd_3970443 < baseStart_3970443 := by decide
  rcases family_descends (prefixWord ++ tailWord_3970443) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3970459 : List Nat := [1, 1, 1, 1, 1, 1, 2, 1, 3, 11]
def baseStart_3970459 : Nat := 118140960795 + 3970459 * 2 ^ 59
def prefixEnd_3970459 : Nat := 4983230072969 + 3 ^ 40 * 3970459 * 2
def baseEnd_3970459 : Nat := 679584628656662098200899

theorem tailTrace_3970459 : CollatzResearch.WordTrace tailWord_3970459 prefixEnd_3970459 679584628656662098200899 := by
  unfold tailWord_3970459
  simp only [CollatzResearch.WordTrace]
  refine ⟨144814536722712618255978431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96543024481808412170652287 144814536722712618255978431)
  ·
    refine ⟨217221805084068927383967647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144814536722712618255978431 217221805084068927383967647)
    ·
      refine ⟨325832707626103391075951471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 217221805084068927383967647 325832707626103391075951471)
      ·
        refine ⟨488749061439155086613927207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 325832707626103391075951471 488749061439155086613927207)
        ·
          refine ⟨733123592158732629920890811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 488749061439155086613927207 733123592158732629920890811)
          ·
            refine ⟨1099685388238098944881336217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 733123592158732629920890811 1099685388238098944881336217)
            ·
              refine ⟨824764041178574208661002163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1099685388238098944881336217 824764041178574208661002163)
              ·
                refine ⟨1237146061767861312991503245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 824764041178574208661002163 1237146061767861312991503245)
                ·
                  refine ⟨463929773162947992371813717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1237146061767861312991503245 463929773162947992371813717)
                  ·
                    refine ⟨679584628656662098200899, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 11 463929773162947992371813717 679584628656662098200899)
                    ·
                      rfl

theorem cell23_3970459_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 3, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 3, 11].length) (baseStart_3970459 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3970459 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3970459 prefixEnd_3970459 := by exact prefixLift 3970459
  have htrace : WordTrace (prefixWord ++ tailWord_3970459) baseStart_3970459 baseEnd_3970459 := by
    simpa [prefixWord, tailWord_3970459, baseEnd_3970459] using wordTrace_append hprefix tailTrace_3970459
  have hstable : (prefixWord ++ tailWord_3970459).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3970459).length < 2 ^ (prefixWord ++ tailWord_3970459).sum := by decide
  have hdescent : baseEnd_3970459 < baseStart_3970459 := by decide
  rcases family_descends (prefixWord ++ tailWord_3970459) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3970463 : List Nat := [1, 1, 2, 5, 1, 3, 2, 2, 6]
def baseStart_3970463 : Nat := 118140960795 + 3970463 * 2 ^ 59
def prefixEnd_3970463 : Nat := 4983230072969 + 3 ^ 40 * 3970463 * 2
def baseEnd_3970463 : Nat := 226528437765844919883631

theorem tailTrace_3970463 : CollatzResearch.WordTrace tailWord_3970463 prefixEnd_3970463 226528437765844919883631 := by
  unfold tailWord_3970463
  simp only [CollatzResearch.WordTrace]
  refine ⟨144814682614698126939124043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96543121743132084626082695 144814682614698126939124043)
  ·
    refine ⟨217222023922047190408686065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144814682614698126939124043 217222023922047190408686065)
    ·
      refine ⟨162916517941535392806514549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 217222023922047190408686065 162916517941535392806514549)
      ·
        refine ⟨15273423557018943075610739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 162916517941535392806514549 15273423557018943075610739)
        ·
          refine ⟨22910135335528414613416109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15273423557018943075610739 22910135335528414613416109)
          ·
            refine ⟨8591300750823155480031041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22910135335528414613416109 8591300750823155480031041)
            ·
              refine ⟨6443475563117366610023281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8591300750823155480031041 6443475563117366610023281)
              ·
                refine ⟨4832606672338024957517461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6443475563117366610023281 4832606672338024957517461)
                ·
                  refine ⟨226528437765844919883631, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4832606672338024957517461 226528437765844919883631)
                  ·
                    rfl

theorem cell23_3970463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 3, 2, 2, 6].length) (baseStart_3970463 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3970463 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3970463 prefixEnd_3970463 := by exact prefixLift 3970463
  have htrace : WordTrace (prefixWord ++ tailWord_3970463) baseStart_3970463 baseEnd_3970463 := by
    simpa [prefixWord, tailWord_3970463, baseEnd_3970463] using wordTrace_append hprefix tailTrace_3970463
  have hstable : (prefixWord ++ tailWord_3970463).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3970463).length < 2 ^ (prefixWord ++ tailWord_3970463).sum := by decide
  have hdescent : baseEnd_3970463 < baseStart_3970463 := by decide
  rcases family_descends (prefixWord ++ tailWord_3970463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3970476 : List Nat := [2, 2, 1, 1, 1, 1, 5, 2, 3, 5]
def baseStart_3970476 : Nat := 118140960795 + 3970476 * 2 ^ 59
def prefixEnd_3970476 : Nat := 4983230072969 + 3 ^ 40 * 3970476 * 2
def baseEnd_3970476 : Nat := 679587538380370909363373

theorem tailTrace_3970476 : CollatzResearch.WordTrace tailWord_3970476 prefixEnd_3970476 679587538380370909363373 := by
  unfold tailWord_3970476
  simp only [CollatzResearch.WordTrace]
  refine ⟨72407578381825515079673641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96543437842434020106231521 72407578381825515079673641)
  ·
    refine ⟨54305683786369136309755231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72407578381825515079673641 54305683786369136309755231)
    ·
      refine ⟨81458525679553704464632847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54305683786369136309755231 81458525679553704464632847)
      ·
        refine ⟨122187788519330556696949271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81458525679553704464632847 122187788519330556696949271)
        ·
          refine ⟨183281682778995835045423907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 122187788519330556696949271 183281682778995835045423907)
          ·
            refine ⟨274922524168493752568135861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 183281682778995835045423907 274922524168493752568135861)
            ·
              refine ⟨25773986640796289303262737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 274922524168493752568135861 25773986640796289303262737)
              ·
                refine ⟨19330489980597216977447053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25773986640796289303262737 19330489980597216977447053)
                ·
                  refine ⟨7248933742723956366542645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19330489980597216977447053 7248933742723956366542645)
                  ·
                    refine ⟨679587538380370909363373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7248933742723956366542645 679587538380370909363373)
                    ·
                      rfl

theorem cell23_3970476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 3, 5].length) (baseStart_3970476 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3970476 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3970476 prefixEnd_3970476 := by exact prefixLift 3970476
  have htrace : WordTrace (prefixWord ++ tailWord_3970476) baseStart_3970476 baseEnd_3970476 := by
    simpa [prefixWord, tailWord_3970476, baseEnd_3970476] using wordTrace_append hprefix tailTrace_3970476
  have hstable : (prefixWord ++ tailWord_3970476).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3970476).length < 2 ^ (prefixWord ++ tailWord_3970476).sum := by decide
  have hdescent : baseEnd_3970476 < baseStart_3970476 := by decide
  rcases family_descends (prefixWord ++ tailWord_3970476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3970483 : List Nat := [1, 1, 1, 2, 3, 1, 1, 4, 4, 3, 2]
def baseStart_3970483 : Nat := 118140960795 + 3970483 * 2 ^ 59
def prefixEnd_3970483 : Nat := 4983230072969 + 3 ^ 40 * 3970483 * 2
def baseEnd_3970483 : Nat := 2038766209505694200702587

theorem tailTrace_3970483 : CollatzResearch.WordTrace tailWord_3970483 prefixEnd_3970483 2038766209505694200702587 := by
  unfold tailWord_3970483
  simp only [CollatzResearch.WordTrace]
  refine ⟨144815412074625670354852103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96543608049750446903234735 144815412074625670354852103)
  ·
    refine ⟨217223118111938505532278155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144815412074625670354852103 217223118111938505532278155)
    ·
      refine ⟨325834677167907758298417233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 217223118111938505532278155 325834677167907758298417233)
      ·
        refine ⟨244376007875930818723812925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 325834677167907758298417233 244376007875930818723812925)
        ·
          refine ⟨91641002953474057021429847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 244376007875930818723812925 91641002953474057021429847)
          ·
            refine ⟨137461504430211085532144771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91641002953474057021429847 137461504430211085532144771)
            ·
              refine ⟨206192256645316628298217157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 137461504430211085532144771 206192256645316628298217157)
              ·
                refine ⟨38661048120996867805915717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 206192256645316628298217157 38661048120996867805915717)
                ·
                  refine ⟨7248946522686912713609197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 38661048120996867805915717 7248946522686912713609197)
                  ·
                    refine ⟨2718354946007592267603449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7248946522686912713609197 2718354946007592267603449)
                    ·
                      refine ⟨2038766209505694200702587, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2718354946007592267603449 2038766209505694200702587)
                      ·
                        rfl

theorem cell23_3970483_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 1, 4, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 1, 4, 4, 3, 2].length) (baseStart_3970483 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3970483 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3970483 prefixEnd_3970483 := by exact prefixLift 3970483
  have htrace : WordTrace (prefixWord ++ tailWord_3970483) baseStart_3970483 baseEnd_3970483 := by
    simpa [prefixWord, tailWord_3970483, baseEnd_3970483] using wordTrace_append hprefix tailTrace_3970483
  have hstable : (prefixWord ++ tailWord_3970483).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3970483).length < 2 ^ (prefixWord ++ tailWord_3970483).sum := by decide
  have hdescent : baseEnd_3970483 < baseStart_3970483 := by decide
  rcases family_descends (prefixWord ++ tailWord_3970483) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3970493 : List Nat := [1, 4, 1, 2, 2, 1, 2, 4, 1, 5]
def baseStart_3970493 : Nat := 118140960795 + 3970493 * 2 ^ 59
def prefixEnd_3970493 : Nat := 4983230072969 + 3 ^ 40 * 3970493 * 2
def baseEnd_3970493 : Nat := 679590448104079720525847

theorem tailTrace_3970493 : CollatzResearch.WordTrace tailWord_3970493 prefixEnd_3970493 679590448104079720525847 := by
  unfold tailWord_3970493
  simp only [CollatzResearch.WordTrace]
  refine ⟨144815776804589442062716133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96543851203059628041810755 144815776804589442062716133)
  ·
    refine ⟨27152958150860520386759275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 144815776804589442062716133 27152958150860520386759275)
    ·
      refine ⟨40729437226290780580138913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27152958150860520386759275 40729437226290780580138913)
      ·
        refine ⟨30547077919718085435104185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40729437226290780580138913 30547077919718085435104185)
        ·
          refine ⟨22910308439788564076328139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30547077919718085435104185 22910308439788564076328139)
          ·
            refine ⟨34365462659682846114492209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22910308439788564076328139 34365462659682846114492209)
            ·
              refine ⟨25774096994762134585869157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34365462659682846114492209 25774096994762134585869157)
              ·
                refine ⟨4832643186517900234850467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25774096994762134585869157 4832643186517900234850467)
                ·
                  refine ⟨7248964779776850352275701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4832643186517900234850467 7248964779776850352275701)
                  ·
                    refine ⟨679590448104079720525847, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7248964779776850352275701 679590448104079720525847)
                    ·
                      rfl

theorem cell23_3970493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 2, 4, 1, 5].length) (baseStart_3970493 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3970493 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3970493 prefixEnd_3970493 := by exact prefixLift 3970493
  have htrace : WordTrace (prefixWord ++ tailWord_3970493) baseStart_3970493 baseEnd_3970493 := by
    simpa [prefixWord, tailWord_3970493, baseEnd_3970493] using wordTrace_append hprefix tailTrace_3970493
  have hstable : (prefixWord ++ tailWord_3970493).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3970493).length < 2 ^ (prefixWord ++ tailWord_3970493).sum := by decide
  have hdescent : baseEnd_3970493 < baseStart_3970493 := by decide
  rcases family_descends (prefixWord ++ tailWord_3970493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3970510 : List Nat := [4, 1, 1, 1, 2, 1, 6, 1, 1, 5]
def baseStart_3970510 : Nat := 118140960795 + 3970510 * 2 ^ 59
def prefixEnd_3970510 : Nat := 4983230072969 + 3 ^ 40 * 3970510 * 2
def baseEnd_3970510 : Nat := 679593357827788531688321

theorem tailTrace_3970510 : CollatzResearch.WordTrace tailWord_3970510 prefixEnd_3970510 679593357827788531688321 := by
  unfold tailWord_3970510
  simp only [CollatzResearch.WordTrace]
  refine ⟨18102049605690981745760623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 96544264563685235977389989 18102049605690981745760623)
  ·
    refine ⟨27153074408536472618640935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18102049605690981745760623 27153074408536472618640935)
    ·
      refine ⟨40729611612804708927961403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27153074408536472618640935 40729611612804708927961403)
      ·
        refine ⟨61094417419207063391942105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40729611612804708927961403 61094417419207063391942105)
        ·
          refine ⟨45820813064405297543956579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61094417419207063391942105 45820813064405297543956579)
          ·
            refine ⟨68731219596607946315934869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45820813064405297543956579 68731219596607946315934869)
            ·
              refine ⟨3221775918590997483559447, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 68731219596607946315934869 3221775918590997483559447)
              ·
                refine ⟨4832663877886496225339171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3221775918590997483559447 4832663877886496225339171)
                ·
                  refine ⟨7248995816829744338008757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4832663877886496225339171 7248995816829744338008757)
                  ·
                    refine ⟨679593357827788531688321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7248995816829744338008757 679593357827788531688321)
                    ·
                      rfl

theorem cell23_3970510_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 6, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 6, 1, 1, 5].length) (baseStart_3970510 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3970510 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3970510 prefixEnd_3970510 := by exact prefixLift 3970510
  have htrace : WordTrace (prefixWord ++ tailWord_3970510) baseStart_3970510 baseEnd_3970510 := by
    simpa [prefixWord, tailWord_3970510, baseEnd_3970510] using wordTrace_append hprefix tailTrace_3970510
  have hstable : (prefixWord ++ tailWord_3970510).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3970510).length < 2 ^ (prefixWord ++ tailWord_3970510).sum := by decide
  have hdescent : baseEnd_3970510 < baseStart_3970510 := by decide
  rcases family_descends (prefixWord ++ tailWord_3970510) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3970533 : List Nat := [1, 3, 1, 5, 1, 1, 1, 1, 3, 1, 5]
def baseStart_3970533 : Nat := 118140960795 + 3970533 * 2 ^ 59
def prefixEnd_3970533 : Nat := 4983230072969 + 3 ^ 40 * 3970533 * 2
def baseEnd_3970533 : Nat := 2038791883538419005077357

theorem tailTrace_3970533 : CollatzResearch.WordTrace tailWord_3970533 prefixEnd_3970533 2038791883538419005077357 := by
  unfold tailWord_3970533
  simp only [CollatzResearch.WordTrace]
  refine ⟨144817235724444528894172253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96544823816296352596114835 144817235724444528894172253)
  ·
    refine ⟨54306463396666698335314595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 144817235724444528894172253 54306463396666698335314595)
    ·
      refine ⟨81459695095000047502971893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54306463396666698335314595 81459695095000047502971893)
      ·
        refine ⟨7636846415156254453403615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 81459695095000047502971893 7636846415156254453403615)
        ·
          refine ⟨11455269622734381680105423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7636846415156254453403615 11455269622734381680105423)
          ·
            refine ⟨17182904434101572520158135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11455269622734381680105423 17182904434101572520158135)
            ·
              refine ⟨25774356651152358780237203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17182904434101572520158135 25774356651152358780237203)
              ·
                refine ⟨38661534976728538170355805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25774356651152358780237203 38661534976728538170355805)
                ·
                  refine ⟨14498075616273201813883427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38661534976728538170355805 14498075616273201813883427)
                  ·
                    refine ⟨21747113424409802720825141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14498075616273201813883427 21747113424409802720825141)
                    ·
                      refine ⟨2038791883538419005077357, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 21747113424409802720825141 2038791883538419005077357)
                      ·
                        rfl

theorem cell23_3970533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 1, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 1, 1, 1, 3, 1, 5].length) (baseStart_3970533 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3970533 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3970533 prefixEnd_3970533 := by exact prefixLift 3970533
  have htrace : WordTrace (prefixWord ++ tailWord_3970533) baseStart_3970533 baseEnd_3970533 := by
    simpa [prefixWord, tailWord_3970533, baseEnd_3970533] using wordTrace_append hprefix tailTrace_3970533
  have hstable : (prefixWord ++ tailWord_3970533).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3970533).length < 2 ^ (prefixWord ++ tailWord_3970533).sum := by decide
  have hdescent : baseEnd_3970533 < baseStart_3970533 := by decide
  rcases family_descends (prefixWord ++ tailWord_3970533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3970536 : List Nat := [2, 1, 4, 1, 1, 2, 2, 10]
def baseStart_3970536 : Nat := 118140960795 + 3970536 * 2 ^ 59
def prefixEnd_3970536 : Nat := 4983230072969 + 3 ^ 40 * 3970536 * 2
def baseEnd_3970536 : Nat := 75510867554828981234809

theorem tailTrace_3970536 : CollatzResearch.WordTrace tailWord_3970536 prefixEnd_3970536 75510867554828981234809 := by
  unfold tailWord_3970536
  simp only [CollatzResearch.WordTrace]
  refine ⟨72408672571716830203265731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96544896762289106937687641 72408672571716830203265731)
  ·
    refine ⟨108613008857575245304898597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72408672571716830203265731 108613008857575245304898597)
    ·
      refine ⟨20364939160795358494668487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 108613008857575245304898597 20364939160795358494668487)
      ·
        refine ⟨30547408741193037742002731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20364939160795358494668487 30547408741193037742002731)
        ·
          refine ⟨45821113111789556613004097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30547408741193037742002731 45821113111789556613004097)
          ·
            refine ⟨34365834833842167459753073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45821113111789556613004097 34365834833842167459753073)
            ·
              refine ⟨25774376125381625594814805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34365834833842167459753073 25774376125381625594814805)
              ·
                refine ⟨75510867554828981234809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 25774376125381625594814805 75510867554828981234809)
                ·
                  rfl

theorem cell23_3970536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 2, 10].length) (baseStart_3970536 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3970536 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3970536 prefixEnd_3970536 := by exact prefixLift 3970536
  have htrace : WordTrace (prefixWord ++ tailWord_3970536) baseStart_3970536 baseEnd_3970536 := by
    simpa [prefixWord, tailWord_3970536, baseEnd_3970536] using wordTrace_append hprefix tailTrace_3970536
  have hstable : (prefixWord ++ tailWord_3970536).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3970536).length < 2 ^ (prefixWord ++ tailWord_3970536).sum := by decide
  have hdescent : baseEnd_3970536 < baseStart_3970536 := by decide
  rcases family_descends (prefixWord ++ tailWord_3970536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3970543 : List Nat := [1, 1, 2, 1, 4, 1, 5, 1, 1, 2, 4]
def baseStart_3970543 : Nat := 118140960795 + 3970543 * 2 ^ 59
def prefixEnd_3970543 : Nat := 4983230072969 + 3 ^ 40 * 3970543 * 2
def baseEnd_3970543 : Nat := 2038797018344963965952311

theorem tailTrace_3970543 : CollatzResearch.WordTrace tailWord_3970543 prefixEnd_3970543 2038797018344963965952311 := by
  unfold tailWord_3970543
  simp only [CollatzResearch.WordTrace]
  refine ⟨144817600454408300602036283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96545066969605533734690855 144817600454408300602036283)
  ·
    refine ⟨217226400681612450903054425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144817600454408300602036283 217226400681612450903054425)
    ·
      refine ⟨162919800511209338177290819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 217226400681612450903054425 162919800511209338177290819)
      ·
        refine ⟨244379700766814007265936229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 162919800511209338177290819 244379700766814007265936229)
        ·
          refine ⟨45821193893777626362363043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 244379700766814007265936229 45821193893777626362363043)
          ·
            refine ⟨68731790840666439543544565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45821193893777626362363043 68731790840666439543544565)
            ·
              refine ⟨6443605391312478707207303, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 68731790840666439543544565 6443605391312478707207303)
              ·
                refine ⟨9665408086968718060810955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6443605391312478707207303 9665408086968718060810955)
                ·
                  refine ⟨14498112130453077091216433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9665408086968718060810955 14498112130453077091216433)
                  ·
                    refine ⟨10873584097839807818412325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14498112130453077091216433 10873584097839807818412325)
                    ·
                      refine ⟨2038797018344963965952311, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10873584097839807818412325 2038797018344963965952311)
                      ·
                        rfl

theorem cell23_3970543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 5, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 5, 1, 1, 2, 4].length) (baseStart_3970543 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3970543 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3970543 prefixEnd_3970543 := by exact prefixLift 3970543
  have htrace : WordTrace (prefixWord ++ tailWord_3970543) baseStart_3970543 baseEnd_3970543 := by
    simpa [prefixWord, tailWord_3970543, baseEnd_3970543] using wordTrace_append hprefix tailTrace_3970543
  have hstable : (prefixWord ++ tailWord_3970543).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3970543).length < 2 ^ (prefixWord ++ tailWord_3970543).sum := by decide
  have hdescent : baseEnd_3970543 < baseStart_3970543 := by decide
  rcases family_descends (prefixWord ++ tailWord_3970543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3970558 : List Nat := [4, 2, 2, 3, 1, 2, 1, 3, 1, 1, 3]
def baseStart_3970558 : Nat := 118140960795 + 3970558 * 2 ^ 59
def prefixEnd_3970558 : Nat := 4983230072969 + 3 ^ 40 * 3970558 * 2
def baseEnd_3970558 : Nat := 2038804720554781407264743

theorem tailTrace_3970558 : CollatzResearch.WordTrace tailWord_3970558 prefixEnd_3970558 2038804720554781407264743 := by
  unfold tailWord_3970558
  simp only [CollatzResearch.WordTrace]
  refine ⟨18102268443669244770479041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 96545431699569305442554885 18102268443669244770479041)
  ·
    refine ⟨13576701332751933577859281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18102268443669244770479041 13576701332751933577859281)
    ·
      refine ⟨10182525999563950183394461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13576701332751933577859281 10182525999563950183394461)
      ·
        refine ⟨3818447249836481318772923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10182525999563950183394461 3818447249836481318772923)
        ·
          refine ⟨5727670874754721978159385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3818447249836481318772923 5727670874754721978159385)
          ·
            refine ⟨4295753156066041483619539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5727670874754721978159385 4295753156066041483619539)
            ·
              refine ⟨6443629734099062225429309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4295753156066041483619539 6443629734099062225429309)
              ·
                refine ⟨2416361150287148334535991, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6443629734099062225429309 2416361150287148334535991)
                ·
                  refine ⟨3624541725430722501803987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2416361150287148334535991 3624541725430722501803987)
                  ·
                    refine ⟨5436812588146083752705981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3624541725430722501803987 5436812588146083752705981)
                    ·
                      refine ⟨2038804720554781407264743, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5436812588146083752705981 2038804720554781407264743)
                      ·
                        rfl

theorem cell23_3970558_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 1, 2, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 1, 2, 1, 3, 1, 1, 3].length) (baseStart_3970558 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3970558 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3970558 prefixEnd_3970558 := by exact prefixLift 3970558
  have htrace : WordTrace (prefixWord ++ tailWord_3970558) baseStart_3970558 baseEnd_3970558 := by
    simpa [prefixWord, tailWord_3970558, baseEnd_3970558] using wordTrace_append hprefix tailTrace_3970558
  have hstable : (prefixWord ++ tailWord_3970558).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3970558).length < 2 ^ (prefixWord ++ tailWord_3970558).sum := by decide
  have hdescent : baseEnd_3970558 < baseStart_3970558 := by decide
  rcases family_descends (prefixWord ++ tailWord_3970558) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3970581 : List Nat := [1, 3, 2, 1, 3, 3, 3, 2, 1, 2, 2]
def baseStart_3970581 : Nat := 118140960795 + 3970581 * 2 ^ 59
def prefixEnd_3970581 : Nat := 4983230072969 + 3 ^ 40 * 3970581 * 2
def baseEnd_3970581 : Nat := 2038816530609834817277137

theorem tailTrace_3970581 : CollatzResearch.WordTrace tailWord_3970581 prefixEnd_3970581 2038816530609834817277137 := by
  unfold tailWord_3970581
  simp only [CollatzResearch.WordTrace]
  refine ⟨144818986428270633091919597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96545990952180422061279731 144818986428270633091919597)
  ·
    refine ⟨54307119910601487409469849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 144818986428270633091919597 54307119910601487409469849)
    ·
      refine ⟨40730339932951115557102387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54307119910601487409469849 40730339932951115557102387)
      ·
        refine ⟨61095509899426673335653581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40730339932951115557102387 61095509899426673335653581)
        ·
          refine ⟨22910816212285002500870093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 61095509899426673335653581 22910816212285002500870093)
          ·
            refine ⟨8591556079606875937826285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22910816212285002500870093 8591556079606875937826285)
            ·
              refine ⟨3221833529852578476684857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8591556079606875937826285 3221833529852578476684857)
              ·
                refine ⟨2416375147389433857513643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3221833529852578476684857 2416375147389433857513643)
                ·
                  refine ⟨3624562721084150786270465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2416375147389433857513643 3624562721084150786270465)
                  ·
                    refine ⟨2718422040813113089702849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3624562721084150786270465 2718422040813113089702849)
                    ·
                      refine ⟨2038816530609834817277137, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2718422040813113089702849 2038816530609834817277137)
                      ·
                        rfl

theorem cell23_3970581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 3, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 3, 3, 2, 1, 2, 2].length) (baseStart_3970581 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3970581 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3970581 prefixEnd_3970581 := by exact prefixLift 3970581
  have htrace : WordTrace (prefixWord ++ tailWord_3970581) baseStart_3970581 baseEnd_3970581 := by
    simpa [prefixWord, tailWord_3970581, baseEnd_3970581] using wordTrace_append hprefix tailTrace_3970581
  have hstable : (prefixWord ++ tailWord_3970581).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3970581).length < 2 ^ (prefixWord ++ tailWord_3970581).sum := by decide
  have hdescent : baseEnd_3970581 < baseStart_3970581 := by decide
  rcases family_descends (prefixWord ++ tailWord_3970581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3970623 : List Nat := [1, 1, 2, 2, 3, 3, 2, 1, 2, 1, 5]
def baseStart_3970623 : Nat := 118140960795 + 3970623 * 2 ^ 59
def prefixEnd_3970623 : Nat := 4983230072969 + 3 ^ 40 * 3970623 * 2
def baseEnd_3970623 : Nat := 2038838096797323652951943

theorem tailTrace_3970623 : CollatzResearch.WordTrace tailWord_3970623 prefixEnd_3970623 2038838096797323652951943 := by
  unfold tailWord_3970623
  simp only [CollatzResearch.WordTrace]
  refine ⟨144820518294118474264948523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96547012196078982843299015 144820518294118474264948523)
  ·
    refine ⟨217230777441177711397422785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144820518294118474264948523 217230777441177711397422785)
    ·
      refine ⟨162923083080883283548067089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 217230777441177711397422785 162923083080883283548067089)
      ·
        refine ⟨122192312310662462661050317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 162923083080883283548067089 122192312310662462661050317)
        ·
          refine ⟨45822117116498423497893869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 122192312310662462661050317 45822117116498423497893869)
          ·
            refine ⟨17183293918686908811710201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45822117116498423497893869 17183293918686908811710201)
            ·
              refine ⟨12887470439015181608782651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17183293918686908811710201 12887470439015181608782651)
              ·
                refine ⟨19331205658522772413173977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12887470439015181608782651 19331205658522772413173977)
                ·
                  refine ⟨14498404243892079309880483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19331205658522772413173977 14498404243892079309880483)
                  ·
                    refine ⟨21747606365838118964820725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14498404243892079309880483 21747606365838118964820725)
                    ·
                      refine ⟨2038838096797323652951943, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 21747606365838118964820725 2038838096797323652951943)
                      ·
                        rfl

theorem cell23_3970623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 3, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 3, 2, 1, 2, 1, 5].length) (baseStart_3970623 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3970623 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3970623 prefixEnd_3970623 := by exact prefixLift 3970623
  have htrace : WordTrace (prefixWord ++ tailWord_3970623) baseStart_3970623 baseEnd_3970623 := by
    simpa [prefixWord, tailWord_3970623, baseEnd_3970623] using wordTrace_append hprefix tailTrace_3970623
  have hstable : (prefixWord ++ tailWord_3970623).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3970623).length < 2 ^ (prefixWord ++ tailWord_3970623).sum := by decide
  have hdescent : baseEnd_3970623 < baseStart_3970623 := by decide
  rcases family_descends (prefixWord ++ tailWord_3970623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3970677 : List Nat := [1, 3, 4, 2, 1, 1, 1, 5, 5]
def baseStart_3970677 : Nat := 118140960795 + 3970677 * 2 ^ 59
def prefixEnd_3970677 : Nat := 4983230072969 + 3 ^ 40 * 3970677 * 2
def baseEnd_3970677 : Nat := 226540647194740715741855

theorem tailTrace_3970677 : CollatzResearch.WordTrace tailWord_3970677 prefixEnd_3970677 226540647194740715741855 := by
  unfold tailWord_3970677
  simp only [CollatzResearch.WordTrace]
  refine ⟨144822487835922841487414285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96548325223948560991609523 144822487835922841487414285)
  ·
    refine ⟨54308432938471065557780357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 144822487835922841487414285 54308432938471065557780357)
    ·
      refine ⟨10182831175963324792083817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 54308432938471065557780357 10182831175963324792083817)
      ·
        refine ⟨7637123381972493594062863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10182831175963324792083817 7637123381972493594062863)
        ·
          refine ⟨11455685072958740391094295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7637123381972493594062863 11455685072958740391094295)
          ·
            refine ⟨17183527609438110586641443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11455685072958740391094295 17183527609438110586641443)
            ·
              refine ⟨25775291414157165879962165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17183527609438110586641443 25775291414157165879962165)
              ·
                refine ⟨2416433570077234301246453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 25775291414157165879962165 2416433570077234301246453)
                ·
                  refine ⟨226540647194740715741855, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2416433570077234301246453 226540647194740715741855)
                  ·
                    rfl

theorem cell23_3970677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 1, 1, 5, 5].length) (baseStart_3970677 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3970677 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3970677 prefixEnd_3970677 := by exact prefixLift 3970677
  have htrace : WordTrace (prefixWord ++ tailWord_3970677) baseStart_3970677 baseEnd_3970677 := by
    simpa [prefixWord, tailWord_3970677, baseEnd_3970677] using wordTrace_append hprefix tailTrace_3970677
  have hstable : (prefixWord ++ tailWord_3970677).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3970677).length < 2 ^ (prefixWord ++ tailWord_3970677).sum := by decide
  have hdescent : baseEnd_3970677 < baseStart_3970677 := by decide
  rcases family_descends (prefixWord ++ tailWord_3970677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3970723 : List Nat := [1, 1, 1, 4, 1, 1, 3, 1, 2, 4, 4]
def baseStart_3970723 : Nat := 118140960795 + 3970723 * 2 ^ 59
def prefixEnd_3970723 : Nat := 4983230072969 + 3 ^ 40 * 3970723 * 2
def baseEnd_3970723 : Nat := 2038889444862773261701483

theorem tailTrace_3970723 : CollatzResearch.WordTrace tailWord_3970723 prefixEnd_3970723 2038889444862773261701483 := by
  unfold tailWord_3970723
  simp only [CollatzResearch.WordTrace]
  refine ⟨144824165593756191343588823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96549443729170794229059215 144824165593756191343588823)
  ·
    refine ⟨217236248390634287015383235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144824165593756191343588823 217236248390634287015383235)
    ·
      refine ⟨325854372585951430523074853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 217236248390634287015383235 325854372585951430523074853)
      ·
        refine ⟨61097694859865893223076535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 325854372585951430523074853 61097694859865893223076535)
        ·
          refine ⟨91646542289798839834614803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61097694859865893223076535 91646542289798839834614803)
          ·
            refine ⟨137469813434698259751922205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91646542289798839834614803 137469813434698259751922205)
            ·
              refine ⟨51551180038011847406970827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 137469813434698259751922205 51551180038011847406970827)
              ·
                refine ⟨77326770057017771110456241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51551180038011847406970827 77326770057017771110456241)
                ·
                  refine ⟨57995077542763328332842181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 77326770057017771110456241 57995077542763328332842181)
                  ·
                    refine ⟨10874077039268124062407909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 57995077542763328332842181 10874077039268124062407909)
                    ·
                      refine ⟨2038889444862773261701483, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10874077039268124062407909 2038889444862773261701483)
                      ·
                        rfl

theorem cell23_3970723_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 3, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 3, 1, 2, 4, 4].length) (baseStart_3970723 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3970723 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3970723 prefixEnd_3970723 := by exact prefixLift 3970723
  have htrace : WordTrace (prefixWord ++ tailWord_3970723) baseStart_3970723 baseEnd_3970723 := by
    simpa [prefixWord, tailWord_3970723, baseEnd_3970723] using wordTrace_append hprefix tailTrace_3970723
  have hstable : (prefixWord ++ tailWord_3970723).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3970723).length < 2 ^ (prefixWord ++ tailWord_3970723).sum := by decide
  have hdescent : baseEnd_3970723 < baseStart_3970723 := by decide
  rcases family_descends (prefixWord ++ tailWord_3970723) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3970728 : List Nat := [2, 1, 7, 1, 1, 2, 1, 3, 5]
def baseStart_3970728 : Nat := 118140960795 + 3970728 * 2 ^ 59
def prefixEnd_3970728 : Nat := 4983230072969 + 3 ^ 40 * 3970728 * 2
def baseEnd_3970728 : Nat := 226543556918449526904329

theorem tailTrace_3970728 : CollatzResearch.WordTrace tailWord_3970728 prefixEnd_3970728 226543556918449526904329 := by
  unfold tailWord_3970728
  simp only [CollatzResearch.WordTrace]
  refine ⟨72412173979369038598760419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96549565305825384798347225 72412173979369038598760419)
  ·
    refine ⟨108618260969053557898140629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72412173979369038598760419 108618260969053557898140629)
    ·
      refine ⟨2545740491462192763237671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 108618260969053557898140629 2545740491462192763237671)
      ·
        refine ⟨3818610737193289144856507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2545740491462192763237671 3818610737193289144856507)
        ·
          refine ⟨5727916105789933717284761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3818610737193289144856507 5727916105789933717284761)
          ·
            refine ⟨4295937079342450287963571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5727916105789933717284761 4295937079342450287963571)
            ·
              refine ⟨6443905619013675431945357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4295937079342450287963571 6443905619013675431945357)
              ·
                refine ⟨2416464607130128286979509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6443905619013675431945357 2416464607130128286979509)
                ·
                  refine ⟨226543556918449526904329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2416464607130128286979509 226543556918449526904329)
                  ·
                    rfl

theorem cell23_3970728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 1, 2, 1, 3, 5].length) (baseStart_3970728 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3970728 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3970728 prefixEnd_3970728 := by exact prefixLift 3970728
  have htrace : WordTrace (prefixWord ++ tailWord_3970728) baseStart_3970728 baseEnd_3970728 := by
    simpa [prefixWord, tailWord_3970728, baseEnd_3970728] using wordTrace_append hprefix tailTrace_3970728
  have hstable : (prefixWord ++ tailWord_3970728).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3970728).length < 2 ^ (prefixWord ++ tailWord_3970728).sum := by decide
  have hdescent : baseEnd_3970728 < baseStart_3970728 := by decide
  rcases family_descends (prefixWord ++ tailWord_3970728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3970750 : List Nat := [4, 2, 1, 1, 2, 2, 2, 1, 8]
def baseStart_3970750 : Nat := 118140960795 + 3970750 * 2 ^ 59
def prefixEnd_3970750 : Nat := 4983230072969 + 3 ^ 40 * 3970750 * 2
def baseEnd_3970750 : Nat := 226544812093382739562651

theorem tailTrace_3970750 : CollatzResearch.WordTrace tailWord_3970750 prefixEnd_3970750 226544812093382739562651 := by
  unfold tailWord_3970750
  simp only [CollatzResearch.WordTrace]
  refine ⟨18103143795582296869352713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 96550100243105583303214469 18103143795582296869352713)
  ·
    refine ⟨13577357846686722652014535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18103143795582296869352713 13577357846686722652014535)
    ·
      refine ⟨20366036770030083978021803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13577357846686722652014535 20366036770030083978021803)
      ·
        refine ⟨30549055155045125967032705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20366036770030083978021803 30549055155045125967032705)
        ·
          refine ⟨22911791366283844475274529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30549055155045125967032705 22911791366283844475274529)
          ·
            refine ⟨17183843524712883356455897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22911791366283844475274529 17183843524712883356455897)
            ·
              refine ⟨12887882643534662517341923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17183843524712883356455897 12887882643534662517341923)
              ·
                refine ⟨19331823965301993776012885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12887882643534662517341923 19331823965301993776012885)
                ·
                  refine ⟨226544812093382739562651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 19331823965301993776012885 226544812093382739562651)
                  ·
                    rfl

theorem cell23_3970750_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 2, 2, 1, 8].length) (baseStart_3970750 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3970750 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3970750 prefixEnd_3970750 := by exact prefixLift 3970750
  have htrace : WordTrace (prefixWord ++ tailWord_3970750) baseStart_3970750 baseEnd_3970750 := by
    simpa [prefixWord, tailWord_3970750, baseEnd_3970750] using wordTrace_append hprefix tailTrace_3970750
  have hstable : (prefixWord ++ tailWord_3970750).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3970750).length < 2 ^ (prefixWord ++ tailWord_3970750).sum := by decide
  have hdescent : baseEnd_3970750 < baseStart_3970750 := by decide
  rcases family_descends (prefixWord ++ tailWord_3970750) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3970781 : List Nat := [1, 4, 3, 3, 1, 1, 2, 1, 2, 2, 3]
def baseStart_3970781 : Nat := 118140960795 + 3970781 * 2 ^ 59
def prefixEnd_3970781 : Nat := 4983230072969 + 3 ^ 40 * 3970781 * 2
def baseEnd_3970781 : Nat := 2038919226740734034776217

theorem tailTrace_3970781 : CollatzResearch.WordTrace tailWord_3970781 prefixEnd_3970781 2038919226740734034776217 := by
  unfold tailWord_3970781
  simp only [CollatzResearch.WordTrace]
  refine ⟨144826281027546067249200197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96550854018364044832800131 144826281027546067249200197)
  ·
    refine ⟨27154927692664887609225037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 144826281027546067249200197 27154927692664887609225037)
    ·
      refine ⟨10183097884749332853459389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27154927692664887609225037 10183097884749332853459389)
      ·
        refine ⟨3818661706780999820047271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10183097884749332853459389 3818661706780999820047271)
        ·
          refine ⟨5727992560171499730070907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3818661706780999820047271 5727992560171499730070907)
          ·
            refine ⟨8591988840257249595106361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5727992560171499730070907 8591988840257249595106361)
            ·
              refine ⟨6443991630192937196329771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8591988840257249595106361 6443991630192937196329771)
              ·
                refine ⟨9665987445289405794494657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6443991630192937196329771 9665987445289405794494657)
                ·
                  refine ⟨7249490583967054345870993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9665987445289405794494657 7249490583967054345870993)
                  ·
                    refine ⟨5437117937975290759403245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7249490583967054345870993 5437117937975290759403245)
                    ·
                      refine ⟨2038919226740734034776217, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5437117937975290759403245 2038919226740734034776217)
                      ·
                        rfl

theorem cell23_3970781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 1, 1, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 1, 1, 2, 1, 2, 2, 3].length) (baseStart_3970781 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3970781 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3970781 prefixEnd_3970781 := by exact prefixLift 3970781
  have htrace : WordTrace (prefixWord ++ tailWord_3970781) baseStart_3970781 baseEnd_3970781 := by
    simpa [prefixWord, tailWord_3970781, baseEnd_3970781] using wordTrace_append hprefix tailTrace_3970781
  have hstable : (prefixWord ++ tailWord_3970781).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3970781).length < 2 ^ (prefixWord ++ tailWord_3970781).sum := by decide
  have hdescent : baseEnd_3970781 < baseStart_3970781 := by decide
  rcases family_descends (prefixWord ++ tailWord_3970781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3970827 : List Nat := [1, 1, 1, 1, 5, 1, 4, 3, 2, 4]
def baseStart_3970827 : Nat := 118140960795 + 3970827 * 2 ^ 59
def prefixEnd_3970827 : Nat := 4983230072969 + 3 ^ 40 * 3970827 * 2
def baseEnd_3970827 : Nat := 679647615616946951600335

theorem tailTrace_3970827 : CollatzResearch.WordTrace tailWord_3970827 prefixEnd_3970827 679647615616946951600335 := by
  unfold tailWord_3970827
  simp only [CollatzResearch.WordTrace]
  refine ⟨144827958785379417105374735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96551972523586278070249823 144827958785379417105374735)
  ·
    refine ⟨217241938178069125658062103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144827958785379417105374735 217241938178069125658062103)
    ·
      refine ⟨325862907267103688487093155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 217241938178069125658062103 325862907267103688487093155)
      ·
        refine ⟨488794360900655532730639733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 325862907267103688487093155 488794360900655532730639733)
        ·
          refine ⟨45824471334436456193497475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 488794360900655532730639733 45824471334436456193497475)
          ·
            refine ⟨68736707001654684290246213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45824471334436456193497475 68736707001654684290246213)
            ·
              refine ⟨12888132562810253304421165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 68736707001654684290246213 12888132562810253304421165)
              ·
                refine ⟨4833049711053844989157937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12888132562810253304421165 4833049711053844989157937)
                ·
                  refine ⟨3624787283290383741868453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4833049711053844989157937 3624787283290383741868453)
                  ·
                    refine ⟨679647615616946951600335, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3624787283290383741868453 679647615616946951600335)
                    ·
                      rfl

theorem cell23_3970827_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 4, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 4, 3, 2, 4].length) (baseStart_3970827 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3970827 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3970827 prefixEnd_3970827 := by exact prefixLift 3970827
  have htrace : WordTrace (prefixWord ++ tailWord_3970827) baseStart_3970827 baseEnd_3970827 := by
    simpa [prefixWord, tailWord_3970827, baseEnd_3970827] using wordTrace_append hprefix tailTrace_3970827
  have hstable : (prefixWord ++ tailWord_3970827).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3970827).length < 2 ^ (prefixWord ++ tailWord_3970827).sum := by decide
  have hdescent : baseEnd_3970827 < baseStart_3970827 := by decide
  rcases family_descends (prefixWord ++ tailWord_3970827) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3970830 : List Nat := [4, 1, 1, 2, 1, 1, 2, 3, 1, 1, 6]
def baseStart_3970830 : Nat := 118140960795 + 3970830 * 2 ^ 59
def prefixEnd_3970830 : Nat := 4983230072969 + 3 ^ 40 * 3970830 * 2
def baseEnd_3970830 : Nat := 2038944387292804343063491

theorem tailTrace_3970830 : CollatzResearch.WordTrace tailWord_3970830 prefixEnd_3970830 2038944387292804343063491 := by
  unfold tailWord_3970830
  simp only [CollatzResearch.WordTrace]
  refine ⟨18103508525546068577216743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 96552045469579032411822629 18103508525546068577216743)
  ·
    refine ⟨27155262788319102865825115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18103508525546068577216743 27155262788319102865825115)
    ·
      refine ⟨40732894182478654298737673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27155262788319102865825115 40732894182478654298737673)
      ·
        refine ⟨30549670636858990724053255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40732894182478654298737673 30549670636858990724053255)
        ·
          refine ⟨45824505955288486086079883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30549670636858990724053255 45824505955288486086079883)
          ·
            refine ⟨68736758932932729129119825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45824505955288486086079883 68736758932932729129119825)
            ·
              refine ⟨51552569199699546846839869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 68736758932932729129119825 51552569199699546846839869)
              ·
                refine ⟨19332213449887330067564951, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 51552569199699546846839869 19332213449887330067564951)
                ·
                  refine ⟨28998320174830995101347427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19332213449887330067564951 28998320174830995101347427)
                  ·
                    refine ⟨43497480262246492652021141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 28998320174830995101347427 43497480262246492652021141)
                    ·
                      refine ⟨2038944387292804343063491, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 43497480262246492652021141 2038944387292804343063491)
                      ·
                        rfl

theorem cell23_3970830_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 2, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 2, 3, 1, 1, 6].length) (baseStart_3970830 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3970830 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3970830 prefixEnd_3970830 := by exact prefixLift 3970830
  have htrace : WordTrace (prefixWord ++ tailWord_3970830) baseStart_3970830 baseEnd_3970830 := by
    simpa [prefixWord, tailWord_3970830, baseEnd_3970830] using wordTrace_append hprefix tailTrace_3970830
  have hstable : (prefixWord ++ tailWord_3970830).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3970830).length < 2 ^ (prefixWord ++ tailWord_3970830).sum := by decide
  have hdescent : baseEnd_3970830 < baseStart_3970830 := by decide
  rcases family_descends (prefixWord ++ tailWord_3970830) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3970834 : List Nat := [3, 2, 4, 1, 1, 1, 2, 1, 3, 1, 4]
def baseStart_3970834 : Nat := 118140960795 + 3970834 * 2 ^ 59
def prefixEnd_3970834 : Nat := 4983230072969 + 3 ^ 40 * 3970834 * 2
def baseEnd_3970834 : Nat := 2038946441215422327413473

theorem tailTrace_3970834 : CollatzResearch.WordTrace tailWord_3970834 prefixEnd_3970834 2038946441215422327413473 := by
  unfold tailWord_3970834
  simp only [CollatzResearch.WordTrace]
  refine ⟨36207053524088514325219889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 96552142730902704867253037 36207053524088514325219889)
  ·
    refine ⟨27155290143066385743914917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36207053524088514325219889 27155290143066385743914917)
    ·
      refine ⟨5091616901824947326984047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 27155290143066385743914917 5091616901824947326984047)
      ·
        refine ⟨7637425352737420990476071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5091616901824947326984047 7637425352737420990476071)
        ·
          refine ⟨11456138029106131485714107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7637425352737420990476071 11456138029106131485714107)
          ·
            refine ⟨17184207043659197228571161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11456138029106131485714107 17184207043659197228571161)
            ·
              refine ⟨12888155282744397921428371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17184207043659197228571161 12888155282744397921428371)
              ·
                refine ⟨19332232924116596882142557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12888155282744397921428371 19332232924116596882142557)
                ·
                  refine ⟨7249587346543723830803459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19332232924116596882142557 7249587346543723830803459)
                  ·
                    refine ⟨10874381019815585746205189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7249587346543723830803459 10874381019815585746205189)
                    ·
                      refine ⟨2038946441215422327413473, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10874381019815585746205189 2038946441215422327413473)
                      ·
                        rfl

theorem cell23_3970834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 1, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 1, 2, 1, 3, 1, 4].length) (baseStart_3970834 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3970834 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3970834 prefixEnd_3970834 := by exact prefixLift 3970834
  have htrace : WordTrace (prefixWord ++ tailWord_3970834) baseStart_3970834 baseEnd_3970834 := by
    simpa [prefixWord, tailWord_3970834, baseEnd_3970834] using wordTrace_append hprefix tailTrace_3970834
  have hstable : (prefixWord ++ tailWord_3970834).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3970834).length < 2 ^ (prefixWord ++ tailWord_3970834).sum := by decide
  have hdescent : baseEnd_3970834 < baseStart_3970834 := by decide
  rcases family_descends (prefixWord ++ tailWord_3970834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3970837 : List Nat := [1, 3, 2, 1, 2, 3, 2, 1, 3, 2, 3]
def baseStart_3970837 : Nat := 118140960795 + 3970837 * 2 ^ 59
def prefixEnd_3970837 : Nat := 4983230072969 + 3 ^ 40 * 3970837 * 2
def baseEnd_3970837 : Nat := 2038947981657385815675959

theorem tailTrace_3970837 : CollatzResearch.WordTrace tailWord_3970837 prefixEnd_3970837 2038947981657385815675959 := by
  unfold tailWord_3970837
  simp only [CollatzResearch.WordTrace]
  refine ⟨144828323515343188813238765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96552215676895459208825843 144828323515343188813238765)
  ·
    refine ⟨54310621318253695804964537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 144828323515343188813238765 54310621318253695804964537)
    ·
      refine ⟨40732965988690271853723403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54310621318253695804964537 40732965988690271853723403)
      ·
        refine ⟨61099448983035407780585105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40732965988690271853723403 61099448983035407780585105)
        ·
          refine ⟨45824586737276555835438829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61099448983035407780585105 45824586737276555835438829)
          ·
            refine ⟨17184220026478708438289561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45824586737276555835438829 17184220026478708438289561)
            ·
              refine ⟨12888165019859031328717171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17184220026478708438289561 12888165019859031328717171)
              ·
                refine ⟨19332247529788546993075757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12888165019859031328717171 19332247529788546993075757)
                ·
                  refine ⟨7249592823670705122403409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19332247529788546993075757 7249592823670705122403409)
                  ·
                    refine ⟨5437194617753028841802557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7249592823670705122403409 5437194617753028841802557)
                    ·
                      refine ⟨2038947981657385815675959, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5437194617753028841802557 2038947981657385815675959)
                      ·
                        rfl

theorem cell23_3970837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 3, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 3, 2, 1, 3, 2, 3].length) (baseStart_3970837 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3970837 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3970837 prefixEnd_3970837 := by exact prefixLift 3970837
  have htrace : WordTrace (prefixWord ++ tailWord_3970837) baseStart_3970837 baseEnd_3970837 := by
    simpa [prefixWord, tailWord_3970837, baseEnd_3970837] using wordTrace_append hprefix tailTrace_3970837
  have hstable : (prefixWord ++ tailWord_3970837).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3970837).length < 2 ^ (prefixWord ++ tailWord_3970837).sum := by decide
  have hdescent : baseEnd_3970837 < baseStart_3970837 := by decide
  rcases family_descends (prefixWord ++ tailWord_3970837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3970851 : List Nat := [1, 1, 1, 4, 2, 1, 3, 5, 1, 2, 2]
def baseStart_3970851 : Nat := 118140960795 + 3970851 * 2 ^ 59
def prefixEnd_3970851 : Nat := 4983230072969 + 3 ^ 40 * 3970851 * 2
def baseEnd_3970851 : Nat := 2038955170386548760900895

theorem tailTrace_3970851 : CollatzResearch.WordTrace tailWord_3970851 prefixEnd_3970851 2038955170386548760900895 := by
  unfold tailWord_3970851
  simp only [CollatzResearch.WordTrace]
  refine ⟨144828834137292469204248407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96552556091528312802832271 144828834137292469204248407)
  ·
    refine ⟨217243251205938703806372611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144828834137292469204248407 217243251205938703806372611)
    ·
      refine ⟨325864876808908055709558917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 217243251205938703806372611 325864876808908055709558917)
      ·
        refine ⟨61099664401670260445542297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 325864876808908055709558917 61099664401670260445542297)
        ·
          refine ⟨45824748301252695334156723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61099664401670260445542297 45824748301252695334156723)
          ·
            refine ⟨68737122451879043001235085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45824748301252695334156723 68737122451879043001235085)
            ·
              refine ⟨25776420919454641125463157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 68737122451879043001235085 25776420919454641125463157)
              ·
                refine ⟨2416539461198872605512171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 25776420919454641125463157 2416539461198872605512171)
                ·
                  refine ⟨3624809191798308908268257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2416539461198872605512171 3624809191798308908268257)
                  ·
                    refine ⟨2718606893848731681201193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3624809191798308908268257 2718606893848731681201193)
                    ·
                      refine ⟨2038955170386548760900895, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2718606893848731681201193 2038955170386548760900895)
                      ·
                        rfl

theorem cell23_3970851_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 3, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 3, 5, 1, 2, 2].length) (baseStart_3970851 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3970851 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3970851 prefixEnd_3970851 := by exact prefixLift 3970851
  have htrace : WordTrace (prefixWord ++ tailWord_3970851) baseStart_3970851 baseEnd_3970851 := by
    simpa [prefixWord, tailWord_3970851, baseEnd_3970851] using wordTrace_append hprefix tailTrace_3970851
  have hstable : (prefixWord ++ tailWord_3970851).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3970851).length < 2 ^ (prefixWord ++ tailWord_3970851).sum := by decide
  have hdescent : baseEnd_3970851 < baseStart_3970851 := by decide
  rcases family_descends (prefixWord ++ tailWord_3970851) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3970868 : List Nat := [2, 5, 1, 1, 2, 2, 2, 1, 3, 2, 2]
def baseStart_3970868 : Nat := 118140960795 + 3970868 * 2 ^ 59
def prefixEnd_3970868 : Nat := 4983230072969 + 3 ^ 40 * 3970868 * 2
def baseEnd_3970868 : Nat := 2038963899557675194388317

theorem tailTrace_3970868 : CollatzResearch.WordTrace tailWord_3970868 prefixEnd_3970868 2038963899557675194388317 := by
  unfold tailWord_3970868
  simp only [CollatzResearch.WordTrace]
  refine ⟨72414727089115440553808629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96552969452153920738411505 72414727089115440553808629)
  ·
    refine ⟨6788880664604572551919559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 72414727089115440553808629 6788880664604572551919559)
    ·
      refine ⟨10183320996906858827879339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6788880664604572551919559 10183320996906858827879339)
      ·
        refine ⟨15274981495360288241819009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10183320996906858827879339 15274981495360288241819009)
        ·
          refine ⟨11456236121520216181364257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15274981495360288241819009 11456236121520216181364257)
          ·
            refine ⟨8592177091140162136023193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11456236121520216181364257 8592177091140162136023193)
            ·
              refine ⟨6444132818355121602017395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8592177091140162136023193 6444132818355121602017395)
              ·
                refine ⟨9666199227532682403026093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6444132818355121602017395 9666199227532682403026093)
                ·
                  refine ⟨3624824710324755901134785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9666199227532682403026093 3624824710324755901134785)
                  ·
                    refine ⟨2718618532743566925851089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3624824710324755901134785 2718618532743566925851089)
                    ·
                      refine ⟨2038963899557675194388317, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2718618532743566925851089 2038963899557675194388317)
                      ·
                        rfl

theorem cell23_3970868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 2, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 2, 2, 1, 3, 2, 2].length) (baseStart_3970868 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3970868 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3970868 prefixEnd_3970868 := by exact prefixLift 3970868
  have htrace : WordTrace (prefixWord ++ tailWord_3970868) baseStart_3970868 baseEnd_3970868 := by
    simpa [prefixWord, tailWord_3970868, baseEnd_3970868] using wordTrace_append hprefix tailTrace_3970868
  have hstable : (prefixWord ++ tailWord_3970868).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3970868).length < 2 ^ (prefixWord ++ tailWord_3970868).sum := by decide
  have hdescent : baseEnd_3970868 < baseStart_3970868 := by decide
  rcases family_descends (prefixWord ++ tailWord_3970868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3970945 : List Nat := [1, 2, 4, 4, 1, 2, 1, 2, 1, 3, 2]
def baseStart_3970945 : Nat := 118140960795 + 3970945 * 2 ^ 59
def prefixEnd_3970945 : Nat := 4983230072969 + 3 ^ 40 * 3970945 * 2
def baseEnd_3970945 : Nat := 2039003437568071393125463

theorem tailTrace_3970945 : CollatzResearch.WordTrace tailWord_3970945 prefixEnd_3970945 2039003437568071393125463 := by
  unfold tailWord_3970945
  simp only [CollatzResearch.WordTrace]
  refine ⟨144832262598951923258170289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96554841732634615505446859 144832262598951923258170289)
  ·
    refine ⟨108624196949213942443627717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 144832262598951923258170289 108624196949213942443627717)
    ·
      refine ⟨20367036927977614208180197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 108624196949213942443627717 20367036927977614208180197)
      ·
        refine ⟨3818819423995802664033787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 20367036927977614208180197 3818819423995802664033787)
        ·
          refine ⟨5728229135993703996050681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3818819423995802664033787 5728229135993703996050681)
          ·
            refine ⟨4296171851995277997038011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5728229135993703996050681 4296171851995277997038011)
            ·
              refine ⟨6444257777992916995557017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4296171851995277997038011 6444257777992916995557017)
              ·
                refine ⟨4833193333494687746667763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6444257777992916995557017 4833193333494687746667763)
                ·
                  refine ⟨7249790000242031620001645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4833193333494687746667763 7249790000242031620001645)
                  ·
                    refine ⟨2718671250090761857500617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7249790000242031620001645 2718671250090761857500617)
                    ·
                      refine ⟨2039003437568071393125463, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2718671250090761857500617 2039003437568071393125463)
                      ·
                        rfl

theorem cell23_3970945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 1, 2, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 1, 2, 1, 2, 1, 3, 2].length) (baseStart_3970945 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3970945 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3970945 prefixEnd_3970945 := by exact prefixLift 3970945
  have htrace : WordTrace (prefixWord ++ tailWord_3970945) baseStart_3970945 baseEnd_3970945 := by
    simpa [prefixWord, tailWord_3970945, baseEnd_3970945] using wordTrace_append hprefix tailTrace_3970945
  have hstable : (prefixWord ++ tailWord_3970945).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3970945).length < 2 ^ (prefixWord ++ tailWord_3970945).sum := by decide
  have hdescent : baseEnd_3970945 < baseStart_3970945 := by decide
  rcases family_descends (prefixWord ++ tailWord_3970945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3970958 : List Nat := [4, 1, 1, 5, 1, 1, 1, 2, 1, 4, 2]
def baseStart_3970958 : Nat := 118140960795 + 3970958 * 2 ^ 59
def prefixEnd_3970958 : Nat := 4983230072969 + 3 ^ 40 * 3970958 * 2
def baseEnd_3970958 : Nat := 2039010112816579842262903

theorem tailTrace_3970958 : CollatzResearch.WordTrace tailWord_3970958 prefixEnd_3970958 2039010112816579842262903 := by
  unfold tailWord_3970958
  simp only [CollatzResearch.WordTrace]
  refine ⟨18104092093488103309799191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 96555157831936550985595685 18104092093488103309799191)
  ·
    refine ⟨27156138140232154964698787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18104092093488103309799191 27156138140232154964698787)
    ·
      refine ⟨40734207210348232447048181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27156138140232154964698787 40734207210348232447048181)
      ·
        refine ⟨3818831925970146791910767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 40734207210348232447048181 3818831925970146791910767)
        ·
          refine ⟨5728247888955220187866151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3818831925970146791910767 5728247888955220187866151)
          ·
            refine ⟨8592371833432830281799227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5728247888955220187866151 8592371833432830281799227)
            ·
              refine ⟨12888557750149245422698841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8592371833432830281799227 12888557750149245422698841)
              ·
                refine ⟨9666418312611934067024131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12888557750149245422698841 9666418312611934067024131)
                ·
                  refine ⟨14499627468917901100536197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9666418312611934067024131 14499627468917901100536197)
                  ·
                    refine ⟨2718680150422106456350537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 14499627468917901100536197 2718680150422106456350537)
                    ·
                      refine ⟨2039010112816579842262903, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2718680150422106456350537 2039010112816579842262903)
                      ·
                        rfl

theorem cell23_3970958_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 1, 1, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 1, 1, 1, 2, 1, 4, 2].length) (baseStart_3970958 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3970958 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3970958 prefixEnd_3970958 := by exact prefixLift 3970958
  have htrace : WordTrace (prefixWord ++ tailWord_3970958) baseStart_3970958 baseEnd_3970958 := by
    simpa [prefixWord, tailWord_3970958, baseEnd_3970958] using wordTrace_append hprefix tailTrace_3970958
  have hstable : (prefixWord ++ tailWord_3970958).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3970958).length < 2 ^ (prefixWord ++ tailWord_3970958).sum := by decide
  have hdescent : baseEnd_3970958 < baseStart_3970958 := by decide
  rcases family_descends (prefixWord ++ tailWord_3970958) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3971017 : List Nat := [1, 2, 1, 1, 2, 1, 2, 5, 1, 4, 3]
def baseStart_3971017 : Nat := 118140960795 + 3971017 * 2 ^ 59
def prefixEnd_3971017 : Nat := 4983230072969 + 3 ^ 40 * 3971017 * 2
def baseEnd_3971017 : Nat := 2039040408175195111425131

theorem tailTrace_3971017 : CollatzResearch.WordTrace tailWord_3971017 prefixEnd_3971017 2039040408175195111425131 := by
  unfold tailWord_3971017
  simp only [CollatzResearch.WordTrace]
  refine ⟨144834888654691079554791305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96556592436460719703194203 144834888654691079554791305)
  ·
    refine ⟨108626166491018309666093479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 144834888654691079554791305 108626166491018309666093479)
    ·
      refine ⟨162939249736527464499140219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108626166491018309666093479 162939249736527464499140219)
      ·
        refine ⟨244408874604791196748710329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 162939249736527464499140219 244408874604791196748710329)
        ·
          refine ⟨183306655953593397561532747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 244408874604791196748710329 183306655953593397561532747)
          ·
            refine ⟨274959983930390096342299121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 183306655953593397561532747 274959983930390096342299121)
            ·
              refine ⟨206219987947792572256724341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 274959983930390096342299121 206219987947792572256724341)
              ·
                refine ⟨19333123870105553649067907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 206219987947792572256724341 19333123870105553649067907)
                ·
                  refine ⟨28999685805158330473601861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19333123870105553649067907 28999685805158330473601861)
                  ·
                    refine ⟨5437441088467186963800349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28999685805158330473601861 5437441088467186963800349)
                    ·
                      refine ⟨2039040408175195111425131, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5437441088467186963800349 2039040408175195111425131)
                      ·
                        rfl

theorem cell23_3971017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 2, 5, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 2, 5, 1, 4, 3].length) (baseStart_3971017 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3971017 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3971017 prefixEnd_3971017 := by exact prefixLift 3971017
  have htrace : WordTrace (prefixWord ++ tailWord_3971017) baseStart_3971017 baseEnd_3971017 := by
    simpa [prefixWord, tailWord_3971017, baseEnd_3971017] using wordTrace_append hprefix tailTrace_3971017
  have hstable : (prefixWord ++ tailWord_3971017).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3971017).length < 2 ^ (prefixWord ++ tailWord_3971017).sum := by decide
  have hdescent : baseEnd_3971017 < baseStart_3971017 := by decide
  rcases family_descends (prefixWord ++ tailWord_3971017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3971041 : List Nat := [1, 2, 3, 1, 2, 1, 4, 4, 1, 4]
def baseStart_3971041 : Nat := 118140960795 + 3971041 * 2 ^ 59
def prefixEnd_3971041 : Nat := 4983230072969 + 3 ^ 40 * 3971041 * 2
def baseEnd_3971041 : Nat := 679684243903634339175007

theorem tailTrace_3971041 : CollatzResearch.WordTrace tailWord_3971041 prefixEnd_3971041 679684243903634339175007 := by
  unfold tailWord_3971041
  simp only [CollatzResearch.WordTrace]
  refine ⟨144835764006604131653664977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96557176004402754435776651 144835764006604131653664977)
  ·
    refine ⟨108626823004953098740248733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 144835764006604131653664977 108626823004953098740248733)
    ·
      refine ⟨40735058626857412027593275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 108626823004953098740248733 40735058626857412027593275)
      ·
        refine ⟨61102587940286118041389913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40735058626857412027593275 61102587940286118041389913)
        ·
          refine ⟨45826940955214588531042435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61102587940286118041389913 45826940955214588531042435)
          ·
            refine ⟨68740411432821882796563653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45826940955214588531042435 68740411432821882796563653)
            ·
              refine ⟨12888827143654103024355685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 68740411432821882796563653 12888827143654103024355685)
              ·
                refine ⟨2416655089435144317066691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12888827143654103024355685 2416655089435144317066691)
                ·
                  refine ⟨3624982634152716475600037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2416655089435144317066691 3624982634152716475600037)
                  ·
                    refine ⟨679684243903634339175007, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3624982634152716475600037 679684243903634339175007)
                    ·
                      rfl

theorem cell23_3971041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 4, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 4, 4, 1, 4].length) (baseStart_3971041 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3971041 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3971041 prefixEnd_3971041 := by exact prefixLift 3971041
  have htrace : WordTrace (prefixWord ++ tailWord_3971041) baseStart_3971041 baseEnd_3971041 := by
    simpa [prefixWord, tailWord_3971041, baseEnd_3971041] using wordTrace_append hprefix tailTrace_3971041
  have hstable : (prefixWord ++ tailWord_3971041).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3971041).length < 2 ^ (prefixWord ++ tailWord_3971041).sum := by decide
  have hdescent : baseEnd_3971041 < baseStart_3971041 := by decide
  rcases family_descends (prefixWord ++ tailWord_3971041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3971067 : List Nat := [1, 1, 1, 1, 1, 3, 4, 3, 3, 5]
def baseStart_3971067 : Nat := 118140960795 + 3971067 * 2 ^ 59
def prefixEnd_3971067 : Nat := 4983230072969 + 3 ^ 40 * 3971067 * 2
def baseEnd_3971067 : Nat := 679688694069306638599967

theorem tailTrace_3971067 : CollatzResearch.WordTrace tailWord_3971067 prefixEnd_3971067 679688694069306638599967 := by
  unfold tailWord_3971067
  simp only [CollatzResearch.WordTrace]
  refine ⟨144836712304509938094111455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96557808203006625396074303 144836712304509938094111455)
  ·
    refine ⟨217255068456764907141167183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144836712304509938094111455 217255068456764907141167183)
    ·
      refine ⟨325882602685147360711750775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 217255068456764907141167183 325882602685147360711750775)
      ·
        refine ⟨488823904027721041067626163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 325882602685147360711750775 488823904027721041067626163)
        ·
          refine ⟨733235856041581561601439245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 488823904027721041067626163 733235856041581561601439245)
          ·
            refine ⟨274963446015593085600539717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 733235856041581561601439245 274963446015593085600539717)
            ·
              refine ⟨51555646127923703550101197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 274963446015593085600539717 51555646127923703550101197)
              ·
                refine ⟨19333367297971388831287949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 51555646127923703550101197 19333367297971388831287949)
                ·
                  refine ⟨7250012736739270811732981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19333367297971388831287949 7250012736739270811732981)
                  ·
                    refine ⟨679688694069306638599967, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7250012736739270811732981 679688694069306638599967)
                    ·
                      rfl

theorem cell23_3971067_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 4, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 4, 3, 3, 5].length) (baseStart_3971067 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3971067 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3971067 prefixEnd_3971067 := by exact prefixLift 3971067
  have htrace : WordTrace (prefixWord ++ tailWord_3971067) baseStart_3971067 baseEnd_3971067 := by
    simpa [prefixWord, tailWord_3971067, baseEnd_3971067] using wordTrace_append hprefix tailTrace_3971067
  have hstable : (prefixWord ++ tailWord_3971067).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3971067).length < 2 ^ (prefixWord ++ tailWord_3971067).sum := by decide
  have hdescent : baseEnd_3971067 < baseStart_3971067 := by decide
  rcases family_descends (prefixWord ++ tailWord_3971067) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3971084 : List Nat := [2, 2, 1, 2, 3, 1, 1, 5, 1, 5]
def baseStart_3971084 : Nat := 118140960795 + 3971084 * 2 ^ 59
def prefixEnd_3971084 : Nat := 4983230072969 + 3 ^ 40 * 3971084 * 2
def baseEnd_3971084 : Nat := 679691603793015449762441

theorem tailTrace_3971084 : CollatzResearch.WordTrace tailWord_3971084 prefixEnd_3971084 679691603793015449762441 := by
  unfold tailWord_3971084
  simp only [CollatzResearch.WordTrace]
  refine ⟨72418666172724174998740153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96558221563632233331653537 72418666172724174998740153)
  ·
    refine ⟨54313999629543131249055115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72418666172724174998740153 54313999629543131249055115)
    ·
      refine ⟨81470999444314696873582673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54313999629543131249055115 81470999444314696873582673)
      ·
        refine ⟨61103249583236022655187005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81470999444314696873582673 61103249583236022655187005)
        ·
          refine ⟨22913718593713508495695127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 61103249583236022655187005 22913718593713508495695127)
          ·
            refine ⟨34370577890570262743542691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22913718593713508495695127 34370577890570262743542691)
            ·
              refine ⟨51555866835855394115314037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34370577890570262743542691 51555866835855394115314037)
              ·
                refine ⟨4833362515861443198310691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 51555866835855394115314037 4833362515861443198310691)
                ·
                  refine ⟨7250043773792164797466037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4833362515861443198310691 7250043773792164797466037)
                  ·
                    refine ⟨679691603793015449762441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7250043773792164797466037 679691603793015449762441)
                    ·
                      rfl

theorem cell23_3971084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 1, 5, 1, 5].length) (baseStart_3971084 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3971084 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3971084 prefixEnd_3971084 := by exact prefixLift 3971084
  have htrace : WordTrace (prefixWord ++ tailWord_3971084) baseStart_3971084 baseEnd_3971084 := by
    simpa [prefixWord, tailWord_3971084, baseEnd_3971084] using wordTrace_append hprefix tailTrace_3971084
  have hstable : (prefixWord ++ tailWord_3971084).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3971084).length < 2 ^ (prefixWord ++ tailWord_3971084).sum := by decide
  have hdescent : baseEnd_3971084 < baseStart_3971084 := by decide
  rcases family_descends (prefixWord ++ tailWord_3971084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3971092 : List Nat := [2, 4, 3, 2, 2, 1, 1, 1, 3, 4]
def baseStart_3971092 : Nat := 118140960795 + 3971092 * 2 ^ 59
def prefixEnd_3971092 : Nat := 4983230072969 + 3 ^ 40 * 3971092 * 2
def baseEnd_3971092 : Nat := 679692973074760772662429

theorem tailTrace_3971092 : CollatzResearch.WordTrace tailWord_3971092 prefixEnd_3971092 679692973074760772662429 := by
  unfold tailWord_3971092
  simp only [CollatzResearch.WordTrace]
  refine ⟨72418812064709683681885765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96558416086279578242514353 72418812064709683681885765)
  ·
    refine ⟨13578527262133065690353581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 72418812064709683681885765 13578527262133065690353581)
    ·
      refine ⟨5091947723299899633882593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13578527262133065690353581 5091947723299899633882593)
      ·
        refine ⟨3818960792474924725411945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5091947723299899633882593 3818960792474924725411945)
        ·
          refine ⟨2864220594356193544058959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3818960792474924725411945 2864220594356193544058959)
          ·
            refine ⟨4296330891534290316088439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2864220594356193544058959 4296330891534290316088439)
            ·
              refine ⟨6444496337301435474132659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4296330891534290316088439 6444496337301435474132659)
              ·
                refine ⟨9666744505952153211198989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6444496337301435474132659 9666744505952153211198989)
                ·
                  refine ⟨3625029189732057454199621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9666744505952153211198989 3625029189732057454199621)
                  ·
                    refine ⟨679692973074760772662429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3625029189732057454199621 679692973074760772662429)
                    ·
                      rfl

theorem cell23_3971092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 2, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 2, 1, 1, 1, 3, 4].length) (baseStart_3971092 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3971092 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3971092 prefixEnd_3971092 := by exact prefixLift 3971092
  have htrace : WordTrace (prefixWord ++ tailWord_3971092) baseStart_3971092 baseEnd_3971092 := by
    simpa [prefixWord, tailWord_3971092, baseEnd_3971092] using wordTrace_append hprefix tailTrace_3971092
  have hstable : (prefixWord ++ tailWord_3971092).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3971092).length < 2 ^ (prefixWord ++ tailWord_3971092).sum := by decide
  have hdescent : baseEnd_3971092 < baseStart_3971092 := by decide
  rcases family_descends (prefixWord ++ tailWord_3971092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3971098 : List Nat := [3, 1, 1, 3, 1, 5, 1, 1, 3, 1, 3]
def baseStart_3971098 : Nat := 118140960795 + 3971098 * 2 ^ 59
def prefixEnd_3971098 : Nat := 4983230072969 + 3 ^ 40 * 3971098 * 2
def baseEnd_3971098 : Nat := 2039082000108209294512259

theorem tailTrace_3971098 : CollatzResearch.WordTrace tailWord_3971098 prefixEnd_3971098 2039082000108209294512259 := by
  unfold tailWord_3971098
  simp only [CollatzResearch.WordTrace]
  refine ⟨36209460741849407597122487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 96558561978265086925659965 36209460741849407597122487)
  ·
    refine ⟨54314191112774111395683731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36209460741849407597122487 54314191112774111395683731)
    ·
      refine ⟨81471286669161167093525597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54314191112774111395683731 81471286669161167093525597)
      ·
        refine ⟨30551732500935437660072099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 81471286669161167093525597 30551732500935437660072099)
        ·
          refine ⟨45827598751403156490108149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30551732500935437660072099 45827598751403156490108149)
          ·
            refine ⟨4296337382944045920947639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 45827598751403156490108149 4296337382944045920947639)
            ·
              refine ⟨6444506074416068881421459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4296337382944045920947639 6444506074416068881421459)
              ·
                refine ⟨9666759111624103322132189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6444506074416068881421459 9666759111624103322132189)
                ·
                  refine ⟨3625034666859038745799571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9666759111624103322132189 3625034666859038745799571)
                  ·
                    refine ⟨5437552000288558118699357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3625034666859038745799571 5437552000288558118699357)
                    ·
                      refine ⟨2039082000108209294512259, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5437552000288558118699357 2039082000108209294512259)
                      ·
                        rfl

theorem cell23_3971098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 5, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 5, 1, 1, 3, 1, 3].length) (baseStart_3971098 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3971098 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3971098 prefixEnd_3971098 := by exact prefixLift 3971098
  have htrace : WordTrace (prefixWord ++ tailWord_3971098) baseStart_3971098 baseEnd_3971098 := by
    simpa [prefixWord, tailWord_3971098, baseEnd_3971098] using wordTrace_append hprefix tailTrace_3971098
  have hstable : (prefixWord ++ tailWord_3971098).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3971098).length < 2 ^ (prefixWord ++ tailWord_3971098).sum := by decide
  have hdescent : baseEnd_3971098 < baseStart_3971098 := by decide
  rcases family_descends (prefixWord ++ tailWord_3971098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3971118 : List Nat := [4, 1, 3, 1, 1, 4, 1, 2, 1, 5]
def baseStart_3971118 : Nat := 118140960795 + 3971118 * 2 ^ 59
def prefixEnd_3971118 : Nat := 4983230072969 + 3 ^ 40 * 3971118 * 2
def baseEnd_3971118 : Nat := 679697423240433072087389

theorem tailTrace_3971118 : CollatzResearch.WordTrace tailWord_3971118 prefixEnd_3971118 679697423240433072087389 := by
  unfold tailWord_3971118
  simp only [CollatzResearch.WordTrace]
  refine ⟨18104821553415646725527251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 96559048284883449202812005 18104821553415646725527251)
  ·
    refine ⟨27157232330123470088290877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18104821553415646725527251 27157232330123470088290877)
    ·
      refine ⟨10183962123796301283109079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27157232330123470088290877 10183962123796301283109079)
      ·
        refine ⟨15275943185694451924663619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10183962123796301283109079 15275943185694451924663619)
        ·
          refine ⟨22913914778541677886995429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15275943185694451924663619 22913914778541677886995429)
          ·
            refine ⟨4296359020976564603811643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 22913914778541677886995429 4296359020976564603811643)
            ·
              refine ⟨6444538531464846905717465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4296359020976564603811643 6444538531464846905717465)
              ·
                refine ⟨4833403898598635179288099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6444538531464846905717465 4833403898598635179288099)
                ·
                  refine ⟨7250105847897952768932149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4833403898598635179288099 7250105847897952768932149)
                  ·
                    refine ⟨679697423240433072087389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7250105847897952768932149 679697423240433072087389)
                    ·
                      rfl

theorem cell23_3971118_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 4, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 4, 1, 2, 1, 5].length) (baseStart_3971118 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3971118 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3971118 prefixEnd_3971118 := by exact prefixLift 3971118
  have htrace : WordTrace (prefixWord ++ tailWord_3971118) baseStart_3971118 baseEnd_3971118 := by
    simpa [prefixWord, tailWord_3971118, baseEnd_3971118] using wordTrace_append hprefix tailTrace_3971118
  have hstable : (prefixWord ++ tailWord_3971118).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3971118).length < 2 ^ (prefixWord ++ tailWord_3971118).sum := by decide
  have hdescent : baseEnd_3971118 < baseStart_3971118 := by decide
  rcases family_descends (prefixWord ++ tailWord_3971118) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3971121 : List Nat := [1, 2, 2, 3, 1, 3, 3, 2, 1, 1, 4]
def baseStart_3971121 : Nat := 118140960795 + 3971121 * 2 ^ 59
def prefixEnd_3971121 : Nat := 4983230072969 + 3 ^ 40 * 3971121 * 2
def baseEnd_3971121 : Nat := 2039093810163262704524653

theorem tailTrace_3971121 : CollatzResearch.WordTrace tailWord_3971121 prefixEnd_3971121 2039093810163262704524653 := by
  unfold tailWord_3971121
  simp only [CollatzResearch.WordTrace]
  refine ⟨144838681846314305316577217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96559121230876203544384811 144838681846314305316577217)
  ·
    refine ⟨108629011384735728987432913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 144838681846314305316577217 108629011384735728987432913)
    ·
      refine ⟨81471758538551796740574685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 108629011384735728987432913 81471758538551796740574685)
      ·
        refine ⟨30551909451956923777715507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 81471758538551796740574685 30551909451956923777715507)
        ·
          refine ⟨45827864177935385666573261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30551909451956923777715507 45827864177935385666573261)
          ·
            refine ⟨17185449066725769624964973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45827864177935385666573261 17185449066725769624964973)
            ·
              refine ⟨6444543400022163609361865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17185449066725769624964973 6444543400022163609361865)
              ·
                refine ⟨4833407550016622707021399, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6444543400022163609361865 4833407550016622707021399)
                ·
                  refine ⟨7250111325024934060532099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4833407550016622707021399 7250111325024934060532099)
                  ·
                    refine ⟨10875166987537401090798149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7250111325024934060532099 10875166987537401090798149)
                    ·
                      refine ⟨2039093810163262704524653, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10875166987537401090798149 2039093810163262704524653)
                      ·
                        rfl

theorem cell23_3971121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 3, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 3, 3, 2, 1, 1, 4].length) (baseStart_3971121 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3971121 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3971121 prefixEnd_3971121 := by exact prefixLift 3971121
  have htrace : WordTrace (prefixWord ++ tailWord_3971121) baseStart_3971121 baseEnd_3971121 := by
    simpa [prefixWord, tailWord_3971121, baseEnd_3971121] using wordTrace_append hprefix tailTrace_3971121
  have hstable : (prefixWord ++ tailWord_3971121).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3971121).length < 2 ^ (prefixWord ++ tailWord_3971121).sum := by decide
  have hdescent : baseEnd_3971121 < baseStart_3971121 := by decide
  rcases family_descends (prefixWord ++ tailWord_3971121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3971127 : List Nat := [1, 1, 3, 1, 2, 2, 4, 9]
def baseStart_3971127 : Nat := 118140960795 + 3971127 * 2 ^ 59
def prefixEnd_3971127 : Nat := 4983230072969 + 3 ^ 40 * 3971127 * 2
def baseEnd_3971127 : Nat := 75522107075821840038875

theorem tailTrace_3971127 : CollatzResearch.WordTrace tailWord_3971127 prefixEnd_3971127 75522107075821840038875 := by
  unfold tailWord_3971127
  simp only [CollatzResearch.WordTrace]
  refine ⟨144838900684292568341295635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96559267122861712227530423 144838900684292568341295635)
  ·
    refine ⟨217258351026438852511943453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144838900684292568341295635 217258351026438852511943453)
    ·
      refine ⟨81471881634914569691978795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 217258351026438852511943453 81471881634914569691978795)
      ·
        refine ⟨122207822452371854537968193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81471881634914569691978795 122207822452371854537968193)
        ·
          refine ⟨91655866839278890903476145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 122207822452371854537968193 91655866839278890903476145)
          ·
            refine ⟨68741900129459168177607109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 91655866839278890903476145 68741900129459168177607109)
            ·
              refine ⟨12889106274273594033301333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 68741900129459168177607109 12889106274273594033301333)
              ·
                refine ⟨75522107075821840038875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 12889106274273594033301333 75522107075821840038875)
                ·
                  rfl

theorem cell23_3971127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 4, 9].length) (baseStart_3971127 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3971127 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3971127 prefixEnd_3971127 := by exact prefixLift 3971127
  have htrace : WordTrace (prefixWord ++ tailWord_3971127) baseStart_3971127 baseEnd_3971127 := by
    simpa [prefixWord, tailWord_3971127, baseEnd_3971127] using wordTrace_append hprefix tailTrace_3971127
  have hstable : (prefixWord ++ tailWord_3971127).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3971127).length < 2 ^ (prefixWord ++ tailWord_3971127).sum := by decide
  have hdescent : baseEnd_3971127 < baseStart_3971127 := by decide
  rcases family_descends (prefixWord ++ tailWord_3971127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3971204 : List Nat := [2, 3, 2, 1, 2, 1, 1, 1, 4, 6]
def baseStart_3971204 : Nat := 118140960795 + 3971204 * 2 ^ 59
def prefixEnd_3971204 : Nat := 4983230072969 + 3 ^ 40 * 3971204 * 2
def baseEnd_3971204 : Nat := 679712143019195293262257

theorem tailTrace_3971204 : CollatzResearch.WordTrace tailWord_3971204 prefixEnd_3971204 679712143019195293262257 := by
  unfold tailWord_3971204
  simp only [CollatzResearch.WordTrace]
  refine ⟨72420854552506805245924333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96561139403342406994565777 72420854552506805245924333)
  ·
    refine ⟨27157820457190051967221625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 72420854552506805245924333 27157820457190051967221625)
    ·
      refine ⟨20368365342892538975416219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27157820457190051967221625 20368365342892538975416219)
      ·
        refine ⟨30552548014338808463124329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20368365342892538975416219 30552548014338808463124329)
        ·
          refine ⟨22914411010754106347343247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30552548014338808463124329 22914411010754106347343247)
          ·
            refine ⟨34371616516131159521014871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22914411010754106347343247 34371616516131159521014871)
            ·
              refine ⟨51557424774196739281522307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34371616516131159521014871 51557424774196739281522307)
              ·
                refine ⟨77336137161295108922283461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51557424774196739281522307 77336137161295108922283461)
                ·
                  refine ⟨14500525717742832922928149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 77336137161295108922283461 14500525717742832922928149)
                  ·
                    refine ⟨679712143019195293262257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14500525717742832922928149 679712143019195293262257)
                    ·
                      rfl

theorem cell23_3971204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 1, 1, 4, 6].length) (baseStart_3971204 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3971204 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3971204 prefixEnd_3971204 := by exact prefixLift 3971204
  have htrace : WordTrace (prefixWord ++ tailWord_3971204) baseStart_3971204 baseEnd_3971204 := by
    simpa [prefixWord, tailWord_3971204, baseEnd_3971204] using wordTrace_append hprefix tailTrace_3971204
  have hstable : (prefixWord ++ tailWord_3971204).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3971204).length < 2 ^ (prefixWord ++ tailWord_3971204).sum := by decide
  have hdescent : baseEnd_3971204 < baseStart_3971204 := by decide
  rcases family_descends (prefixWord ++ tailWord_3971204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3971205 : List Nat := [1, 3, 1, 1, 5, 3, 1, 2, 2, 1, 3]
def baseStart_3971205 : Nat := 118140960795 + 3971205 * 2 ^ 59
def prefixEnd_3971205 : Nat := 4983230072969 + 3 ^ 40 * 3971205 * 2
def baseEnd_3971205 : Nat := 2039136942538240375874267

theorem tailTrace_3971205 : CollatzResearch.WordTrace tailWord_3971205 prefixEnd_3971205 2039136942538240375874267 := by
  unfold tailWord_3971205
  simp only [CollatzResearch.WordTrace]
  refine ⟨144841745578009987662635069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96561163718673325108423379 144841745578009987662635069)
  ·
    refine ⟨54315654591753745373488151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 144841745578009987662635069 54315654591753745373488151)
    ·
      refine ⟨81473481887630618060232227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54315654591753745373488151 81473481887630618060232227)
      ·
        refine ⟨122210222831445927090348341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81473481887630618060232227 122210222831445927090348341)
        ·
          refine ⟨11457208390448055664720157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 122210222831445927090348341 11457208390448055664720157)
          ·
            refine ⟨4296453146418020874270059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11457208390448055664720157 4296453146418020874270059)
            ·
              refine ⟨6444679719627031311405089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4296453146418020874270059 6444679719627031311405089)
              ·
                refine ⟨4833509789720273483553817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6444679719627031311405089 4833509789720273483553817)
                ·
                  refine ⟨3625132342290205112665363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4833509789720273483553817 3625132342290205112665363)
                  ·
                    refine ⟨5437698513435307668998045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3625132342290205112665363 5437698513435307668998045)
                    ·
                      refine ⟨2039136942538240375874267, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5437698513435307668998045 2039136942538240375874267)
                      ·
                        rfl

theorem cell23_3971205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 3, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 3, 1, 2, 2, 1, 3].length) (baseStart_3971205 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3971205 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3971205 prefixEnd_3971205 := by exact prefixLift 3971205
  have htrace : WordTrace (prefixWord ++ tailWord_3971205) baseStart_3971205 baseEnd_3971205 := by
    simpa [prefixWord, tailWord_3971205, baseEnd_3971205] using wordTrace_append hprefix tailTrace_3971205
  have hstable : (prefixWord ++ tailWord_3971205).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3971205).length < 2 ^ (prefixWord ++ tailWord_3971205).sum := by decide
  have hdescent : baseEnd_3971205 < baseStart_3971205 := by decide
  rcases family_descends (prefixWord ++ tailWord_3971205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3971245 : List Nat := [1, 5, 2, 1, 2, 1, 1, 2, 4, 2, 2]
def baseStart_3971245 : Nat := 118140960795 + 3971245 * 2 ^ 59
def prefixEnd_3971245 : Nat := 4983230072969 + 3 ^ 40 * 3971245 * 2
def baseEnd_3971245 : Nat := 2039157481764420219374083

theorem tailTrace_3971245 : CollatzResearch.WordTrace tailWord_3971245 prefixEnd_3971245 2039157481764420219374083 := by
  unfold tailWord_3971245
  simp only [CollatzResearch.WordTrace]
  refine ⟨144843204497865074494091189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96562136331910049662727459 144843204497865074494091189)
  ·
    refine ⟨13579050421674850733821049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 144843204497865074494091189 13579050421674850733821049)
    ·
      refine ⟨10184287816256138050365787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13579050421674850733821049 10184287816256138050365787)
      ·
        refine ⟨15276431724384207075548681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10184287816256138050365787 15276431724384207075548681)
        ·
          refine ⟨11457323793288155306661511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15276431724384207075548681 11457323793288155306661511)
          ·
            refine ⟨17185985689932232959992267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11457323793288155306661511 17185985689932232959992267)
            ·
              refine ⟨25778978534898349439988401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17185985689932232959992267 25778978534898349439988401)
              ·
                refine ⟨19334233901173762079991301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25778978534898349439988401 19334233901173762079991301)
                ·
                  refine ⟨3625168856470080389998369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19334233901173762079991301 3625168856470080389998369)
                  ·
                    refine ⟨2718876642352560292498777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3625168856470080389998369 2718876642352560292498777)
                    ·
                      refine ⟨2039157481764420219374083, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2718876642352560292498777 2039157481764420219374083)
                      ·
                        rfl

theorem cell23_3971245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 1, 1, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 1, 1, 2, 4, 2, 2].length) (baseStart_3971245 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3971245 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3971245 prefixEnd_3971245 := by exact prefixLift 3971245
  have htrace : WordTrace (prefixWord ++ tailWord_3971245) baseStart_3971245 baseEnd_3971245 := by
    simpa [prefixWord, tailWord_3971245, baseEnd_3971245] using wordTrace_append hprefix tailTrace_3971245
  have hstable : (prefixWord ++ tailWord_3971245).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3971245).length < 2 ^ (prefixWord ++ tailWord_3971245).sum := by decide
  have hdescent : baseEnd_3971245 < baseStart_3971245 := by decide
  rcases family_descends (prefixWord ++ tailWord_3971245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3971268 : List Nat := [2, 3, 3, 1, 2, 3, 1, 1, 7]
def baseStart_3971268 : Nat := 118140960795 + 3971268 * 2 ^ 59
def prefixEnd_3971268 : Nat := 4983230072969 + 3 ^ 40 * 3971268 * 2
def baseEnd_3971268 : Nat := 226574365757719292154053

theorem tailTrace_3971268 : CollatzResearch.WordTrace tailWord_3971268 prefixEnd_3971268 226574365757719292154053 := by
  unfold tailWord_3971268
  simp only [CollatzResearch.WordTrace]
  refine ⟨72422021688390874711089229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96562695584521166281452305 72422021688390874711089229)
  ·
    refine ⟨27158258133146578016658461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 72422021688390874711089229 27158258133146578016658461)
    ·
      refine ⟨10184346799929966756246923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27158258133146578016658461 10184346799929966756246923)
      ·
        refine ⟨15276520199894950134370385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10184346799929966756246923 15276520199894950134370385)
        ·
          refine ⟨11457390149921212600777789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15276520199894950134370385 11457390149921212600777789)
          ·
            refine ⟨4296521306220454725291671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11457390149921212600777789 4296521306220454725291671)
            ·
              refine ⟨6444781959330682087937507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4296521306220454725291671 6444781959330682087937507)
              ·
                refine ⟨9667172938996023131906261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6444781959330682087937507 9667172938996023131906261)
                ·
                  refine ⟨226574365757719292154053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9667172938996023131906261 226574365757719292154053)
                  ·
                    rfl

theorem cell23_3971268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 3, 1, 1, 7].length) (baseStart_3971268 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3971268 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3971268 prefixEnd_3971268 := by exact prefixLift 3971268
  have htrace : WordTrace (prefixWord ++ tailWord_3971268) baseStart_3971268 baseEnd_3971268 := by
    simpa [prefixWord, tailWord_3971268, baseEnd_3971268] using wordTrace_append hprefix tailTrace_3971268
  have hstable : (prefixWord ++ tailWord_3971268).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3971268).length < 2 ^ (prefixWord ++ tailWord_3971268).sum := by decide
  have hdescent : baseEnd_3971268 < baseStart_3971268 := by decide
  rcases family_descends (prefixWord ++ tailWord_3971268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3971318 : List Nat := [5, 1, 1, 1, 1, 1, 4, 2, 2, 1, 4]
def baseStart_3971318 : Nat := 118140960795 + 3971318 * 2 ^ 59
def prefixEnd_3971318 : Nat := 4983230072969 + 3 ^ 40 * 3971318 * 2
def baseEnd_3971318 : Nat := 2039194965852198433761247

theorem tailTrace_3971318 : CollatzResearch.WordTrace tailWord_3971318 prefixEnd_3971318 2039194965852198433761247 := by
  unfold tailWord_3971318
  simp only [CollatzResearch.WordTrace]
  refine ⟨9052866689162537997593663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 96563911351067071974332405 9052866689162537997593663)
  ·
    refine ⟨13579300033743806996390495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9052866689162537997593663 13579300033743806996390495)
    ·
      refine ⟨20368950050615710494585743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13579300033743806996390495 20368950050615710494585743)
      ·
        refine ⟨30553425075923565741878615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20368950050615710494585743 30553425075923565741878615)
        ·
          refine ⟨45830137613885348612817923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30553425075923565741878615 45830137613885348612817923)
          ·
            refine ⟨68745206420828022919226885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45830137613885348612817923 68745206420828022919226885)
            ·
              refine ⟨12889726203905254297355041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 68745206420828022919226885 12889726203905254297355041)
              ·
                refine ⟨9667294652928940723016281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12889726203905254297355041 9667294652928940723016281)
                ·
                  refine ⟨7250470989696705542262211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9667294652928940723016281 7250470989696705542262211)
                  ·
                    refine ⟨10875706484545058313393317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7250470989696705542262211 10875706484545058313393317)
                    ·
                      refine ⟨2039194965852198433761247, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10875706484545058313393317 2039194965852198433761247)
                      ·
                        rfl

theorem cell23_3971318_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 4, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 4, 2, 2, 1, 4].length) (baseStart_3971318 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3971318 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3971318 prefixEnd_3971318 := by exact prefixLift 3971318
  have htrace : WordTrace (prefixWord ++ tailWord_3971318) baseStart_3971318 baseEnd_3971318 := by
    simpa [prefixWord, tailWord_3971318, baseEnd_3971318] using wordTrace_append hprefix tailTrace_3971318
  have hstable : (prefixWord ++ tailWord_3971318).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3971318).length < 2 ^ (prefixWord ++ tailWord_3971318).sum := by decide
  have hdescent : baseEnd_3971318 < baseStart_3971318 := by decide
  rcases family_descends (prefixWord ++ tailWord_3971318) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3971321 : List Nat := [1, 2, 1, 3, 1, 1, 2, 3, 4, 2, 3]
def baseStart_3971321 : Nat := 118140960795 + 3971321 * 2 ^ 59
def prefixEnd_3971321 : Nat := 4983230072969 + 3 ^ 40 * 3971321 * 2
def baseEnd_3971321 : Nat := 2039196506294161922023733

theorem tailTrace_3971321 : CollatzResearch.WordTrace tailWord_3971321 prefixEnd_3971321 2039196506294161922023733 := by
  unfold tailWord_3971321
  simp only [CollatzResearch.WordTrace]
  refine ⟨144845976445589739473857817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96563984297059826315905211 144845976445589739473857817)
  ·
    refine ⟨108634482334192304605393363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 144845976445589739473857817 108634482334192304605393363)
    ·
      refine ⟨162951723501288456908090045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108634482334192304605393363 162951723501288456908090045)
      ·
        refine ⟨61106896312983171340533767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 162951723501288456908090045 61106896312983171340533767)
        ·
          refine ⟨91660344469474757010800651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61106896312983171340533767 91660344469474757010800651)
          ·
            refine ⟨137490516704212135516200977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91660344469474757010800651 137490516704212135516200977)
            ·
              refine ⟨103117887528159101637150733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 137490516704212135516200977 103117887528159101637150733)
              ·
                refine ⟨38669207823059663113931525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 103117887528159101637150733 38669207823059663113931525)
                ·
                  refine ⟨7250476466823686833862161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 38669207823059663113931525 7250476466823686833862161)
                  ·
                    refine ⟨5437857350117765125396621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7250476466823686833862161 5437857350117765125396621)
                    ·
                      refine ⟨2039196506294161922023733, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5437857350117765125396621 2039196506294161922023733)
                      ·
                        rfl

theorem cell23_3971321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 2, 3, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 2, 3, 4, 2, 3].length) (baseStart_3971321 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3971321 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3971321 prefixEnd_3971321 := by exact prefixLift 3971321
  have htrace : WordTrace (prefixWord ++ tailWord_3971321) baseStart_3971321 baseEnd_3971321 := by
    simpa [prefixWord, tailWord_3971321, baseEnd_3971321] using wordTrace_append hprefix tailTrace_3971321
  have hstable : (prefixWord ++ tailWord_3971321).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3971321).length < 2 ^ (prefixWord ++ tailWord_3971321).sum := by decide
  have hdescent : baseEnd_3971321 < baseStart_3971321 := by decide
  rcases family_descends (prefixWord ++ tailWord_3971321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3971362 : List Nat := [3, 3, 1, 1, 3, 2, 2, 3, 1, 4]
def baseStart_3971362 : Nat := 118140960795 + 3971362 * 2 ^ 59
def prefixEnd_3971362 : Nat := 4983230072969 + 3 ^ 40 * 3971362 * 2
def baseEnd_3971362 : Nat := 679739186333665420537015

theorem tailTrace_3971362 : CollatzResearch.WordTrace tailWord_3971362 prefixEnd_3971362 679739186333665420537015 := by
  unfold tailWord_3971362
  simp only [CollatzResearch.WordTrace]
  refine ⟨36211867959610300869025085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 96564981225627468984066893 36211867959610300869025085)
  ·
    refine ⟨13579450484853862825884407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36211867959610300869025085 13579450484853862825884407)
    ·
      refine ⟨20369175727280794238826611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13579450484853862825884407 20369175727280794238826611)
      ·
        refine ⟨30553763590921191358239917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20369175727280794238826611 30553763590921191358239917)
        ·
          refine ⟨11457661346595446759339969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30553763590921191358239917 11457661346595446759339969)
          ·
            refine ⟨8593246009946585069504977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11457661346595446759339969 8593246009946585069504977)
            ·
              refine ⟨6444934507459938802128733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8593246009946585069504977 6444934507459938802128733)
              ·
                refine ⟨2416850440297477050798275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6444934507459938802128733 2416850440297477050798275)
                ·
                  refine ⟨3625275660446215576197413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2416850440297477050798275 3625275660446215576197413)
                  ·
                    refine ⟨679739186333665420537015, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3625275660446215576197413 679739186333665420537015)
                    ·
                      rfl

theorem cell23_3971362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 2, 2, 3, 1, 4].length) (baseStart_3971362 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3971362 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3971362 prefixEnd_3971362 := by exact prefixLift 3971362
  have htrace : WordTrace (prefixWord ++ tailWord_3971362) baseStart_3971362 baseEnd_3971362 := by
    simpa [prefixWord, tailWord_3971362, baseEnd_3971362] using wordTrace_append hprefix tailTrace_3971362
  have hstable : (prefixWord ++ tailWord_3971362).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3971362).length < 2 ^ (prefixWord ++ tailWord_3971362).sum := by decide
  have hdescent : baseEnd_3971362 < baseStart_3971362 := by decide
  rcases family_descends (prefixWord ++ tailWord_3971362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3971385 : List Nat := [1, 2, 1, 6, 1, 1, 1, 3, 3, 1, 3]
def baseStart_3971385 : Nat := 118140960795 + 3971385 * 2 ^ 59
def prefixEnd_3971385 : Nat := 4983230072969 + 3 ^ 40 * 3971385 * 2
def baseEnd_3971385 : Nat := 2039229369056049671623439

theorem tailTrace_3971385 : CollatzResearch.WordTrace tailWord_3971385 prefixEnd_3971385 2039229369056049671623439 := by
  unfold tailWord_3971385
  simp only [CollatzResearch.WordTrace]
  refine ⟨144848310717357878404187609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96565540478238585602791739 144848310717357878404187609)
  ·
    refine ⟨108636233038018408803140707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 144848310717357878404187609 108636233038018408803140707)
    ·
      refine ⟨162954349557027613204711061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108636233038018408803140707 162954349557027613204711061)
      ·
        refine ⟨7638485135485669368970831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 162954349557027613204711061 7638485135485669368970831)
        ·
          refine ⟨11457727703228504053456247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7638485135485669368970831 11457727703228504053456247)
          ·
            refine ⟨17186591554842756080184371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11457727703228504053456247 17186591554842756080184371)
            ·
              refine ⟨25779887332264134120276557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17186591554842756080184371 25779887332264134120276557)
              ·
                refine ⟨9667457749599050295103709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25779887332264134120276557 9667457749599050295103709)
                ·
                  refine ⟨3625296656099643860663891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9667457749599050295103709 3625296656099643860663891)
                  ·
                    refine ⟨5437944984149465790995837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3625296656099643860663891 5437944984149465790995837)
                    ·
                      refine ⟨2039229369056049671623439, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5437944984149465790995837 2039229369056049671623439)
                      ·
                        rfl

theorem cell23_3971385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 1, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 1, 1, 3, 3, 1, 3].length) (baseStart_3971385 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3971385 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3971385 prefixEnd_3971385 := by exact prefixLift 3971385
  have htrace : WordTrace (prefixWord ++ tailWord_3971385) baseStart_3971385 baseEnd_3971385 := by
    simpa [prefixWord, tailWord_3971385, baseEnd_3971385] using wordTrace_append hprefix tailTrace_3971385
  have hstable : (prefixWord ++ tailWord_3971385).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3971385).length < 2 ^ (prefixWord ++ tailWord_3971385).sum := by decide
  have hdescent : baseEnd_3971385 < baseStart_3971385 := by decide
  rcases family_descends (prefixWord ++ tailWord_3971385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3971408 : List Nat := [2, 1, 1, 1, 1, 6, 1, 4, 1, 1, 4]
def baseStart_3971408 : Nat := 118140960795 + 3971408 * 2 ^ 59
def prefixEnd_3971408 : Nat := 4983230072969 + 3 ^ 40 * 3971408 * 2
def baseEnd_3971408 : Nat := 2039241179111103081635833

theorem tailTrace_3971408 : CollatzResearch.WordTrace tailWord_3971408 prefixEnd_3971408 2039241179111103081635833 := by
  unfold tailWord_3971408
  simp only [CollatzResearch.WordTrace]
  refine ⟨72424574798137276666137439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96566099730849702221516585 72424574798137276666137439)
  ·
    refine ⟨108636862197205914999206159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72424574798137276666137439 108636862197205914999206159)
    ·
      refine ⟨162955293295808872498809239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108636862197205914999206159 162955293295808872498809239)
      ·
        refine ⟨244432939943713308748213859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 162955293295808872498809239 244432939943713308748213859)
        ·
          refine ⟨366649409915569963122320789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 244432939943713308748213859 366649409915569963122320789)
          ·
            refine ⟨17186691089792342021358787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 366649409915569963122320789 17186691089792342021358787)
            ·
              refine ⟨25780036634688513032038181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17186691089792342021358787 25780036634688513032038181)
              ·
                refine ⟨4833756869004096193507159, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25780036634688513032038181 4833756869004096193507159)
                ·
                  refine ⟨7250635303506144290260739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4833756869004096193507159 7250635303506144290260739)
                  ·
                    refine ⟨10875952955259216435391109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7250635303506144290260739 10875952955259216435391109)
                    ·
                      refine ⟨2039241179111103081635833, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10875952955259216435391109 2039241179111103081635833)
                      ·
                        rfl

theorem cell23_3971408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 6, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 6, 1, 4, 1, 1, 4].length) (baseStart_3971408 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3971408 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3971408 prefixEnd_3971408 := by exact prefixLift 3971408
  have htrace : WordTrace (prefixWord ++ tailWord_3971408) baseStart_3971408 baseEnd_3971408 := by
    simpa [prefixWord, tailWord_3971408, baseEnd_3971408] using wordTrace_append hprefix tailTrace_3971408
  have hstable : (prefixWord ++ tailWord_3971408).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3971408).length < 2 ^ (prefixWord ++ tailWord_3971408).sum := by decide
  have hdescent : baseEnd_3971408 < baseStart_3971408 := by decide
  rcases family_descends (prefixWord ++ tailWord_3971408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3971428 : List Nat := [2, 3, 1, 1, 3, 1, 4, 1, 1, 1, 5]
def baseStart_3971428 : Nat := 118140960795 + 3971428 * 2 ^ 59
def prefixEnd_3971428 : Nat := 4983230072969 + 3 ^ 40 * 3971428 * 2
def baseEnd_3971428 : Nat := 2039251448724193003385741

theorem tailTrace_3971428 : CollatzResearch.WordTrace tailWord_3971428 prefixEnd_3971428 2039251448724193003385741 := by
  unfold tailWord_3971428
  simp only [CollatzResearch.WordTrace]
  refine ⟨72424939528101048374001469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96566586037468064498668625 72424939528101048374001469)
  ·
    refine ⟨27159352323037893140250551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 72424939528101048374001469 27159352323037893140250551)
    ·
      refine ⟨40739028484556839710375827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27159352323037893140250551 40739028484556839710375827)
      ·
        refine ⟨61108542726835259565563741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40739028484556839710375827 61108542726835259565563741)
        ·
          refine ⟨22915703522563222337086403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 61108542726835259565563741 22915703522563222337086403)
          ·
            refine ⟨34373555283844833505629605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22915703522563222337086403 34373555283844833505629605)
            ·
              refine ⟨6445041615720906282305551, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 34373555283844833505629605 6445041615720906282305551)
              ·
                refine ⟨9667562423581359423458327, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6445041615720906282305551 9667562423581359423458327)
                ·
                  refine ⟨14501343635372039135187491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9667562423581359423458327 14501343635372039135187491)
                  ·
                    refine ⟨21752015453058058702781237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14501343635372039135187491 21752015453058058702781237)
                    ·
                      refine ⟨2039251448724193003385741, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 21752015453058058702781237 2039251448724193003385741)
                      ·
                        rfl

theorem cell23_3971428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 4, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 4, 1, 1, 1, 5].length) (baseStart_3971428 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3971428 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3971428 prefixEnd_3971428 := by exact prefixLift 3971428
  have htrace : WordTrace (prefixWord ++ tailWord_3971428) baseStart_3971428 baseEnd_3971428 := by
    simpa [prefixWord, tailWord_3971428, baseEnd_3971428] using wordTrace_append hprefix tailTrace_3971428
  have hstable : (prefixWord ++ tailWord_3971428).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3971428).length < 2 ^ (prefixWord ++ tailWord_3971428).sum := by decide
  have hdescent : baseEnd_3971428 < baseStart_3971428 := by decide
  rcases family_descends (prefixWord ++ tailWord_3971428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3971431 : List Nat := [1, 1, 5, 1, 3, 1, 11]
def baseStart_3971431 : Nat := 118140960795 + 3971431 * 2 ^ 59
def prefixEnd_3971431 : Nat := 4983230072969 + 3 ^ 40 * 3971431 * 2
def baseEnd_3971431 : Nat := 25175962829211808538867

theorem tailTrace_3971431 : CollatzResearch.WordTrace tailWord_3971431 prefixEnd_3971431 25175962829211808538867 := by
  unfold tailWord_3971431
  simp only [CollatzResearch.WordTrace]
  refine ⟨144849988475191228260362147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96566658983460818840241431 144849988475191228260362147)
  ·
    refine ⟨217274982712786842390543221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144849988475191228260362147 217274982712786842390543221)
    ·
      refine ⟨20369529629323766474113427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 217274982712786842390543221 20369529629323766474113427)
      ·
        refine ⟨30554294443985649711170141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20369529629323766474113427 30554294443985649711170141)
        ·
          refine ⟨11457860416494618641688803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30554294443985649711170141 11457860416494618641688803)
          ·
            refine ⟨17186790624741927962533205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11457860416494618641688803 17186790624741927962533205)
            ·
              refine ⟨25175962829211808538867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 17186790624741927962533205 25175962829211808538867)
              ·
                rfl

theorem cell23_3971431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 1, 11].length) (baseStart_3971431 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3971431 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3971431 prefixEnd_3971431 := by exact prefixLift 3971431
  have htrace : WordTrace (prefixWord ++ tailWord_3971431) baseStart_3971431 baseEnd_3971431 := by
    simpa [prefixWord, tailWord_3971431, baseEnd_3971431] using wordTrace_append hprefix tailTrace_3971431
  have hstable : (prefixWord ++ tailWord_3971431).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3971431).length < 2 ^ (prefixWord ++ tailWord_3971431).sum := by decide
  have hdescent : baseEnd_3971431 < baseStart_3971431 := by decide
  rcases family_descends (prefixWord ++ tailWord_3971431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3971442 : List Nat := [3, 2, 1, 2, 1, 3, 3, 1, 3, 2, 2]
def baseStart_3971442 : Nat := 118140960795 + 3971442 * 2 ^ 59
def prefixEnd_3971442 : Nat := 4983230072969 + 3 ^ 40 * 3971442 * 2
def baseEnd_3971442 : Nat := 2039258637453355948610677

theorem tailTrace_3971442 : CollatzResearch.WordTrace tailWord_3971442 prefixEnd_3971442 2039258637453355948610677 := by
  unfold tailWord_3971442
  simp only [CollatzResearch.WordTrace]
  refine ⟨36212597419537844284753145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 96566926452100918092675053 36212597419537844284753145)
  ·
    refine ⟨27159448064653383213564859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36212597419537844284753145 27159448064653383213564859)
    ·
      refine ⟨40739172096980074820347289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27159448064653383213564859 40739172096980074820347289)
      ·
        refine ⟨30554379072735056115260467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40739172096980074820347289 30554379072735056115260467)
        ·
          refine ⟨45831568609102584172890701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30554379072735056115260467 45831568609102584172890701)
          ·
            refine ⟨17186838228413469064834013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45831568609102584172890701 17186838228413469064834013)
            ·
              refine ⟨6445064335655050899312755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17186838228413469064834013 6445064335655050899312755)
              ·
                refine ⟨9667596503482576348969133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6445064335655050899312755 9667596503482576348969133)
                ·
                  refine ⟨3625348688805966130863425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9667596503482576348969133 3625348688805966130863425)
                  ·
                    refine ⟨2719011516604474598147569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3625348688805966130863425 2719011516604474598147569)
                    ·
                      refine ⟨2039258637453355948610677, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2719011516604474598147569 2039258637453355948610677)
                      ·
                        rfl

theorem cell23_3971442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 3, 3, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 3, 3, 1, 3, 2, 2].length) (baseStart_3971442 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3971442 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3971442 prefixEnd_3971442 := by exact prefixLift 3971442
  have htrace : WordTrace (prefixWord ++ tailWord_3971442) baseStart_3971442 baseEnd_3971442 := by
    simpa [prefixWord, tailWord_3971442, baseEnd_3971442] using wordTrace_append hprefix tailTrace_3971442
  have hstable : (prefixWord ++ tailWord_3971442).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3971442).length < 2 ^ (prefixWord ++ tailWord_3971442).sum := by decide
  have hdescent : baseEnd_3971442 < baseStart_3971442 := by decide
  rcases family_descends (prefixWord ++ tailWord_3971442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3971518 : List Nat := [4, 2, 1, 1, 1, 1, 2, 1, 4, 1, 5]
def baseStart_3971518 : Nat := 118140960795 + 3971518 * 2 ^ 59
def prefixEnd_3971518 : Nat := 4983230072969 + 3 ^ 40 * 3971518 * 2
def baseEnd_3971518 : Nat := 2039297661983097651260327

theorem tailTrace_3971518 : CollatzResearch.WordTrace tailWord_3971518 prefixEnd_3971518 2039297661983097651260327 := by
  unfold tailWord_3971518
  simp only [CollatzResearch.WordTrace]
  refine ⟨18106645203234505264847401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 96568774417250694745852805 18106645203234505264847401)
  ·
    refine ⟨13579983902425878948635551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18106645203234505264847401 13579983902425878948635551)
    ·
      refine ⟨20369975853638818422953327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13579983902425878948635551 20369975853638818422953327)
      ·
        refine ⟨30554963780458227634429991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20369975853638818422953327 30554963780458227634429991)
        ·
          refine ⟨45832445670687341451644987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30554963780458227634429991 45832445670687341451644987)
          ·
            refine ⟨68748668506031012177467481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45832445670687341451644987 68748668506031012177467481)
            ·
              refine ⟨51561501379523259133100611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 68748668506031012177467481 51561501379523259133100611)
              ·
                refine ⟨77342252069284888699650917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51561501379523259133100611 77342252069284888699650917)
                ·
                  refine ⟨14501672262990916631184547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 77342252069284888699650917 14501672262990916631184547)
                  ·
                    refine ⟨21752508394486374946776821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14501672262990916631184547 21752508394486374946776821)
                    ·
                      refine ⟨2039297661983097651260327, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 21752508394486374946776821 2039297661983097651260327)
                      ·
                        rfl

theorem cell23_3971518_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 2, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 2, 1, 4, 1, 5].length) (baseStart_3971518 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3971518 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3971518 prefixEnd_3971518 := by exact prefixLift 3971518
  have htrace : WordTrace (prefixWord ++ tailWord_3971518) baseStart_3971518 baseEnd_3971518 := by
    simpa [prefixWord, tailWord_3971518, baseEnd_3971518] using wordTrace_append hprefix tailTrace_3971518
  have hstable : (prefixWord ++ tailWord_3971518).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3971518).length < 2 ^ (prefixWord ++ tailWord_3971518).sum := by decide
  have hdescent : baseEnd_3971518 < baseStart_3971518 := by decide
  rcases family_descends (prefixWord ++ tailWord_3971518) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3971531 : List Nat := [1, 1, 1, 1, 3, 3, 1, 2, 1, 2, 7]
def baseStart_3971531 : Nat := 118140960795 + 3971531 * 2 ^ 59
def prefixEnd_3971531 : Nat := 4983230072969 + 3 ^ 40 * 3971531 * 2
def baseEnd_3971531 : Nat := 2039304337231606100397767

theorem tailTrace_3971531 : CollatzResearch.WordTrace tailWord_3971531 prefixEnd_3971531 2039304337231606100397767 := by
  unfold tailWord_3971531
  simp only [CollatzResearch.WordTrace]
  refine ⟨144853635774828945339002447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96569090516552630226001631 144853635774828945339002447)
  ·
    refine ⟨217280453662243418008503671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144853635774828945339002447 217280453662243418008503671)
    ·
      refine ⟨325920680493365127012755507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 217280453662243418008503671 325920680493365127012755507)
      ·
        refine ⟨488881020740047690519133261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 325920680493365127012755507 488881020740047690519133261)
        ·
          refine ⟨183330382777517883944674973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 488881020740047690519133261 183330382777517883944674973)
          ·
            refine ⟨68748893541569206479253115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 183330382777517883944674973 68748893541569206479253115)
            ·
              refine ⟨103123340312353809718879673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68748893541569206479253115 103123340312353809718879673)
              ·
                refine ⟨77342505234265357289159755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 103123340312353809718879673 77342505234265357289159755)
                ·
                  refine ⟨116013757851398035933739633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 77342505234265357289159755 116013757851398035933739633)
                  ·
                    refine ⟨87010318388548526950304725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 116013757851398035933739633 87010318388548526950304725)
                    ·
                      refine ⟨2039304337231606100397767, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 87010318388548526950304725 2039304337231606100397767)
                      ·
                        rfl

theorem cell23_3971531_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 1, 2, 1, 2, 7].length) (baseStart_3971531 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3971531 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3971531 prefixEnd_3971531 := by exact prefixLift 3971531
  have htrace : WordTrace (prefixWord ++ tailWord_3971531) baseStart_3971531 baseEnd_3971531 := by
    simpa [prefixWord, tailWord_3971531, baseEnd_3971531] using wordTrace_append hprefix tailTrace_3971531
  have hstable : (prefixWord ++ tailWord_3971531).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3971531).length < 2 ^ (prefixWord ++ tailWord_3971531).sum := by decide
  have hdescent : baseEnd_3971531 < baseStart_3971531 := by decide
  rcases family_descends (prefixWord ++ tailWord_3971531) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3971555 : List Nat := [1, 1, 1, 6, 3, 1, 2, 1, 7]
def baseStart_3971555 : Nat := 118140960795 + 3971555 * 2 ^ 59
def prefixEnd_3971555 : Nat := 4983230072969 + 3 ^ 40 * 3971555 * 2
def baseEnd_3971555 : Nat := 226590740085257111833073

theorem tailTrace_3971555 : CollatzResearch.WordTrace tailWord_3971555 prefixEnd_3971555 226590740085257111833073 := by
  unfold tailWord_3971555
  simp only [CollatzResearch.WordTrace]
  refine ⟨144854511126741997437876119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96569674084494664958584079 144854511126741997437876119)
  ·
    refine ⟨217281766690112996156814179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144854511126741997437876119 217281766690112996156814179)
    ·
      refine ⟨325922650035169494235221269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 217281766690112996156814179 325922650035169494235221269)
      ·
        refine ⟨15277624220398570042275997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 325922650035169494235221269 15277624220398570042275997)
        ·
          refine ⟨5729109082649463765853499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15277624220398570042275997 5729109082649463765853499)
          ·
            refine ⟨8593663623974195648780249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5729109082649463765853499 8593663623974195648780249)
            ·
              refine ⟨6445247717980646736585187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8593663623974195648780249 6445247717980646736585187)
              ·
                refine ⟨9667871576970970104877781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6445247717980646736585187 9667871576970970104877781)
                ·
                  refine ⟨226590740085257111833073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9667871576970970104877781 226590740085257111833073)
                  ·
                    rfl

theorem cell23_3971555_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 3, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 3, 1, 2, 1, 7].length) (baseStart_3971555 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3971555 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3971555 prefixEnd_3971555 := by exact prefixLift 3971555
  have htrace : WordTrace (prefixWord ++ tailWord_3971555) baseStart_3971555 baseEnd_3971555 := by
    simpa [prefixWord, tailWord_3971555, baseEnd_3971555] using wordTrace_append hprefix tailTrace_3971555
  have hstable : (prefixWord ++ tailWord_3971555).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3971555).length < 2 ^ (prefixWord ++ tailWord_3971555).sum := by decide
  have hdescent : baseEnd_3971555 < baseStart_3971555 := by decide
  rcases family_descends (prefixWord ++ tailWord_3971555) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3971566 : List Nat := [4, 1, 2, 1, 2, 3, 3, 1, 2, 2, 2]
def baseStart_3971566 : Nat := 118140960795 + 3971566 * 2 ^ 59
def prefixEnd_3971566 : Nat := 4983230072969 + 3 ^ 40 * 3971566 * 2
def baseEnd_3971566 : Nat := 2039322309054513463460107

theorem tailTrace_3971566 : CollatzResearch.WordTrace tailWord_3971566 prefixEnd_3971566 2039322309054513463460107 := by
  unfold tailWord_3971566
  simp only [CollatzResearch.WordTrace]
  refine ⟨18106864041212768289565819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 96569941553134764211017701 18106864041212768289565819)
  ·
    refine ⟨27160296061819152434348729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18106864041212768289565819 27160296061819152434348729)
    ·
      refine ⟨20370222046364364325761547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27160296061819152434348729 20370222046364364325761547)
      ·
        refine ⟨30555333069546546488642321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20370222046364364325761547 30555333069546546488642321)
        ·
          refine ⟨22916499802159909866481741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30555333069546546488642321 22916499802159909866481741)
          ·
            refine ⟨8593687425809966199930653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22916499802159909866481741 8593687425809966199930653)
            ·
              refine ⟨3222632784678737324973995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8593687425809966199930653 3222632784678737324973995)
              ·
                refine ⟨4833949177018105987460993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3222632784678737324973995 4833949177018105987460993)
                ·
                  refine ⟨3625461882763579490595745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4833949177018105987460993 3625461882763579490595745)
                  ·
                    refine ⟨2719096412072684617946809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3625461882763579490595745 2719096412072684617946809)
                    ·
                      refine ⟨2039322309054513463460107, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2719096412072684617946809 2039322309054513463460107)
                      ·
                        rfl

theorem cell23_3971566_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 3, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 3, 3, 1, 2, 2, 2].length) (baseStart_3971566 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3971566 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3971566 prefixEnd_3971566 := by exact prefixLift 3971566
  have htrace : WordTrace (prefixWord ++ tailWord_3971566) baseStart_3971566 baseEnd_3971566 := by
    simpa [prefixWord, tailWord_3971566, baseEnd_3971566] using wordTrace_append hprefix tailTrace_3971566
  have hstable : (prefixWord ++ tailWord_3971566).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3971566).length < 2 ^ (prefixWord ++ tailWord_3971566).sum := by decide
  have hdescent : baseEnd_3971566 < baseStart_3971566 := by decide
  rcases family_descends (prefixWord ++ tailWord_3971566) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3971605 : List Nat := [1, 3, 2, 1, 3, 1, 3, 2, 2, 1, 4]
def baseStart_3971605 : Nat := 118140960795 + 3971605 * 2 ^ 59
def prefixEnd_3971605 : Nat := 4983230072969 + 3 ^ 40 * 3971605 * 2
def baseEnd_3971605 : Nat := 2039342334800038810872427

theorem tailTrace_3971605 : CollatzResearch.WordTrace tailWord_3971605 prefixEnd_3971605 2039342334800038810872427 := by
  unfold tailWord_3971605
  simp only [CollatzResearch.WordTrace]
  refine ⟨144856334776560855977196269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96570889851040570651464179 144856334776560855977196269)
  ·
    refine ⟨54321125541210320991448601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 144856334776560855977196269 54321125541210320991448601)
    ·
      refine ⟨40740844155907740743586451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54321125541210320991448601 40740844155907740743586451)
      ·
        refine ⟨61111266233861611115379677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40740844155907740743586451 61111266233861611115379677)
        ·
          refine ⟨22916724837698104168267379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 61111266233861611115379677 22916724837698104168267379)
          ·
            refine ⟨34375087256547156252401069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22916724837698104168267379 34375087256547156252401069)
            ·
              refine ⟨12890657721205183594650401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34375087256547156252401069 12890657721205183594650401)
              ·
                refine ⟨9667993290903887695987801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12890657721205183594650401 9667993290903887695987801)
                ·
                  refine ⟨7250994968177915771990851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9667993290903887695987801 7250994968177915771990851)
                  ·
                    refine ⟨10876492452266873657986277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7250994968177915771990851 10876492452266873657986277)
                    ·
                      refine ⟨2039342334800038810872427, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10876492452266873657986277 2039342334800038810872427)
                      ·
                        rfl

theorem cell23_3971605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 3, 2, 2, 1, 4].length) (baseStart_3971605 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3971605 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3971605 prefixEnd_3971605 := by exact prefixLift 3971605
  have htrace : WordTrace (prefixWord ++ tailWord_3971605) baseStart_3971605 baseEnd_3971605 := by
    simpa [prefixWord, tailWord_3971605, baseEnd_3971605] using wordTrace_append hprefix tailTrace_3971605
  have hstable : (prefixWord ++ tailWord_3971605).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3971605).length < 2 ^ (prefixWord ++ tailWord_3971605).sum := by decide
  have hdescent : baseEnd_3971605 < baseStart_3971605 := by decide
  rcases family_descends (prefixWord ++ tailWord_3971605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3971642 : List Nat := [3, 1, 1, 1, 3, 4, 2, 1, 2, 2, 3]
def baseStart_3971642 : Nat := 118140960795 + 3971642 * 2 ^ 59
def prefixEnd_3971642 : Nat := 4983230072969 + 3 ^ 40 * 3971642 * 2
def baseEnd_3971642 : Nat := 2039361333584255166109757

theorem tailTrace_3971642 : CollatzResearch.WordTrace tailWord_3971642 prefixEnd_3971642 2039361333584255166109757 := by
  unfold tailWord_3971642
  simp only [CollatzResearch.WordTrace]
  refine ⟨36214421069356702824073295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 96571789518284540864195453 36214421069356702824073295)
  ·
    refine ⟨54321631604035054236109943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36214421069356702824073295 54321631604035054236109943)
    ·
      refine ⟨81482447406052581354164915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54321631604035054236109943 81482447406052581354164915)
      ·
        refine ⟨122223671109078872031247373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81482447406052581354164915 122223671109078872031247373)
        ·
          refine ⟨45833876665904577011717765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 122223671109078872031247373 45833876665904577011717765)
          ·
            refine ⟨8593851874857108189697081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 45833876665904577011717765 8593851874857108189697081)
            ·
              refine ⟨6445388906142831142272811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8593851874857108189697081 6445388906142831142272811)
              ·
                refine ⟨9668083359214246713409217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6445388906142831142272811 9668083359214246713409217)
                ·
                  refine ⟨7251062519410685035056913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9668083359214246713409217 7251062519410685035056913)
                  ·
                    refine ⟨5438296889558013776292685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7251062519410685035056913 5438296889558013776292685)
                    ·
                      refine ⟨2039361333584255166109757, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5438296889558013776292685 2039361333584255166109757)
                      ·
                        rfl

theorem cell23_3971642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 4, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 4, 2, 1, 2, 2, 3].length) (baseStart_3971642 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3971642 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3971642 prefixEnd_3971642 := by exact prefixLift 3971642
  have htrace : WordTrace (prefixWord ++ tailWord_3971642) baseStart_3971642 baseEnd_3971642 := by
    simpa [prefixWord, tailWord_3971642, baseEnd_3971642] using wordTrace_append hprefix tailTrace_3971642
  have hstable : (prefixWord ++ tailWord_3971642).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3971642).length < 2 ^ (prefixWord ++ tailWord_3971642).sum := by decide
  have hdescent : baseEnd_3971642 < baseStart_3971642 := by decide
  rcases family_descends (prefixWord ++ tailWord_3971642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3971695 : List Nat := [1, 1, 2, 1, 3, 2, 4, 1, 3, 1, 4]
def baseStart_3971695 : Nat := 118140960795 + 3971695 * 2 ^ 59
def prefixEnd_3971695 : Nat := 4983230072969 + 3 ^ 40 * 3971695 * 2
def baseEnd_3971695 : Nat := 2039388548058943458747013

theorem tailTrace_3971695 : CollatzResearch.WordTrace tailWord_3971695 prefixEnd_3971695 2039388548058943458747013 := by
  unfold tailWord_3971695
  simp only [CollatzResearch.WordTrace]
  refine ⟨144859617346234801347972539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96573078230823200898648359 144859617346234801347972539)
  ·
    refine ⟨217289426019352202021958809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144859617346234801347972539 217289426019352202021958809)
    ·
      refine ⟨162967069514514151516469107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 217289426019352202021958809 162967069514514151516469107)
      ·
        refine ⟨244450604271771227274703661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 162967069514514151516469107 244450604271771227274703661)
        ·
          refine ⟨91668976601914210228013873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 244450604271771227274703661 91668976601914210228013873)
          ·
            refine ⟨68751732451435657671010405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 91668976601914210228013873 68751732451435657671010405)
            ·
              refine ⟨12890949834644185813314451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 68751732451435657671010405 12890949834644185813314451)
              ·
                refine ⟨19336424751966278719971677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12890949834644185813314451 19336424751966278719971677)
                ·
                  refine ⟨7251159281987354519989379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19336424751966278719971677 7251159281987354519989379)
                  ·
                    refine ⟨10876738922981031779984069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7251159281987354519989379 10876738922981031779984069)
                    ·
                      refine ⟨2039388548058943458747013, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10876738922981031779984069 2039388548058943458747013)
                      ·
                        rfl

theorem cell23_3971695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 4, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 4, 1, 3, 1, 4].length) (baseStart_3971695 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3971695 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3971695 prefixEnd_3971695 := by exact prefixLift 3971695
  have htrace : WordTrace (prefixWord ++ tailWord_3971695) baseStart_3971695 baseEnd_3971695 := by
    simpa [prefixWord, tailWord_3971695, baseEnd_3971695] using wordTrace_append hprefix tailTrace_3971695
  have hstable : (prefixWord ++ tailWord_3971695).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3971695).length < 2 ^ (prefixWord ++ tailWord_3971695).sum := by decide
  have hdescent : baseEnd_3971695 < baseStart_3971695 := by decide
  rcases family_descends (prefixWord ++ tailWord_3971695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3971705 : List Nat := [1, 2, 1, 3, 3, 2, 2, 2, 1, 6]
def baseStart_3971705 : Nat := 118140960795 + 3971705 * 2 ^ 59
def prefixEnd_3971705 : Nat := 4983230072969 + 3 ^ 40 * 3971705 * 2
def baseEnd_3971705 : Nat := 679797894288496139873989

theorem tailTrace_3971705 : CollatzResearch.WordTrace tailWord_3971705 prefixEnd_3971705 679797894288496139873989 := by
  unfold tailWord_3971705
  simp only [CollatzResearch.WordTrace]
  refine ⟨144859982076198573055836569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96573321384132382037224379 144859982076198573055836569)
  ·
    refine ⟨108644986557148929791877427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 144859982076198573055836569 108644986557148929791877427)
    ·
      refine ⟨162967479835723394687816141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108644986557148929791877427 162967479835723394687816141)
      ·
        refine ⟨61112804938396273007931053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 162967479835723394687816141 61112804938396273007931053)
        ·
          refine ⟨22917301851898602377974145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 61112804938396273007931053 22917301851898602377974145)
          ·
            refine ⟨17187976388923951783480609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22917301851898602377974145 17187976388923951783480609)
            ·
              refine ⟨12890982291692963837610457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17187976388923951783480609 12890982291692963837610457)
              ·
                refine ⟨9668236718769722878207843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12890982291692963837610457 9668236718769722878207843)
                ·
                  refine ⟨14502355078154584317311765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9668236718769722878207843 14502355078154584317311765)
                  ·
                    refine ⟨679797894288496139873989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14502355078154584317311765 679797894288496139873989)
                    ·
                      rfl

theorem cell23_3971705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 2, 2, 2, 1, 6].length) (baseStart_3971705 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3971705 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3971705 prefixEnd_3971705 := by exact prefixLift 3971705
  have htrace : WordTrace (prefixWord ++ tailWord_3971705) baseStart_3971705 baseEnd_3971705 := by
    simpa [prefixWord, tailWord_3971705, baseEnd_3971705] using wordTrace_append hprefix tailTrace_3971705
  have hstable : (prefixWord ++ tailWord_3971705).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3971705).length < 2 ^ (prefixWord ++ tailWord_3971705).sum := by decide
  have hdescent : baseEnd_3971705 < baseStart_3971705 := by decide
  rcases family_descends (prefixWord ++ tailWord_3971705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3971712 : List Nat := [2, 1, 1, 2, 1, 6, 1, 3, 1, 1, 4]
def baseStart_3971712 : Nat := 118140960795 + 3971712 * 2 ^ 59
def prefixEnd_3971712 : Nat := 4983230072969 + 3 ^ 40 * 3971712 * 2
def baseEnd_3971712 : Nat := 2039397277230069892234435

theorem tailTrace_3971712 : CollatzResearch.WordTrace tailWord_3971712 prefixEnd_3971712 2039397277230069892234435 := by
  unfold tailWord_3971712
  simp only [CollatzResearch.WordTrace]
  refine ⟨72430118693586606625670695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96573491591448808834227593 72430118693586606625670695)
  ·
    refine ⟨108645178040379909938506043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72430118693586606625670695 108645178040379909938506043)
    ·
      refine ⟨162967767060569864907759065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108645178040379909938506043 162967767060569864907759065)
      ·
        refine ⟨122225825295427398680819299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 162967767060569864907759065 122225825295427398680819299)
        ·
          refine ⟨183338737943141098021228949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 122225825295427398680819299 183338737943141098021228949)
          ·
            refine ⟨8594003341084738969745107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 183338737943141098021228949 8594003341084738969745107)
            ·
              refine ⟨12891005011627108454617661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8594003341084738969745107 12891005011627108454617661)
              ·
                refine ⟨4834126879360165670481623, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12891005011627108454617661 4834126879360165670481623)
                ·
                  refine ⟨7251190319040248505722435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4834126879360165670481623 7251190319040248505722435)
                  ·
                    refine ⟨10876785478560372758583653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7251190319040248505722435 10876785478560372758583653)
                    ·
                      refine ⟨2039397277230069892234435, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10876785478560372758583653 2039397277230069892234435)
                      ·
                        rfl

theorem cell23_3971712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 6, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 6, 1, 3, 1, 1, 4].length) (baseStart_3971712 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3971712 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3971712 prefixEnd_3971712 := by exact prefixLift 3971712
  have htrace : WordTrace (prefixWord ++ tailWord_3971712) baseStart_3971712 baseEnd_3971712 := by
    simpa [prefixWord, tailWord_3971712, baseEnd_3971712] using wordTrace_append hprefix tailTrace_3971712
  have hstable : (prefixWord ++ tailWord_3971712).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3971712).length < 2 ^ (prefixWord ++ tailWord_3971712).sum := by decide
  have hdescent : baseEnd_3971712 < baseStart_3971712 := by decide
  rcases family_descends (prefixWord ++ tailWord_3971712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3971728 : List Nat := [2, 1, 1, 1, 1, 1, 3, 1, 1, 4, 7]
def baseStart_3971728 : Nat := 118140960795 + 3971728 * 2 ^ 59
def prefixEnd_3971728 : Nat := 4983230072969 + 3 ^ 40 * 3971728 * 2
def baseEnd_3971728 : Nat := 2039405492920541829634361

theorem tailTrace_3971728 : CollatzResearch.WordTrace tailWord_3971728 prefixEnd_3971728 2039405492920541829634361 := by
  unfold tailWord_3971728
  simp only [CollatzResearch.WordTrace]
  refine ⟨72430410477557623991961919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96573880636743498655949225 72430410477557623991961919)
  ·
    refine ⟨108645615716336435987942879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72430410477557623991961919 108645615716336435987942879)
    ·
      refine ⟨162968423574504653981914319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108645615716336435987942879 162968423574504653981914319)
      ·
        refine ⟨244452635361756980972871479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 162968423574504653981914319 244452635361756980972871479)
        ·
          refine ⟨366678953042635471459307219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 244452635361756980972871479 366678953042635471459307219)
          ·
            refine ⟨550018429563953207188960829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 366678953042635471459307219 550018429563953207188960829)
            ·
              refine ⟨206256911086482452695860311, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 550018429563953207188960829 206256911086482452695860311)
              ·
                refine ⟨309385366629723679043790467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 206256911086482452695860311 309385366629723679043790467)
                ·
                  refine ⟨464078049944585518565685701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 309385366629723679043790467 464078049944585518565685701)
                  ·
                    refine ⟨87014634364609784731066069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 464078049944585518565685701 87014634364609784731066069)
                    ·
                      refine ⟨2039405492920541829634361, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 87014634364609784731066069 2039405492920541829634361)
                      ·
                        rfl

theorem cell23_3971728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 4, 7].length) (baseStart_3971728 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3971728 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3971728 prefixEnd_3971728 := by exact prefixLift 3971728
  have htrace : WordTrace (prefixWord ++ tailWord_3971728) baseStart_3971728 baseEnd_3971728 := by
    simpa [prefixWord, tailWord_3971728, baseEnd_3971728] using wordTrace_append hprefix tailTrace_3971728
  have hstable : (prefixWord ++ tailWord_3971728).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3971728).length < 2 ^ (prefixWord ++ tailWord_3971728).sum := by decide
  have hdescent : baseEnd_3971728 < baseStart_3971728 := by decide
  rcases family_descends (prefixWord ++ tailWord_3971728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3971732 : List Nat := [2, 4, 2, 2, 1, 1, 1, 1, 3, 1, 5]
def baseStart_3971732 : Nat := 118140960795 + 3971732 * 2 ^ 59
def prefixEnd_3971732 : Nat := 4983230072969 + 3 ^ 40 * 3971732 * 2
def baseEnd_3971732 : Nat := 2039407546843159813984343

theorem tailTrace_3971732 : CollatzResearch.WordTrace tailWord_3971732 prefixEnd_3971732 2039407546843159813984343 := by
  unfold tailWord_3971732
  simp only [CollatzResearch.WordTrace]
  refine ⟨72430483423550378333534725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96573977898067171111379633 72430483423550378333534725)
  ·
    refine ⟨13580715641915695937537761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 72430483423550378333534725 13580715641915695937537761)
    ·
      refine ⟨10185536731436771953153321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13580715641915695937537761 10185536731436771953153321)
      ·
        refine ⟨7639152548577578964864991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10185536731436771953153321 7639152548577578964864991)
        ·
          refine ⟨11458728822866368447297487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7639152548577578964864991 11458728822866368447297487)
          ·
            refine ⟨17188093234299552670946231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11458728822866368447297487 17188093234299552670946231)
            ·
              refine ⟨25782139851449329006419347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17188093234299552670946231 25782139851449329006419347)
              ·
                refine ⟨38673209777173993509629021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25782139851449329006419347 38673209777173993509629021)
                ·
                  refine ⟨14502453666440247566110883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38673209777173993509629021 14502453666440247566110883)
                  ·
                    refine ⟨21753680499660371349166325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14502453666440247566110883 21753680499660371349166325)
                    ·
                      refine ⟨2039407546843159813984343, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 21753680499660371349166325 2039407546843159813984343)
                      ·
                        rfl

theorem cell23_3971732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 1, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 1, 1, 1, 3, 1, 5].length) (baseStart_3971732 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3971732 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3971732 prefixEnd_3971732 := by exact prefixLift 3971732
  have htrace : WordTrace (prefixWord ++ tailWord_3971732) baseStart_3971732 baseEnd_3971732 := by
    simpa [prefixWord, tailWord_3971732, baseEnd_3971732] using wordTrace_append hprefix tailTrace_3971732
  have hstable : (prefixWord ++ tailWord_3971732).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3971732).length < 2 ^ (prefixWord ++ tailWord_3971732).sum := by decide
  have hdescent : baseEnd_3971732 < baseStart_3971732 := by decide
  rcases family_descends (prefixWord ++ tailWord_3971732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3971742 : List Nat := [4, 3, 1, 1, 1, 1, 3, 1, 1, 1, 6]
def baseStart_3971742 : Nat := 118140960795 + 3971742 * 2 ^ 59
def prefixEnd_3971742 : Nat := 4983230072969 + 3 ^ 40 * 3971742 * 2
def baseEnd_3971742 : Nat := 2039412681649704774859297

theorem tailTrace_3971742 : CollatzResearch.WordTrace tailWord_3971742 prefixEnd_3971742 2039412681649704774859297 := by
  unfold tailWord_3971742
  simp only [CollatzResearch.WordTrace]
  refine ⟨18107666447133066046866685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 96574221051376352249955653 18107666447133066046866685)
  ·
    refine ⟨6790374917674899767575007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18107666447133066046866685 6790374917674899767575007)
    ·
      refine ⟨10185562376512349651362511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6790374917674899767575007 10185562376512349651362511)
      ·
        refine ⟨15278343564768524477043767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10185562376512349651362511 15278343564768524477043767)
        ·
          refine ⟨22917515347152786715565651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15278343564768524477043767 22917515347152786715565651)
          ·
            refine ⟨34376273020729180073348477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22917515347152786715565651 34376273020729180073348477)
            ·
              refine ⟨12891102382773442527505679, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34376273020729180073348477 12891102382773442527505679)
              ·
                refine ⟨19336653574160163791258519, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12891102382773442527505679 19336653574160163791258519)
                ·
                  refine ⟨29004980361240245686887779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19336653574160163791258519 29004980361240245686887779)
                  ·
                    refine ⟨43507470541860368530331669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29004980361240245686887779 43507470541860368530331669)
                    ·
                      refine ⟨2039412681649704774859297, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 43507470541860368530331669 2039412681649704774859297)
                      ·
                        rfl

theorem cell23_3971742_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 3, 1, 1, 1, 6].length) (baseStart_3971742 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3971742 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3971742 prefixEnd_3971742 := by exact prefixLift 3971742
  have htrace : WordTrace (prefixWord ++ tailWord_3971742) baseStart_3971742 baseEnd_3971742 := by
    simpa [prefixWord, tailWord_3971742, baseEnd_3971742] using wordTrace_append hprefix tailTrace_3971742
  have hstable : (prefixWord ++ tailWord_3971742).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3971742).length < 2 ^ (prefixWord ++ tailWord_3971742).sum := by decide
  have hdescent : baseEnd_3971742 < baseStart_3971742 := by decide
  rcases family_descends (prefixWord ++ tailWord_3971742) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3971763 : List Nat := [1, 1, 1, 2, 3, 6, 1, 3, 1, 2, 2]
def baseStart_3971763 : Nat := 118140960795 + 3971763 * 2 ^ 59
def prefixEnd_3971763 : Nat := 4983230072969 + 3 ^ 40 * 3971763 * 2
def baseEnd_3971763 : Nat := 2039423464743449192696701

theorem tailTrace_3971763 : CollatzResearch.WordTrace tailWord_3971763 prefixEnd_3971763 2039423464743449192696701 := by
  unfold tailWord_3971763
  simp only [CollatzResearch.WordTrace]
  refine ⟨144862097509988448961447943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96574731673325632640965295 144862097509988448961447943)
  ·
    refine ⟨217293146264982673442171915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144862097509988448961447943 217293146264982673442171915)
    ·
      refine ⟨325939719397474010163257873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 217293146264982673442171915 325939719397474010163257873)
      ·
        refine ⟨244454789548105507622443405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 325939719397474010163257873 244454789548105507622443405)
        ·
          refine ⟨91670546080539565358416277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 244454789548105507622443405 91670546080539565358416277)
          ·
            refine ⟨4297056847525292126175763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 91670546080539565358416277 4297056847525292126175763)
            ·
              refine ⟨6445585271287938189263645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4297056847525292126175763 6445585271287938189263645)
              ·
                refine ⟨2417094476732976820973867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6445585271287938189263645 2417094476732976820973867)
                ·
                  refine ⟨3625641715099465231460801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2417094476732976820973867 3625641715099465231460801)
                  ·
                    refine ⟨2719231286324598923595601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3625641715099465231460801 2719231286324598923595601)
                    ·
                      refine ⟨2039423464743449192696701, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2719231286324598923595601 2039423464743449192696701)
                      ·
                        rfl

theorem cell23_3971763_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 6, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 6, 1, 3, 1, 2, 2].length) (baseStart_3971763 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3971763 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3971763 prefixEnd_3971763 := by exact prefixLift 3971763
  have htrace : WordTrace (prefixWord ++ tailWord_3971763) baseStart_3971763 baseEnd_3971763 := by
    simpa [prefixWord, tailWord_3971763, baseEnd_3971763] using wordTrace_append hprefix tailTrace_3971763
  have hstable : (prefixWord ++ tailWord_3971763).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3971763).length < 2 ^ (prefixWord ++ tailWord_3971763).sum := by decide
  have hdescent : baseEnd_3971763 < baseStart_3971763 := by decide
  rcases family_descends (prefixWord ++ tailWord_3971763) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3971766 : List Nat := [5, 1, 3, 1, 2, 1, 2, 1, 1, 1, 5]
def baseStart_3971766 : Nat := 118140960795 + 3971766 * 2 ^ 59
def prefixEnd_3971766 : Nat := 4983230072969 + 3 ^ 40 * 3971766 * 2
def baseEnd_3971766 : Nat := 2039425005185412680959187

theorem tailTrace_3971766 : CollatzResearch.WordTrace tailWord_3971766 prefixEnd_3971766 2039425005185412680959187 := by
  unfold tailWord_3971766
  simp only [CollatzResearch.WordTrace]
  refine ⟨9053887933061098779612947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 96574804619318386982538101 9053887933061098779612947)
  ·
    refine ⟨13580831899591648169419421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9053887933061098779612947 13580831899591648169419421)
    ·
      refine ⟨5092811962346868063532283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13580831899591648169419421 5092811962346868063532283)
      ·
        refine ⟨7639217943520302095298425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5092811962346868063532283 7639217943520302095298425)
        ·
          refine ⟨5729413457640226571473819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7639217943520302095298425 5729413457640226571473819)
          ·
            refine ⟨8594120186460339857210729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5729413457640226571473819 8594120186460339857210729)
            ·
              refine ⟨6445590139845254892908047, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8594120186460339857210729 6445590139845254892908047)
              ·
                refine ⟨9668385209767882339362071, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6445590139845254892908047 9668385209767882339362071)
                ·
                  refine ⟨14502577814651823509043107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9668385209767882339362071 14502577814651823509043107)
                  ·
                    refine ⟨21753866721977735263564661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14502577814651823509043107 21753866721977735263564661)
                    ·
                      refine ⟨2039425005185412680959187, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 21753866721977735263564661 2039425005185412680959187)
                      ·
                        rfl

theorem cell23_3971766_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 2, 1, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 2, 1, 2, 1, 1, 1, 5].length) (baseStart_3971766 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3971766 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3971766 prefixEnd_3971766 := by exact prefixLift 3971766
  have htrace : WordTrace (prefixWord ++ tailWord_3971766) baseStart_3971766 baseEnd_3971766 := by
    simpa [prefixWord, tailWord_3971766, baseEnd_3971766] using wordTrace_append hprefix tailTrace_3971766
  have hstable : (prefixWord ++ tailWord_3971766).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3971766).length < 2 ^ (prefixWord ++ tailWord_3971766).sum := by decide
  have hdescent : baseEnd_3971766 < baseStart_3971766 := by decide
  rcases family_descends (prefixWord ++ tailWord_3971766) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3971780 : List Nat := [2, 3, 3, 1, 1, 3, 3, 2, 1, 2, 2]
def baseStart_3971780 : Nat := 118140960795 + 3971780 * 2 ^ 59
def prefixEnd_3971780 : Nat := 4983230072969 + 3 ^ 40 * 3971780 * 2
def baseEnd_3971780 : Nat := 2039432193914575626184123

theorem tailTrace_3971780 : CollatzResearch.WordTrace tailWord_3971780 prefixEnd_3971780 2039432193914575626184123 := by
  unfold tailWord_3971780
  simp only [CollatzResearch.WordTrace]
  refine ⟨72431358775463430432408397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96575145033951240576544529 72431358775463430432408397)
  ·
    refine ⟨27161759540798786412153149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 72431358775463430432408397 27161759540798786412153149)
    ·
      refine ⟨10185659827799544904557431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27161759540798786412153149 10185659827799544904557431)
      ·
        refine ⟨15278489741699317356836147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10185659827799544904557431 15278489741699317356836147)
        ·
          refine ⟨22917734612548976035254221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15278489741699317356836147 22917734612548976035254221)
          ·
            refine ⟨8594150479705866013220333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22917734612548976035254221 8594150479705866013220333)
            ·
              refine ⟨3222806429889699754957625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8594150479705866013220333 3222806429889699754957625)
              ·
                refine ⟨2417104822417274816218219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3222806429889699754957625 2417104822417274816218219)
                ·
                  refine ⟨3625657233625912224327329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2417104822417274816218219 3625657233625912224327329)
                  ·
                    refine ⟨2719242925219434168245497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3625657233625912224327329 2719242925219434168245497)
                    ·
                      refine ⟨2039432193914575626184123, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2719242925219434168245497 2039432193914575626184123)
                      ·
                        rfl

theorem cell23_3971780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 3, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 3, 3, 2, 1, 2, 2].length) (baseStart_3971780 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3971780 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3971780 prefixEnd_3971780 := by exact prefixLift 3971780
  have htrace : WordTrace (prefixWord ++ tailWord_3971780) baseStart_3971780 baseEnd_3971780 := by
    simpa [prefixWord, tailWord_3971780, baseEnd_3971780] using wordTrace_append hprefix tailTrace_3971780
  have hstable : (prefixWord ++ tailWord_3971780).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3971780).length < 2 ^ (prefixWord ++ tailWord_3971780).sum := by decide
  have hdescent : baseEnd_3971780 < baseStart_3971780 := by decide
  rcases family_descends (prefixWord ++ tailWord_3971780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3971822 : List Nat := [4, 1, 2, 1, 1, 3, 2, 1, 2, 1, 5]
def baseStart_3971822 : Nat := 118140960795 + 3971822 * 2 ^ 59
def prefixEnd_3971822 : Nat := 4983230072969 + 3 ^ 40 * 3971822 * 2
def baseEnd_3971822 : Nat := 2039453760102064461858929

theorem tailTrace_3971822 : CollatzResearch.WordTrace tailWord_3971822 prefixEnd_3971822 2039453760102064461858929 := by
  unfold tailWord_3971822
  simp only [CollatzResearch.WordTrace]
  refine ⟨18108031177096837754730715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 96576166277849801358563813 18108031177096837754730715)
  ·
    refine ⟨27162046765645256632096073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18108031177096837754730715 27162046765645256632096073)
    ·
      refine ⟨20371535074233942474072055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27162046765645256632096073 20371535074233942474072055)
      ·
        refine ⟨30557302611350913711108083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20371535074233942474072055 30557302611350913711108083)
        ·
          refine ⟨45835953917026370566662125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30557302611350913711108083 45835953917026370566662125)
          ·
            refine ⟨17188482718884888962498297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45835953917026370566662125 17188482718884888962498297)
            ·
              refine ⟨12891362039163666721873723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17188482718884888962498297 12891362039163666721873723)
              ·
                refine ⟨19337043058745500082810585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12891362039163666721873723 19337043058745500082810585)
                ·
                  refine ⟨14502782294059125062107939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19337043058745500082810585 14502782294059125062107939)
                  ·
                    refine ⟨21754173441088687593161909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14502782294059125062107939 21754173441088687593161909)
                    ·
                      refine ⟨2039453760102064461858929, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 21754173441088687593161909 2039453760102064461858929)
                      ·
                        rfl

theorem cell23_3971822_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 3, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 3, 2, 1, 2, 1, 5].length) (baseStart_3971822 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3971822 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3971822 prefixEnd_3971822 := by exact prefixLift 3971822
  have htrace : WordTrace (prefixWord ++ tailWord_3971822) baseStart_3971822 baseEnd_3971822 := by
    simpa [prefixWord, tailWord_3971822, baseEnd_3971822] using wordTrace_append hprefix tailTrace_3971822
  have hstable : (prefixWord ++ tailWord_3971822).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3971822).length < 2 ^ (prefixWord ++ tailWord_3971822).sum := by decide
  have hdescent : baseEnd_3971822 < baseStart_3971822 := by decide
  rcases family_descends (prefixWord ++ tailWord_3971822) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3971836 : List Nat := [2, 2, 2, 1, 3, 2, 1, 4, 2, 2, 2]
def baseStart_3971836 : Nat := 118140960795 + 3971836 * 2 ^ 59
def prefixEnd_3971836 : Nat := 4983230072969 + 3 ^ 40 * 3971836 * 2
def baseEnd_3971836 : Nat := 2039460948831227407083865

theorem tailTrace_3971836 : CollatzResearch.WordTrace tailWord_3971836 prefixEnd_3971836 2039460948831227407083865 := by
  unfold tailWord_3971836
  simp only [CollatzResearch.WordTrace]
  refine ⟨72432380019361991214427681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96576506692482654952570241 72432380019361991214427681)
  ·
    refine ⟨54324285014521493410820761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72432380019361991214427681 54324285014521493410820761)
    ·
      refine ⟨40743213760891120058115571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54324285014521493410820761 40743213760891120058115571)
      ·
        refine ⟨61114820641336680087173357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40743213760891120058115571 61114820641336680087173357)
        ·
          refine ⟨22918057740501255032690009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 61114820641336680087173357 22918057740501255032690009)
          ·
            refine ⟨17188543305375941274517507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22918057740501255032690009 17188543305375941274517507)
            ·
              refine ⟨25782814958063911911776261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17188543305375941274517507 25782814958063911911776261)
              ·
                refine ⟨4834277804636983483458049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25782814958063911911776261 4834277804636983483458049)
                ·
                  refine ⟨3625708353477737612593537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4834277804636983483458049 3625708353477737612593537)
                  ·
                    refine ⟨2719281265108303209445153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3625708353477737612593537 2719281265108303209445153)
                    ·
                      refine ⟨2039460948831227407083865, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2719281265108303209445153 2039460948831227407083865)
                      ·
                        rfl

theorem cell23_3971836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 2, 1, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 2, 1, 4, 2, 2, 2].length) (baseStart_3971836 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3971836 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3971836 prefixEnd_3971836 := by exact prefixLift 3971836
  have htrace : WordTrace (prefixWord ++ tailWord_3971836) baseStart_3971836 baseEnd_3971836 := by
    simpa [prefixWord, tailWord_3971836, baseEnd_3971836] using wordTrace_append hprefix tailTrace_3971836
  have hstable : (prefixWord ++ tailWord_3971836).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3971836).length < 2 ^ (prefixWord ++ tailWord_3971836).sum := by decide
  have hdescent : baseEnd_3971836 < baseStart_3971836 := by decide
  rcases family_descends (prefixWord ++ tailWord_3971836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3971855 : List Nat := [1, 1, 2, 1, 1, 1, 6, 2, 1, 7]
def baseStart_3971855 : Nat := 118140960795 + 3971855 * 2 ^ 59
def prefixEnd_3971855 : Nat := 4983230072969 + 3 ^ 40 * 3971855 * 2
def baseEnd_3971855 : Nat := 679823568321220944248759

theorem tailTrace_3971855 : CollatzResearch.WordTrace tailWord_3971855 prefixEnd_3971855 679823568321220944248759 := by
  unfold tailWord_3971855
  simp only [CollatzResearch.WordTrace]
  refine ⟨144865453025655148673797019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96576968683770099115864679 144865453025655148673797019)
  ·
    refine ⟨217298179538482723010695529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144865453025655148673797019 217298179538482723010695529)
    ·
      refine ⟨162973634653862042258021647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 217298179538482723010695529 162973634653862042258021647)
      ·
        refine ⟨244460451980793063387032471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 162973634653862042258021647 244460451980793063387032471)
        ·
          refine ⟨366690677971189595080548707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 244460451980793063387032471 366690677971189595080548707)
          ·
            refine ⟨550036016956784392620823061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 366690677971189595080548707 550036016956784392620823061)
            ·
              refine ⟨25782938294849268404101081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 550036016956784392620823061 25782938294849268404101081)
              ·
                refine ⟨19337203721136951303075811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25782938294849268404101081 19337203721136951303075811)
                ·
                  refine ⟨29005805581705426954613717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19337203721136951303075811 29005805581705426954613717)
                  ·
                    refine ⟨679823568321220944248759, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 29005805581705426954613717 679823568321220944248759)
                    ·
                      rfl

theorem cell23_3971855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 6, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 6, 2, 1, 7].length) (baseStart_3971855 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3971855 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3971855 prefixEnd_3971855 := by exact prefixLift 3971855
  have htrace : WordTrace (prefixWord ++ tailWord_3971855) baseStart_3971855 baseEnd_3971855 := by
    simpa [prefixWord, tailWord_3971855, baseEnd_3971855] using wordTrace_append hprefix tailTrace_3971855
  have hstable : (prefixWord ++ tailWord_3971855).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3971855).length < 2 ^ (prefixWord ++ tailWord_3971855).sum := by decide
  have hdescent : baseEnd_3971855 < baseStart_3971855 := by decide
  rcases family_descends (prefixWord ++ tailWord_3971855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3971865 : List Nat := [1, 2, 1, 2, 1, 1, 1, 4, 3, 2, 5]
def baseStart_3971865 : Nat := 118140960795 + 3971865 * 2 ^ 59
def prefixEnd_3971865 : Nat := 4983230072969 + 3 ^ 40 * 3971865 * 2
def baseEnd_3971865 : Nat := 2039475839770207793621231

theorem tailTrace_3971865 : CollatzResearch.WordTrace tailWord_3971865 prefixEnd_3971865 2039475839770207793621231 := by
  unfold tailWord_3971865
  simp only [CollatzResearch.WordTrace]
  refine ⟨144865817755618920381661049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96577211837079280254440699 144865817755618920381661049)
  ·
    refine ⟨108649363316714190286245787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 144865817755618920381661049 108649363316714190286245787)
    ·
      refine ⟨162974044975071285429368681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108649363316714190286245787 162974044975071285429368681)
      ·
        refine ⟨122230533731303464072026511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 162974044975071285429368681 122230533731303464072026511)
        ·
          refine ⟨183345800596955196108039767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 122230533731303464072026511 183345800596955196108039767)
          ·
            refine ⟨275018700895432794162059651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 183345800596955196108039767 275018700895432794162059651)
            ·
              refine ⟨412528051343149191243089477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 275018700895432794162059651 412528051343149191243089477)
              ·
                refine ⟨77349009626840473358079277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 412528051343149191243089477 77349009626840473358079277)
                ·
                  refine ⟨29005878610065177509279729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 77349009626840473358079277 29005878610065177509279729)
                  ·
                    refine ⟨21754408957548883131959797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29005878610065177509279729 21754408957548883131959797)
                    ·
                      refine ⟨2039475839770207793621231, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 21754408957548883131959797 2039475839770207793621231)
                      ·
                        rfl

theorem cell23_3971865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 4, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 4, 3, 2, 5].length) (baseStart_3971865 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3971865 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3971865 prefixEnd_3971865 := by exact prefixLift 3971865
  have htrace : WordTrace (prefixWord ++ tailWord_3971865) baseStart_3971865 baseEnd_3971865 := by
    simpa [prefixWord, tailWord_3971865, baseEnd_3971865] using wordTrace_append hprefix tailTrace_3971865
  have hstable : (prefixWord ++ tailWord_3971865).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3971865).length < 2 ^ (prefixWord ++ tailWord_3971865).sum := by decide
  have hdescent : baseEnd_3971865 < baseStart_3971865 := by decide
  rcases family_descends (prefixWord ++ tailWord_3971865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3971872 : List Nat := [2, 1, 1, 5, 1, 3, 1, 1, 1, 7]
def baseStart_3971872 : Nat := 118140960795 + 3971872 * 2 ^ 59
def prefixEnd_3971872 : Nat := 4983230072969 + 3 ^ 40 * 3971872 * 2
def baseEnd_3971872 : Nat := 679826478044929755411233

theorem tailTrace_3971872 : CollatzResearch.WordTrace tailWord_3971872 prefixEnd_3971872 679826478044929755411233 := by
  unfold tailWord_3971872
  simp only [CollatzResearch.WordTrace]
  refine ⟨72433036533296780288582935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96577382044395707051443913 72433036533296780288582935)
  ·
    refine ⟨108649554799945170432874403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72433036533296780288582935 108649554799945170432874403)
    ·
      refine ⟨162974332199917755649311605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108649554799945170432874403 162974332199917755649311605)
      ·
        refine ⟨15278843643742289592122963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 162974332199917755649311605 15278843643742289592122963)
        ·
          refine ⟨22918265465613434388184445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15278843643742289592122963 22918265465613434388184445)
          ·
            refine ⟨8594349549605037895569167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22918265465613434388184445 8594349549605037895569167)
            ·
              refine ⟨12891524324407556843353751, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8594349549605037895569167 12891524324407556843353751)
              ·
                refine ⟨19337286486611335265030627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12891524324407556843353751 19337286486611335265030627)
                ·
                  refine ⟨29005929729917002897545941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19337286486611335265030627 29005929729917002897545941)
                  ·
                    refine ⟨679826478044929755411233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 29005929729917002897545941 679826478044929755411233)
                    ·
                      rfl

theorem cell23_3971872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 3, 1, 1, 1, 7].length) (baseStart_3971872 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3971872 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3971872 prefixEnd_3971872 := by exact prefixLift 3971872
  have htrace : WordTrace (prefixWord ++ tailWord_3971872) baseStart_3971872 baseEnd_3971872 := by
    simpa [prefixWord, tailWord_3971872, baseEnd_3971872] using wordTrace_append hprefix tailTrace_3971872
  have hstable : (prefixWord ++ tailWord_3971872).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3971872).length < 2 ^ (prefixWord ++ tailWord_3971872).sum := by decide
  have hdescent : baseEnd_3971872 < baseStart_3971872 := by decide
  rcases family_descends (prefixWord ++ tailWord_3971872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3971876 : List Nat := [2, 3, 1, 3, 3, 1, 2, 3, 5]
def baseStart_3971876 : Nat := 118140960795 + 3971876 * 2 ^ 59
def prefixEnd_3971876 : Nat := 4983230072969 + 3 ^ 40 * 3971876 * 2
def baseEnd_3971876 : Nat := 226609054228600805620409

theorem tailTrace_3971876 : CollatzResearch.WordTrace tailWord_3971876 prefixEnd_3971876 226609054228600805620409 := by
  unfold tailWord_3971876
  simp only [CollatzResearch.WordTrace]
  refine ⟨72433109479289534630155741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96577479305719379506874321 72433109479289534630155741)
  ·
    refine ⟨27162416054733575486308403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 72433109479289534630155741 27162416054733575486308403)
    ·
      refine ⟨40743624082100363229462605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27162416054733575486308403 40743624082100363229462605)
      ·
        refine ⟨15278859030787636211048477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40743624082100363229462605 15278859030787636211048477)
        ·
          refine ⟨5729572136545363579143179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15278859030787636211048477 5729572136545363579143179)
          ·
            refine ⟨8594358204818045368714769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5729572136545363579143179 8594358204818045368714769)
            ·
              refine ⟨6445768653613534026536077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8594358204818045368714769 6445768653613534026536077)
              ·
                refine ⟨2417163245105075259951029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6445768653613534026536077 2417163245105075259951029)
                ·
                  refine ⟨226609054228600805620409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2417163245105075259951029 226609054228600805620409)
                  ·
                    rfl

theorem cell23_3971876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 3, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 3, 1, 2, 3, 5].length) (baseStart_3971876 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3971876 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3971876 prefixEnd_3971876 := by exact prefixLift 3971876
  have htrace : WordTrace (prefixWord ++ tailWord_3971876) baseStart_3971876 baseEnd_3971876 := by
    simpa [prefixWord, tailWord_3971876, baseEnd_3971876] using wordTrace_append hprefix tailTrace_3971876
  have hstable : (prefixWord ++ tailWord_3971876).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3971876).length < 2 ^ (prefixWord ++ tailWord_3971876).sum := by decide
  have hdescent : baseEnd_3971876 < baseStart_3971876 := by decide
  rcases family_descends (prefixWord ++ tailWord_3971876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3971912 : List Nat := [2, 1, 3, 1, 1, 3, 1, 1, 3, 4, 3]
def baseStart_3971912 : Nat := 118140960795 + 3971912 * 2 ^ 59
def prefixEnd_3971912 : Nat := 4983230072969 + 3 ^ 40 * 3971912 * 2
def baseEnd_3971912 : Nat := 2039499973360969109733515

theorem tailTrace_3971912 : CollatzResearch.WordTrace tailWord_3971912 prefixEnd_3971912 2039499973360969109733515 := by
  unfold tailWord_3971912
  simp only [CollatzResearch.WordTrace]
  refine ⟨72433765993224323704310995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96578354657632431605747993 72433765993224323704310995)
  ·
    refine ⟨108650648989836485556466493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72433765993224323704310995 108650648989836485556466493)
    ·
      refine ⟨40743993371188682083674935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 108650648989836485556466493 40743993371188682083674935)
      ·
        refine ⟨61115990056783023125512403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40743993371188682083674935 61115990056783023125512403)
        ·
          refine ⟨91673985085174534688268605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61115990056783023125512403 91673985085174534688268605)
          ·
            refine ⟨34377744406940450508100727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 91673985085174534688268605 34377744406940450508100727)
            ·
              refine ⟨51566616610410675762151091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34377744406940450508100727 51566616610410675762151091)
              ·
                refine ⟨77349924915616013643226637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51566616610410675762151091 77349924915616013643226637)
                ·
                  refine ⟨29006221843356005116209989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 77349924915616013643226637 29006221843356005116209989)
                  ·
                    refine ⟨5438666595629250959289373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29006221843356005116209989 5438666595629250959289373)
                    ·
                      refine ⟨2039499973360969109733515, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5438666595629250959289373 2039499973360969109733515)
                      ·
                        rfl

theorem cell23_3971912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 1, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 1, 1, 3, 4, 3].length) (baseStart_3971912 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3971912 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3971912 prefixEnd_3971912 := by exact prefixLift 3971912
  have htrace : WordTrace (prefixWord ++ tailWord_3971912) baseStart_3971912 baseEnd_3971912 := by
    simpa [prefixWord, tailWord_3971912, baseEnd_3971912] using wordTrace_append hprefix tailTrace_3971912
  have hstable : (prefixWord ++ tailWord_3971912).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3971912).length < 2 ^ (prefixWord ++ tailWord_3971912).sum := by decide
  have hdescent : baseEnd_3971912 < baseStart_3971912 := by decide
  rcases family_descends (prefixWord ++ tailWord_3971912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3971922 : List Nat := [3, 2, 2, 1, 1, 2, 1, 1, 2, 4, 4]
def baseStart_3971922 : Nat := 118140960795 + 3971922 * 2 ^ 59
def prefixEnd_3971922 : Nat := 4983230072969 + 3 ^ 40 * 3971922 * 2
def baseEnd_3971922 : Nat := 2039505108167514070608469

theorem tailTrace_3971922 : CollatzResearch.WordTrace tailWord_3971922 prefixEnd_3971922 2039505108167514070608469 := by
  unfold tailWord_3971922
  simp only [CollatzResearch.WordTrace]
  refine ⟨36216974179103104779121505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 96578597810941612744324013 36216974179103104779121505)
  ·
    refine ⟨27162730634327328584341129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36216974179103104779121505 27162730634327328584341129)
    ·
      refine ⟨20372047975745496438255847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27162730634327328584341129 20372047975745496438255847)
      ·
        refine ⟨30558071963618244657383771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20372047975745496438255847 30558071963618244657383771)
        ·
          refine ⟨45837107945427366986075657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30558071963618244657383771 45837107945427366986075657)
          ·
            refine ⟨34377830959070525239556743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45837107945427366986075657 34377830959070525239556743)
            ·
              refine ⟨51566746438605787859335115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34377830959070525239556743 51566746438605787859335115)
              ·
                refine ⟨77350119657908681789002673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51566746438605787859335115 77350119657908681789002673)
                ·
                  refine ⟨58012589743431511341752005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 77350119657908681789002673 58012589743431511341752005)
                  ·
                    refine ⟨10877360576893408376578501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 58012589743431511341752005 10877360576893408376578501)
                    ·
                      refine ⟨2039505108167514070608469, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10877360576893408376578501 2039505108167514070608469)
                      ·
                        rfl

theorem cell23_3971922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 1, 1, 2, 4, 4].length) (baseStart_3971922 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3971922 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3971922 prefixEnd_3971922 := by exact prefixLift 3971922
  have htrace : WordTrace (prefixWord ++ tailWord_3971922) baseStart_3971922 baseEnd_3971922 := by
    simpa [prefixWord, tailWord_3971922, baseEnd_3971922] using wordTrace_append hprefix tailTrace_3971922
  have hstable : (prefixWord ++ tailWord_3971922).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3971922).length < 2 ^ (prefixWord ++ tailWord_3971922).sum := by decide
  have hdescent : baseEnd_3971922 < baseStart_3971922 := by decide
  rcases family_descends (prefixWord ++ tailWord_3971922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3971953 : List Nat := [1, 2, 2, 2, 1, 5, 3, 2, 1, 4]
def baseStart_3971953 : Nat := 118140960795 + 3971953 * 2 ^ 59
def prefixEnd_3971953 : Nat := 4983230072969 + 3 ^ 40 * 3971953 * 2
def baseEnd_3971953 : Nat := 679840342022601149773609

theorem tailTrace_3971953 : CollatzResearch.WordTrace tailWord_3971953 prefixEnd_3971953 679840342022601149773609 := by
  unfold tailWord_3971953
  simp only [CollatzResearch.WordTrace]
  refine ⟨144869027379300111410864513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96579351586200074273909675 144869027379300111410864513)
  ·
    refine ⟨108651770534475083558148385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 144869027379300111410864513 108651770534475083558148385)
    ·
      refine ⟨81488827900856312668611289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 108651770534475083558148385 81488827900856312668611289)
      ·
        refine ⟨61116620925642234501458467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81488827900856312668611289 61116620925642234501458467)
        ·
          refine ⟨91674931388463351752187701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61116620925642234501458467 91674931388463351752187701)
          ·
            refine ⟨8594524817668439226767597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 91674931388463351752187701 8594524817668439226767597)
            ·
              refine ⟨3222946806625664710037849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8594524817668439226767597 3222946806625664710037849)
              ·
                refine ⟨2417210104969248532528387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3222946806625664710037849 2417210104969248532528387)
                ·
                  refine ⟨3625815157453872798792581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2417210104969248532528387 3625815157453872798792581)
                  ·
                    refine ⟨679840342022601149773609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3625815157453872798792581 679840342022601149773609)
                    ·
                      rfl

theorem cell23_3971953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 5, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 5, 3, 2, 1, 4].length) (baseStart_3971953 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3971953 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3971953 prefixEnd_3971953 := by exact prefixLift 3971953
  have htrace : WordTrace (prefixWord ++ tailWord_3971953) baseStart_3971953 baseEnd_3971953 := by
    simpa [prefixWord, tailWord_3971953, baseEnd_3971953] using wordTrace_append hprefix tailTrace_3971953
  have hstable : (prefixWord ++ tailWord_3971953).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3971953).length < 2 ^ (prefixWord ++ tailWord_3971953).sum := by decide
  have hdescent : baseEnd_3971953 < baseStart_3971953 := by decide
  rcases family_descends (prefixWord ++ tailWord_3971953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3971962 : List Nat := [3, 1, 1, 1, 1, 1, 3, 4, 3, 5]
def baseStart_3971962 : Nat := 118140960795 + 3971962 * 2 ^ 59
def prefixEnd_3971962 : Nat := 4983230072969 + 3 ^ 40 * 3971962 * 2
def baseEnd_3971962 : Nat := 679841882464564638036095

theorem tailTrace_3971962 : CollatzResearch.WordTrace tailWord_3971962 prefixEnd_3971962 679841882464564638036095 := by
  unfold tailWord_3971962
  simp only [CollatzResearch.WordTrace]
  refine ⟨36217338909066876486985535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 96579570424178337298628093 36217338909066876486985535)
  ·
    refine ⟨54326008363600314730478303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36217338909066876486985535 54326008363600314730478303)
    ·
      refine ⟨81489012545400472095717455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54326008363600314730478303 81489012545400472095717455)
      ·
        refine ⟨122233518818100708143576183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81489012545400472095717455 122233518818100708143576183)
        ·
          refine ⟨183350278227151062215364275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 122233518818100708143576183 183350278227151062215364275)
          ·
            refine ⟨275025417340726593323046413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 183350278227151062215364275 275025417340726593323046413)
            ·
              refine ⟨103134531502772472496142405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 275025417340726593323046413 103134531502772472496142405)
              ·
                refine ⟨19337724656769838593026701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 103134531502772472496142405 19337724656769838593026701)
                ·
                  refine ⟨7251646746288689472385013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19337724656769838593026701 7251646746288689472385013)
                  ·
                    refine ⟨679841882464564638036095, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7251646746288689472385013 679841882464564638036095)
                    ·
                      rfl

theorem cell23_3971962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 3, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 3, 4, 3, 5].length) (baseStart_3971962 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3971962 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3971962 prefixEnd_3971962 := by exact prefixLift 3971962
  have htrace : WordTrace (prefixWord ++ tailWord_3971962) baseStart_3971962 baseEnd_3971962 := by
    simpa [prefixWord, tailWord_3971962, baseEnd_3971962] using wordTrace_append hprefix tailTrace_3971962
  have hstable : (prefixWord ++ tailWord_3971962).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3971962).length < 2 ^ (prefixWord ++ tailWord_3971962).sum := by decide
  have hdescent : baseEnd_3971962 < baseStart_3971962 := by decide
  rcases family_descends (prefixWord ++ tailWord_3971962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3971979 : List Nat := [1, 1, 1, 1, 4, 2, 5, 2, 1, 5]
def baseStart_3971979 : Nat := 118140960795 + 3971979 * 2 ^ 59
def prefixEnd_3971979 : Nat := 4983230072969 + 3 ^ 40 * 3971979 * 2
def baseEnd_3971979 : Nat := 679844792188273449198569

theorem tailTrace_3971979 : CollatzResearch.WordTrace tailWord_3971979 prefixEnd_3971979 679844792188273449198569 := by
  unfold tailWord_3971979
  simp only [CollatzResearch.WordTrace]
  refine ⟨144869975677205917851310991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96579983784803945234207327 144869975677205917851310991)
  ·
    refine ⟨217304963515808876776966487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144869975677205917851310991 217304963515808876776966487)
    ·
      refine ⟨325957445273713315165449731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 217304963515808876776966487 325957445273713315165449731)
      ·
        refine ⟨488936167910569972748174597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 325957445273713315165449731 488936167910569972748174597)
        ·
          refine ⟨91675531483231869890282737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 488936167910569972748174597 91675531483231869890282737)
          ·
            refine ⟨68756648612423902417712053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 91675531483231869890282737 68756648612423902417712053)
            ·
              refine ⟨6445935807414740851660505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 68756648612423902417712053 6445935807414740851660505)
              ·
                refine ⟨4834451855561055638745379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6445935807414740851660505 4834451855561055638745379)
                ·
                  refine ⟨7251677783341583458118069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4834451855561055638745379 7251677783341583458118069)
                  ·
                    refine ⟨679844792188273449198569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7251677783341583458118069 679844792188273449198569)
                    ·
                      rfl

theorem cell23_3971979_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 5, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 5, 2, 1, 5].length) (baseStart_3971979 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3971979 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3971979 prefixEnd_3971979 := by exact prefixLift 3971979
  have htrace : WordTrace (prefixWord ++ tailWord_3971979) baseStart_3971979 baseEnd_3971979 := by
    simpa [prefixWord, tailWord_3971979, baseEnd_3971979] using wordTrace_append hprefix tailTrace_3971979
  have hstable : (prefixWord ++ tailWord_3971979).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3971979).length < 2 ^ (prefixWord ++ tailWord_3971979).sum := by decide
  have hdescent : baseEnd_3971979 < baseStart_3971979 := by decide
  rcases family_descends (prefixWord ++ tailWord_3971979) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3972049 : List Nat := [1, 2, 2, 1, 2, 1, 3, 4, 1, 3, 3]
def baseStart_3972049 : Nat := 118140960795 + 3972049 * 2 ^ 59
def prefixEnd_3972049 : Nat := 4983230072969 + 3 ^ 40 * 3972049 * 2
def baseEnd_3972049 : Nat := 2039570320210635073720385

theorem tailTrace_3972049 : CollatzResearch.WordTrace tailWord_3972049 prefixEnd_3972049 2039570320210635073720385 := by
  unfold tailWord_3972049
  simp only [CollatzResearch.WordTrace]
  refine ⟨144872528786952319806359201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96581685857968213204239467 144872528786952319806359201)
  ·
    refine ⟨108654396590214239854769401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 144872528786952319806359201 108654396590214239854769401)
    ·
      refine ⟨81490797442660679891077051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 108654396590214239854769401 81490797442660679891077051)
      ·
        refine ⟨122236196163991019836615577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81490797442660679891077051 122236196163991019836615577)
        ·
          refine ⟨91677147122993264877461683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 122236196163991019836615577 91677147122993264877461683)
          ·
            refine ⟨137515720684489897316192525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91677147122993264877461683 137515720684489897316192525)
            ·
              refine ⟨51568395256683711493572197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 137515720684489897316192525 51568395256683711493572197)
              ·
                refine ⟨9669074110628195905044787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 51568395256683711493572197 9669074110628195905044787)
                ·
                  refine ⟨14503611165942293857567181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9669074110628195905044787 14503611165942293857567181)
                  ·
                    refine ⟨5438854187228360196587693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14503611165942293857567181 5438854187228360196587693)
                    ·
                      refine ⟨2039570320210635073720385, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5438854187228360196587693 2039570320210635073720385)
                      ·
                        rfl

theorem cell23_3972049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 3, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 3, 4, 1, 3, 3].length) (baseStart_3972049 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3972049 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3972049 prefixEnd_3972049 := by exact prefixLift 3972049
  have htrace : WordTrace (prefixWord ++ tailWord_3972049) baseStart_3972049 baseEnd_3972049 := by
    simpa [prefixWord, tailWord_3972049, baseEnd_3972049] using wordTrace_append hprefix tailTrace_3972049
  have hstable : (prefixWord ++ tailWord_3972049).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3972049).length < 2 ^ (prefixWord ++ tailWord_3972049).sum := by decide
  have hdescent : baseEnd_3972049 < baseStart_3972049 := by decide
  rcases family_descends (prefixWord ++ tailWord_3972049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3972050 : List Nat := [3, 2, 2, 3, 1, 3, 2, 1, 1, 1, 4]
def baseStart_3972050 : Nat := 118140960795 + 3972050 * 2 ^ 59
def prefixEnd_3972050 : Nat := 4983230072969 + 3 ^ 40 * 3972050 * 2
def baseEnd_3972050 : Nat := 2039570833691289569807881

theorem tailTrace_3972050 : CollatzResearch.WordTrace tailWord_3972050 prefixEnd_3972050 2039570833691289569807881 := by
  unfold tailWord_3972050
  simp only [CollatzResearch.WordTrace]
  refine ⟨36218141314987174244286401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 96581710173299131318097069 36218141314987174244286401)
  ·
    refine ⟨27163605986240380683214801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36218141314987174244286401 27163605986240380683214801)
    ·
      refine ⟨20372704489680285512411101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27163605986240380683214801 20372704489680285512411101)
      ·
        refine ⟨7639764183630107067154163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20372704489680285512411101 7639764183630107067154163)
        ·
          refine ⟨11459646275445160600731245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7639764183630107067154163 11459646275445160600731245)
          ·
            refine ⟨4297367353291935225274217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11459646275445160600731245 4297367353291935225274217)
            ·
              refine ⟨3223025514968951418955663, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4297367353291935225274217 3223025514968951418955663)
              ·
                refine ⟨4834538272453427128433495, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3223025514968951418955663 4834538272453427128433495)
                ·
                  refine ⟨7251807408680140692650243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4834538272453427128433495 7251807408680140692650243)
                  ·
                    refine ⟨10877711113020211038975365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7251807408680140692650243 10877711113020211038975365)
                    ·
                      refine ⟨2039570833691289569807881, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10877711113020211038975365 2039570833691289569807881)
                      ·
                        rfl

theorem cell23_3972050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 3, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 3, 2, 1, 1, 1, 4].length) (baseStart_3972050 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3972050 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3972050 prefixEnd_3972050 := by exact prefixLift 3972050
  have htrace : WordTrace (prefixWord ++ tailWord_3972050) baseStart_3972050 baseEnd_3972050 := by
    simpa [prefixWord, tailWord_3972050, baseEnd_3972050] using wordTrace_append hprefix tailTrace_3972050
  have hstable : (prefixWord ++ tailWord_3972050).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3972050).length < 2 ^ (prefixWord ++ tailWord_3972050).sum := by decide
  have hdescent : baseEnd_3972050 < baseStart_3972050 := by decide
  rcases family_descends (prefixWord ++ tailWord_3972050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3972053 : List Nat := [1, 3, 2, 3, 3, 1, 1, 3, 1, 2, 3]
def baseStart_3972053 : Nat := 118140960795 + 3972053 * 2 ^ 59
def prefixEnd_3972053 : Nat := 4983230072969 + 3 ^ 40 * 3972053 * 2
def baseEnd_3972053 : Nat := 2039572374133253058070367

theorem tailTrace_3972053 : CollatzResearch.WordTrace tailWord_3972053 prefixEnd_3972053 2039572374133253058070367 := by
  unfold tailWord_3972053
  simp only [CollatzResearch.WordTrace]
  refine ⟨144872674678937828489504813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96581783119291885659669875 144872674678937828489504813)
  ·
    refine ⟨54327253004601685683564305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 144872674678937828489504813 54327253004601685683564305)
    ·
      refine ⟨40745439753451264262673229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54327253004601685683564305 40745439753451264262673229)
      ·
        refine ⟨15279539907544224098502461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40745439753451264262673229 15279539907544224098502461)
        ·
          refine ⟨5729827465329084036938423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15279539907544224098502461 5729827465329084036938423)
          ·
            refine ⟨8594741197993626055407635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5729827465329084036938423 8594741197993626055407635)
            ·
              refine ⟨12892111796990439083111453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8594741197993626055407635 12892111796990439083111453)
              ·
                refine ⟨4834541923871414656166795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12892111796990439083111453 4834541923871414656166795)
                ·
                  refine ⟨7251812885807121984250193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4834541923871414656166795 7251812885807121984250193)
                  ·
                    refine ⟨5438859664355341488187645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7251812885807121984250193 5438859664355341488187645)
                    ·
                      refine ⟨2039572374133253058070367, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5438859664355341488187645 2039572374133253058070367)
                      ·
                        rfl

theorem cell23_3972053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 3, 1, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 3, 1, 1, 3, 1, 2, 3].length) (baseStart_3972053 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3972053 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3972053 prefixEnd_3972053 := by exact prefixLift 3972053
  have htrace : WordTrace (prefixWord ++ tailWord_3972053) baseStart_3972053 baseEnd_3972053 := by
    simpa [prefixWord, tailWord_3972053, baseEnd_3972053] using wordTrace_append hprefix tailTrace_3972053
  have hstable : (prefixWord ++ tailWord_3972053).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3972053).length < 2 ^ (prefixWord ++ tailWord_3972053).sum := by decide
  have hdescent : baseEnd_3972053 < baseStart_3972053 := by decide
  rcases family_descends (prefixWord ++ tailWord_3972053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3972084 : List Nat := [2, 6, 2, 1, 1, 1, 2, 2, 1, 1, 4]
def baseStart_3972084 : Nat := 118140960795 + 3972084 * 2 ^ 59
def prefixEnd_3972084 : Nat := 4983230072969 + 3 ^ 40 * 3972084 * 2
def baseEnd_3972084 : Nat := 2039588292033542436782725

theorem tailTrace_3972084 : CollatzResearch.WordTrace tailWord_3972084 prefixEnd_3972084 2039588292033542436782725 := by
  unfold tailWord_3972084
  simp only [CollatzResearch.WordTrace]
  refine ⟨72436902670912760391941653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96582536894550347189255537 72436902670912760391941653)
  ·
    refine ⟨3395479812699035643372265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 72436902670912760391941653 3395479812699035643372265)
    ·
      refine ⟨2546609859524276732529199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3395479812699035643372265 2546609859524276732529199)
      ·
        refine ⟨3819914789286415098793799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2546609859524276732529199 3819914789286415098793799)
        ·
          refine ⟨5729872183929622648190699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3819914789286415098793799 5729872183929622648190699)
          ·
            refine ⟨8594808275894433972286049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5729872183929622648190699 8594808275894433972286049)
            ·
              refine ⟨6446106206920825479214537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8594808275894433972286049 6446106206920825479214537)
              ·
                refine ⟨4834579655190619109410903, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6446106206920825479214537 4834579655190619109410903)
                ·
                  refine ⟨7251869482785928664116355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4834579655190619109410903 7251869482785928664116355)
                  ·
                    refine ⟨10877804224178892996174533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7251869482785928664116355 10877804224178892996174533)
                    ·
                      refine ⟨2039588292033542436782725, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10877804224178892996174533 2039588292033542436782725)
                      ·
                        rfl

theorem cell23_3972084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 1, 1, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 1, 1, 2, 2, 1, 1, 4].length) (baseStart_3972084 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3972084 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3972084 prefixEnd_3972084 := by exact prefixLift 3972084
  have htrace : WordTrace (prefixWord ++ tailWord_3972084) baseStart_3972084 baseEnd_3972084 := by
    simpa [prefixWord, tailWord_3972084, baseEnd_3972084] using wordTrace_append hprefix tailTrace_3972084
  have hstable : (prefixWord ++ tailWord_3972084).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3972084).length < 2 ^ (prefixWord ++ tailWord_3972084).sum := by decide
  have hdescent : baseEnd_3972084 < baseStart_3972084 := by decide
  rcases family_descends (prefixWord ++ tailWord_3972084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3972139 : List Nat := [1, 1, 1, 1, 2, 1, 6, 1, 1, 5, 3]
def baseStart_3972139 : Nat := 118140960795 + 3972139 * 2 ^ 59
def prefixEnd_3972139 : Nat := 4983230072969 + 3 ^ 40 * 3972139 * 2
def baseEnd_3972139 : Nat := 2039616533469539721594971

theorem tailTrace_3972139 : CollatzResearch.WordTrace tailWord_3972139 prefixEnd_3972139 2039616533469539721594971 := by
  unfold tailWord_3972139
  simp only [CollatzResearch.WordTrace]
  refine ⟨144875811356626265177135471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96583874237750843451423647 144875811356626265177135471)
  ·
    refine ⟨217313717034939397765703207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144875811356626265177135471 217313717034939397765703207)
    ·
      refine ⟨325970575552409096648554811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 217313717034939397765703207 325970575552409096648554811)
      ·
        refine ⟨488955863328613644972832217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 325970575552409096648554811 488955863328613644972832217)
        ·
          refine ⟨366716897496460233729624163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 488955863328613644972832217 366716897496460233729624163)
          ·
            refine ⟨550075346244690350594436245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 366716897496460233729624163 550075346244690350594436245)
            ·
              refine ⟨25784781855219860184114199, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 550075346244690350594436245 25784781855219860184114199)
              ·
                refine ⟨38677172782829790276171299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25784781855219860184114199 38677172782829790276171299)
                ·
                  refine ⟨58015759174244685414256949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38677172782829790276171299 58015759174244685414256949)
                  ·
                    refine ⟨5438977422585439257586589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 58015759174244685414256949 5438977422585439257586589)
                    ·
                      refine ⟨2039616533469539721594971, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5438977422585439257586589 2039616533469539721594971)
                      ·
                        rfl

theorem cell23_3972139_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 6, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 6, 1, 1, 5, 3].length) (baseStart_3972139 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3972139 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3972139 prefixEnd_3972139 := by exact prefixLift 3972139
  have htrace : WordTrace (prefixWord ++ tailWord_3972139) baseStart_3972139 baseEnd_3972139 := by
    simpa [prefixWord, tailWord_3972139, baseEnd_3972139] using wordTrace_append hprefix tailTrace_3972139
  have hstable : (prefixWord ++ tailWord_3972139).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3972139).length < 2 ^ (prefixWord ++ tailWord_3972139).sum := by decide
  have hdescent : baseEnd_3972139 < baseStart_3972139 := by decide
  rcases family_descends (prefixWord ++ tailWord_3972139) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3972190 : List Nat := [4, 4, 1, 1, 1, 1, 1, 1, 1, 5, 3]
def baseStart_3972190 : Nat := 118140960795 + 3972190 * 2 ^ 59
def prefixEnd_3972190 : Nat := 4983230072969 + 3 ^ 40 * 3972190 * 2
def baseEnd_3972190 : Nat := 2039642720982919022057237

theorem tailTrace_3972190 : CollatzResearch.WordTrace tailWord_3972190 prefixEnd_3972190 2039642720982919022057237 := by
  unfold tailWord_3972190
  simp only [CollatzResearch.WordTrace]
  refine ⟨18109708934930187610905253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 96585114319627667258161349 18109708934930187610905253)
  ·
    refine ⟨3395570425299410177044735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 18109708934930187610905253 3395570425299410177044735)
    ·
      refine ⟨5093355637949115265567103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3395570425299410177044735 5093355637949115265567103)
      ·
        refine ⟨7640033456923672898350655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5093355637949115265567103 7640033456923672898350655)
        ·
          refine ⟨11460050185385509347525983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7640033456923672898350655 11460050185385509347525983)
          ·
            refine ⟨17190075278078264021288975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11460050185385509347525983 17190075278078264021288975)
            ·
              refine ⟨25785112917117396031933463, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17190075278078264021288975 25785112917117396031933463)
              ·
                refine ⟨38677669375676094047900195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25785112917117396031933463 38677669375676094047900195)
                ·
                  refine ⟨58016504063514141071850293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38677669375676094047900195 58016504063514141071850293)
                  ·
                    refine ⟨5439047255954450725485965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 58016504063514141071850293 5439047255954450725485965)
                    ·
                      refine ⟨2039642720982919022057237, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5439047255954450725485965 2039642720982919022057237)
                      ·
                        rfl

theorem cell23_3972190_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 1, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 1, 1, 1, 1, 5, 3].length) (baseStart_3972190 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3972190 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3972190 prefixEnd_3972190 := by exact prefixLift 3972190
  have htrace : WordTrace (prefixWord ++ tailWord_3972190) baseStart_3972190 baseEnd_3972190 := by
    simpa [prefixWord, tailWord_3972190, baseEnd_3972190] using wordTrace_append hprefix tailTrace_3972190
  have hstable : (prefixWord ++ tailWord_3972190).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3972190).length < 2 ^ (prefixWord ++ tailWord_3972190).sum := by decide
  have hdescent : baseEnd_3972190 < baseStart_3972190 := by decide
  rcases family_descends (prefixWord ++ tailWord_3972190) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3972209 : List Nat := [1, 2, 2, 2, 1, 1, 2, 1, 1, 6, 4]
def baseStart_3972209 : Nat := 118140960795 + 3972209 * 2 ^ 59
def prefixEnd_3972209 : Nat := 4983230072969 + 3 ^ 40 * 3972209 * 2
def baseEnd_3972209 : Nat := 2039652477115354447719649

theorem tailTrace_3972209 : CollatzResearch.WordTrace tailWord_3972209 prefixEnd_3972209 2039652477115354447719649 := by
  unfold tailWord_3972209
  simp only [CollatzResearch.WordTrace]
  refine ⟨144878364466372667132183681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96585576310915111421455787 144878364466372667132183681)
  ·
    refine ⟨108658773349779500349137761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 144878364466372667132183681 108658773349779500349137761)
    ·
      refine ⟨81494080012334625261853321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 108658773349779500349137761 81494080012334625261853321)
      ·
        refine ⟨61120560009250968946389991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81494080012334625261853321 61120560009250968946389991)
        ·
          refine ⟨91680840013876453419584987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61120560009250968946389991 91680840013876453419584987)
          ·
            refine ⟨137521260020814680129377481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91680840013876453419584987 137521260020814680129377481)
            ·
              refine ⟨103140945015611010097033111, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 137521260020814680129377481 103140945015611010097033111)
              ·
                refine ⟨154711417523416515145549667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 103140945015611010097033111 154711417523416515145549667)
                ·
                  refine ⟨232067126285124772718324501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 154711417523416515145549667 232067126285124772718324501)
                  ·
                    refine ⟨10878146544615223721171461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 232067126285124772718324501 10878146544615223721171461)
                    ·
                      refine ⟨2039652477115354447719649, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10878146544615223721171461 2039652477115354447719649)
                      ·
                        rfl

theorem cell23_3972209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 2, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 2, 1, 1, 6, 4].length) (baseStart_3972209 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3972209 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3972209 prefixEnd_3972209 := by exact prefixLift 3972209
  have htrace : WordTrace (prefixWord ++ tailWord_3972209) baseStart_3972209 baseEnd_3972209 := by
    simpa [prefixWord, tailWord_3972209, baseEnd_3972209] using wordTrace_append hprefix tailTrace_3972209
  have hstable : (prefixWord ++ tailWord_3972209).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3972209).length < 2 ^ (prefixWord ++ tailWord_3972209).sum := by decide
  have hdescent : baseEnd_3972209 < baseStart_3972209 := by decide
  rcases family_descends (prefixWord ++ tailWord_3972209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3972253 : List Nat := [1, 4, 2, 1, 1, 2, 5, 1, 6]
def baseStart_3972253 : Nat := 118140960795 + 3972253 * 2 ^ 59
def prefixEnd_3972253 : Nat := 4983230072969 + 3 ^ 40 * 3972253 * 2
def baseEnd_3972253 : Nat := 226630563362683586174383

theorem tailTrace_3972253 : CollatzResearch.WordTrace tailWord_3972253 prefixEnd_3972253 226630563362683586174383 := by
  unfold tailWord_3972253
  simp only [CollatzResearch.WordTrace]
  refine ⟨144879969278213262646785413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96586646185475508431190275 144879969278213262646785413)
  ·
    refine ⟨27164994239664986746272265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 144879969278213262646785413 27164994239664986746272265)
    ·
      refine ⟨20373745679748740059704199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27164994239664986746272265 20373745679748740059704199)
      ·
        refine ⟨30560618519623110089556299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20373745679748740059704199 30560618519623110089556299)
        ·
          refine ⟨45840927779434665134334449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30560618519623110089556299 45840927779434665134334449)
          ·
            refine ⟨34380695834575998850750837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45840927779434665134334449 34380695834575998850750837)
            ·
              refine ⟨3223190234491499892257891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 34380695834575998850750837 3223190234491499892257891)
              ·
                refine ⟨4834785351737249838386837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3223190234491499892257891 4834785351737249838386837)
                ·
                  refine ⟨226630563362683586174383, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4834785351737249838386837 226630563362683586174383)
                  ·
                    rfl

theorem cell23_3972253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 5, 1, 6].length) (baseStart_3972253 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3972253 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3972253 prefixEnd_3972253 := by exact prefixLift 3972253
  have htrace : WordTrace (prefixWord ++ tailWord_3972253) baseStart_3972253 baseEnd_3972253 := by
    simpa [prefixWord, tailWord_3972253, baseEnd_3972253] using wordTrace_append hprefix tailTrace_3972253
  have hstable : (prefixWord ++ tailWord_3972253).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3972253).length < 2 ^ (prefixWord ++ tailWord_3972253).sum := by decide
  have hdescent : baseEnd_3972253 < baseStart_3972253 := by decide
  rcases family_descends (prefixWord ++ tailWord_3972253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3972259 : List Nat := [1, 1, 1, 4, 1, 1, 1, 3, 2, 1, 7]
def baseStart_3972259 : Nat := 118140960795 + 3972259 * 2 ^ 59
def prefixEnd_3972259 : Nat := 4983230072969 + 3 ^ 40 * 3972259 * 2
def baseEnd_3972259 : Nat := 2039678151148079252094419

theorem tailTrace_3972259 : CollatzResearch.WordTrace tailWord_3972259 prefixEnd_3972259 2039678151148079252094419 := by
  unfold tailWord_3972259
  simp only [CollatzResearch.WordTrace]
  refine ⟨144880188116191525671503831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96586792077461017114335887 144880188116191525671503831)
  ·
    refine ⟨217320282174287288507255747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144880188116191525671503831 217320282174287288507255747)
    ·
      refine ⟨325980423261430932760883621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 217320282174287288507255747 325980423261430932760883621)
      ·
        refine ⟨61121329361518299892665679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 325980423261430932760883621 61121329361518299892665679)
        ·
          refine ⟨91681994042277449838998519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61121329361518299892665679 91681994042277449838998519)
          ·
            refine ⟨137522991063416174758497779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91681994042277449838998519 137522991063416174758497779)
            ·
              refine ⟨206284486595124262137746669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 137522991063416174758497779 206284486595124262137746669)
              ·
                refine ⟨77356682473171598301655001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 206284486595124262137746669 77356682473171598301655001)
                ·
                  refine ⟨58017511854878698726241251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 77356682473171598301655001 58017511854878698726241251)
                  ·
                    refine ⟨87026267782318048089361877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 58017511854878698726241251 87026267782318048089361877)
                    ·
                      refine ⟨2039678151148079252094419, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 87026267782318048089361877 2039678151148079252094419)
                      ·
                        rfl

theorem cell23_3972259_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 1, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 1, 3, 2, 1, 7].length) (baseStart_3972259 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3972259 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3972259 prefixEnd_3972259 := by exact prefixLift 3972259
  have htrace : WordTrace (prefixWord ++ tailWord_3972259) baseStart_3972259 baseEnd_3972259 := by
    simpa [prefixWord, tailWord_3972259, baseEnd_3972259] using wordTrace_append hprefix tailTrace_3972259
  have hstable : (prefixWord ++ tailWord_3972259).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3972259).length < 2 ^ (prefixWord ++ tailWord_3972259).sum := by decide
  have hdescent : baseEnd_3972259 < baseStart_3972259 := by decide
  rcases family_descends (prefixWord ++ tailWord_3972259) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3972280 : List Nat := [2, 1, 2, 1, 2, 1, 2, 7, 1, 1, 3]
def baseStart_3972280 : Nat := 118140960795 + 3972280 * 2 ^ 59
def prefixEnd_3972280 : Nat := 4983230072969 + 3 ^ 40 * 3972280 * 2
def baseEnd_3972280 : Nat := 2039688934241823669931823

theorem tailTrace_3972280 : CollatzResearch.WordTrace tailWord_3972280 prefixEnd_3972280 2039688934241823669931823 := by
  unfold tailWord_3972280
  simp only [CollatzResearch.WordTrace]
  refine ⟨72440477024557723129009147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96587302699410297505345529 72440477024557723129009147)
  ·
    refine ⟨108660715536836584693513721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72440477024557723129009147 108660715536836584693513721)
    ·
      refine ⟨81495536652627438520135291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 108660715536836584693513721 81495536652627438520135291)
      ·
        refine ⟨122243304978941157780202937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81495536652627438520135291 122243304978941157780202937)
        ·
          refine ⟨91682478734205868335152203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 122243304978941157780202937 91682478734205868335152203)
          ·
            refine ⟨137523718101308802502728305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91682478734205868335152203 137523718101308802502728305)
            ·
              refine ⟨103142788575981601877046229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 137523718101308802502728305 103142788575981601877046229)
              ·
                refine ⟨2417409107249568793993271, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 103142788575981601877046229 2417409107249568793993271)
                ·
                  refine ⟨3626113660874353190989907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2417409107249568793993271 3626113660874353190989907)
                  ·
                    refine ⟨5439170491311529786484861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3626113660874353190989907 5439170491311529786484861)
                    ·
                      refine ⟨2039688934241823669931823, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5439170491311529786484861 2039688934241823669931823)
                      ·
                        rfl

theorem cell23_3972280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 2, 7, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 2, 7, 1, 1, 3].length) (baseStart_3972280 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3972280 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3972280 prefixEnd_3972280 := by exact prefixLift 3972280
  have htrace : WordTrace (prefixWord ++ tailWord_3972280) baseStart_3972280 baseEnd_3972280 := by
    simpa [prefixWord, tailWord_3972280, baseEnd_3972280] using wordTrace_append hprefix tailTrace_3972280
  have hstable : (prefixWord ++ tailWord_3972280).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3972280).length < 2 ^ (prefixWord ++ tailWord_3972280).sum := by decide
  have hdescent : baseEnd_3972280 < baseStart_3972280 := by decide
  rcases family_descends (prefixWord ++ tailWord_3972280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3972317 : List Nat := [1, 4, 3, 2, 2, 2, 1, 2, 1, 5]
def baseStart_3972317 : Nat := 118140960795 + 3972317 * 2 ^ 59
def prefixEnd_3972317 : Nat := 4983230072969 + 3 ^ 40 * 3972317 * 2
def baseEnd_3972317 : Nat := 679902644342013341723051

theorem tailTrace_3972317 : CollatzResearch.WordTrace tailWord_3972317 prefixEnd_3972317 679902644342013341723051 := by
  unfold tailWord_3972317
  simp only [CollatzResearch.WordTrace]
  refine ⟨144882303549981401577115205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96588202366654267718076803 144882303549981401577115205)
  ·
    refine ⟨27165431915621512795709101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 144882303549981401577115205 27165431915621512795709101)
    ·
      refine ⟨10187036968358067298390913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27165431915621512795709101 10187036968358067298390913)
      ·
        refine ⟨7640277726268550473793185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10187036968358067298390913 7640277726268550473793185)
        ·
          refine ⟨5730208294701412855344889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7640277726268550473793185 5730208294701412855344889)
          ·
            refine ⟨4297656221026059641508667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5730208294701412855344889 4297656221026059641508667)
            ·
              refine ⟨6446484331539089462263001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4297656221026059641508667 6446484331539089462263001)
              ·
                refine ⟨4834863248654317096697251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6446484331539089462263001 4834863248654317096697251)
                ·
                  refine ⟨7252294872981475645045877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4834863248654317096697251 7252294872981475645045877)
                  ·
                    refine ⟨679902644342013341723051, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7252294872981475645045877 679902644342013341723051)
                    ·
                      rfl

theorem cell23_3972317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 2, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 2, 2, 1, 2, 1, 5].length) (baseStart_3972317 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3972317 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3972317 prefixEnd_3972317 := by exact prefixLift 3972317
  have htrace : WordTrace (prefixWord ++ tailWord_3972317) baseStart_3972317 baseEnd_3972317 := by
    simpa [prefixWord, tailWord_3972317, baseEnd_3972317] using wordTrace_append hprefix tailTrace_3972317
  have hstable : (prefixWord ++ tailWord_3972317).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3972317).length < 2 ^ (prefixWord ++ tailWord_3972317).sum := by decide
  have hdescent : baseEnd_3972317 < baseStart_3972317 := by decide
  rcases family_descends (prefixWord ++ tailWord_3972317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3972320 : List Nat := [2, 1, 1, 3, 1, 6, 1, 2, 1, 1, 4]
def baseStart_3972320 : Nat := 118140960795 + 3972320 * 2 ^ 59
def prefixEnd_3972320 : Nat := 4983230072969 + 3 ^ 40 * 3972320 * 2
def baseEnd_3972320 : Nat := 2039709473468003513431639

theorem tailTrace_3972320 : CollatzResearch.WordTrace tailWord_3972320 prefixEnd_3972320 2039709473468003513431639 := by
  unfold tailWord_3972320
  simp only [CollatzResearch.WordTrace]
  refine ⟨72441206484485266544737207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96588275312647022059649609 72441206484485266544737207)
  ·
    refine ⟨108661809726727899817105811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72441206484485266544737207 108661809726727899817105811)
    ·
      refine ⟨162992714590091849725658717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108661809726727899817105811 162992714590091849725658717)
      ·
        refine ⟨61122267971284443647122019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 162992714590091849725658717 61122267971284443647122019)
        ·
          refine ⟨91683401956926665470683029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61122267971284443647122019 91683401956926665470683029)
          ·
            refine ⟨4297659466730937443938267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 91683401956926665470683029 4297659466730937443938267)
            ·
              refine ⟨6446489200096406165907401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4297659466730937443938267 6446489200096406165907401)
              ·
                refine ⟨4834866900072304624430551, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6446489200096406165907401 4834866900072304624430551)
                ·
                  refine ⟨7252300350108456936645827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4834866900072304624430551 7252300350108456936645827)
                  ·
                    refine ⟨10878450525162685404968741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7252300350108456936645827 10878450525162685404968741)
                    ·
                      refine ⟨2039709473468003513431639, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10878450525162685404968741 2039709473468003513431639)
                      ·
                        rfl

theorem cell23_3972320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 6, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 6, 1, 2, 1, 1, 4].length) (baseStart_3972320 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3972320 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3972320 prefixEnd_3972320 := by exact prefixLift 3972320
  have htrace : WordTrace (prefixWord ++ tailWord_3972320) baseStart_3972320 baseEnd_3972320 := by
    simpa [prefixWord, tailWord_3972320, baseEnd_3972320] using wordTrace_append hprefix tailTrace_3972320
  have hstable : (prefixWord ++ tailWord_3972320).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3972320).length < 2 ^ (prefixWord ++ tailWord_3972320).sum := by decide
  have hdescent : baseEnd_3972320 < baseStart_3972320 := by decide
  rcases family_descends (prefixWord ++ tailWord_3972320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3972333 : List Nat := [1, 5, 1, 2, 2, 1, 1, 1, 3, 2, 4]
def baseStart_3972333 : Nat := 118140960795 + 3972333 * 2 ^ 59
def prefixEnd_3972333 : Nat := 4983230072969 + 3 ^ 40 * 3972333 * 2
def baseEnd_3972333 : Nat := 2039716148716511962569079

theorem tailTrace_3972333 : CollatzResearch.WordTrace tailWord_3972333 prefixEnd_3972333 2039716148716511962569079 := by
  unfold tailWord_3972333
  simp only [CollatzResearch.WordTrace]
  refine ⟨144882887117923436309697653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96588591411948957539798435 144882887117923436309697653)
  ·
    refine ⟨13582770667305322154034155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 144882887117923436309697653 13582770667305322154034155)
    ·
      refine ⟨20374156000957983231051233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13582770667305322154034155 20374156000957983231051233)
      ·
        refine ⟨15280617000718487423288425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20374156000957983231051233 15280617000718487423288425)
        ·
          refine ⟨11460462750538865567466319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15280617000718487423288425 11460462750538865567466319)
          ·
            refine ⟨17190694125808298351199479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11460462750538865567466319 17190694125808298351199479)
            ·
              refine ⟨25786041188712447526799219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17190694125808298351199479 25786041188712447526799219)
              ·
                refine ⟨38679061783068671290198829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25786041188712447526799219 38679061783068671290198829)
                ·
                  refine ⟨14504648168650751733824561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38679061783068671290198829 14504648168650751733824561)
                  ·
                    refine ⟨10878486126488063800368421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14504648168650751733824561 10878486126488063800368421)
                    ·
                      refine ⟨2039716148716511962569079, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10878486126488063800368421 2039716148716511962569079)
                      ·
                        rfl

theorem cell23_3972333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 1, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 1, 1, 1, 3, 2, 4].length) (baseStart_3972333 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3972333 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3972333 prefixEnd_3972333 := by exact prefixLift 3972333
  have htrace : WordTrace (prefixWord ++ tailWord_3972333) baseStart_3972333 baseEnd_3972333 := by
    simpa [prefixWord, tailWord_3972333, baseEnd_3972333] using wordTrace_append hprefix tailTrace_3972333
  have hstable : (prefixWord ++ tailWord_3972333).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3972333).length < 2 ^ (prefixWord ++ tailWord_3972333).sum := by decide
  have hdescent : baseEnd_3972333 < baseStart_3972333 := by decide
  rcases family_descends (prefixWord ++ tailWord_3972333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3972337 : List Nat := [1, 2, 2, 2, 2, 1, 1, 7, 1, 2, 2]
def baseStart_3972337 : Nat := 118140960795 + 3972337 * 2 ^ 59
def prefixEnd_3972337 : Nat := 4983230072969 + 3 ^ 40 * 3972337 * 2
def baseEnd_3972337 : Nat := 2039718202639129946919061

theorem tailTrace_3972337 : CollatzResearch.WordTrace tailWord_3972337 prefixEnd_3972337 2039718202639129946919061 := by
  unfold tailWord_3972337
  simp only [CollatzResearch.WordTrace]
  refine ⟨144883033009908944992843265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96588688673272629995228843 144883033009908944992843265)
  ·
    refine ⟨108662274757431708744632449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 144883033009908944992843265 108662274757431708744632449)
    ·
      refine ⟨81496706068073781558474337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 108662274757431708744632449 81496706068073781558474337)
      ·
        refine ⟨61122529551055336168855753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81496706068073781558474337 61122529551055336168855753)
        ·
          refine ⟨45841897163291502126641815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61122529551055336168855753 45841897163291502126641815)
          ·
            refine ⟨68762845744937253189962723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45841897163291502126641815 68762845744937253189962723)
            ·
              refine ⟨103144268617405879784944085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68762845744937253189962723 103144268617405879784944085)
              ·
                refine ⟨2417443795720450307459627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 103144268617405879784944085 2417443795720450307459627)
                ·
                  refine ⟨3626165693580675461189441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2417443795720450307459627 3626165693580675461189441)
                  ·
                    refine ⟨2719624270185506595892081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3626165693580675461189441 2719624270185506595892081)
                    ·
                      refine ⟨2039718202639129946919061, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2719624270185506595892081 2039718202639129946919061)
                      ·
                        rfl

theorem cell23_3972337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 1, 7, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 1, 7, 1, 2, 2].length) (baseStart_3972337 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3972337 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3972337 prefixEnd_3972337 := by exact prefixLift 3972337
  have htrace : WordTrace (prefixWord ++ tailWord_3972337) baseStart_3972337 baseEnd_3972337 := by
    simpa [prefixWord, tailWord_3972337, baseEnd_3972337] using wordTrace_append hprefix tailTrace_3972337
  have hstable : (prefixWord ++ tailWord_3972337).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3972337).length < 2 ^ (prefixWord ++ tailWord_3972337).sum := by decide
  have hdescent : baseEnd_3972337 < baseStart_3972337 := by decide
  rcases family_descends (prefixWord ++ tailWord_3972337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3972360 : List Nat := [2, 1, 3, 2, 5, 1, 1, 8]
def baseStart_3972360 : Nat := 118140960795 + 3972360 * 2 ^ 59
def prefixEnd_3972360 : Nat := 4983230072969 + 3 ^ 40 * 3972360 * 2
def baseEnd_3972360 : Nat := 75545556025710494701165

theorem tailTrace_3972360 : CollatzResearch.WordTrace tailWord_3972360 prefixEnd_3972360 75545556025710494701165 := by
  unfold tailWord_3972360
  simp only [CollatzResearch.WordTrace]
  refine ⟨72441935944412809960465267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96589247925883746613953689 72441935944412809960465267)
  ·
    refine ⟨108662903916619214940697901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72441935944412809960465267 108662903916619214940697901)
    ·
      refine ⟨40748588968732205602761713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 108662903916619214940697901 40748588968732205602761713)
      ·
        refine ⟨30561441726549154202071285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40748588968732205602761713 30561441726549154202071285)
        ·
          refine ⟨2865135161863983206444183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 30561441726549154202071285 2865135161863983206444183)
          ·
            refine ⟨4297702742795974809666275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2865135161863983206444183 4297702742795974809666275)
            ·
              refine ⟨6446554114193962214499413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4297702742795974809666275 6446554114193962214499413)
              ·
                refine ⟨75545556025710494701165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 6446554114193962214499413 75545556025710494701165)
                ·
                  rfl

theorem cell23_3972360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 5, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 5, 1, 1, 8].length) (baseStart_3972360 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3972360 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3972360 prefixEnd_3972360 := by exact prefixLift 3972360
  have htrace : WordTrace (prefixWord ++ tailWord_3972360) baseStart_3972360 baseEnd_3972360 := by
    simpa [prefixWord, tailWord_3972360, baseEnd_3972360] using wordTrace_append hprefix tailTrace_3972360
  have hstable : (prefixWord ++ tailWord_3972360).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3972360).length < 2 ^ (prefixWord ++ tailWord_3972360).sum := by decide
  have hdescent : baseEnd_3972360 < baseStart_3972360 := by decide
  rcases family_descends (prefixWord ++ tailWord_3972360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3972380 : List Nat := [2, 2, 3, 1, 1, 1, 4, 1, 3, 3, 2]
def baseStart_3972380 : Nat := 118140960795 + 3972380 * 2 ^ 59
def prefixEnd_3972380 : Nat := 4983230072969 + 3 ^ 40 * 3972380 * 2
def baseEnd_3972380 : Nat := 2039740282307273278681363

theorem tailTrace_3972380 : CollatzResearch.WordTrace tailWord_3972380 prefixEnd_3972380 2039740282307273278681363 := by
  unfold tailWord_3972380
  simp only [CollatzResearch.WordTrace]
  refine ⟨72442300674376581668329297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96589734232502108891105729 72442300674376581668329297)
  ·
    refine ⟨54331725505782436251246973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72442300674376581668329297 54331725505782436251246973)
    ·
      refine ⟨20374397064668413594217615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 54331725505782436251246973 20374397064668413594217615)
      ·
        refine ⟨30561595597002620391326423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20374397064668413594217615 30561595597002620391326423)
        ·
          refine ⟨45842393395503930586989635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30561595597002620391326423 45842393395503930586989635)
          ·
            refine ⟨68763590093255895880484453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45842393395503930586989635 68763590093255895880484453)
            ·
              refine ⟨12893173142485480477590835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 68763590093255895880484453 12893173142485480477590835)
              ·
                refine ⟨19339759713728220716386253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12893173142485480477590835 19339759713728220716386253)
                ·
                  refine ⟨7252409892648082768644845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19339759713728220716386253 7252409892648082768644845)
                  ·
                    refine ⟨2719653709743031038241817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7252409892648082768644845 2719653709743031038241817)
                    ·
                      refine ⟨2039740282307273278681363, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2719653709743031038241817 2039740282307273278681363)
                      ·
                        rfl

theorem cell23_3972380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 4, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 4, 1, 3, 3, 2].length) (baseStart_3972380 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3972380 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3972380 prefixEnd_3972380 := by exact prefixLift 3972380
  have htrace : WordTrace (prefixWord ++ tailWord_3972380) baseStart_3972380 baseEnd_3972380 := by
    simpa [prefixWord, tailWord_3972380, baseEnd_3972380] using wordTrace_append hprefix tailTrace_3972380
  have hstable : (prefixWord ++ tailWord_3972380).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3972380).length < 2 ^ (prefixWord ++ tailWord_3972380).sum := by decide
  have hdescent : baseEnd_3972380 < baseStart_3972380 := by decide
  rcases family_descends (prefixWord ++ tailWord_3972380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3972393 : List Nat := [1, 2, 1, 1, 1, 1, 1, 2, 7, 4, 2]
def baseStart_3972393 : Nat := 118140960795 + 3972393 * 2 ^ 59
def prefixEnd_3972393 : Nat := 4983230072969 + 3 ^ 40 * 3972393 * 2
def baseEnd_3972393 : Nat := 2039746957555781727818803

theorem tailTrace_3972393 : CollatzResearch.WordTrace tailWord_3972393 prefixEnd_3972393 2039746957555781727818803 := by
  unfold tailWord_3972393
  simp only [CollatzResearch.WordTrace]
  refine ⟨144885075497706066556881833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96590050331804044371254555 144885075497706066556881833)
  ·
    refine ⟨108663806623279549917661375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 144885075497706066556881833 108663806623279549917661375)
    ·
      refine ⟨162995709934919324876492063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108663806623279549917661375 162995709934919324876492063)
      ·
        refine ⟨244493564902378987314738095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 162995709934919324876492063 244493564902378987314738095)
        ·
          refine ⟨366740347353568480972107143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 244493564902378987314738095 366740347353568480972107143)
          ·
            refine ⟨550110521030352721458160715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 366740347353568480972107143 550110521030352721458160715)
            ·
              refine ⟨825165781545529082187241073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 550110521030352721458160715 825165781545529082187241073)
              ·
                refine ⟨618874336159146811640430805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 825165781545529082187241073 618874336159146811640430805)
                ·
                  refine ⟨14504867253730003397822597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 618874336159146811640430805 14504867253730003397822597)
                  ·
                    refine ⟨2719662610074375637091737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 14504867253730003397822597 2719662610074375637091737)
                    ·
                      refine ⟨2039746957555781727818803, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2719662610074375637091737 2039746957555781727818803)
                      ·
                        rfl

theorem cell23_3972393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 2, 7, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 2, 7, 4, 2].length) (baseStart_3972393 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3972393 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3972393 prefixEnd_3972393 := by exact prefixLift 3972393
  have htrace : WordTrace (prefixWord ++ tailWord_3972393) baseStart_3972393 baseEnd_3972393 := by
    simpa [prefixWord, tailWord_3972393, baseEnd_3972393] using wordTrace_append hprefix tailTrace_3972393
  have hstable : (prefixWord ++ tailWord_3972393).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3972393).length < 2 ^ (prefixWord ++ tailWord_3972393).sum := by decide
  have hdescent : baseEnd_3972393 < baseStart_3972393 := by decide
  rcases family_descends (prefixWord ++ tailWord_3972393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3972396 : List Nat := [2, 2, 1, 1, 1, 3, 1, 3, 1, 3, 5]
def baseStart_3972396 : Nat := 118140960795 + 3972396 * 2 ^ 59
def prefixEnd_3972396 : Nat := 4983230072969 + 3 ^ 40 * 3972396 * 2
def baseEnd_3972396 : Nat := 2039748497997745216081289

theorem tailTrace_3972396 : CollatzResearch.WordTrace tailWord_3972396 prefixEnd_3972396 2039748497997745216081289 := by
  unfold tailWord_3972396
  simp only [CollatzResearch.WordTrace]
  refine ⟨72442592458347599034620521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96590123277796798712827361 72442592458347599034620521)
  ·
    refine ⟨54331944343760699275965391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72442592458347599034620521 54331944343760699275965391)
    ·
      refine ⟨81497916515641048913948087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54331944343760699275965391 81497916515641048913948087)
      ·
        refine ⟨122246874773461573370922131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81497916515641048913948087 122246874773461573370922131)
        ·
          refine ⟨183370312160192360056383197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 122246874773461573370922131 183370312160192360056383197)
          ·
            refine ⟨68763867060072135021143699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 183370312160192360056383197 68763867060072135021143699)
            ·
              refine ⟨103145800590108202531715549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68763867060072135021143699 103145800590108202531715549)
              ·
                refine ⟨38679675221290575949393331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 103145800590108202531715549 38679675221290575949393331)
                ·
                  refine ⟨58019512831935863924089997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38679675221290575949393331 58019512831935863924089997)
                  ·
                    refine ⟨21757317311975948971533749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 58019512831935863924089997 21757317311975948971533749)
                    ·
                      refine ⟨2039748497997745216081289, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 21757317311975948971533749 2039748497997745216081289)
                      ·
                        rfl

theorem cell23_3972396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 3, 5].length) (baseStart_3972396 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3972396 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3972396 prefixEnd_3972396 := by exact prefixLift 3972396
  have htrace : WordTrace (prefixWord ++ tailWord_3972396) baseStart_3972396 baseEnd_3972396 := by
    simpa [prefixWord, tailWord_3972396, baseEnd_3972396] using wordTrace_append hprefix tailTrace_3972396
  have hstable : (prefixWord ++ tailWord_3972396).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3972396).length < 2 ^ (prefixWord ++ tailWord_3972396).sum := by decide
  have hdescent : baseEnd_3972396 < baseStart_3972396 := by decide
  rcases family_descends (prefixWord ++ tailWord_3972396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3972420 : List Nat := [2, 3, 4, 1, 1, 1, 2, 1, 2, 6]
def baseStart_3972420 : Nat := 118140960795 + 3972420 * 2 ^ 59
def prefixEnd_3972420 : Nat := 4983230072969 + 3 ^ 40 * 3972420 * 2
def baseEnd_3972420 : Nat := 679920273844484374060393

theorem tailTrace_3972420 : CollatzResearch.WordTrace tailWord_3972420 prefixEnd_3972420 679920273844484374060393 := by
  unfold tailWord_3972420
  simp only [CollatzResearch.WordTrace]
  refine ⟨72443030134304125084057357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96590706845738833445409809 72443030134304125084057357)
  ·
    refine ⟨27166136300364046906521509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 72443030134304125084057357 27166136300364046906521509)
    ·
      refine ⟨5093650556318258794972783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 27166136300364046906521509 5093650556318258794972783)
      ·
        refine ⟨7640475834477388192459175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5093650556318258794972783 7640475834477388192459175)
        ·
          refine ⟨11460713751716082288688763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7640475834477388192459175 11460713751716082288688763)
          ·
            refine ⟨17191070627574123433033145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11460713751716082288688763 17191070627574123433033145)
            ·
              refine ⟨12893302970680592574774859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17191070627574123433033145 12893302970680592574774859)
              ·
                refine ⟨19339954456020888862162289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12893302970680592574774859 19339954456020888862162289)
                ·
                  refine ⟨14504965842015666646621717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19339954456020888862162289 14504965842015666646621717)
                  ·
                    refine ⟨679920273844484374060393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14504965842015666646621717 679920273844484374060393)
                    ·
                      rfl

theorem cell23_3972420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 1, 2, 1, 2, 6].length) (baseStart_3972420 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3972420 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3972420 prefixEnd_3972420 := by exact prefixLift 3972420
  have htrace : WordTrace (prefixWord ++ tailWord_3972420) baseStart_3972420 baseEnd_3972420 := by
    simpa [prefixWord, tailWord_3972420, baseEnd_3972420] using wordTrace_append hprefix tailTrace_3972420
  have hstable : (prefixWord ++ tailWord_3972420).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3972420).length < 2 ^ (prefixWord ++ tailWord_3972420).sum := by decide
  have hdescent : baseEnd_3972420 < baseStart_3972420 := by decide
  rcases family_descends (prefixWord ++ tailWord_3972420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3972423 : List Nat := [1, 1, 4, 1, 2, 3, 2, 1, 2, 2, 4]
def baseStart_3972423 : Nat := 118140960795 + 3972423 * 2 ^ 59
def prefixEnd_3972423 : Nat := 4983230072969 + 3 ^ 40 * 3972423 * 2
def baseEnd_3972423 : Nat := 2039762361975416610443665

theorem tailTrace_3972423 : CollatzResearch.WordTrace tailWord_3972423 prefixEnd_3972423 2039762361975416610443665 := by
  unfold tailWord_3972423
  simp only [CollatzResearch.WordTrace]
  refine ⟨144886169687597381680473923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96590779791731587786982615 144886169687597381680473923)
  ·
    refine ⟨217329254531396072520710885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144886169687597381680473923 217329254531396072520710885)
    ·
      refine ⟨40749235224636763597633291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 217329254531396072520710885 40749235224636763597633291)
      ·
        refine ⟨61123852836955145396449937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40749235224636763597633291 61123852836955145396449937)
        ·
          refine ⟨45842889627716359047337453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61123852836955145396449937 45842889627716359047337453)
          ·
            refine ⟨17191083610393634642751545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45842889627716359047337453 17191083610393634642751545)
            ·
              refine ⟨12893312707795225982063659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17191083610393634642751545 12893312707795225982063659)
              ·
                refine ⟨19339969061692838973095489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12893312707795225982063659 19339969061692838973095489)
                ·
                  refine ⟨14504976796269629229821617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19339969061692838973095489 14504976796269629229821617)
                  ·
                    refine ⟨10878732597202221922366213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14504976796269629229821617 10878732597202221922366213)
                    ·
                      refine ⟨2039762361975416610443665, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10878732597202221922366213 2039762361975416610443665)
                      ·
                        rfl

theorem cell23_3972423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 3, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 3, 2, 1, 2, 2, 4].length) (baseStart_3972423 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3972423 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3972423 prefixEnd_3972423 := by exact prefixLift 3972423
  have htrace : WordTrace (prefixWord ++ tailWord_3972423) baseStart_3972423 baseEnd_3972423 := by
    simpa [prefixWord, tailWord_3972423, baseEnd_3972423] using wordTrace_append hprefix tailTrace_3972423
  have hstable : (prefixWord ++ tailWord_3972423).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3972423).length < 2 ^ (prefixWord ++ tailWord_3972423).sum := by decide
  have hdescent : baseEnd_3972423 < baseStart_3972423 := by decide
  rcases family_descends (prefixWord ++ tailWord_3972423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3972426 : List Nat := [3, 1, 2, 1, 1, 1, 1, 2, 1, 1, 9]
def baseStart_3972426 : Nat := 118140960795 + 3972426 * 2 ^ 59
def prefixEnd_3972426 : Nat := 4983230072969 + 3 ^ 40 * 3972426 * 2
def baseEnd_3972426 : Nat := 2039763902417380098706151

theorem tailTrace_3972426 : CollatzResearch.WordTrace tailWord_3972426 prefixEnd_3972426 2039763902417380098706151 := by
  unfold tailWord_3972426
  simp only [CollatzResearch.WordTrace]
  refine ⟨36221569776646628298208283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 96590852737724342128555421 36221569776646628298208283)
  ·
    refine ⟨54332354664969942447312425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36221569776646628298208283 54332354664969942447312425)
    ·
      refine ⟨40749265998727456835484319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54332354664969942447312425 40749265998727456835484319)
      ·
        refine ⟨61123898998091185253226479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40749265998727456835484319 61123898998091185253226479)
        ·
          refine ⟨91685848497136777879839719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61123898998091185253226479 91685848497136777879839719)
          ·
            refine ⟨137528772745705166819759579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91685848497136777879839719 137528772745705166819759579)
            ·
              refine ⟨206293159118557750229639369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 137528772745705166819759579 206293159118557750229639369)
              ·
                refine ⟨154719869338918312672229527, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 206293159118557750229639369 154719869338918312672229527)
                ·
                  refine ⟨232079804008377469008344291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 154719869338918312672229527 232079804008377469008344291)
                  ·
                    refine ⟨348119706012566203512516437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 232079804008377469008344291 348119706012566203512516437)
                    ·
                      refine ⟨2039763902417380098706151, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 348119706012566203512516437 2039763902417380098706151)
                      ·
                        rfl

theorem cell23_3972426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 1, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 1, 2, 1, 1, 9].length) (baseStart_3972426 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3972426 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3972426 prefixEnd_3972426 := by exact prefixLift 3972426
  have htrace : WordTrace (prefixWord ++ tailWord_3972426) baseStart_3972426 baseEnd_3972426 := by
    simpa [prefixWord, tailWord_3972426, baseEnd_3972426] using wordTrace_append hprefix tailTrace_3972426
  have hstable : (prefixWord ++ tailWord_3972426).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3972426).length < 2 ^ (prefixWord ++ tailWord_3972426).sum := by decide
  have hdescent : baseEnd_3972426 < baseStart_3972426 := by decide
  rcases family_descends (prefixWord ++ tailWord_3972426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3972463 : List Nat := [1, 1, 2, 1, 3, 1, 5, 2, 2, 5]
def baseStart_3972463 : Nat := 118140960795 + 3972463 * 2 ^ 59
def prefixEnd_3972463 : Nat := 4983230072969 + 3 ^ 40 * 3972463 * 2
def baseEnd_3972463 : Nat := 679927633733865484647827

theorem tailTrace_3972463 : CollatzResearch.WordTrace tailWord_3972463 prefixEnd_3972463 679927633733865484647827 := by
  unfold tailWord_3972463
  simp only [CollatzResearch.WordTrace]
  refine ⟨144887628607452468511930043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96591752404968312341286695 144887628607452468511930043)
  ·
    refine ⟨217331442911178702767895065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144887628607452468511930043 217331442911178702767895065)
    ·
      refine ⟨162998582183384027075921299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 217331442911178702767895065 162998582183384027075921299)
      ·
        refine ⟨244497873275076040613881949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 162998582183384027075921299 244497873275076040613881949)
        ·
          refine ⟨91686702478153515230205731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 244497873275076040613881949 91686702478153515230205731)
          ·
            refine ⟨137530053717230272845308597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91686702478153515230205731 137530053717230272845308597)
            ·
              refine ⟨12893442535990338079247681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 137530053717230272845308597 12893442535990338079247681)
              ·
                refine ⟨9670081901992753559435761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12893442535990338079247681 9670081901992753559435761)
                ·
                  refine ⟨7252561426494565169576821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9670081901992753559435761 7252561426494565169576821)
                  ·
                    refine ⟨679927633733865484647827, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7252561426494565169576821 679927633733865484647827)
                    ·
                      rfl

theorem cell23_3972463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 5, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 5, 2, 2, 5].length) (baseStart_3972463 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3972463 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3972463 prefixEnd_3972463 := by exact prefixLift 3972463
  have htrace : WordTrace (prefixWord ++ tailWord_3972463) baseStart_3972463 baseEnd_3972463 := by
    simpa [prefixWord, tailWord_3972463, baseEnd_3972463] using wordTrace_append hprefix tailTrace_3972463
  have hstable : (prefixWord ++ tailWord_3972463).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3972463).length < 2 ^ (prefixWord ++ tailWord_3972463).sum := by decide
  have hdescent : baseEnd_3972463 < baseStart_3972463 := by decide
  rcases family_descends (prefixWord ++ tailWord_3972463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3972478 : List Nat := [4, 2, 3, 2, 1, 1, 1, 3, 2, 2, 2]
def baseStart_3972478 : Nat := 118140960795 + 3972478 * 2 ^ 59
def prefixEnd_3972478 : Nat := 4983230072969 + 3 ^ 40 * 3972478 * 2
def baseEnd_3972478 : Nat := 2039790603411413895255913

theorem tailTrace_3972478 : CollatzResearch.WordTrace tailWord_3972478 prefixEnd_3972478 2039790603411413895255913 := by
  unfold tailWord_3972478
  simp only [CollatzResearch.WordTrace]
  refine ⟨18111021962799765759215761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 96592117134932084049150725 18111021962799765759215761)
  ·
    refine ⟨13583266472099824319411821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18111021962799765759215761 13583266472099824319411821)
    ·
      refine ⟨5093724927037434119779433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13583266472099824319411821 5093724927037434119779433)
      ·
        refine ⟨3820293695278075589834575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5093724927037434119779433 3820293695278075589834575)
        ·
          refine ⟨5730440542917113384751863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3820293695278075589834575 5730440542917113384751863)
          ·
            refine ⟨8595660814375670077127795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5730440542917113384751863 8595660814375670077127795)
            ·
              refine ⟨12893491221563505115691693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8595660814375670077127795 12893491221563505115691693)
              ·
                refine ⟨4835059208086314418384385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12893491221563505115691693 4835059208086314418384385)
                ·
                  refine ⟨3626294406064735813788289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4835059208086314418384385 3626294406064735813788289)
                  ·
                    refine ⟨2719720804548551860341217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3626294406064735813788289 2719720804548551860341217)
                    ·
                      refine ⟨2039790603411413895255913, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2719720804548551860341217 2039790603411413895255913)
                      ·
                        rfl

theorem cell23_3972478_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 1, 1, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 1, 1, 1, 3, 2, 2, 2].length) (baseStart_3972478 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3972478 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3972478 prefixEnd_3972478 := by exact prefixLift 3972478
  have htrace : WordTrace (prefixWord ++ tailWord_3972478) baseStart_3972478 baseEnd_3972478 := by
    simpa [prefixWord, tailWord_3972478, baseEnd_3972478] using wordTrace_append hprefix tailTrace_3972478
  have hstable : (prefixWord ++ tailWord_3972478).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3972478).length < 2 ^ (prefixWord ++ tailWord_3972478).sum := by decide
  have hdescent : baseEnd_3972478 < baseStart_3972478 := by decide
  rcases family_descends (prefixWord ++ tailWord_3972478) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3972560 : List Nat := [2, 1, 1, 1, 1, 2, 2, 5, 1, 5, 2]
def baseStart_3972560 : Nat := 118140960795 + 3972560 * 2 ^ 59
def prefixEnd_3972560 : Nat := 4983230072969 + 3 ^ 40 * 3972560 * 2
def baseEnd_3972560 : Nat := 2039832708825082574430535

theorem tailTrace_3972560 : CollatzResearch.WordTrace tailWord_3972560 prefixEnd_3972560 2039832708825082574430535 := by
  unfold tailWord_3972560
  simp only [CollatzResearch.WordTrace]
  refine ⟨72445583244050527039105567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96594110992067369385474089 72445583244050527039105567)
  ·
    refine ⟨108668374866075790558658351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72445583244050527039105567 108668374866075790558658351)
    ·
      refine ⟨163002562299113685837987527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108668374866075790558658351 163002562299113685837987527)
      ·
        refine ⟨244503843448670528756981291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 163002562299113685837987527 244503843448670528756981291)
        ·
          refine ⟨366755765173005793135471937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 244503843448670528756981291 366755765173005793135471937)
          ·
            refine ⟨275066823879754344851603953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 366755765173005793135471937 275066823879754344851603953)
            ·
              refine ⟨206300117909815758638702965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 275066823879754344851603953 206300117909815758638702965)
              ·
                refine ⟨19340636054045227372378403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 206300117909815758638702965 19340636054045227372378403)
                ·
                  refine ⟨29010954081067841058567605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19340636054045227372378403 29010954081067841058567605)
                  ·
                    refine ⟨2719776945100110099240713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 29010954081067841058567605 2719776945100110099240713)
                    ·
                      refine ⟨2039832708825082574430535, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2719776945100110099240713 2039832708825082574430535)
                      ·
                        rfl

theorem cell23_3972560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 5, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 5, 1, 5, 2].length) (baseStart_3972560 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3972560 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3972560 prefixEnd_3972560 := by exact prefixLift 3972560
  have htrace : WordTrace (prefixWord ++ tailWord_3972560) baseStart_3972560 baseEnd_3972560 := by
    simpa [prefixWord, tailWord_3972560, baseEnd_3972560] using wordTrace_append hprefix tailTrace_3972560
  have hstable : (prefixWord ++ tailWord_3972560).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3972560).length < 2 ^ (prefixWord ++ tailWord_3972560).sum := by decide
  have hdescent : baseEnd_3972560 < baseStart_3972560 := by decide
  rcases family_descends (prefixWord ++ tailWord_3972560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3972584 : List Nat := [2, 1, 4, 1, 1, 2, 1, 6, 1, 1, 3]
def baseStart_3972584 : Nat := 118140960795 + 3972584 * 2 ^ 59
def prefixEnd_3972584 : Nat := 4983230072969 + 3 ^ 40 * 3972584 * 2
def baseEnd_3972584 : Nat := 2039845032360790480530425

theorem tailTrace_3972584 : CollatzResearch.WordTrace tailWord_3972584 prefixEnd_3972584 2039845032360790480530425 := by
  unfold tailWord_3972584
  simp only [CollatzResearch.WordTrace]
  refine ⟨72446020920007053088542403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96594694560009404118056537 72446020920007053088542403)
  ·
    refine ⟨108669031380010579632813605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72446020920007053088542403 108669031380010579632813605)
    ·
      refine ⟨20375443383751983681152551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 108669031380010579632813605 20375443383751983681152551)
      ·
        refine ⟨30563165075627975521728827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20375443383751983681152551 30563165075627975521728827)
        ·
          refine ⟨45844747613441963282593241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30563165075627975521728827 45844747613441963282593241)
          ·
            refine ⟨34383560710081472461944931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45844747613441963282593241 34383560710081472461944931)
            ·
              refine ⟨51575341065122208692917397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34383560710081472461944931 51575341065122208692917397)
              ·
                refine ⟨2417594112427603532480503, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 51575341065122208692917397 2417594112427603532480503)
                ·
                  refine ⟨3626391168641405298720755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2417594112427603532480503 3626391168641405298720755)
                  ·
                    refine ⟨5439586752962107948081133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3626391168641405298720755 5439586752962107948081133)
                    ·
                      refine ⟨2039845032360790480530425, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5439586752962107948081133 2039845032360790480530425)
                      ·
                        rfl

theorem cell23_3972584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 1, 6, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 1, 6, 1, 1, 3].length) (baseStart_3972584 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3972584 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3972584 prefixEnd_3972584 := by exact prefixLift 3972584
  have htrace : WordTrace (prefixWord ++ tailWord_3972584) baseStart_3972584 baseEnd_3972584 := by
    simpa [prefixWord, tailWord_3972584, baseEnd_3972584] using wordTrace_append hprefix tailTrace_3972584
  have hstable : (prefixWord ++ tailWord_3972584).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3972584).length < 2 ^ (prefixWord ++ tailWord_3972584).sum := by decide
  have hdescent : baseEnd_3972584 < baseStart_3972584 := by decide
  rcases family_descends (prefixWord ++ tailWord_3972584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3972600 : List Nat := [2, 1, 2, 1, 1, 5, 3, 1, 1, 6]
def baseStart_3972600 : Nat := 118140960795 + 3972600 * 2 ^ 59
def prefixEnd_3972600 : Nat := 4983230072969 + 3 ^ 40 * 3972600 * 2
def baseEnd_3972600 : Nat := 679951082683754139310117

theorem tailTrace_3972600 : CollatzResearch.WordTrace tailWord_3972600 prefixEnd_3972600 679951082683754139310117 := by
  unfold tailWord_3972600
  simp only [CollatzResearch.WordTrace]
  refine ⟨72446312703978070454833627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96595083605304093939778169 72446312703978070454833627)
  ·
    refine ⟨108669469055967105682250441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72446312703978070454833627 108669469055967105682250441)
    ·
      refine ⟨81502101791975329261687831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 108669469055967105682250441 81502101791975329261687831)
      ·
        refine ⟨122253152687962993892531747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81502101791975329261687831 122253152687962993892531747)
        ·
          refine ⟨183379729031944490838797621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 122253152687962993892531747 183379729031944490838797621)
          ·
            refine ⟨17191849596744796016137277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 183379729031944490838797621 17191849596744796016137277)
            ·
              refine ⟨6446943598779298506051479, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17191849596744796016137277 6446943598779298506051479)
              ·
                refine ⟨9670415398168947759077219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6446943598779298506051479 9670415398168947759077219)
                ·
                  refine ⟨14505623097253421638615829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9670415398168947759077219 14505623097253421638615829)
                  ·
                    refine ⟨679951082683754139310117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14505623097253421638615829 679951082683754139310117)
                    ·
                      rfl

theorem cell23_3972600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 5, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 5, 3, 1, 1, 6].length) (baseStart_3972600 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3972600 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3972600 prefixEnd_3972600 := by exact prefixLift 3972600
  have htrace : WordTrace (prefixWord ++ tailWord_3972600) baseStart_3972600 baseEnd_3972600 := by
    simpa [prefixWord, tailWord_3972600, baseEnd_3972600] using wordTrace_append hprefix tailTrace_3972600
  have hstable : (prefixWord ++ tailWord_3972600).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3972600).length < 2 ^ (prefixWord ++ tailWord_3972600).sum := by decide
  have hdescent : baseEnd_3972600 < baseStart_3972600 := by decide
  rcases family_descends (prefixWord ++ tailWord_3972600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3972603 : List Nat := [1, 1, 1, 1, 1, 3, 2, 5, 1, 1, 6]
def baseStart_3972603 : Nat := 118140960795 + 3972603 * 2 ^ 59
def prefixEnd_3972603 : Nat := 4983230072969 + 3 ^ 40 * 3972603 * 2
def baseEnd_3972603 : Nat := 2039854788493225906192837

theorem tailTrace_3972603 : CollatzResearch.WordTrace tailWord_3972603 prefixEnd_3972603 2039854788493225906192837 := by
  unfold tailWord_3972603
  simp only [CollatzResearch.WordTrace]
  refine ⟨144892734826945272422026463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96595156551296848281350975 144892734826945272422026463)
  ·
    refine ⟨217339102240417908633039695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144892734826945272422026463 217339102240417908633039695)
    ·
      refine ⟨326008653360626862949559543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 217339102240417908633039695 326008653360626862949559543)
      ·
        refine ⟨489012980040940294424339315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 326008653360626862949559543 489012980040940294424339315)
        ·
          refine ⟨733519470061410441636508973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 489012980040940294424339315 733519470061410441636508973)
          ·
            refine ⟨275069801273028915613690865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 733519470061410441636508973 275069801273028915613690865)
            ·
              refine ⟨206302350954771686710268149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 275069801273028915613690865 206302350954771686710268149)
              ·
                refine ⟨19340845402009845629087639, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 206302350954771686710268149 19340845402009845629087639)
                ·
                  refine ⟨29011268103014768443631459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19340845402009845629087639 29011268103014768443631459)
                  ·
                    refine ⟨43516902154522152665447189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29011268103014768443631459 43516902154522152665447189)
                    ·
                      refine ⟨2039854788493225906192837, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 43516902154522152665447189 2039854788493225906192837)
                      ·
                        rfl

theorem cell23_3972603_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 2, 5, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 2, 5, 1, 1, 6].length) (baseStart_3972603 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3972603 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3972603 prefixEnd_3972603 := by exact prefixLift 3972603
  have htrace : WordTrace (prefixWord ++ tailWord_3972603) baseStart_3972603 baseEnd_3972603 := by
    simpa [prefixWord, tailWord_3972603, baseEnd_3972603] using wordTrace_append hprefix tailTrace_3972603
  have hstable : (prefixWord ++ tailWord_3972603).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3972603).length < 2 ^ (prefixWord ++ tailWord_3972603).sum := by decide
  have hdescent : baseEnd_3972603 < baseStart_3972603 := by decide
  rcases family_descends (prefixWord ++ tailWord_3972603) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3972607 : List Nat := [1, 1, 2, 2, 1, 2, 2, 3, 5, 2, 2]
def baseStart_3972607 : Nat := 118140960795 + 3972607 * 2 ^ 59
def prefixEnd_3972607 : Nat := 4983230072969 + 3 ^ 40 * 3972607 * 2
def baseEnd_3972607 : Nat := 2039856842415843890542819

theorem tailTrace_3972607 : CollatzResearch.WordTrace tailWord_3972607 prefixEnd_3972607 2039856842415843890542819 := by
  unfold tailWord_3972607
  simp only [CollatzResearch.WordTrace]
  refine ⟨144892880718930781105172075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96595253812620520736781383 144892880718930781105172075)
  ·
    refine ⟨217339321078396171657758113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144892880718930781105172075 217339321078396171657758113)
    ·
      refine ⟨163004490808797128743318585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 217339321078396171657758113 163004490808797128743318585)
      ·
        refine ⟨122253368106597846557488939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 163004490808797128743318585 122253368106597846557488939)
        ·
          refine ⟨183380052159896769836233409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 122253368106597846557488939 183380052159896769836233409)
          ·
            refine ⟨137535039119922577377175057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 183380052159896769836233409 137535039119922577377175057)
            ·
              refine ⟨103151279339941933032881293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 137535039119922577377175057 103151279339941933032881293)
              ·
                refine ⟨38681729752478224887330485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 103151279339941933032881293 38681729752478224887330485)
                ·
                  refine ⟨3626412164294833583187233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 38681729752478224887330485 3626412164294833583187233)
                  ·
                    refine ⟨2719809123221125187390425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3626412164294833583187233 2719809123221125187390425)
                    ·
                      refine ⟨2039856842415843890542819, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2719809123221125187390425 2039856842415843890542819)
                      ·
                        rfl

theorem cell23_3972607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 2, 3, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 2, 3, 5, 2, 2].length) (baseStart_3972607 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3972607 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3972607 prefixEnd_3972607 := by exact prefixLift 3972607
  have htrace : WordTrace (prefixWord ++ tailWord_3972607) baseStart_3972607 baseEnd_3972607 := by
    simpa [prefixWord, tailWord_3972607, baseEnd_3972607] using wordTrace_append hprefix tailTrace_3972607
  have hstable : (prefixWord ++ tailWord_3972607).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3972607).length < 2 ^ (prefixWord ++ tailWord_3972607).sum := by decide
  have hdescent : baseEnd_3972607 < baseStart_3972607 := by decide
  rcases family_descends (prefixWord ++ tailWord_3972607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3972627 : List Nat := [1, 1, 1, 2, 1, 6, 2, 3, 1, 2, 3]
def baseStart_3972627 : Nat := 118140960795 + 3972627 * 2 ^ 59
def prefixEnd_3972627 : Nat := 4983230072969 + 3 ^ 40 * 3972627 * 2
def baseEnd_3972627 : Nat := 2039867112028933812292727

theorem tailTrace_3972627 : CollatzResearch.WordTrace tailWord_3972627 prefixEnd_3972627 2039867112028933812292727 := by
  unfold tailWord_3972627
  simp only [CollatzResearch.WordTrace]
  refine ⟨144893610178858324520900135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96595740119238883013933423 144893610178858324520900135)
  ·
    refine ⟨217340415268287486781350203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144893610178858324520900135 217340415268287486781350203)
    ·
      refine ⟨326010622902431230172025305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 217340415268287486781350203 326010622902431230172025305)
      ·
        refine ⟨244507967176823422629018979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 326010622902431230172025305 244507967176823422629018979)
        ·
          refine ⟨366761950765235133943528469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 244507967176823422629018979 366761950765235133943528469)
          ·
            refine ⟨17191966442120396903602897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 366761950765235133943528469 17191966442120396903602897)
            ·
              refine ⟨12893974831590297677702173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17191966442120396903602897 12893974831590297677702173)
              ·
                refine ⟨4835240561846361629138315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12893974831590297677702173 4835240561846361629138315)
                ·
                  refine ⟨7252860842769542443707473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4835240561846361629138315 7252860842769542443707473)
                  ·
                    refine ⟨5439645632077156832780605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7252860842769542443707473 5439645632077156832780605)
                    ·
                      refine ⟨2039867112028933812292727, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5439645632077156832780605 2039867112028933812292727)
                      ·
                        rfl

theorem cell23_3972627_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 6, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 6, 2, 3, 1, 2, 3].length) (baseStart_3972627 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3972627 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3972627 prefixEnd_3972627 := by exact prefixLift 3972627
  have htrace : WordTrace (prefixWord ++ tailWord_3972627) baseStart_3972627 baseEnd_3972627 := by
    simpa [prefixWord, tailWord_3972627, baseEnd_3972627] using wordTrace_append hprefix tailTrace_3972627
  have hstable : (prefixWord ++ tailWord_3972627).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3972627).length < 2 ^ (prefixWord ++ tailWord_3972627).sum := by decide
  have hdescent : baseEnd_3972627 < baseStart_3972627 := by decide
  rcases family_descends (prefixWord ++ tailWord_3972627) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3972633 : List Nat := [1, 2, 1, 2, 1, 1, 2, 1, 4, 2, 6]
def baseStart_3972633 : Nat := 118140960795 + 3972633 * 2 ^ 59
def prefixEnd_3972633 : Nat := 4983230072969 + 3 ^ 40 * 3972633 * 2
def baseEnd_3972633 : Nat := 2039870192912860788817699

theorem tailTrace_3972633 : CollatzResearch.WordTrace tailWord_3972633 prefixEnd_3972633 2039870192912860788817699 := by
  unfold tailWord_3972633
  simp only [CollatzResearch.WordTrace]
  refine ⟨144893829016836587545618553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96595886011224391697079035 144893829016836587545618553)
  ·
    refine ⟨108670371762627440659213915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 144893829016836587545618553 108670371762627440659213915)
    ·
      refine ⟨163005557643941160988820873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108670371762627440659213915 163005557643941160988820873)
      ·
        refine ⟨122254168232955870741615655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 163005557643941160988820873 122254168232955870741615655)
        ·
          refine ⟨183381252349433806112423483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 122254168232955870741615655 183381252349433806112423483)
          ·
            refine ⟨275071878524150709168635225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 183381252349433806112423483 275071878524150709168635225)
            ·
              refine ⟨206303908893113031876476419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 275071878524150709168635225 206303908893113031876476419)
              ·
                refine ⟨309455863339669547814714629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 206303908893113031876476419 309455863339669547814714629)
                ·
                  refine ⟨58022974376188040215258993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 309455863339669547814714629 58022974376188040215258993)
                  ·
                    refine ⟨43517230782141030161444245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 58022974376188040215258993 43517230782141030161444245)
                    ·
                      refine ⟨2039870192912860788817699, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 43517230782141030161444245 2039870192912860788817699)
                      ·
                        rfl

theorem cell23_3972633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 2, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 2, 1, 4, 2, 6].length) (baseStart_3972633 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3972633 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3972633 prefixEnd_3972633 := by exact prefixLift 3972633
  have htrace : WordTrace (prefixWord ++ tailWord_3972633) baseStart_3972633 baseEnd_3972633 := by
    simpa [prefixWord, tailWord_3972633, baseEnd_3972633] using wordTrace_append hprefix tailTrace_3972633
  have hstable : (prefixWord ++ tailWord_3972633).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3972633).length < 2 ^ (prefixWord ++ tailWord_3972633).sum := by decide
  have hdescent : baseEnd_3972633 < baseStart_3972633 := by decide
  rcases family_descends (prefixWord ++ tailWord_3972633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3972641 : List Nat := [1, 2, 3, 2, 2, 4, 1, 1, 3, 2, 2]
def baseStart_3972641 : Nat := 118140960795 + 3972641 * 2 ^ 59
def prefixEnd_3972641 : Nat := 4983230072969 + 3 ^ 40 * 3972641 * 2
def baseEnd_3972641 : Nat := 2039874300758096757517663

theorem tailTrace_3972641 : CollatzResearch.WordTrace tailWord_3972641 prefixEnd_3972641 2039874300758096757517663 := by
  unfold tailWord_3972641
  simp only [CollatzResearch.WordTrace]
  refine ⟨144894120800807604911909777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96596080533871736607939851 144894120800807604911909777)
  ·
    refine ⟨108670590600605703683932333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 144894120800807604911909777 108670590600605703683932333)
    ·
      refine ⟨40751471475227138881474625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 108670590600605703683932333 40751471475227138881474625)
      ·
        refine ⟨30563603606420354161105969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40751471475227138881474625 30563603606420354161105969)
        ·
          refine ⟨22922702704815265620829477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30563603606420354161105969 22922702704815265620829477)
          ·
            refine ⟨4298006757152862303905527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 22922702704815265620829477 4298006757152862303905527)
            ·
              refine ⟨6447010135729293455858291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4298006757152862303905527 6447010135729293455858291)
              ·
                refine ⟨9670515203593940183787437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6447010135729293455858291 9670515203593940183787437)
                ·
                  refine ⟨3626443201347727568920289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9670515203593940183787437 3626443201347727568920289)
                  ·
                    refine ⟨2719832401010795676690217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3626443201347727568920289 2719832401010795676690217)
                    ·
                      refine ⟨2039874300758096757517663, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2719832401010795676690217 2039874300758096757517663)
                      ·
                        rfl

theorem cell23_3972641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 4, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 4, 1, 1, 3, 2, 2].length) (baseStart_3972641 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3972641 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3972641 prefixEnd_3972641 := by exact prefixLift 3972641
  have htrace : WordTrace (prefixWord ++ tailWord_3972641) baseStart_3972641 baseEnd_3972641 := by
    simpa [prefixWord, tailWord_3972641, baseEnd_3972641] using wordTrace_append hprefix tailTrace_3972641
  have hstable : (prefixWord ++ tailWord_3972641).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3972641).length < 2 ^ (prefixWord ++ tailWord_3972641).sum := by decide
  have hdescent : baseEnd_3972641 < baseStart_3972641 := by decide
  rcases family_descends (prefixWord ++ tailWord_3972641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3972650 : List Nat := [3, 1, 4, 1, 1, 1, 1, 1, 2, 2, 6]
def baseStart_3972650 : Nat := 118140960795 + 3972650 * 2 ^ 59
def prefixEnd_3972650 : Nat := 4983230072969 + 3 ^ 40 * 3972650 * 2
def baseEnd_3972650 : Nat := 2039878922083987222305121

theorem tailTrace_3972650 : CollatzResearch.WordTrace tailWord_3972650 prefixEnd_3972650 2039878922083987222305121 := by
  unfold tailWord_3972650
  simp only [CollatzResearch.WordTrace]
  refine ⟨36223612264443749862246851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 96596299371849999632658269 36223612264443749862246851)
  ·
    refine ⟨54335418396665624793370277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36223612264443749862246851 54335418396665624793370277)
    ·
      refine ⟨10187890949374804648756927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 54335418396665624793370277 10187890949374804648756927)
      ·
        refine ⟨15281836424062206973135391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10187890949374804648756927 15281836424062206973135391)
        ·
          refine ⟨22922754636093310459703087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15281836424062206973135391 22922754636093310459703087)
          ·
            refine ⟨34384131954139965689554631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22922754636093310459703087 34384131954139965689554631)
            ·
              refine ⟨51576197931209948534331947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34384131954139965689554631 51576197931209948534331947)
              ·
                refine ⟨77364296896814922801497921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51576197931209948534331947 77364296896814922801497921)
                ·
                  refine ⟨58023222672611192101123441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 77364296896814922801497921 58023222672611192101123441)
                  ·
                    refine ⟨43517417004458394075842581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 58023222672611192101123441 43517417004458394075842581)
                    ·
                      refine ⟨2039878922083987222305121, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 43517417004458394075842581 2039878922083987222305121)
                      ·
                        rfl

theorem cell23_3972650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 1, 1, 2, 2, 6].length) (baseStart_3972650 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3972650 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3972650 prefixEnd_3972650 := by exact prefixLift 3972650
  have htrace : WordTrace (prefixWord ++ tailWord_3972650) baseStart_3972650 baseEnd_3972650 := by
    simpa [prefixWord, tailWord_3972650, baseEnd_3972650] using wordTrace_append hprefix tailTrace_3972650
  have hstable : (prefixWord ++ tailWord_3972650).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3972650).length < 2 ^ (prefixWord ++ tailWord_3972650).sum := by decide
  have hdescent : baseEnd_3972650 < baseStart_3972650 := by decide
  rcases family_descends (prefixWord ++ tailWord_3972650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3972678 : List Nat := [6, 1, 1, 1, 4, 1, 1, 1, 1, 1, 5]
def baseStart_3972678 : Nat := 118140960795 + 3972678 * 2 ^ 59
def prefixEnd_3972678 : Nat := 4983230072969 + 3 ^ 40 * 3972678 * 2
def baseEnd_3972678 : Nat := 2039893299542313112754993

theorem tailTrace_3972678 : CollatzResearch.WordTrace tailWord_3972678 prefixEnd_3972678 2039893299542313112754993 := by
  unfold tailWord_3972678
  simp only [CollatzResearch.WordTrace]
  refine ⟨4527983446927298757218959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 96596980201115706820671125 4527983446927298757218959)
  ·
    refine ⟨6791975170390948135828439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4527983446927298757218959 6791975170390948135828439)
    ·
      refine ⟨10187962755586422203742659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6791975170390948135828439 10187962755586422203742659)
      ·
        refine ⟨15281944133379633305613989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10187962755586422203742659 15281944133379633305613989)
        ·
          refine ⟨2865364525008681244802623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15281944133379633305613989 2865364525008681244802623)
          ·
            refine ⟨4298046787513021867203935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2865364525008681244802623 4298046787513021867203935)
            ·
              refine ⟨6447070181269532800805903, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4298046787513021867203935 6447070181269532800805903)
              ·
                refine ⟨9670605271904299201208855, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6447070181269532800805903 9670605271904299201208855)
                ·
                  refine ⟨14505907907856448801813283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9670605271904299201208855 14505907907856448801813283)
                  ·
                    refine ⟨21758861861784673202719925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14505907907856448801813283 21758861861784673202719925)
                    ·
                      refine ⟨2039893299542313112754993, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 21758861861784673202719925 2039893299542313112754993)
                      ·
                        rfl

theorem cell23_3972678_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 4, 1, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 4, 1, 1, 1, 1, 1, 5].length) (baseStart_3972678 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3972678 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3972678 prefixEnd_3972678 := by exact prefixLift 3972678
  have htrace : WordTrace (prefixWord ++ tailWord_3972678) baseStart_3972678 baseEnd_3972678 := by
    simpa [prefixWord, tailWord_3972678, baseEnd_3972678] using wordTrace_append hprefix tailTrace_3972678
  have hstable : (prefixWord ++ tailWord_3972678).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3972678).length < 2 ^ (prefixWord ++ tailWord_3972678).sum := by decide
  have hdescent : baseEnd_3972678 < baseStart_3972678 := by decide
  rcases family_descends (prefixWord ++ tailWord_3972678) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3972714 : List Nat := [3, 1, 3, 2, 1, 2, 1, 3, 1, 4, 2]
def baseStart_3972714 : Nat := 118140960795 + 3972714 * 2 ^ 59
def prefixEnd_3972714 : Nat := 4983230072969 + 3 ^ 40 * 3972714 * 2
def baseEnd_3972714 : Nat := 2039911784845874971904827

theorem tailTrace_3972714 : CollatzResearch.WordTrace tailWord_3972714 prefixEnd_3972714 2039911784845874971904827 := by
  unfold tailWord_3972714
  simp only [CollatzResearch.WordTrace]
  refine ⟨36224195832385784594829299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 96597855553028758919544797 36224195832385784594829299)
  ·
    refine ⟨54336293748578676892243949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36224195832385784594829299 54336293748578676892243949)
    ·
      refine ⟨20376110155717003834591481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 54336293748578676892243949 20376110155717003834591481)
      ·
        refine ⟨15282082616787752875943611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20376110155717003834591481 15282082616787752875943611)
        ·
          refine ⟨22923123925181629313915417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15282082616787752875943611 22923123925181629313915417)
          ·
            refine ⟨17192342943886221985436563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22923123925181629313915417 17192342943886221985436563)
            ·
              refine ⟨25788514415829332978154845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17192342943886221985436563 25788514415829332978154845)
              ·
                refine ⟨9670692905935999866808067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25788514415829332978154845 9670692905935999866808067)
                ·
                  refine ⟨14506039358903999800212101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9670692905935999866808067 14506039358903999800212101)
                  ·
                    refine ⟨2719882379794499962539769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 14506039358903999800212101 2719882379794499962539769)
                    ·
                      refine ⟨2039911784845874971904827, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2719882379794499962539769 2039911784845874971904827)
                      ·
                        rfl

theorem cell23_3972714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 2, 1, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 2, 1, 3, 1, 4, 2].length) (baseStart_3972714 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3972714 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3972714 prefixEnd_3972714 := by exact prefixLift 3972714
  have htrace : WordTrace (prefixWord ++ tailWord_3972714) baseStart_3972714 baseEnd_3972714 := by
    simpa [prefixWord, tailWord_3972714, baseEnd_3972714] using wordTrace_append hprefix tailTrace_3972714
  have hstable : (prefixWord ++ tailWord_3972714).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3972714).length < 2 ^ (prefixWord ++ tailWord_3972714).sum := by decide
  have hdescent : baseEnd_3972714 < baseStart_3972714 := by decide
  rcases family_descends (prefixWord ++ tailWord_3972714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3972720 : List Nat := [2, 1, 1, 1, 6, 1, 1, 1, 9]
def baseStart_3972720 : Nat := 118140960795 + 3972720 * 2 ^ 59
def prefixEnd_3972720 : Nat := 4983230072969 + 3 ^ 40 * 3972720 * 2
def baseEnd_3972720 : Nat := 226657207303311327603311

theorem tailTrace_3972720 : CollatzResearch.WordTrace tailWord_3972720 prefixEnd_3972720 226657207303311327603311 := by
  unfold tailWord_3972720
  simp only [CollatzResearch.WordTrace]
  refine ⟨72448501083760700702017807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96598001445014267602690409 72448501083760700702017807)
  ·
    refine ⟨108672751625641051053026711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72448501083760700702017807 108672751625641051053026711)
    ·
      refine ⟨163009127438461576579540067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108672751625641051053026711 163009127438461576579540067)
      ·
        refine ⟨244513691157692364869310101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 163009127438461576579540067 244513691157692364869310101)
        ·
          refine ⟨11461579273016829603248911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 244513691157692364869310101 11461579273016829603248911)
          ·
            refine ⟨17192368909525244404873367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11461579273016829603248911 17192368909525244404873367)
            ·
              refine ⟨25788553364287866607310051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17192368909525244404873367 25788553364287866607310051)
              ·
                refine ⟨38682830046431799910965077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25788553364287866607310051 38682830046431799910965077)
                ·
                  refine ⟨226657207303311327603311, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 38682830046431799910965077 226657207303311327603311)
                  ·
                    rfl

theorem cell23_3972720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 1, 1, 1, 9].length) (baseStart_3972720 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3972720 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3972720 prefixEnd_3972720 := by exact prefixLift 3972720
  have htrace : WordTrace (prefixWord ++ tailWord_3972720) baseStart_3972720 baseEnd_3972720 := by
    simpa [prefixWord, tailWord_3972720, baseEnd_3972720] using wordTrace_append hprefix tailTrace_3972720
  have hstable : (prefixWord ++ tailWord_3972720).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3972720).length < 2 ^ (prefixWord ++ tailWord_3972720).sum := by decide
  have hdescent : baseEnd_3972720 < baseStart_3972720 := by decide
  rcases family_descends (prefixWord ++ tailWord_3972720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3972754 : List Nat := [3, 2, 3, 1, 3, 1, 2, 1, 7]
def baseStart_3972754 : Nat := 118140960795 + 3972754 * 2 ^ 59
def prefixEnd_3972754 : Nat := 4983230072969 + 3 ^ 40 * 3972754 * 2
def baseEnd_3972754 : Nat := 226659147119117201711627

theorem tailTrace_3972754 : CollatzResearch.WordTrace tailWord_3972754 prefixEnd_3972754 226659147119117201711627 := by
  unfold tailWord_3972754
  simp only [CollatzResearch.WordTrace]
  refine ⟨36224560562349556302693329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 96598828166265483473848877 36224560562349556302693329)
  ·
    refine ⟨27168420421762167227019997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36224560562349556302693329 27168420421762167227019997)
    ·
      refine ⟨10188157658160812710132499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27168420421762167227019997 10188157658160812710132499)
      ·
        refine ⟨15282236487241219065198749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10188157658160812710132499 15282236487241219065198749)
        ·
          refine ⟨5730838682715457149449531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15282236487241219065198749 5730838682715457149449531)
          ·
            refine ⟨8596258024073185724174297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5730838682715457149449531 8596258024073185724174297)
            ·
              refine ⟨6447193518054889293130723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8596258024073185724174297 6447193518054889293130723)
              ·
                refine ⟨9670790277082333939696085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6447193518054889293130723 9670790277082333939696085)
                ·
                  refine ⟨226659147119117201711627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9670790277082333939696085 226659147119117201711627)
                  ·
                    rfl

theorem cell23_3972754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 3, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 3, 1, 2, 1, 7].length) (baseStart_3972754 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3972754 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3972754 prefixEnd_3972754 := by exact prefixLift 3972754
  have htrace : WordTrace (prefixWord ++ tailWord_3972754) baseStart_3972754 baseEnd_3972754 := by
    simpa [prefixWord, tailWord_3972754, baseEnd_3972754] using wordTrace_append hprefix tailTrace_3972754
  have hstable : (prefixWord ++ tailWord_3972754).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3972754).length < 2 ^ (prefixWord ++ tailWord_3972754).sum := by decide
  have hdescent : baseEnd_3972754 < baseStart_3972754 := by decide
  rcases family_descends (prefixWord ++ tailWord_3972754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3972757 : List Nat := [1, 3, 2, 1, 1, 1, 1, 3, 1, 7, 2]
def baseStart_3972757 : Nat := 118140960795 + 3972757 * 2 ^ 59
def prefixEnd_3972757 : Nat := 4983230072969 + 3 ^ 40 * 3972757 * 2
def baseEnd_3972757 : Nat := 2039933864514018303667129

theorem tailTrace_3972757 : CollatzResearch.WordTrace tailWord_3972757 prefixEnd_3972757 2039933864514018303667129 := by
  unfold tailWord_3972757
  simp only [CollatzResearch.WordTrace]
  refine ⟨144898351668387356723132525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96598901112258237815421683 144898351668387356723132525)
  ·
    refine ⟨54336881875645258771174697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 144898351668387356723132525 54336881875645258771174697)
    ·
      refine ⟨40752661406733944078381023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54336881875645258771174697 40752661406733944078381023)
      ·
        refine ⟨61128992110100916117571535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40752661406733944078381023 61128992110100916117571535)
        ·
          refine ⟨91693488165151374176357303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61128992110100916117571535 91693488165151374176357303)
          ·
            refine ⟨137540232247727061264535955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91693488165151374176357303 137540232247727061264535955)
            ·
              refine ⟨206310348371590591896803933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 137540232247727061264535955 206310348371590591896803933)
              ·
                refine ⟨77366380639346471961301475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 206310348371590591896803933 77366380639346471961301475)
                ·
                  refine ⟨116049570959019707941952213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 77366380639346471961301475 116049570959019707941952213)
                  ·
                    refine ⟨2719911819352024404889505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 116049570959019707941952213 2719911819352024404889505)
                    ·
                      refine ⟨2039933864514018303667129, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2719911819352024404889505 2039933864514018303667129)
                      ·
                        rfl

theorem cell23_3972757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 3, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 3, 1, 7, 2].length) (baseStart_3972757 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3972757 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3972757 prefixEnd_3972757 := by exact prefixLift 3972757
  have htrace : WordTrace (prefixWord ++ tailWord_3972757) baseStart_3972757 baseEnd_3972757 := by
    simpa [prefixWord, tailWord_3972757, baseEnd_3972757] using wordTrace_append hprefix tailTrace_3972757
  have hstable : (prefixWord ++ tailWord_3972757).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3972757).length < 2 ^ (prefixWord ++ tailWord_3972757).sum := by decide
  have hdescent : baseEnd_3972757 < baseStart_3972757 := by decide
  rcases family_descends (prefixWord ++ tailWord_3972757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3972787 : List Nat := [1, 1, 1, 2, 3, 3, 2, 3, 2, 1, 4]
def baseStart_3972787 : Nat := 118140960795 + 3972787 * 2 ^ 59
def prefixEnd_3972787 : Nat := 4983230072969 + 3 ^ 40 * 3972787 * 2
def baseEnd_3972787 : Nat := 2039949268933653186291991

theorem tailTrace_3972787 : CollatzResearch.WordTrace tailWord_3972787 prefixEnd_3972787 2039949268933653186291991 := by
  unfold tailWord_3972787
  simp only [CollatzResearch.WordTrace]
  refine ⟨144899445858278671846724615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96599630572185781231149743 144899445858278671846724615)
  ·
    refine ⟨217349168787418007770086923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144899445858278671846724615 217349168787418007770086923)
    ·
      refine ⟨326023753181127011655130385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 217349168787418007770086923 326023753181127011655130385)
      ·
        refine ⟨244517814885845258741347789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 326023753181127011655130385 244517814885845258741347789)
        ·
          refine ⟨91694180582191972028005421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 244517814885845258741347789 91694180582191972028005421)
          ·
            refine ⟨34385317718321989510502033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 91694180582191972028005421 34385317718321989510502033)
            ·
              refine ⟨25788988288741492132876525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34385317718321989510502033 25788988288741492132876525)
              ·
                refine ⟨9670870608278059549828697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25788988288741492132876525 9670870608278059549828697)
                ·
                  refine ⟨7253152956208544662371523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9670870608278059549828697 7253152956208544662371523)
                  ·
                    refine ⟨10879729434312816993557285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7253152956208544662371523 10879729434312816993557285)
                    ·
                      refine ⟨2039949268933653186291991, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10879729434312816993557285 2039949268933653186291991)
                      ·
                        rfl

theorem cell23_3972787_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 2, 3, 2, 1, 4].length) (baseStart_3972787 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3972787 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3972787 prefixEnd_3972787 := by exact prefixLift 3972787
  have htrace : WordTrace (prefixWord ++ tailWord_3972787) baseStart_3972787 baseEnd_3972787 := by
    simpa [prefixWord, tailWord_3972787, baseEnd_3972787] using wordTrace_append hprefix tailTrace_3972787
  have hstable : (prefixWord ++ tailWord_3972787).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3972787).length < 2 ^ (prefixWord ++ tailWord_3972787).sum := by decide
  have hdescent : baseEnd_3972787 < baseStart_3972787 := by decide
  rcases family_descends (prefixWord ++ tailWord_3972787) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3972804 : List Nat := [2, 3, 3, 1, 1, 1, 3, 2, 2, 1, 4]
def baseStart_3972804 : Nat := 118140960795 + 3972804 * 2 ^ 59
def prefixEnd_3972804 : Nat := 4983230072969 + 3 ^ 40 * 3972804 * 2
def baseEnd_3972804 : Nat := 2039957998104779619779413

theorem tailTrace_3972804 : CollatzResearch.WordTrace tailWord_3972804 prefixEnd_3972804 2039957998104779619779413 := by
  unfold tailWord_3972804
  simp only [CollatzResearch.WordTrace]
  refine ⟨72450032949608541875046733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96600043932811389166728977 72450032949608541875046733)
  ·
    refine ⟨27168762356103203203142525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 72450032949608541875046733 27168762356103203203142525)
    ·
      refine ⟨10188285883538701201178447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27168762356103203203142525 10188285883538701201178447)
      ·
        refine ⟨15282428825308051801767671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10188285883538701201178447 15282428825308051801767671)
        ·
          refine ⟨22923643237962077702651507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15282428825308051801767671 22923643237962077702651507)
          ·
            refine ⟨34385464856943116553977261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22923643237962077702651507 34385464856943116553977261)
            ·
              refine ⟨12894549321353668707741473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34385464856943116553977261 12894549321353668707741473)
              ·
                refine ⟨9670911991015251530806105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12894549321353668707741473 9670911991015251530806105)
                ·
                  refine ⟨7253183993261438648104579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9670911991015251530806105 7253183993261438648104579)
                  ·
                    refine ⟨10879775989892157972156869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7253183993261438648104579 10879775989892157972156869)
                    ·
                      refine ⟨2039957998104779619779413, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10879775989892157972156869 2039957998104779619779413)
                      ·
                        rfl

theorem cell23_3972804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 3, 2, 2, 1, 4].length) (baseStart_3972804 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3972804 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3972804 prefixEnd_3972804 := by exact prefixLift 3972804
  have htrace : WordTrace (prefixWord ++ tailWord_3972804) baseStart_3972804 baseEnd_3972804 := by
    simpa [prefixWord, tailWord_3972804, baseEnd_3972804] using wordTrace_append hprefix tailTrace_3972804
  have hstable : (prefixWord ++ tailWord_3972804).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3972804).length < 2 ^ (prefixWord ++ tailWord_3972804).sum := by decide
  have hdescent : baseEnd_3972804 < baseStart_3972804 := by decide
  rcases family_descends (prefixWord ++ tailWord_3972804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3972904 : List Nat := [2, 1, 5, 1, 1, 2, 2, 2, 1, 6]
def baseStart_3972904 : Nat := 118140960795 + 3972904 * 2 ^ 59
def prefixEnd_3972904 : Nat := 4983230072969 + 3 ^ 40 * 3972904 * 2
def baseEnd_3972904 : Nat := 680003115390076409509651

theorem tailTrace_3972904 : CollatzResearch.WordTrace tailWord_3972904 prefixEnd_3972904 680003115390076409509651 := by
  unfold tailWord_3972904
  simp only [CollatzResearch.WordTrace]
  refine ⟨72451856599427400414366883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96602475465903200552489177 72451856599427400414366883)
  ·
    refine ⟨108677784899141100621550325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72451856599427400414366883 108677784899141100621550325)
    ·
      refine ⟨10188542334294478183270343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 108677784899141100621550325 10188542334294478183270343)
      ·
        refine ⟨15282813501441717274905515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10188542334294478183270343 15282813501441717274905515)
        ·
          refine ⟨22924220252162575912358273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15282813501441717274905515 22924220252162575912358273)
          ·
            refine ⟨17193165189121931934268705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22924220252162575912358273 17193165189121931934268705)
            ·
              refine ⟨12894873891841448950701529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17193165189121931934268705 12894873891841448950701529)
              ·
                refine ⟨9671155418881086713026147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12894873891841448950701529 9671155418881086713026147)
                ·
                  refine ⟨14506733128321630069539221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9671155418881086713026147 14506733128321630069539221)
                  ·
                    refine ⟨680003115390076409509651, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14506733128321630069539221 680003115390076409509651)
                    ·
                      rfl

theorem cell23_3972904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 2, 2, 2, 1, 6].length) (baseStart_3972904 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3972904 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3972904 prefixEnd_3972904 := by exact prefixLift 3972904
  have htrace : WordTrace (prefixWord ++ tailWord_3972904) baseStart_3972904 baseEnd_3972904 := by
    simpa [prefixWord, tailWord_3972904, baseEnd_3972904] using wordTrace_append hprefix tailTrace_3972904
  have hstable : (prefixWord ++ tailWord_3972904).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3972904).length < 2 ^ (prefixWord ++ tailWord_3972904).sum := by decide
  have hdescent : baseEnd_3972904 < baseStart_3972904 := by decide
  rcases family_descends (prefixWord ++ tailWord_3972904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3972941 : List Nat := [1, 6, 1, 2, 1, 2, 1, 1, 1, 1, 6]
def baseStart_3972941 : Nat := 118140960795 + 3972941 * 2 ^ 59
def prefixEnd_3972941 : Nat := 4983230072969 + 3 ^ 40 * 3972941 * 2
def baseEnd_3972941 : Nat := 2040028344954445583766283

theorem tailTrace_3972941 : CollatzResearch.WordTrace tailWord_3972941 prefixEnd_3972941 2040028344954445583766283 := by
  unfold tailWord_3972941
  simp only [CollatzResearch.WordTrace]
  refine ⟨144905062699720756147830677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96603375133147170765220451 144905062699720756147830677)
  ·
    refine ⟨6792424814049410444429563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 144905062699720756147830677 6792424814049410444429563)
    ·
      refine ⟨10188637221074115666644345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6792424814049410444429563 10188637221074115666644345)
      ·
        refine ⟨7641477915805586749983259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10188637221074115666644345 7641477915805586749983259)
        ·
          refine ⟨11462216873708380124974889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7641477915805586749983259 11462216873708380124974889)
          ·
            refine ⟨8596662655281285093731167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11462216873708380124974889 8596662655281285093731167)
            ·
              refine ⟨12894993982921927640596751, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8596662655281285093731167 12894993982921927640596751)
              ·
                refine ⟨19342490974382891460895127, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12894993982921927640596751 19342490974382891460895127)
                ·
                  refine ⟨29013736461574337191342691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19342490974382891460895127 29013736461574337191342691)
                  ·
                    refine ⟨43520604692361505787014037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29013736461574337191342691 43520604692361505787014037)
                    ·
                      refine ⟨2040028344954445583766283, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 43520604692361505787014037 2040028344954445583766283)
                      ·
                        rfl

theorem cell23_3972941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 2, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 2, 1, 1, 1, 1, 6].length) (baseStart_3972941 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3972941 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3972941 prefixEnd_3972941 := by exact prefixLift 3972941
  have htrace : WordTrace (prefixWord ++ tailWord_3972941) baseStart_3972941 baseEnd_3972941 := by
    simpa [prefixWord, tailWord_3972941, baseEnd_3972941] using wordTrace_append hprefix tailTrace_3972941
  have hstable : (prefixWord ++ tailWord_3972941).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3972941).length < 2 ^ (prefixWord ++ tailWord_3972941).sum := by decide
  have hdescent : baseEnd_3972941 < baseStart_3972941 := by decide
  rcases family_descends (prefixWord ++ tailWord_3972941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
